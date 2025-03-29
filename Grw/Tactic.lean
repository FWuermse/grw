import Lean.Elab.Tactic
import Lean.Elab.Term
import Grw.Attribute
import Grw.Morphism
import Grw.Eauto
import Grw.PaperTactic
import Batteries

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.Elab.Term
open Attribute

namespace Tactic

/--
The result of a rewrite.

`rewCar` is the carrier relation.
`rewMVars` are constraints that result throughout the algorithm.
-/
structure RewriteResultInfo where
  rewCar : Expr
  rewFrom : Expr
  rewTo : Expr
  rewPrf : Expr
  rewMVars : List Expr
  deriving BEq, Repr

/--
The Information about the hypothesis uses in a rewrite (e.g. `h` for `grewrite [h]`).

`prf`: Proof of the term (`h` in the above rewrite).
`prf` must be of type `∀ ci,...,cj, r c1 c2` and the type of c1 and c2 is the carrier `car`. When variables are telescoped and not reassigned not during unification those locally bound vars are stored in `holes`.
-/
structure HypInfo where
  prf : Expr
  car : Expr
  rel : Expr
  sort : Bool -- Even required? Does it matter in Lean?
  c1 : Expr -- Lhs of rel
  c2 : Expr -- Rhs of rel
  holes : List MVarId

private def toHypInfo (term : Expr) : MetaM HypInfo := do
  let T ← inferType term
  match T with
  | .app (.app r lhs) rhs => do
    pure ⟨term, ← inferType lhs, r, lhs.isSort, lhs, rhs, []⟩
  | .forallE _ _ (.app (.app _ _) _) _ => do
    -- TODO: recursive approach. Current approach only works for one bvar in Pi
    let (exprs, _, .app (.app r lhs) rhs) ← forallMetaTelescope T | throwError "MetaTelescope broke structure of rw lemma"
    let subgoals := exprs.map fun e => e.mvarId!
    pure ⟨← mkAppM' term exprs, ← inferType lhs, r, lhs.isSort, lhs, rhs, subgoals.toList⟩
  | _ => throwError "The given rewrite hypothesis {term}:{T} must be of the form ∀ Φs, R αs t u."

/--
`fail` not clear right now
`id` is when we don't rewrite because no subterm can't be unified (ATOM or binary APP).
`success` successful subterm rewrite.
-/
inductive RewriteResult where
  | fail
  | id
  | success (r : RewriteResultInfo)

abbrev RWM  := ReaderT HypInfo MetaM <| List MVarId × RewriteResult

private def srep : Nat → String
  | n => n.fold (fun _ _ s => s ++ "  ") ""

-- TODO: don't bother tracking the subgoals not to be solved via TCR. Lean will do that automatically.
private def unify (Ψ : List MVarId) (t : Expr) (l2r : Bool) : RWM  := do
  let ρ ← read
  let lhs := if l2r then ρ.c1 else ρ.c2
  let rhs := if l2r then ρ.c2 else ρ.c1
  -- Take all initial holes and add collect the ones not reassigned to make them subgoals for the user to solve.
  if ← isDefEq lhs t then
    let subgoals ← ρ.holes.filterM fun mv => do pure !(← mv.isAssignedOrDelayedAssigned)
    pure (Ψ, .success ⟨ρ.rel, t, rhs, ρ.prf, subgoals.map mkMVar⟩)
  else
    pure (Ψ, .id)

/--
Note from paper:
The variant unify∗ ρ(Γ, Ψ, τ ) tries unification on all subterms and succeeds if at least one
unification does. The function unify(Γ, Ψ, t, u) does a standard unification of t and u.
-/
private def unifyStar (Ψ : List MVarId) (t : Expr) (l2r : Bool) : RWM := do
  let ρ ← read
  let lhs := if l2r then ρ.c1 else ρ.c2
  let rhs := if l2r then ρ.c2 else ρ.c1
  let b ← IO.mkRef false
  forEachExpr t fun t' => do
    b.set <| (← isDefEq lhs t') || (← b.get)
  if ← b.get then
    let subgoals ← ρ.holes.filterM fun mv => do pure !(← mv.isAssignedOrDelayedAssigned)
    pure (Ψ, RewriteResult.success ⟨ρ.rel, t, rhs, ρ.prf, subgoals.map mkMVar⟩)
  else
    pure (Ψ, .id)

private def respectfulN (mvars : List Expr) : MetaM  Expr :=
  match mvars with
  | x :: [] => pure x
  | x :: xs => do mkAppM ``respectful #[x, ← respectfulN xs]
  | _ => throwError "Cannot create empty respectful chain."

/--
We use this inference function whenever we failed passing the expected relation (←) or (→).
This can happend if the algorithm immediately unifies and returns for instance.
-/
private def subrelInference (p : Expr) (r : Expr) (desiredRel : Expr) : MetaM (Expr × Expr × List MVarId) := do
  if r == desiredRel then
    pure (p, desiredRel, [])
  else
    let constraint ← mkFreshExprMVar <| ← mkAppM ``Subrel #[r, desiredRel]
    let prf ← mkAppOptM ``Subrel.subrelation #[none, r, desiredRel, constraint, none, none, p]
    pure (prf, desiredRel, [constraint.mvarId!])

/--
`rew` always succeeds and returns a tuple (Ψ, R, τ', p) with the output constraints, a relation R, a new term τ' and a proof p : R τ τ'. In case no rewrite happens we can just have an application of ATOM.
This output tuple represents the proof sekelton that is used in the proof search.
-/
partial def subterm (Ψ : List MVarId) (t : Expr) (desiredRel : Option Expr) (l2r : Bool) (depth : Nat) : RWM  := do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"{srep <| depth}subterm Ψ ({t}) ρ") do
  let ρ ← read
  if let (Ψ', .success res) ← unify Ψ t l2r ρ then
    trace[Meta.Tactic.grewrite] "{srep depth} |UNIFY⇓ {res.rewFrom} ↝ {res.rewTo}"
    return (Ψ', .success res)
  match t with
  /-
  We iterate over the args of an app and build a proof for Proper (prf arg₁ ==> ... ==> prf argₙ) f.
  If the first arguments are all id we can optimize the proof by leaving this part of an app composed e.g.:
  Proper (prf arg₃ ==> ... ==> prf argₙ) (f arg₁ arg₂)

  In case we want to rewrite f directly we have to use a different approach. In that case we chain all arguments in a pointwise_relation and conclude with a final subrelation. Note the invariant that a rewrite on f implies that ρ cannot be applied to any of f's arguments directly but possibly its subterms.

  Ψ collects the constraints (holes in the proof).
  respectfulList collects info about recursive rewrites on the app args.
  -/
  | .app f _ => do
    let Tf ← whnf <| ← inferType f
    if let .some (_, _) := Tf.arrow? then
      let mut fn := f.getAppFn
      let appArgs ← t.getAppArgs.mapM fun t => do pure (t, ← inferType t)
      let mut prefixId := true
      let mut Ψ := Ψ
      let mut respectfulList := []
      let mut prfArgs := []
      let mut rewMVars := []
      let mut u := fn
      -- If ρ matches f of an application f a b then ρ cannot match any other aplicant directly
      if let (_, .success res) ← unify Ψ fn l2r ρ then
        let rel ← mkFreshExprMVar <| ← mkAppM ``relation #[← inferType t]
        let prf ← appArgs.foldrM (fun (_, T) acc => mkAppM ``pointwiseRelation #[T, acc]) rel
        let sub ← mkFreshExprMVar <| ← mkAppM ``Subrel #[res.rewCar, prf]
        let p ← mkAppOptM ``Subrel.subrelation <| #[none, none, none, sub, none, none, res.rewPrf] ++ appArgs.map fun (t, _) => .some t
        u := mkAppN res.rewTo <| appArgs.map Prod.fst
        let (Ψ'', snd) ← subterm Ψ u desiredRel l2r (depth + 1)
        -- TODO: include both shadowed rels in psi
        if let .success res := snd then do
          let desiredRel := match desiredRel with
          | some r => r
          | none => rel
          let (p₁, rel, Ψ₁) ← subrelInference p rel desiredRel
          let (p₂, _, Ψ₂) ← subrelInference res.rewPrf res.rewCar desiredRel
          -- Invariant: all desired rels are Prop and transitive and res is of desired rel
          let tr ← mkFreshExprMVar <| ← mkAppOptM ``Transitive #[none, rel]
          let p ← mkAppOptM ``Transitive.trans #[none, none, tr, t, u, res.rewTo, p₁, p₂]
          trace[Meta.Tactic.grewrite] "{srep depth} |APP - MULTI f RW {t}"
          return (Ψ ++ Ψ'' ++ Ψ₁ ++ Ψ₂ ++ [tr.mvarId!], .success ⟨rel, t, res.rewTo, p, []⟩)
        trace[Meta.Tactic.grewrite] "{srep depth} |APP - SINGLE f RW {t}"
        return (Ψ ++ [rel.mvarId!], .success ⟨rel, t, u, p, []⟩)
      for (t, T) in appArgs do
        let desiredRel ← mkFreshExprMVar <| ← mkAppM ``relation #[T]
        let (Ψ', res) ← subterm Ψ t desiredRel l2r (depth+1) ρ
        if prefixId then
          if let .id := res then
            -- If id happens at the beginning of an app we don't need to consider it
            fn := .app fn t
            u := .app u t
            continue
          else
            -- As soon as we hit a success rw we need to include further ids in the overall proof
            prefixId := false
        let _ ← match res with
        | .id =>
          let rel ← mkFreshExprMVar <| ← mkAppM ``relation #[T]
          let proxy ← mkFreshExprMVar <| ← mkAppM ``ProperProxy #[rel, t]
          let proxyPrf ← mkAppOptM ``ProperProxy.proxy #[none, none, none, proxy]
          respectfulList := respectfulList ++ [rel]
          Ψ := Ψ ++ [rel.mvarId!, proxy.mvarId!]
          prfArgs := prfArgs ++ [proxyPrf]
          u := .app u t
        | .success rew =>
          respectfulList := respectfulList ++ [rew.rewCar]
          Ψ := Ψ ++ Ψ'
          prfArgs := prfArgs ++ [rew.rewPrf]
          u := .app u rew.rewTo
          rewMVars := rew.rewMVars ++ rewMVars
        | .fail => return (Ψ, .fail)
      if prefixId then
        trace[Meta.Tactic.grewrite] "{srep depth} |APP - ALL ID {t}"
        return (Ψ, .id)
      let rel ← match desiredRel with
      | .some rel => pure rel
      -- TODO: is it ever none?
      | .none => mkFreshExprMVar <| ← mkAppM ``relation #[appArgs.toList.getLast!.snd]
      respectfulList := respectfulList ++ [rel]
      let respectful ← respectfulN respectfulList
      let prp ← mkFreshExprMVar <| ← mkAppM ``Proper #[respectful, fn]
      let prfs := prfArgs.toArray.flatMap (#[none, none, .some .])
      let p ← mkAppOptM ``Proper.proper <| #[none, none, none, prp] ++ prfs
      if rel.isMVar then
        Ψ := Ψ ++ [rel.mvarId!]
      trace[Meta.Tactic.grewrite] "{srep depth} |APP {t}"
      return (Ψ ++ [prp.mvarId!], .success ⟨respectfulList.getLast!, t, u, p, rewMVars⟩)
    else
      pure (Ψ, .id)
  | .lam n T _b i => do
    trace[Meta.Tactic.grewrite] "{srep depth} |LAM {t}"
    lambdaTelescope t fun _xs b => do
      let (Ψ, .success ⟨S, _, b, p, subgoals⟩) ← subterm Ψ b none l2r (depth+1) ρ | return (Ψ, .id)
      let car ← match ← inferType S with
      | .forallE _ T _ _ => pure T -- TODO: test this case
      | .app _ car => pure car
      | _ => throwError m!"{S} in {t} must be a relation."
      let S ← mkAppM ``pointwiseRelation #[car, S]
      let p := .lam n T p i
      let u := .lam n T b i
      pure (Ψ, .success ⟨S, t, u, p, subgoals⟩)
  | .forallE n T b i => do
    if let .some (α, β) := t.arrow? then
      trace[Meta.Tactic.grewrite] "{srep depth} |Arrow {t}"
      let (Ψ, .success ⟨S, _, b, p, subgoals⟩) ← subterm Ψ (mkApp2 (mkConst ``impl) α β) desiredRel l2r (depth+1) | pure (Ψ, .id)
      let .app (.app _ α) β := b | throwError "Rewrite of `Impl α β` resulted in a different (thus wrong) type."
      let u ← mkArrow α β
      return (Ψ, .success ⟨S, t, u, p, subgoals⟩)
    else
      trace[Meta.Tactic.grewrite] "{srep depth} |PI {t}"
      let (Ψ', res) ← unifyStar Ψ T l2r
      match res with
      | .success info => return (Ψ', .success info)
      | .id =>
        let (Ψ, .success ⟨S, _, .app _ (.lam n T b i), p, subgoals⟩) ← subterm Ψ (← mkAppM ``all #[T, .lam n T b i]) none l2r (depth+1)
          | throwError "Rewrite of `all λ x ↦ y` resulted in a different (thus wrong) type."
        let u := .forallE n T b i
        pure (Ψ, .success ⟨S, t, u, p, subgoals⟩)
      | .fail => return (Ψ, .fail)
  | _ => do
    trace[Meta.Tactic.grewrite] "{srep depth} |ATOM {t}"
    pure (Ψ, .id)

/--
See (https://github.com/coq/coq/pull/13969)[Coq]
-/
private def inferRelation (goal : MVarId) (name : Name) : MetaM <| List MVarId := do
  let type ← goal.getType
  let .app (.const ``relation _) (.sort 0) := type | throwError "Cannot infer relation"
  goal.apply <| ← mkConstWithFreshMVarLevels name

private def solveRespectfulN (goal : MVarId) : MetaM MVarId := do
  -- check if goal is isolated respectful chain
  let type ← goal.getType
  let isLam := (← whnf type.getAppFn).isLambda
  let type ← inferType type.getAppFn
  if let .app (.const ``relation _) arrow := type then
    if (← whnf arrow).arrow?.isSome && isLam then
      let subgoal ← unfoldTarget goal ``respectful
      let subgoal ← subgoal.intros
      return subgoal.snd
  throwError m!"{type} is not of type (τ₀ ⟹ ... ⟹ τₙ)"

private def unfoldName (name : Name) (goal : MVarId) : MetaM MVarId := do
  let type ← goal.getType
  let hasFlip := type.find? (
    match . with
    | .const n _ => n == name
    | _ => false)
  if hasFlip.isSome then
    return ← unfoldTarget goal name
  throwError m!"No definition {name} occurs in term {type}"

private def unfoldSymRflTran (goal : MVarId) : MetaM MVarId := do
  for constructor in [``Reflexive.mk, ``Symmetric.mk, ``Transitive.mk] do
    try
      let unfoldRefl := mkConstWithFreshMVarLevels constructor
      let subgoals ← commitIfNoEx do goal.apply (← unfoldRefl)
      let subgoals ← subgoals.mapM MVarId.intros
      -- TODO: does invariant subgoal.length == 1 hold?
      return subgoals.get! 0 |>.snd
    catch _ =>
      continue
  throwError "All constructors failed"

abbrev NewGoalsM := MetaM <| List MVarId

private def tryTactic (subgoals : List MVarId) (name : String) (tactic : MVarId → MetaM MVarId) : NewGoalsM := do
  let mut subgoals := subgoals
  for goal in subgoals do
    try
      let unfolded ← tactic goal
      subgoals := subgoals.replace goal unfolded
      trace[Meta.Tactic.grewrite]m!"✅️ applied tactic {name} on {← goal.getType}, now: {← unfolded.getType}"
    catch _ =>
      trace[Meta.Tactic.grewrite]m!"No progress with {name}: {← goal.getType}"
  return subgoals

private def tryHyp (goal : MVarId) (hyp : Expr) : MetaM <| Except MVarId <| List MVarId := do
  let mut subgoals := []
  try
    subgoals ← goal.apply hyp
    trace[Meta.Tactic.grewrite]m!"✅️ applied hint {hyp}"
    return .ok subgoals
  catch e =>
    trace[Meta.Tactic.grewrite]m!"\t❌️ Could not apply hint: \n\t {e.toMessageData}"
    return .error goal

private def relCmp (a b : Expr) : MetaM Bool := do
  let T₁ ← match a with
  | .app (.const ``relation _) T => pure T
  | .forallE _ T (.forallE _ T' b _) _ =>
    if T == T' && b == .sort 0 then
      pure T
    else
      return false
  | _ => return false
  let T₂ ← match b with
  | .app (.const ``relation _) T => pure T
  | .forallE _ T (.forallE _ T' b _) _ =>
    if T == T' && b == .sort 0 then
      pure T
    else
      return false
  | _ => return false
  return T₁ == T₂

private def tryClose (goals : List MVarId) : TacticM Bool := do
  for goal in goals do
    try
      goal.assumption
      trace[Meta.Tactic.grewrite]m!"✅️ assumption solved goal {← goal.getType}"
    catch _ =>
      trace[Meta.Tactic.grewrite]m!"❌️ Assumption on {← goal.getType} failed"
  if goals.isEmpty then
    trace[Meta.Tactic.grewrite]"🏁 no more open goals"
    return true
  /-
  TODO: store tactics based on what they could possibly simplify (e.G. Proper for solveProper)
  Check mathlib for tactic registration. (see Lean.registerTagAttribute, persistantEnvExtension)
  Env extension as discrtree (check simp attribute)
  serialise Discrtree keys
  -/
  let mut subgoals := goals
  subgoals ← tryTactic subgoals "unfoldSRT" (unfoldSymRflTran)
  subgoals ← tryTactic subgoals "⟹...⟹" (solveRespectfulN)
  subgoals ← tryTactic subgoals "unfold flip" (unfoldName ``flip)
  subgoals ← tryTactic subgoals "unfold impl" (unfoldName ``impl)
  let sc ← Simp.Context.mkDefault
  subgoals ← tryTactic subgoals "simp_all" fun g => do
    match ← simpAll g sc with
    | (.some r, _) => pure r
    | (_, _) => throwError "simp_all made no progress"
  if subgoals.isEmpty then
    trace[Meta.Tactic.grewrite]"🏁 no more open goals"
    return true
  else
    return false

private partial def dfs (goals : List MVarId) (hintDB : DiscrTree Name) (ρ : HypInfo) : TacticM (List MVarId) := do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"search") do
  if goals.isEmpty then
    return []
  let mut (next, rest) := goals.splitAt 1
  let goal := next.get! 0
  let goalType ← goal.getType
  trace[Meta.Tactic.grewrite]m!"trying goal: {goalType}"
  let matchingHintNames ← hintDB.getMatch goalType
  let mut subgoals := []
  -- If we're trying to solve a goal of the type of ρ.rel it may be useful to try ρ.rel
  if ← relCmp goalType (← inferType ρ.rel) then
    let s ← saveState
    let res ← tryHyp goal ρ.rel
    match res with
    | .ok sg =>
      subgoals ← dfs (sg ++ rest) hintDB ρ
      if (← tryClose subgoals) then
        return []
      else if ← goal.isAssignedOrDelayedAssigned then
        subgoals ← dfs (sg ++ rest) hintDB ρ
      else
        restoreState s
    | .error _ => pure ()
  for name in matchingHintNames do
    let s ← saveState
    let matchingHint ← mkConstWithFreshMVarLevels name
    trace[Meta.Tactic.grewrite]m!"⏩ goal {goalType} matches hint: {matchingHint}"
    let res ← tryHyp goal matchingHint
    match res with
    | .ok sg =>
      subgoals ← dfs (sg ++ rest) hintDB ρ
      if (← tryClose subgoals) then
        return []
      else if ← goal.isAssignedOrDelayedAssigned then
        subgoals ← dfs (sg ++ rest) hintDB ρ
      else
        restoreState s
    | .error _ => pure ()
  subgoals ← dfs (rest) hintDB ρ
  let _ ← tryClose subgoals
  return goals

def search (Ψ : List MVarId) (prf : Expr) (ρ : HypInfo) (d : Option LocalDecl) : TacticM Unit := do
  let env ← getEnv
  let mut hintDB := dbEx.getState env
  -- See (https://github.com/coq/coq/pull/13969)[Coq]
  -- Outsource
  let rels := [``Iff, ``impl, ``Eq, ``flip]
  for rel in rels do
    hintDB ← hintDB.insert (← mkAppM ``relation #[.sort 0]) rel
  let _ ← dfs Ψ hintDB ρ
  if let .some d := d then
    let goal ← getMainGoal
    let newExpr := Expr.app prf d.toExpr
    let (_, goal) ← goal.assertHypotheses #[{userName := d.userName, type := ← inferType newExpr, value := newExpr}]
    -- Check other APIs to preserve sequence (may me part of the Hypotheses APIs)
    let goal ← goal.tryClear d.fvarId
    replaceMainGoal [goal]
  else
    let goal ← getMainGoal
    let mut subgoals ← goal.apply (← instantiateMVars prf)
    subgoals ← tryTactic subgoals "unfold flip" (unfoldName ``flip)
    subgoals ← tryTactic subgoals "unfold impl" (unfoldName ``impl)
    subgoals ← tryTactic subgoals "unfold impl" (unfoldName ``all)
    replaceMainGoal subgoals

private def nopSearch (Ψ : List MVarId) (p : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let subgoals ← goal.apply (← instantiateMVars p)
  replaceMainGoal subgoals

declare_syntax_cat rw
syntax ("←")? ident : rw

declare_syntax_cat rewrite
syntax "grewrite" "[" rw,+ "]" ("at" ident)? : rewrite

def algorithm (ps : TSyntax `rewrite) : TacticM Unit := withMainContext do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"algorithm") do
  let (ps, id) ← match ps with
  | `(rewrite| grewrite [$ps:rw,*] at $id:ident) => pure (ps, .some id.getId)
  | `(rewrite| grewrite [$ps:rw,*]) => pure (ps, Option.none)
  | _ => throwError "Unsupported syntax"
  let lctx ← getLCtx
  -- Confirm all passed lemmas are in the local context
  let mut args : List (Expr × Name × Bool × TSyntax `rw) := []
  let mut location : Option LocalDecl := none
  for ps' in lctx do
    if let .some id := id then
      if ps'.userName == id then
      location := ps'
  for p in ps.getElems do
    let (id, l2r) ← match p with
    | `(rw|← $i:ident) => do pure (i.getId, false)
    | `(rw|$i:ident) => do pure (i.getId, true)
    | s => throwError m!"syntax {s} is invalid."
    let ld := lctx.findDecl? fun ld => if ld.userName == id then .some ld else Option.none
    if let .some ld := ld then
      args := args.insert (ld.toExpr, ld.userName, l2r, p)
    else
      let expr ← mkConstWithFreshMVarLevels id
      args := args.insert (expr, id, l2r, p)
  for (expr, name, l2r, stx) in args do
    let goal ← getMainGoal
    let goalType ← match location with
    | none => do goal.getType
    | some l => do inferType l.toExpr
    let Ψ := []
    let ρ ← toHypInfo expr
    let desired : Expr ← match location with
    | none => do mkAppM ``flip #[mkConst ``impl]
    | some _ => do pure <| Lean.mkConst ``impl
    let (Ψ, res) ← subterm Ψ goalType desired l2r 0 ρ
    match res with
    | .id => logWarningAt stx m!"Nothing to rewrite for {name}."
    | .fail => logError "Rewrite failed to generate constraints."
    | .success ⟨r, t, u, p, _subgoals⟩ =>
      -- TODO: set subgoals
      let (p, r, Ψ') ← subrelInference p r desired
      let Ψ := Ψ' ++ Ψ
      withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"constraints") do
        trace[Meta.Tactic.grewrite]m!"{← Ψ.mapM (·.getType)}"
      withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"proof") do
        trace[Meta.Tactic.grewrite]m!"{p}"
      search Ψ p ρ location

elab rw:rewrite : tactic =>
  algorithm rw

declare_syntax_cat grw_assert
syntax "assert_constraints" "[" rw,+ "]" ("at" ident)? : grw_assert

/-
This function just mimics the rewrite algorithm and compares the output of the constraint generation algorithm with the provided constraints `ts`.
-/
private def assertConstraints (ps : TSyntax `grw_assert) (ts : Syntax.TSepArray `term ",") : TacticM Unit := withMainContext do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"algorithm") do
  let (ps, id) ← match ps with
  | `(grw_assert| assert_constraints [$ps:rw,*] at $id:ident) => pure (ps, .some id.getId)
  | `(grw_assert| assert_constraints [$ps:rw,*]) => pure (ps, Option.none)
  | _ => throwError "Unsupported syntax"
  let lctx ← getLCtx
  -- Confirm all passed lemmas are in the local context
  let mut args : List (Expr × Name × Bool × TSyntax `rw) := []
  let mut location : Option LocalDecl := none
  for ps' in lctx do
    if let .some id := id then
      if ps'.userName == id then
      location := ps'
  for p in ps.getElems do
    let (id, l2r) ← match p with
    | `(rw|← $i:ident) => do pure (i.getId, false)
    | `(rw|$i:ident) => do pure (i.getId, true)
    | s => throwError m!"syntax {s} is invalid."
    let ld := lctx.findDecl? fun ld => if ld.userName == id then .some ld else Option.none
    if let .some ld := ld then
      args := args.insert (ld.toExpr, ld.userName, l2r, p)
    else
      let expr ← mkConstWithFreshMVarLevels id
      args := args.insert (expr, id, l2r, p)
  for (expr, name, l2r, stx) in args do
    let goal ← getMainGoal
    let goalType ← match location with
    | none => do goal.getType
    | some l => do inferType l.toExpr
    let Ψ := []
    let ρ ← toHypInfo expr
    let desired : Expr ← match location with
    | none => do mkAppM ``flip #[mkConst ``impl]
    | some _ => do pure <| Lean.mkConst ``impl
    let (Ψ, res) ← subterm Ψ goalType desired l2r 0 ρ
    match res with
    | .id => logWarningAt stx m!"Nothing to rewrite for {name}."
    | .fail => logError "Rewrite failed to generate constraints."
    | .success ⟨r, t, u, p, _subgoals⟩ =>
      -- TODO: set subgoals
      let (p, r, Ψ') ← subrelInference p r desired
      let Ψ := Ψ' ++ Ψ
      let ts ← ts.getElems.mapM (fun t => do Elab.Tactic.elabTerm t.raw none)
      let Ψ ← Ψ.mapM (fun e => do e.getType)
      for (e, i) in Ψ.zipIdx do
        if ← isDefEq e <| ts.get! i then
          continue
        else
          throwError "Constraints don't match at idx: {i}, {e} ≠ {ts.get! i}"
      -- Check if p can be applied
      let _ ← withoutModifyingState do
        let _ ← goal.apply p
        -- TODO: maybe check resulting type of first goal with some given "expected" type

elab rw:grw_assert t:term,+ ";": tactic =>
  assertConstraints rw t

end Tactic
