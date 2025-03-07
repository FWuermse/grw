import Lean.Elab.Tactic
import Grw.Morphism
import Grw.Eauto
import Grw.PaperTactic
import Batteries
import Aesop

open Lean
open Lean.Meta
open Lean.Elab.Tactic

set_option trace.aesop true
set_option trace.aesop.ruleSet true

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
  | _ => throwError "The given rewrite hypothesis {term} must be of the form ∀ Φs, R αs t u."

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
    pure (Ψ, RewriteResult.success ⟨ρ.rel, t, rhs, ρ.prf, subgoals.map mkMVar⟩)
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

private def atom (Ψ : List MVarId) (t : Expr) (r2l : Bool) : RWM  := do
  -- TODO probably a duplicate check.
  if let (Ψ, .success res) ← unifyStar Ψ t r2l then
    return (Ψ, .success res)
  let T ← inferType t
  let S ← mkFreshExprMVar <| ← mkAppM ``relation #[T]
  let m ← mkFreshExprMVar <| ← mkAppM ``Proper #[S, t]
  -- TODO confirm below line
  let p ← mkAppOptM ``Proper.proper #[none, none, none, m]
  -- paper says include S.mvardId! But those will implicitly reappear when setting new goals
  return (Ψ ∪ [m.mvarId!], .success ⟨S, t, t, p, []⟩)

private def respectfulN (mvars : List Expr) : MetaM  Expr :=
  match mvars with
  | x :: [] => pure x
  | x :: xs => do mkAppM ``respectful #[x, ← respectfulN xs]
  | _ => throwError "Cannot create empty respectful chain."

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
          Ψ := Ψ ∪ [proxy.mvarId!, rel.mvarId!]
          prfArgs := prfArgs ++ [proxyPrf]
          u := .app u t
        | .success rew =>
          logInfo m!"Proof arg {t}: {rew.rewPrf}"
          respectfulList := respectfulList ++ [rew.rewCar]
          Ψ := Ψ' ∪ Ψ
          prfArgs := prfArgs ++ [rew.rewPrf]
          u := .app u rew.rewTo
          rewMVars := rew.rewMVars ++ rewMVars
        | .fail => return (Ψ, .fail)
      if prefixId then
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
      logInfo m!"Resulting proof: {p}"
      trace[Meta.Tactic.grewrite] "{srep depth} |APP {t}"
      return (Ψ ∪ [prp.mvarId!], .success ⟨respectfulList.getLast!, t, u, p, rewMVars⟩)
    else
      atom Ψ t l2r
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
      | .fail => return (Ψ , .fail)
  | _ => do
    trace[Meta.Tactic.grewrite] "{srep depth} |ATOM {t}"
    pure (Ψ, .id)

def aesopSearch (Ψ : List MVarId) (p : Expr) : TacticM Unit := do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"proofSearch") do
  trace[Meta.Tactic.grewrite] "{Ψ}"
    let mut progress := true
    while progress do
      -- Bruteforce approach just for testing purposes.
      progress := false
      for goal in Ψ do
        try
          let rs ← Aesop.Frontend.getGlobalRuleSet `grewrite
          let options : Aesop.Options := {strategy := Aesop.Strategy.depthFirst, enableSimp := false, enableUnfold := false, useDefaultSimpSet := false}
          let rs ← Aesop.mkLocalRuleSet #[rs] (← options.toOptions')
          let _ ← Aesop.search goal (ruleSet? := .some rs) (options := options)
          progress := progress || true;
        catch _ =>
          pure ()
  let goal ← getMainGoal
  let subgoals ← goal.apply (← instantiateMVars p)
  replaceMainGoal subgoals

def eautoSearch (Ψ : List MVarId) (p : Expr) : TacticM Unit := do
  -- Try to solve the constraints with `typeclasses_eauto with grewrite`
  let success ← Eauto.eautoMain Ψ #[`grewrite] true
  if !success then
    throwError "grewrite: unable to solve constraints"

  let goal ← getMainGoal
  let subgoals ← goal.apply (← instantiateMVars p)
  replaceMainGoal subgoals

macro "pphint1" : tactic =>
  `(tactic| first
    | apply eqProperProxy
    | apply reflexiveProperProxy)

macro "pphint2" : tactic =>
  `(tactic| first
    | apply hasAssignableMVar sorry
    | apply properProperProxy)

macro "solveRespectful" : tactic =>
  `(tactic| all_goals
    (rw [respectful]
     intro _ _ H
     simp_all
     try rw [flip, impl]))

macro "solveRespectfulN" : tactic =>
  `(tactic| repeat solveRespectful)

macro "solveProper" : tactic =>
  `(tactic|
    (apply Proper.mk
     solveRespectfulN))

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
      logInfo m!"solveRespectfulN: {type}"
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

partial def dfs (goals : List MVarId) (hintDB : DiscrTree Expr) (ρ : HypInfo) : TacticM (List MVarId) := do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"search") do
  for goal in goals do
    let mut subgoals := []
    let goalType ← goal.getType
    trace[Meta.Tactic.grewrite]m!"trying goal: {goalType}"
    let mut s ← saveState
    try
      goal.assumption
      trace[Meta.Tactic.grewrite]m!"✅️ assumption solved goal {goalType}"
    catch _ =>
      trace[Meta.Tactic.grewrite]m!"❌️ Assumption on {goalType} failed"
    let matchingHints ← hintDB.getMatch goalType
    /-
    TODO: store tactics based on what they could possibly simplify (e.G. Proper for solveProper)
    Check mathlib for tactic registration. (see Lean.registerTagAttribute, persistantEnvExtension)
    Env extension as discrtree (check simp attribute)
    serialise Discrtree keys

    Paper:
    - Lean issue with Instance search
    - Why do we need tactics aswell?
    - mvars -> assigments behaviour etc.
    - Introduction mention my contribution (Paper algo, coq algo, first description of coq algo, algos equiv?, impl in lean)
    -/
    for matchingHint in matchingHints do
      trace[Meta.Tactic.grewrite]m!"⏩ goal {goalType} matches hint: {matchingHint}"
      try
        subgoals ← goal.apply matchingHint
        trace[Meta.Tactic.grewrite]m!"✅️ applied hint {matchingHint}"
        subgoals ← dfs (goals.filter (. != goal) ++ subgoals) hintDB ρ
        if subgoals.isEmpty then
          trace[Meta.Tactic.grewrite]"🏁 no more open goals"
          return subgoals
      catch e =>
        trace[Meta.Tactic.grewrite]m!"❌️ Could not apply hint"
        continue
    -- tactics:
    subgoals ← tryTactic subgoals "unfoldSRT" (unfoldSymRflTran)
    subgoals ← tryTactic subgoals "⟹...⟹" (solveRespectfulN)
    subgoals ← tryTactic subgoals "unfold flip" (unfoldName ``flip)
    subgoals ← tryTactic subgoals "unfold impl" (unfoldName ``impl)
    let sc ← Simp.Context.mkDefault
    subgoals ← tryTactic subgoals "simp_all" fun g => do
      match ← simpAll g sc with
      | (.some r, _) => pure r
      | (_, _) => throwError "simp_all made no progress"
    if !(← goal.isAssignedOrDelayedAssigned) then
      s := { s with term.meta.core.infoState := (← Elab.MonadInfoTree.getInfoState), term.meta.core.messages := (← getThe Core.State).messages }
      s.restore
  return goals

def search (Ψ : List MVarId) (prf : Expr) (ρ : HypInfo) : TacticM Unit := do
  let hints := [``reflexiveProper, ``reflexiveProperProxy, ``reflexiveReflexiveProxy, ``properAndIff, ``eqProperProxy, ``flipReflexive, ``implReflexive, ``implTransitive, ``subrelationRefl, ``iffImplSubrelation, ``iffInverseImplSubrelation]
  let hints ← hints.mapM (do mkConstWithFreshMVarLevels .)
  let mut hintDB : DiscrTree Expr := DiscrTree.empty
  for hint in hints do
    let type ← inferType hint
    let (fvars, _, type) ← forallMetaTelescope type
    hintDB ← hintDB.insert type hint
  let _ ← dfs Ψ hintDB ρ
  let goal ← getMainGoal
  let subgoals ← goal.apply (← instantiateMVars prf)
  replaceMainGoal subgoals

def nopSearch (Ψ : List MVarId) (p : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let subgoals ← goal.apply (← instantiateMVars p)
  replaceMainGoal subgoals

def subrelInference (p : Expr) (r : Expr) : MetaM (Expr × List MVarId) := do
  let flipImpl ← mkAppM ``flip #[mkConst ``impl]
  match ← inferType p with
  | .app (.app (.app (.app (.app (.app (.const ``flip _) _) _) _) (.const ``impl _)) _) _ => pure (p, [])
  | _ => do
    let constraint ← mkFreshExprMVar <| ← mkAppM ``Subrel #[r, flipImpl]
    let prf ← mkAppOptM ``Subrel.subrelation #[none, r, flipImpl, constraint, none, none, p]
    pure (prf, [constraint.mvarId!])

declare_syntax_cat rw
syntax ("←")? ident: rw

def algorithm (ps : Syntax.TSepArray `rw ",") : TacticM Unit := withMainContext do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"algorithm") do
  let lctx ← getLCtx
  -- Confirm all passed lemmas are in the local context
  let mut ldecls : List (LocalDecl × Bool × TSyntax `rw) := []
  for ps' in lctx do
    for p in ps.getElems do
      let (name, l2r) ← match p with
      | `(rw|← $i:ident) => do pure (i.getId, false)
      | `(rw|$i:ident) => do pure (i.getId, true)
      | s => throwError m!"syntax {s} is invalid."
      if name == ps'.userName then
        ldecls := ldecls ++ [(ps', l2r, p)]
      else
        continue
  for (ldecl, l2r, stx) in ldecls do
    let goal ← getMainGoal
    let goalType ← goal.getType
    let Ψ := []
    let ρ ← toHypInfo ldecl.toExpr
    let flipImpl ← mkAppM ``flip #[mkConst ``impl]
    let (Ψ, res) ← subterm Ψ goalType flipImpl l2r 0 ρ
    match res with
    | .id => logWarningAt stx m!"Nothing to rewrite for {ldecl.userName}."
    | .fail => logError "Rewrite failed to generate constraints."
    | .success ⟨r, t, u, p, _subgoals⟩ =>
      -- TODO: set subgoals
      let (p, Ψ') ← subrelInference p r
      let Ψ := Ψ' ++ Ψ
      trace[Meta.Tactic.grewrite]"\n{t} ↝ {u}\nrel: {r}\nproof: {p}\nconstraints: \n{← Ψ.mapM fun mv => mv.getType}\n"
      search Ψ p ρ
    /-
    -- Paper approach
    let (Ψ, r, u, p) ← rew [] goalType 0 ldecl.toExpr
    let finalGoal ← mkAppM ``Subrel #[r, ← mkAppM ``flip #[mkConst ``impl]]
    let m ← mkFreshExprMVar finalGoal
    let p ← mkAppOptM ``Subrel.subrelation #[none, none, none, m, none, none, p]
    let Ψ := Ψ.insert m.mvarId!
    trace[Meta.Tactic.grewrite]"\n{goalType} ↝ {u}\nrel: {r}\nproof: {p}\nconstraints: \n{← Ψ.mapM fun mv => mv.getType}\n"
    --nopSearch Ψ p
    --search Ψ p ρ
    -/

elab "grewrite" "[" ps:rw,+ "]" : tactic =>
  algorithm ps

end Tactic

set_option trace.Meta.Tactic.grewrite true
--set_option trace.Meta.isDefEq true

variable (α β γ: Type)
variable (Rα: relation α) (Rβ: relation β) (Rγ: relation γ)
variable (Pα: α → Prop) (Pβ: β → Prop) (Pγ: γ → Prop)
variable (Pαβγ: α → β → Prop)
variable (fαβ: α → β) (fβγ: β → γ)
variable [Proper_fαβ: Proper (Rα ⟹ Rβ) fαβ]
variable [Proper_Pα: Proper (Rα ⟹ Iff) Pα]
variable [PER Rα] [PER Rβ]
variable (Rαα: relation (Prop → Prop))

/-
Coq constraints:
  ?r : relation Prop
  ?s : subrelation Raa (pointwiseRelation Prop ?r)
  ?s0 : subrelation ?r (flip impl)
-/
example (h: a = b) (finish : b ∧ b) : a ∧ b := by
  grewrite [h]
  . exact finish
  . exact Eq
  . simp_all
  . rfl

/-
Proof sketch:

Generally compare proof types and show by proof irrelevance.

structural induction:

  Lam, Pi, Arrow by triv

  App:
    Case leading atoms:
      Combine with other induction.

      induction on # leading atoms:
      base case: leading atoms = 0:
      case n+1 leading atoms:
    Case no leading atoms:
      induction on app args:
      base case: args = 2; f a; f:σ→τ;:
        case: .id, .rw a
          assumption h: r a b
          Proper.proper (r ⟹ ←) f ((?m: Proper (r ⟹ ←) f) a b h) : f a ← f b
          =
          @Subrel.subrelation Prop (?m1: relation Prop) (←) (?m2: Subrel ?m1 ←) (f a) (f b) (Subrel.subrelation Proper.proper a b h) : f a ← f b
          by propext
        case: rw, id
        case: id, id
        case: rw, rw
      case n+1; f ... a b
        case: b = id
        case: b = rw
    (Case leading f rw): May not be relevant
    (Case all id): Maaaybe redundant
  Atom?:


Soundness über Inferenzregeln (neue regel kann über alte regeln gezeigt (inferiert) werden)
-/
