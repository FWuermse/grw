import Lean.Elab.Tactic
import Lean.Elab.Term
import Grw.Attribute
import Grw.Morphism
import Grw.PaperTactic
import Grw.ProofSearch
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


private def getRelType (r : Expr) : MetaM Expr := do
  match r with
  | .app (.const ``relation _) T => pure T
  | .forallE _ T (.forallE _ T' b _) _ =>
    if T == T' && b == .sort 0 then
      return T
    else
      throwError "You tried to get the type of a relation but {r} is not a relation."
  | _ => throwError "You tried to get the type of a relation but {r} is not a relation."

/--
`id` is when we don't rewrite because no subterm can't be unified (ATOM or binary APP).
`success` successful subterm rewrite.
-/
inductive RewriteResult where
  | id
  | success (r : RewriteResultInfo)

abbrev RWM  := ReaderT HypInfo MetaM <| List MVarId × RewriteResult

private def srep : Nat → String
  | n => n.fold (fun _ _ s => s ++ "  ") ""

-- TODO: don't bother tracking the subgoals not to be solved via TCR. Lean will do that automatically.
private def unify (t : Expr) (l2r : Bool) : RWM  := do
  let ρ ← read
  let lhs := if l2r then ρ.c1 else ρ.c2
  let rhs := if l2r then ρ.c2 else ρ.c1
  -- Take all initial holes and add collect the ones not reassigned to make them subgoals for the user to solve.
  if ← isDefEq lhs t then
    let subgoals ← ρ.holes.filterM fun mv => do pure !(← mv.isAssignedOrDelayedAssigned)
    pure ([], .success ⟨ρ.rel, t, rhs, ρ.prf, subgoals.map mkMVar⟩)
  else
    pure ([], .id)

/--
Note from paper:
The variant unify∗ ρ(Γ, Ψ, τ ) tries unification on all subterms and succeeds if at least one
unification does. The function unify(Γ, Ψ, t, u) does a standard unification of t and u.
-/
private def unifyStar (t : Expr) (l2r : Bool) : RWM := do
  let ρ ← read
  let lhs := if l2r then ρ.c1 else ρ.c2
  let rhs := if l2r then ρ.c2 else ρ.c1
  let b ← IO.mkRef false
  forEachExpr t fun t' => do
    b.set <| (← isDefEq lhs t') || (← b.get)
  if ← b.get then
    let subgoals ← ρ.holes.filterM fun mv => do pure !(← mv.isAssignedOrDelayedAssigned)
    pure ([], RewriteResult.success ⟨ρ.rel, t, rhs, ρ.prf, subgoals.map mkMVar⟩)
  else
    pure ([], .id)

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
partial def subterm (t : Expr) (desiredRel : Option Expr) (l2r : Bool) (depth : Nat) : RWM  := do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"{srep <| depth}subterm Ψ ({t}) ρ") do
  let ρ ← read
  if let (Ψ', .success res) ← unify t l2r ρ then
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
      let mut Ψ := []
      let mut respectfulList := []
      let mut prfArgs := []
      let mut rewMVars := []
      let mut u := fn
      -- If ρ matches f of an application f a b then ρ cannot match any other aplicant directly
      if let (_, .success res) ← unify fn l2r ρ then
        let rel ← mkFreshExprMVar <| ← mkAppM ``relation #[← inferType t]
        let prf ← appArgs.foldrM (fun (_, T) acc => mkAppM ``pointwiseRelation #[T, acc]) rel
        let sub ← mkFreshExprMVar <| ← mkAppM ``Subrel #[res.rewCar, prf]
        let p ← mkAppOptM ``Subrel.subrelation <| #[none, none, none, sub, none, none, res.rewPrf] ++ appArgs.map fun (t, _) => .some t
        u := mkAppN res.rewTo <| appArgs.map Prod.fst
        let (Ψ'', snd) ← subterm u desiredRel l2r (depth + 1)
        -- TODO: include both shadowed rels in psi
        if let .success res := snd then do
          let desiredRel ← match desiredRel with
          | some r => do
            if (← getRelType (← inferType r)) == .sort 0 then
              mkAppM ``flip #[mkConst ``impl]
            else
              pure r
          | none => pure rel
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
        let (Ψ', res) ← subterm t desiredRel l2r (depth+1) ρ
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
      pure ([], .id)
  | .lam n T _b i => do
    trace[Meta.Tactic.grewrite] "{srep depth} |LAM {t}"
    lambdaTelescope t fun _xs b => do
      let (Ψ, .success ⟨S, _, b, p, subgoals⟩) ← subterm b none l2r (depth+1) ρ | return ([], .id)
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
      let (Ψ, .success ⟨S, _, b, p, subgoals⟩) ← subterm (mkApp2 (mkConst ``impl) α β) desiredRel l2r (depth+1) | pure ([], .id)
      let .app (.app _ α) β := b | throwError "Rewrite of `Impl α β` resulted in a different (thus wrong) type."
      let u ← mkArrow α β
      return (Ψ, .success ⟨S, t, u, p, subgoals⟩)
    else
      trace[Meta.Tactic.grewrite] "{srep depth} |PI {t}"
      let (Ψ', res) ← unifyStar T l2r
      match res with
      | .success info => return (Ψ', .success info)
      | .id =>
        let (Ψ, .success ⟨S, _, .app _ (.lam n T b i), p, subgoals⟩) ← subterm (← mkAppM ``all #[T, .lam n T b i]) none l2r (depth+1)
          | throwError "Rewrite of `all λ x ↦ y` resulted in a different (thus wrong) type."
        let u := .forallE n T b i
        pure (Ψ, .success ⟨S, t, u, p, subgoals⟩)
  | _ => do
    trace[Meta.Tactic.grewrite] "{srep depth} |ATOM {t}"
    pure ([], .id)

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
    let ρ ← toHypInfo expr
    let desired : Expr ← match (location, l2r) with
    | (none, true) => do mkAppM ``flip #[mkConst ``impl]
    | (some _, true) => do pure <| Lean.mkConst ``impl
    | (none, false) => do pure <| Lean.mkConst ``impl
    | (some _, false) => do mkAppM ``flip #[mkConst ``impl]
    let (Ψ, res) ← subterm goalType desired l2r 0 ρ
    match res with
    | .id => logWarningAt stx m!"Nothing to rewrite for {name}."
    | .success ⟨r, _, _, p, _subgoals⟩ =>
      -- TODO: set subgoals
      let (p, _, Ψ') ← subrelInference p r desired
      let Ψ := Ψ' ++ Ψ
      withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"constraints") do
        trace[Meta.Tactic.grewrite]m!"{← Ψ.mapM (·.getType)}"
      withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"proof") do
        trace[Meta.Tactic.grewrite]m!"{p}"
      search Ψ p ρ.rel location

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
    let ρ ← toHypInfo expr
    let desired : Expr ← match (location, l2r) with
    | (none, true) => do mkAppM ``flip #[mkConst ``impl]
    | (some _, true) => do pure <| Lean.mkConst ``impl
    | (none, false) => do pure <| Lean.mkConst ``impl
    | (some _, false) => do mkAppM ``flip #[mkConst ``impl]
    let (Ψ, res) ← subterm goalType desired l2r 0 ρ
    match res with
    | .id => logWarningAt stx m!"Nothing to rewrite for {name}."
    | .success ⟨r, _, _, p, _subgoals⟩ =>
      -- TODO: set subgoals
      let (p, _, Ψ') ← subrelInference p r desired
      let Ψ := Ψ' ++ Ψ
      let ts ← ts.getElems.mapM (fun t => do Elab.Tactic.elabTerm t.raw none)
      let Ψ ← Ψ.mapM (fun e => do e.getType)
      for (e, i) in Ψ.zipIdx do
        if ← isDefEq e <| ts.get! i then
          continue
        else
          throwError "Constraints don't match at idx: {i}, {e} ≠ {ts.get! i}"
      -- Check if p can be applied
      if let some l := location then
        let _ ← withoutModifyingState do
          let newExpr := Expr.app p l.toExpr
          let (_, goal) ← goal.assertHypotheses #[{userName := l.userName, type := ← inferType newExpr, value := newExpr}]
          -- Check other APIs to preserve sequence (may me part of the Hypotheses APIs)
          let goal ← goal.tryClear l.fvarId
          replaceMainGoal [goal]
      else
        let _ ← withoutModifyingState do
          let _ ← goal.apply p
          -- TODO: maybe check resulting type of first goal with some given "expected" type

elab rw:grw_assert t:term,+ ";": tactic =>
  assertConstraints rw t

end Tactic
