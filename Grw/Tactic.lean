import Lean.Elab.Tactic
import Grw.Morphism
import Grw.Eauto
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
  deriving BEq

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

def toHypInfo (term : Expr) : MetaM HypInfo := do
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

abbrev RWM := ReaderT HypInfo MetaM <| List MVarId × RewriteResult

private def srep : Nat → String
  | n => n.fold (fun _ s => s ++ "  ") ""

def unify (Ψ : List MVarId) (t : Expr) (l2r : Bool) : RWM := do
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
def unifyStar (Ψ : List MVarId) (t : Expr) (l2r : Bool) : RWM := do
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

def atom (Ψ : List MVarId) (t : Expr) (r2l : Bool) : RWM := do
  -- TODO probably a duplicate check.
  if let (Ψ, .success res) ← unifyStar Ψ t r2l then
    return (Ψ, .success res)
  let T ← inferType t
  let S ← mkFreshExprMVar <| ← mkAppM ``relation #[T]
  let m ← mkFreshExprMVar <| ← mkAppM ``Proper #[S, t]
  -- TODO confirm below line
  let p ← mkAppOptM ``Proper.proper #[none, none, none, m]
  -- paper says include S.mvardId! But those will implicitly reappear when setting new goals
  let u := t
  logInfo m!"{t} ↝ {u}, Proof: {p}, Relation: {S}"
  return (Ψ ∪ [m.mvarId!], .success ⟨S, t, t, p, []⟩)

private def getRelType (rel : Expr) : Expr :=
  if let .app _ b := rel then
    b
  else
    rel

def arrowCount (curr : Nat) : Expr → Nat
  | .forallE _n _T b _i => arrowCount (curr + 1) b
  | .app (.const ``relation _) _ => 2
  | _ => curr

def appCount (curr : Nat) : Expr → Nat
  | .app f _ => appCount curr f + 1 -- Don't decompose rhs further
  | _ => curr + 1

def arrowTypes (curr : List Expr) : Expr → List Expr
  | .forallE _n T b _i => curr ++ [T] ++ (arrowTypes curr b)
  | .app (.const ``relation _) T => [T, T, .sort 0]
  | t => t::curr

def getAtoms : Expr → List Expr
  | .app f e => getAtoms f ++ [e]
  | atom => [atom]

def respectfulN (mvars : List Expr) : MetaM  Expr :=
  match mvars with
  | x :: [] => pure x
  | x :: xs => do mkAppM ``respectful #[x, ← respectfulN xs]
  | _ => throwError "Cannot create empty respectful chain."

def respectfulFromArrow (fst : Expr) (types : List Expr) (lst : Expr) (fargs : List Expr) : MetaM (Expr × List Expr) := do
  let types := types.zip <| fargs.rotate 1 -- We move the first applicant to args and types are aligned
  logInfo m!"{types}"
  let (_, types) := types.splitAt 1
  let (types, _) := types.splitAt <| types.length - 1
  let types ← types.mapM (fun (T, t) => do return (← mkFreshExprMVar <| ← mkAppM ``relation #[T], t))
  let respectful ← respectfulN <| [fst] ++ types.unzip.fst ++ [lst]
  let properProofs ← types.mapM (fun (mvarT, t) => do mkFreshExprMVar <| ← mkAppM ``ProperProxy #[mvarT, t])
  let properProofs ← properProofs.mapM (do mkAppOptM ``ProperProxy.proxy #[none, none, none, .some .])
  return (respectful, properProofs)

/--
`rew` always succeeds and returns a tuple (Ψ, R, τ', p) with the output constraints, a relation R, a new term τ' and a proof p : R τ τ'. In case no rewrite happens we can just have an application of ATOM.

This output tuple represents the proof sekelton that is used in the proof search.
-/
partial def rew (Ψ : List MVarId) (t : Expr) (desiredRel : Option Expr) (l2r : Bool) (depth : Nat) : RWM := do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"{srep <| depth}rew Ψ ({t}) ρ") do
  let ρ ← read
  if let (Ψ', .success res) ← unify Ψ t l2r ρ then
    trace[Meta.Tactic.grewrite] "{srep depth} |UNIFY⇓ {res.rewFrom} ↝ {res.rewTo}"
    return (Ψ', .success res)
  match t with
  | .app f e => do
    let Tf ← whnf <| ← inferType f
    if let .some (_τ, σ) := Tf.arrow? then
      trace[Meta.Tactic.grewrite] "{srep depth} |APPSUB ({f}) ({e})"
      let (Ψ, fRes) ← rew Ψ f none l2r (depth+1) ρ
      let (Ψ, eRes) ← rew Ψ e none l2r (depth+1) ρ
      match (fRes, eRes) with
      | (.id, .id) =>
        pure (Ψ, .id)
      | (.success fInfo, .success eInfo) =>
        -- Expensive case if both sides of the app can be rewritten (usually unfolded non binary apps).
        let fn := f.getAppFn
        -- the next four lines determine the ==> ... ==> chain when we skipped id rws.
        let args := [fInfo.rewCar, eInfo.rewCar] ∪ desiredRel.toList
        let args := if args.length < arrowCount 1 (← inferType fn) then [ρ.rel] ∪ args else args
        let respectful ← respectfulN args
        let prp ← mkFreshExprMVar <| ← mkAppM ``Proper #[respectful, fn]
        let prf ← mkAppOptM ``Proper.proper #[none, none, none, prp, none, none, fInfo.rewPrf, none, none, eInfo.rewPrf]
        let u := .app fInfo.rewTo eInfo.rewTo
        let Ψ := [prp.mvarId!] ∪ Ψ
        logInfo m!"-- from: {t}, to: {u}, proof: {prf} --"
        pure (Ψ, .success ⟨eInfo.rewCar, t, u, prf, fInfo.rewMVars ∪ eInfo.rewMVars⟩)
      | (.id, .success eInfo) =>
        -- When only the rhs succeeds with a rewrite we defer the generated constraints and avoid unneccessary nesting.
        -- TODO: something in this case is hardcoded/static that should be retreived from eInfo!
        let rel ← mkFreshExprMVar <| ← mkAppM ``relation #[σ]
        let rhs ← match desiredRel with
        | .some desired => pure desired
        | .none => do pure rel
        let u := .app f eInfo.rewTo
        -- When we're in the middle of an appN we want to wait with creating the constraints until on top (collecting relation holes as we go to later build ==> ... ==> with them).
        if arrowCount 0 (← inferType f) < 2 then
          let lhs := eInfo.rewCar
          let prp ← mkFreshExprMVar <| ← mkAppM ``Proper #[← mkAppM ``respectful #[lhs, rhs], f]
          let p ← mkAppOptM ``Proper.proper #[none, none, none, prp, none, none, eInfo.rewPrf]
          let Ψ := [prp.mvarId!] ∪ Ψ
          logInfo m!"id eInfo -> do: from: {t}, to: {u}, proof: {p}"
          return (Ψ, .success ⟨rel, t, u, p, eInfo.rewMVars⟩)
        else
          -- At this point our holes are taken care of and we just skip until there is something to do
          logInfo m!"id eInfo -> skip: from: {t}, to: {u}, proof: {eInfo.rewPrf}"
          pure (Ψ, .success ⟨eInfo.rewCar, t, u, eInfo.rewPrf, eInfo.rewMVars⟩)
      | (.success fInfo, .id) => do
        -- When only the lhs succeeds we follow the same approach but use a proxy.
        let u := .app fInfo.rewTo e
        let fn := f.getAppFn
        if arrowCount 0 (← inferType fn) == appCount 0 t - 1 then
          -- We reached the top of an application and generate the efficient constraint Proper (==> ... ==>) f
          let rel ← mkFreshExprMVar <| ← mkAppM ``relation #[σ]
          let arrowTypes := arrowTypes [] (← inferType fn)
          let fargs := getAtoms t
          -- The general case is (?m₁ ==> ... ==> ?mₙ) but the first and/or last can be inferred when known to optimize proof search
          let rhs := if desiredRel.isSome then desiredRel.get! else rel
          let lhs := if ρ.rel != arrowTypes.get! 0 then fInfo.rewCar else ρ.rel
          let (respectful, pps) ← respectfulFromArrow lhs arrowTypes rhs fargs
          let prp ← mkFreshExprMVar <| ← mkAppM ``Proper #[respectful, fn]
          let pparr := pps.toArray.flatMap (#[none, none, .some .])
          let p ← mkAppOptM ``Proper.proper <| #[none, none, none, prp, none, none, fInfo.rewPrf] ++ pparr
          let Ψ := Ψ ∪ pps.map Expr.mvarId! ∪ [p.mvarId!]
          logInfo m!"fInfo id -> do: from: {t}, to: {u}, proof: {p}"
          return (Ψ, .success ⟨rel, t, u, p, fInfo.rewMVars⟩)
        else
          logInfo m!"fInfo id -> skip: from: {t}, to: {u}, proof: {fInfo.rewPrf}"
          pure (Ψ, .success ⟨fInfo.rewCar, t, u, fInfo.rewPrf, fInfo.rewMVars⟩)
      | _ => return (Ψ, .fail)
    else
      atom Ψ t l2r
  | .lam n T _b i => do
    trace[Meta.Tactic.grewrite] "{srep depth} |LAM {t}"
    lambdaTelescope t fun _xs b => do
      let (Ψ, .success ⟨S, _, b, p, subgoals⟩) ← rew Ψ b none l2r (depth+1) ρ | return (Ψ, .id)
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
      let (Ψ, .success ⟨S, _, b, p, subgoals⟩) ← rew Ψ (mkApp2 (mkConst ``impl) α β) desiredRel l2r (depth+1) | pure (Ψ, .id)
      let .app (.app _ α) β := b | throwError "Rewrite of `Impl α β` resulted in a different (thus wrong) type."
      let u ← mkArrow α β
      return (Ψ, .success ⟨S, t, u, p, subgoals⟩)
    else
      trace[Meta.Tactic.grewrite] "{srep depth} |PI {t}"
      let (Ψ', res) ← unifyStar Ψ T l2r
      match res with
      | .success info => return (Ψ', .success info)
      | .id =>
        let (Ψ, .success ⟨S, _, .app _ (.lam n T b i), p, subgoals⟩) ← rew Ψ (← mkAppM ``all #[T, .lam n T b i]) none l2r (depth+1)
          | throwError "Rewrite of `all λ x ↦ y` resulted in a different (thus wrong) type."
        let u := .forallE n T b i
        pure (Ψ, .success ⟨S, t, u, p, subgoals⟩)
      | .fail => return (Ψ , .fail)
  | _ => do
    trace[Meta.Tactic.grewrite] "{srep depth} |ATOM {t}"
    --atom Ψ t l2r
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

def nopSearch (Ψ : List MVarId) (p : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let subgoals ← goal.apply (← instantiateMVars p)
  replaceMainGoal subgoals

def subrelInference (p : Expr) (r : Expr) : MetaM Expr := do
  let flipImpl ← mkAppM ``flip #[mkConst ``impl]
  match ← inferType p with
  | .app (.app (.app (.app (.app (.app (.const ``flip _) _) _) _) (.const ``impl _)) _) _ => pure p
  | t => do
    logInfo m!"Proof {p} is not a direct proof for flip impl and must be inferred"
    mkAppOptM ``Subrel.subrelation #[none, r, flipImpl, ← mkFreshExprMVar <| ← mkAppM ``Subrel #[r, flipImpl], none, none, p]

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
    let (Ψ, res) ← rew Ψ goalType flipImpl l2r 0 ρ
    match res with
    | .id => logWarningAt stx m!"Nothing to rewrite for {ldecl.userName}."
    | .fail => logError "Rewrite failed to generate constraints."
    | .success ⟨r, _t, u, p, _subgoals⟩ =>
    logInfo m!"p: {p}, Ψ: {Ψ}"
    trace[Meta.Tactic.grewrite]"Starting Proof Search:"
    trace[Meta.Tactic.grewrite]"Solving {Ψ}"
    -- TODO: set subgoals
    let p ← subrelInference p r
    nopSearch Ψ p

elab "grewrite" "[" ps:rw,+ "]" : tactic =>
  algorithm ps

end Tactic

variable (α β γ: Type)
variable (Rα: relation α) (Rβ: relation β) (Rγ: relation γ)
variable (Pα: α → Prop) (Pβ: β → Prop) (Pγ: γ → Prop)
variable (Pαβγ: α → β → Prop)
variable (fαβ: α → β) (fβγ: β → γ)
variable [Proper_fαβ: Proper (Rα ⟹ Rβ) fαβ]
variable [Proper_Pα: Proper (Rα ⟹ Iff) Pα]
variable [PER Rα] [PER Rβ]

-- Multiple occurrences
example (h: Rα a a') (finish: Rα a' a'): Rα a a := by
  grewrite [h]
  repeat sorry

-- More complex selection
example (h: Rα a a') (finish: Pα a'): Pα a ∧ Pα a ∧ Pα a ∧ Pα a ∧ Pα a ∧ Pα a := by
  grewrite [h]
  repeat sorry
