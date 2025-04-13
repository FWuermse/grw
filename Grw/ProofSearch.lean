import Lean.Elab.Tactic
import Grw.Morphism
import Batteries

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Attribute
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
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"Try tactic {name}") do
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
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"Try hyp {hyp}") do
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

private def tryClose (goals : List MVarId) : MetaM Bool := do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"Try close") do
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

partial def dfs (goals : List MVarId) (hintDB : DiscrTree (Name × Nat)) (proofRel : Expr) : MetaM (List MVarId) := do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"goals remaining: {goals.length}") do
  -- Try each goal recursively. This implicitly makes the order of constraints important
  for goal in goals do
    let (_, rest) := goals.splitAt 1
    let goalType ← goal.getType
    trace[Meta.Tactic.grewrite]m!"trying goal: {goalType}"
    let mut s ← saveState
    if ← relCmp goalType (← inferType proofRel) then
      if let .ok subgoals ← tryHyp goal proofRel then
        let res ← dfs (subgoals ++ rest) hintDB proofRel
        if res.isEmpty || (← tryClose res) then
          return res
        if res.length >= goals.length then
          s.restore
    s ← saveState
    let hintEntries ← hintDB.getMatch goalType
    let hintEntries := hintEntries.heapSort fun (_, p1) (_, p2) => p1 < p2
    let (names, prios) := hintEntries.unzip
    let matchingHints ← names.mapM mkConstWithFreshMVarLevels
    for (name, matchingHint) in names.zip matchingHints do
      trace[Meta.Tactic.grewrite]m!"⏩ goal {goalType} matches hint: {name}"
      if let .ok subgoals ← tryHyp goal matchingHint then
        let res ← dfs (subgoals ++ rest) hintDB proofRel
        if res.isEmpty || (← tryClose res) then
          return res
        if res.length >= goals.length then
          s.restore
  return goals

def search (Ψ : List MVarId) (prf : Expr) (proofRel : Expr) (d : Option LocalDecl) : TacticM Unit := do
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"search") do
  let env ← getEnv
  let mut hintDB := dbEx.getState env
  -- See (https://github.com/coq/coq/pull/13969)[Coq]
  -- Outsource
  let rels := [``Iff, ``impl, ``Eq, ``flip]
  for rel in rels do
    hintDB ← hintDB.insert (← mkAppM ``relation #[.sort 0]) ⟨rel, 100⟩
  let _ ← dfs Ψ hintDB proofRel
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
