import Lean.Meta
import Grw.Eauto

open Lean
open Lean.Elab.Tactic


structure RewriteProof where
  rewPrf : Expr × Expr
  deriving BEq

structure RewriteResultInfo where
  rewCar : Expr
  rewFrom : Expr
  rewTo : Expr
  rewPrf : RewriteProof
  rewMVars : List MVarId
  deriving BEq

structure HypInfo where
  prf : Expr
  car : Expr
  rel : Expr
  sort : Bool -- Even required? Does it matter in Lean?
  c1 : Expr
  c2 : Expr
  holes : List MVarId

structure RewriteFlags where
  underLambdas : Bool
  onMorphisms : Bool

inductive RewriteResult where
  | Fail
  | Id
  | Except.ok (r : RewriteResultInfo)

structure strategyInput (α : Type) where
  state : α
  env : Environment
  unfresh : Unit -- Idk what this is
  term1 : Expr
  ty1 : Expr
  cstr : Bool × Option Expr
  mvars : List MVarId

structure EvarMap where
  defnEvars : Std.HashMap Nat MVarId
  undfEvars : Std.HashMap Nat MVarId
  evarNames : Unit -- calculate when needed
  candidateEvars : Std.HashSet MVarId
  universes : Unit -- calculate when needed
  convPbs : List MVarId -- Assuming EvarConstraint is a defined type
  lastMods : Std.HashSet MVarId
  evarFlags : Unit -- Not sure what those flags represent
  effects : Unit
  futureGoals : List (List MVarId) -- Representing the stack as a list of lists
  givenUp : Std.HashSet MVarId
  shelf : List (List MVarId)
  extras : Unit -- likely not needed

abbrev Evars := List MVarId × List MVarId

abbrev pureStrategy (α : Type) := strategyInput α → (α × RewriteResult)

def strategy := pureStrategy Unit

def unify (Ψ : List MVarId) (t : Expr) (ρ : Expr) : MetaM <| List MVarId × Expr × Expr × Expr × Bool := do
  let Tₚ ← Meta.inferType ρ
  match Tₚ with
  | .app (.app r lhs) rhs =>
    let unifyable ← Meta.isDefEq lhs t -- Extends the local context
    pure (Ψ, r, ρ, rhs, unifyable)
  | .forallE _ _ (.app (.app _ _) _) _ =>
    let (exprs, _, Expr.app (.app r lhs) rhs) ← Meta.forallMetaTelescope Tₚ | throwError "MetaTelescope broke structure of rw lemma"
    let unifyable ← Meta.isDefEq lhs t -- Extends the local context
    let mut Ψ := Ψ
    for expr in exprs do
      -- Precondition e is forall
      -- Invariant expr is a mvar
      let mvarId := expr.mvarId!
      let reassigned ← mvarId.isAssignedOrDelayedAssigned
      if !reassigned then
        Ψ := Ψ.insert mvarId
    pure (Ψ, r, mkAppN ρ exprs, rhs, unifyable)
  | _ => throwError "{ρ} is not a relation"

#check HypInfo.mk
/--
RW-Hypothesis are the parameters we pass to the rewrite tactic.
They usually appear in the form R a b and we want to return a triple (R, a, b).

`hyp` must be a proof i.e. a term of type R a b.
-/
def decomposeAppliedRelation (Ψ : List MVarId) (h : Expr) : MetaM <| List MVarId × HypInfo := do
  let Tₕ ← Meta.inferType h
  match Tₕ with
  | .app (.app r lhs) rhs =>
    let car ← Meta.inferType lhs
    pure (Ψ, ⟨h, car, r, ← Meta.isProp car, lhs, rhs, Ψ⟩)
  | .forallE _ _ (.app (.app _ _) _) _ =>
    let (exprs, _, Expr.app (.app r lhs) rhs) ← Meta.forallMetaTelescope Tₕ | throwError "MetaTelescope broke structure of rw lemma"
    let car ← Meta.inferType lhs
    let mut Ψ := Ψ
    for expr in exprs do
      let mvarId := expr.mvarId!
      let reassigned ← mvarId.isAssignedOrDelayedAssigned
      if !reassigned then
        Ψ := Ψ.insert mvarId
    pure (Ψ, ⟨h, car, r, ← Meta.isProp car, lhs, rhs, Ψ⟩)
  | _ => throwError "{h} is not a relation proof"

def refreshHypinfo (Ψ : List MVarId) (ρ : Expr) : MetaM <| List MVarId × HypInfo := do
  decomposeAppliedRelation Ψ ρ

/--
Do unification with x considering a term of r x y or y if invoked with ←
-/
def unifyEqn (hyp : HypInfo) (l2r : Bool) (flags : sorry) (evar : Evars) (t : Expr) : TacticM <| List MVarId := do
  try
    let lhs := if l2r then hyp.c1 else hyp.c2
    let unifyable ← Meta.isDefEq lhs t -- Extends the local context
    let mut Ψ := evar.fst
    for mvar in Ψ do
      -- Precondition e is forall
      -- Invariant expr is a mvar
      let reassigned ← mvar.isAssignedOrDelayedAssigned
      if !reassigned then
        Ψ := Ψ.insert mvar
    let success ← Eauto.eautoMain Ψ #[`grewrite] true
    if !success then
      -- solve_remaining_by
      -- Reductionops.nf_evar
      -- Reductionops.infer_conv
      logInfo "When Eauto on unify fails check out what Reductionops.infer_conv does."

    pure ()
  catch e =>
    sorry

/--
Performs a rewrite operation using a provided strategy, handling occurrences and constraint resolution.

`c` is the term to perform the rw on.
`l2r` is the direction of the rw.
-/
def rewriteWith (l2r : Bool) (flags : sorry) (c : Expr) : ReaderT Evars MetaM strategy := do
  let evars ← read
  fun input => do
    let (mvars, t) ← do
      let (goals, cstrs) := evars
      let rew ← refreshHypinfo goals c
      unifyEqn rew l2r flags  t

/-
def resolveMorphism (env : Environment) (m : Expr) (args args' : Array <| Option RewriteResultInfo) (cstr : Bool × Option Expr) (evars : Evars) :
    MetaM ((List MVarId) × Expr × Expr × Expr × Expr) := do
  let first ← match args'.findIdx? fun b => b.isSome with
    | some i => pure i
    | none => throwError "resolveMorphism: no Some found in args'"
  let (morphArgs, morphObjs) := args.split (. == args.get! first)
  let (morphArgs', morphObjs') := args.split (. == args.get! first)
  let appM := mkAppN m <| morphArgs.filterMap id
  let appMType ← inferType appM
  let cstrs := morphObjs'.toList.map fun r => r.map fun r => (r.rewCar, r.rewPrf.getOptRewRel)
  -- Desired signature
  let (evars', appMType', signature, sigArgs) ←
    if cstr.1 then PropGlobal.buildSignature evars env appMType cstrs cstr.2
    else TypeGlobal.buildSignature evars env appMType cstrs cstr.2
  -- Actual signature found
  let (evars'', appMType'') ← Evars.refreshUniverseConstraints evars' appMType'
  let clArgs := #[appMType'', signature, appM]
  let (evars''', properProof) ←
    if cstr.1 then PropGlobal.properType.appPolySort env evars'' clArgs
    else TypeGlobal.properType.appPolySort env evars'' clArgs
  let (doSubrelation, applySubrelation) :=
    if cstr.1 then (PropGlobal.doSubrelation, PropGlobal.applySubrelation)
    else (TypeGlobal.doSubrelation, TypeGlobal.applySubrelation)
  let (_, doSubrelation') ← doSubrelation.appPolyNocheck env evars''' #[]
  let (_, applySubrelation') ← applySubrelation.appPolyNocheck env evars''' #[]
  let doSubrelationId := `do_subrelation
  let env' := env.pushLocalDecl doSubrelationId BinderInfo.default doSubrelation'
  let (evars'''', morph) ← newCstrEvar evars''' env' properProof
  -- Replace the free [doSubrelationId] in the evar by the global reference
  let morph' := morph.replaceConst (mkFVar doSubrelationId) doSubrelation'
  let (projArgs, subst, evars''''', sigArgs', typeArgs) ←
    morphObjs.toArray.zip morphObjs'.toArray.foldlM (init := ([], [], evars'''', sigArgs, []))
      fun (acc, subst, evars, sigArgs, typeArgs') (x, y) => do
        let (carrier, relation) := sigArgs.head!
        let sigArgs' := sigArgs.tail!
        match relation with
        | some relation =>
          let carrier' := subst.foldl (init := carrier) fun acc' s => acc'.replaceFVar s.1 s.2
          let relation' := subst.foldl (init := relation) fun acc' s => acc'.replaceFVar s.1 s.2
          match y with
          | none =>
            let properProof ←
              if cstr.1 then PropGlobal.properProof env evars carrier' relation' x
              else TypeGlobal.properProof env evars carrier' relation' x
            return (properProof :: x :: x :: acc, subst, evars, sigArgs', x :: typeArgs')
          | some r =>
            let (evars', proof) ← getRewPrf env evars r
            return (proof.2 :: r.rewTo :: x :: acc, subst, evars', sigArgs', r.rewTo :: typeArgs')
        | none =>
          if y.isSome then
            throwError "Cannot rewrite inside dependent arguments of a function"
          else
            return (x :: acc, (x, x) :: subst, evars, sigArgs', x :: typeArgs')
  let proj := mkAppN (← PropGlobal.properProj.toExpr) #[appMType'', signature, appM] -- Assuming properProj is accessible
  let proof := mkAppN proj projArgs.reverse.toArray
  let m' := mkAppN m typeArgs.reverse.toArray
  match sigArgs' with
  | (a, some r) :: _ =>
    let a' := subst.foldl (init := a) fun acc' s => acc'.replaceFVar s.1 s.2
    let r' := subst.foldl (init := r) fun acc' s => acc'.replaceFVar s.1 s.2
    return (evars''''', proof, a', r', m')
  | _ => throwError "Unexpected signature arguments"

def subterm (all : Bool) (flags : RewriteFlags) (s : PureStrategy) : PureStrategy :=
  let rec aux (input : StrategyInput) : MetaM RewriteResult := do
    let { state, env, unfresh, term1 := t, ty1 := ty, cstr := (prop, cstr), evars } := input
    let cstr' := cstr.map fun c => (ty, some c)
    match ← inferType t with
    | Expr.app m args =>
      let rewriteArgs (state : a) (success : Option Bool) : MetaM (a × RewriteResult) := do
        let args'AndProgress ← args.foldlM (init := ([], evars, success)) fun (acc, evars, progress) arg => do
          if progress.isSome && !all then
            return (none :: acc, evars, progress)
          else
            let argTy ← inferType arg
            let (state', res) ← s.strategy { state, env, unfresh, term1 := arg, ty1 := argTy, cstr := (prop, none), evars }
            let res' : List (Option RewriteResult) × Evars × Option Bool :=
              match res with
              | RewriteResult.identity =>
                let progress' := if progress.isNone then some false else progress
                (none :: acc, evars, progress')
              | RewriteResult.success r =>
                (some r :: acc, r.rewEvars, some true)
              | RewriteResult.fail => (none :: acc, evars, progress)
            return (state', res')
        let (args'Rev, evars', progress) := args'AndProgress
        let res : RewriteResult :=
          match progress with
          | none => RewriteResult.fail
          | some false => RewriteResult.identity
          | some true =>
            let args' := args'Rev.reverse.toArray
            if args'.any fun
              | none => false
              | some r => not r.rewPrf.isRewCast
            then
              let (evars'', prf, car, rel, c2) ← resolveMorphism env m args args' (prop, cstr') evars'
              let res' : RewriteResultInfo := {
                rewCar := ty
                rewFrom := t
                rewTo := c2
                rewPrf := RewriteProof.rewPrf rel prf
                rewEvars := evars''
              }
              RewriteResult.success (coerce env (prop, cstr) res')
            else
              let args'' := args.zip args'.toList.map Option.getD
              let res' : RewriteResultInfo := {
                rewCar := ty
                rewFrom := t
                rewTo := mkAppM' m args''.toArray
                rewPrf := RewriteProof.rewCast CastKind.DEFAULT
                rewEvars := evars'
              }
              RewriteResult.success res'
        return (state, res)
      if flags.onMorphisms then
        let mTy ← inferType m
        let lift := if prop then PropGlobal.liftCstr else TypeGlobal.liftCstr
        match ← lift env evars args.toList m mTy none with
        | some (evars', cstr', m', mTy', args') =>
          let (state', m'') ← s.strategy { state, env, unfresh, term1 := m', ty1 := mTy', cstr := (prop, cstr'), evars := evars' }
          match m'' with
          | RewriteResult.fail => rewriteArgs state none -- Standard path, try rewrite on arguments
          | RewriteResult.identity => rewriteArgs state (some false)
          | RewriteResult.success r =>
            -- We rewrote the function and get a proof of pointwise rel for the arguments.
            -- We just apply it.
            let prf ← match r.rewPrf with
              | RewriteProof.rewPrf rel prf =>
                let applyPointwise := if prop then PropGlobal.applyPointwise else TypeGlobal.applyPointwise
                let rel' ← applyPointwise env evars rel args'.toList
                return RewriteProof.rewPrf rel' (mkApp prf args')
              | x => pure x
            let res' : RewriteResultInfo := {
              rewCar := ← reduce (mkAppN r.rewCar args'.toArray)
              rewFrom := mkAppM' r.rewFrom args'.toArray
              rewTo := mkAppM' r.rewTo args'.toArray
              rewPrf := prf
              rewEvars := r.rewEvars
            }
            let res : RewriteResult :=
              match prf with
              | RewriteProof.rewPrf rel prf =>
                RewriteResult.success (coerce env (prop, cstr) res')
              | _ => RewriteResult.success res'
            return (state, res)
        | none => rewriteArgs state none
      else
        rewriteArgs state none
    | Expr.forallE n d b bi =>
      if b.hasLooseBVars then
        -- TODO: Handle dependent forall
        throwError "Rewriting under dependent binders is not yet implemented."
      else
        let b' := b.instantiate1 mkProp
        let tx ← inferType d
        let tb ← inferType b'
        let arr := if prop then PropGlobal.arrowMorphism else TypeGlobal.arrowMorphism
        let (evars', mor, unfold) ← arr env evars n tx tb d b'
        let (state', res) ← aux { state, env, unfresh, term1 := mor, ty1 := ty, cstr := (prop, cstr), evars := evars' }
        let res' :=
          match res with
          | RewriteResult.success r => RewriteResult.success { r with rewTo := unfold r.rewTo }
          | RewriteResult.fail | RewriteResult.identity => res
        return (state', res')
    | Expr.lam n b body bi =>
      if flags.underLambdas then
        let unfresh' := unfresh.insert n.name
        let bTy ← inferType b
        withLocalDecl n.name bi bTy fun fVar => do
          let bodyTy ← inferType (body.instantiate1 fVar)
          let unlift := if prop then PropGlobal.unliftCstr else TypeGlobal.unliftCstr
          let (state', b'') ← s.strategy { state, env := env.pushLocalDecl n.name bi bTy, unfresh := unfresh', term1 := body.instantiate1 fVar, ty1 := bodyTy, cstr := (prop, ← unlift env evars cstr), evars }
          let res : RewriteResult :=
            match b'' with
            | RewriteResult.success r =>
              let prf ← match r.rewPrf with
                | RewriteProof.rewPrf rel prf =>
                  let pointwiseOrDepRelation := if prop then PropGlobal.pointwiseOrDepRelation else TypeGlobal.pointwiseOrDepRelation
                  let rel' ← pointwiseOrDepRelation env r.rewEvars n.name b r.rewCar rel
                  return RewriteProof.rewPrf rel' (mkLambdaEx n bi bTy prf))
                | x => pure x
              return RewriteResult.success {
                r with
                rewCar := mkForall n bi bTy r.rewCar
                rewFrom := mkLambdaEx n bi bTy r.rewFrom
                rewTo := mkLambdaEx n bi bTy r.rewTo
              }
            | RewriteResult.fail | RewriteResult.identity => pure b''
          return (state', res)
      else
        return (state, RewriteResult.fail)
    | Expr.mdata _ e =>
      aux { input with term1 := e }
    | _ =>
      return (state, RewriteResult.fail)
  { strategy := aux }

def allSubterms (flags : RewriteFlags := { underLambdas := true, onMorphisms := true }) : PureStrategy :=
  subterm true flags

def oneSubterm (flags : RewriteFlags := { underLambdas := true, onMorphisms := true }) : PureStrategy :=
  subterm false flags
-/
