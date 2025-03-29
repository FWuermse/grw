import Lean

open Lean
open Lean.Meta

namespace Attribute

initialize
  Lean.registerTraceClass `Meta.Tactic.grewrite.hints

structure Hint where
  name : Name
  keys : Array DiscrTree.Key
  deriving Inhabited

initialize dbEx : ScopedEnvExtension Hint Hint (DiscrTree Name) ←
  registerScopedEnvExtension {
    mkInitial := return {},
    ofOLeanEntry := fun dt n => do
      pure n
    toOLeanEntry := id
    addEntry := fun dt n => dt.insertCore n.keys n.name,
    finalizeImport := id,
  }

private def convertTheoremToHint (name : Name) : MetaM Hint := do
  let expr ← mkConstWithFreshMVarLevels name
  let type ← inferType expr
  let (_, _, type) ← forallMetaTelescope type
  trace[Meta.Tactic.grewrite.hints]m!"insert: {type}, {name}"
  let arr ← DiscrTree.mkPath type
  pure ⟨name, arr⟩

-- For relations create new Attribute (e.g. grewrite_rel) but reuse dbEx

initialize registerBuiltinAttribute {
  name := `grw
  descr := "Register theorems to be used in the proof search for the grewrite tactic"
  add := fun name _ kind => do
    let (hint, _) ← convertTheoremToHint name |>.run
    dbEx.add hint kind
}

end Attribute
