/-
  Copyright (c) 2025 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer, Jannis Limperg
-/

import Lean

open Lean
open Lean.Meta

namespace Attribute

initialize
  Lean.registerTraceClass `Meta.Tactic.grewrite.hints

structure Hint where
  name : Name
  prio : Nat
  keys : Array DiscrTree.Key
  deriving Inhabited

initialize dbEx : ScopedEnvExtension Hint Hint (DiscrTree (Name × Nat)) ←
  registerScopedEnvExtension {
    mkInitial := return {},
    ofOLeanEntry := fun dt n => do
      pure n
    toOLeanEntry := id
    addEntry := fun dt n => dt.insertCore n.keys (n.name, n.prio),
    finalizeImport := id,
  }

private def convertTheoremToHint (name : Name) (prio : Nat) : MetaM Hint := do
  let expr ← mkConstWithFreshMVarLevels name
  let type ← inferType expr
  let (_, _, type) ← forallMetaTelescope type
  trace[Meta.Tactic.grewrite.hints]m!"insert: {type}, {name}"
  let arr ← DiscrTree.mkPath type
  pure ⟨name, prio, arr⟩

-- For relations create new Attribute (e.g. grewrite_rel) but reuse dbEx
syntax (name := grw) "grw" (num "%")? : attr

initialize registerBuiltinAttribute {
  name := `grw
  descr := "Register theorems to be used in the proof search for the grewrite tactic"
  add := fun name stx kind => do
    match stx with
    | `(grw| grw $n:num %) =>
      let (hint, _) ← convertTheoremToHint name n.getNat |>.run
      dbEx.add hint kind
    | `(grw| grw) =>
      let (hint, _) ← convertTheoremToHint name 100 |>.run
      dbEx.add hint kind
    | _ => Elab.throwUnsupportedSyntax
}

end Attribute
