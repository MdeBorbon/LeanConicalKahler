import ConicalKahler
import ConicalKahlerTest

/-!
# Axiom audit

Fails (with an error) if any declaration in the `ConicalKahler` namespace depends on an axiom
other than `propext`, `Classical.choice` and `Quot.sound` (in particular `sorryAx`, or any
`axiom` declared in this project). Run with `lake env lean scripts/AxiomAudit.lean`.
-/

open Lean Elab Command

elab "#audit_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name) := #[]
  let mut count : Nat := 0
  for (n, _) in env.constants.map₁.toList do
    if (`ConicalKahler).isPrefixOf n && !n.isInternal then
      count := count + 1
      let axs ← Lean.collectAxioms n
      for a in axs do
        unless allowed.contains a do
          bad := bad.push (n, a)
  if bad.isEmpty then
    logInfo m!"Axiom audit passed: {count} declarations in `ConicalKahler` use only \
      propext, Classical.choice, Quot.sound."
  else
    throwError m!"Axiom audit FAILED: {bad.toList}"

#audit_axioms
