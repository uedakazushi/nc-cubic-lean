import NcCubic
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

/-- Audit every imported project declaration, not just a hand-picked theorem. -/
elab "#audit_nc_cubic" : command => do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`NcCubic).isPrefixOf name then
      count := count + 1
      let axioms ← collectAxioms name
      let forbidden := axioms.filter (fun ax => !allowed.contains ax)
      unless forbidden.isEmpty do
        throwError "Unapproved transitive axioms in {name}: {forbidden}"
  if count == 0 then
    throwError "No NcCubic declarations audited; check the root imports."
  logInfo m!"Axiom audit passed for {count} NcCubic declarations. Allowed: {allowed}"

#audit_nc_cubic
