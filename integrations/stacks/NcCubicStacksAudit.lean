import NcCubicStacks
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

/-- Inspect the adapter declarations and their transitive axiom dependencies.
This does not enumerate the whole Stacks library. -/
elab "#audit_nc_cubic_stacks" : command => do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`NcCubicStacks).isPrefixOf name then
      count := count + 1
      let axioms ← collectAxioms name
      let forbidden := axioms.filter (fun ax => !allowed.contains ax)
      unless forbidden.isEmpty do
        throwError "Unapproved transitive axioms in {name}: {forbidden}"
  if count < 2 then
    throwError "Expected at least two NcCubicStacks adapter declarations; found {count}."
  logInfo m!"Axiom audit passed for {count} NcCubicStacks declarations. Allowed: {allowed}"

#check NcCubicStacks.h1Regular_of_regular
#check NcCubicStacks.syzygy_mem_relSpan_of_regular
#audit_nc_cubic_stacks
