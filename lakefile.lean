import Lake
open Lake DSL

package nc_cubic where
  -- The mathematical code remains independent of Verso.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

-- Focused CM/Koszul imports close the gradient-syzygy obligation P2.
-- This is the same Stacks revision already checked by integrations/stacks.
require Stacks from git
  "https://github.com/AxiomMath/Stacks.git" @
  "5ed82d14634e8d9576bb844c7bd4e3da66d450e7"

lean_lib NcCubic where

/--
Default `lake build` entry point: build proof code, audit, then
build the Stacks adapters and render the Verso Blueprint.
Subprocesses never recursively invoke the root default target.
-/
@[default_target]
target fullProject pkg : Unit := do
  let proofJob ← NcCubic.fetch
  Job.async do
    let _ ← proofJob.await
    proc {
      cmd := "bash"
      args := #["scripts/full_build.sh"]
      cwd := pkg.dir
    }
