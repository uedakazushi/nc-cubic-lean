# Verso Blueprint: Codex handoff

2026-11-07 / v0.2.0.

VersoBlueprint v4.35.0 has been added as a separate Lake package in
`blueprint/verso`. Read its README and the root AGENTS.md.

For the first run:

1. `bash scripts/bootstrap.sh` from the repo root if the main Lean
   dependencies are not present.
2. `python3 scripts/check_blueprint.py` to verify graph labels and edges.
3. `bash scripts/build_blueprint.sh` to resolve dependencies and
   render the Blueprint site.
4. Fix API/package incompatibilities revealed by actual Lean compilation.
   Do not weaken the main proof target.
5. Check the new subpackage lockfile against mathlib and root lock.
   Commit the lockfile only after a successful resolution and build.
6. Update `docs/STATUS.md` with actual verification outcomes, then
   fast-forward push to main.

No GitHub Actions, Pages deployment or external publication is configured.
If network access denies GitHub release asset redirects, check exact hosts
rather than bypassing the policy. The existing main Lean project remains
independent of this documentation package.

Maintain a single task registry in `blueprint/tasks.json` and labeled
mathematical statements in the Verso chapters. Use stable labels and
`(lean := "Qualified.Theorem.Name")` only for declarations that exist
and faithfully support the relevant claim.
