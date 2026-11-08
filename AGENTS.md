# nc-cubic-lean: autonomous formalization instructions

This repository formalizes **Theorem 1.1, item (3)** of
`paper/cubic_poisson_paper_20261104.pdf` (printed pp. 2–3), also called
“Theorem 1.1.3” by the user. Read `docs/RESEARCH_PLAN.md` first, then
`docs/STATUS.md`, `blueprint/README.md`, and `blueprint/tasks.json`.

## Objective and scope

Prove the block normal form for every nonzero Poisson structure on a smooth
complex projective cubic of dimension at least three, and its converse.
The polynomial classification is an intermediate target. Proving that target
does not prove the original geometric theorem until Section 2's representation,
Jacobi lifting, and descent/comparison results are supplied. Do not enlarge the
first goal to quantization, moduli, degeneracy schemes, or general ranks.

## Work without repeated approval

Run `python3 scripts/next_task.py` and choose a ready mathematical task in the
current priority order in `blueprint/tasks.json`; read its
dependencies and acceptance criterion. Search the pinned mathlib and Stacks
sources before reimplementing a result. Split independent tasks among agents
when useful, with disjoint file ownership. Prove a useful lemma, build it, audit
it, and continue to the next ready task. If blocked, work on another ready node
and leave a precise current blocker and next experiment in the research notes.
Do not repeatedly request permission for ordinary proofs, refactoring, dependency
inspection, or commits. Ask only for a material change of mathematical scope,
unavailable credentials/access, or a genuinely destructive operation.

Keep source, definitions, hypotheses, and proof status aligned. The paper is an
input to verify, not an oracle. If a claim is wrong, repair the statement and all
dependent claims, and record the useful counterexample or obstacle. Do not weaken
the target silently to make a proof succeed.

## Trusted mathematical code

- Keep all production declarations under `NcCubic` and import them from
  `NcCubic.lean`. Use focused imports, not `import Mathlib` or `import Stacks`.
- No `sorry`, `admit`, custom `axiom`, `sorryAx`, `unsafe` proof shortcuts,
  `native_decide`, `implemented_by`, or disabled kernel checking in production.
- Unproved targets belong in clearly labelled proposition definitions or the
  blueprint. A definition of a proposition is not a proof. Do not assume the
  desired conclusion, hide it in a typeclass, or introduce an opaque oracle.
- Explicit conditional helper lemmas are useful. Their hypotheses must be
  visible; they do not close the unconditional target.
- `scripts/check.sh` builds the library, audits all declarations in the
  `NcCubic` namespace, and checks project metadata. Allowed logical axioms:
  `propext`, `Classical.choice`, `Quot.sound` only. Symbolic experiments guide
  proofs but do not count as Lean proofs.
- `scripts/check.sh --complete` is a separate final gate. Never make it succeed
  until the original geometric theorem has been stated faithfully and proved.
- Independently review the actual final Lean type against the paper; a successful
  kernel check does not establish faithfulness to the informal statement.

## Dependencies and execution

Lean and mathlib are pinned. Run `bash scripts/bootstrap.sh` once, then
`bash scripts/check.sh`. The optional Stacks package is under
`integrations/stacks/`; read its README before building it. Inspect the actual
Lean statement and source tag of each imported theorem, particularly Frontier
results. Preserve upstream notices when adapting code. Pin any new dependency
and document why it closes a concrete gap. Do not update all dependencies merely
because a newer version exists.

Respect configured proxy, TLS, credentials, and domain policy. A redirect target
may need its own domain entry; do not try to evade a denied destination. Never
print credentials or add them to the repository. A machine-specific runtime
workaround must be documented separately from the mathematical proof.

## Git and handoff

Use the existing private repository `uedakazushi/nc-cubic-lean` and `main`; no GitHub Actions or PR workflow
is needed. The user has authorized saving this project. Commit coherent verified
changes and push to `main` when access is available. Check the remote head first;
use ordinary fast-forward updates, never force-push or discard others' work.
During a long session, save a coherent checkpoint approximately every 30 minutes
and at the end. Do not send messages, open external issues, or contact maintainers
without explicit permission.

Update the current `docs/STATUS.md` and task states; do not accumulate session
logs or old bundles. Report separately what was written, what Lean checked, what
was audited, and what was pushed. Do not call the whole theorem complete merely
because the current library builds.

## Research documents

Use Japanese for project explanations and LuaLaTeX for a new mathematical paper
unless instructed otherwise. Do not create a public paper before there are
substantive verified results. Keep the current research plan, useful notes,
source paper, blueprint, bibliography, and reproduction commands self-contained.
Preserve valid valuable mathematics; remove histories, duplicate files, old ZIPs,
and build artifacts. The general research principles in `docs/RESEARCH_PLAN.md`
apply throughout. Git-backed project files are persisted in this repository.

## Verso mathematical Blueprint

The authored Verso chapters are in `blueprint/verso/NcCubicBlueprint/Chapters/`.
This is a separate Lake package that uses VersoBlueprint v4.35.0; do not add
Verso to the main mathlib-only root package just for documentation.
Both independent workspaces use the same pinned dependency package directory,
root `.lake/packages/`, via `packagesDir = "../../.lake/packages"`. This shares
Git checkouts and compiled Mathlib/Stacks artifacts, while keeping their own
local targets and site outputs. Never revert to separate package stores.
To reuse pre-existing legacy builds, run `scripts/reuse_legacy_builds.py --apply`
only while no Lake or Lean build is running. The migration does not delete
legacy caches; only clean them up after a successful build.
After changing a task or proof, run `python3 scripts/check_blueprint.py`
and update the corresponding labeled Verso statement. When dependencies are
available, run `bash scripts/build_blueprint.sh` and check the HTML graph,
summary, links, and the LuaLaTeX-generated PDF at
`blueprint/verso/_out/site/pdf/main.pdf`. The PDF build requires LuaTeX-ja
for Japanese text. Do not silently skip PDF if the TeX toolchain is missing.
No GitHub Actions or GitHub Pages setup is authorized.
The Verso build, generated HTML/data checks, and resolved lockfile were verified
in the prepared cloud environment on 2026-11-07. Preserve the pinned lockfile.

## Default build entry point (v0.3.0)

Root `lake build` is intended to run NcCubic build, global axiom audit,
Stacks adapter build/audit, Blueprint consistency check, and Verso HTML +
LuaLaTeX PDF rendering through a default Lake custom target and `scripts/full_build.sh`.
Do not remove these checks to mask a dependency or build failure.
For fast proof iterations, `lake build NcCubic` remains available; use
`lake build` before reporting a verified, complete project checkpoint.
The full custom target passed on Lean 4.35.0 in the prepared cloud environment
on 2026-11-07. Continue to run it for complete checkpoints; a fresh-clone
dependency download has not been independently tested.
