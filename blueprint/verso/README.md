# Verso Blueprint (Lean 4.35.0)

2026-11-07 / v0.2.0. This is an **independent Lake package** within the
nc-cubic repository. It renders the theorem dependency graph, progress
summary, and mathematical chapters using the official
[`VersoBlueprint`](https://github.com/leanprover/verso-blueprint)
package at the **v4.35.0** tag. It is not the generic Verso manual alone.

The main proof library and Stacks adapter remain separately pinned and
unchanged. The local dependency on `../..` imports the actual project
declarations. GitHub Actions are deliberately not configured.

## Build locally or in Codex

First set up the main proof workspace from the repository root:

```bash
bash scripts/bootstrap.sh
```

Then, from the root directory:

```bash
bash scripts/build_blueprint.sh
```

The script resolves the Blueprint package dependencies and invokes
`lake exe vbp build`. It renders to
`blueprint/verso/_out/site/html-multi/` with a generated overview,
dependency graph, and progress summary. Open the generated `index.html`
locally, or serve the directory with a simple local HTTP server. Nothing
is uploaded to GitHub Pages.

This build requires network access for the initial VersoBlueprint,
Verso and auxiliary dependency checkout and cache/artifacts. The first
successful `lake update` generates a `lake-manifest.json` for this
subproject. **That lockfile is not committed in this initialization
because this environment could not perform the dependency fetch**.
After a successful build, commit its lockfile and check compatibility
with the root mathlib revision. Until then, reproducible *complete*
dependency closure is not independently verified.

The Verso package and all source modules were selected using upstream
v4.35.0 template paths. No actual site generation has been run during
this initialization, so any import/API error must be corrected through
a real Lean build; do not report an HTML site as built yet.

## What is linked to Lean?

The labeled nodes match the IDs in
[`blueprint/tasks.json`](../tasks.json): P0–P6b, L0–L5, A,
G0–G2 and T. The two currently proved task nodes have an external
Lean association:

- `P6a` -> `NcCubic.Jacobian.jacobi`
- `L2` -> `NcCubic.LieObstruction.no_highest_root_witness`

Each denotes a representative proved theorem. Other declarations
from the same files are mentioned in prose. These two nodes are
marked proved in the task register because the full task acceptance
criteria were checked in the main library, **not merely because
one associated theorem has a successful kernel check**.

Open tasks are informal Blueprint nodes. Do **not** introduce a
`sorry` theorem to get a progress marker. The full target is defined
as a Lean proposition in `NcCubic/Statement.lean`, but not proven.
`A` and `T` must stay visibly open.

## Source of truth and synchronization

- The Verso chapter files are the human-readable *mathematical story*
  and encode dependencies using `(uses := "...")`.
- `blueprint/tasks.json` is the authoritative machine-readable
  task registry, with acceptance criteria and task statuses.
- The Lean kernel and `scripts/check.sh` are authoritative about
  proof correctness; an association in a document is not a proof.
- When a node is proved or split, update the relevant Verso chapter
  **and** tasks.json as one coherent change. Check that the label
  sets and dependency edges agree using `scripts/check_blueprint.py`.
- When adding a new Lean theorem, link it with the `(lean := "...")`
  attribute in the relevant Verso node, or adopt the upstream
  `@[blueprint "label"]` mechanism once the main Lean workspace
  intentionally depends on VersoBlueprint.

The planned extension of the project is to use declarative attributes
on Lean theorems for automatic cross-references and inferred
dependencies. This has **not** been enabled in the mathlib-only proof
workspace to avoid adding a heavy documentation dependency there.

## Manual and template

- https://github.com/leanprover/verso-blueprint/blob/v4.35.0/doc/GETTING_STARTED.md
- https://github.com/leanprover/verso-blueprint/blob/v4.35.0/doc/MANUAL.md
- https://github.com/leanprover/verso-blueprint/tree/v4.35.0/project_template

## Root default build

The repository root has a custom default Lake target. Once Lean 4.35.0
is installed, run `lake build` **at the root** to build the main proof
library, audit it, build/audit the selected Stacks adapters, and render this
Verso site. Use `lake build NcCubic` to build only the proof library.
The new root custom target and Verso dependency closure have not yet passed
an end-to-end build in a fresh clone. Treat any first-run failure as a
required repair task, not as a successful verification.
