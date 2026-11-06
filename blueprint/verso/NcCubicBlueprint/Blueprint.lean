import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import NcCubic
import NcCubicBlueprint.Chapters.Foundations
import NcCubicBlueprint.Chapters.LieTheory
import NcCubicBlueprint.Chapters.Completion

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Cubic Poisson structures: Lean Blueprint" =>

This is the working mathematical blueprint for Theorem 1.1(3) of the
supplied manuscript dated 2026-11-04. It describes the normal form of
Poisson structures on smooth complex projective cubic hypersurfaces
of dimension at least three.

*The classification theorem is not yet formalized.* A Lean-compilable
definition of the affine target is not a proof of that target. The project
also requires a separate geometric bridge from Poisson bivector sections
on the projective hypersurface to the polynomial model.

The stable labels P0–P6b, L0–L5, A, G0–G2 and T follow the
task register at blueprint/tasks.json in the repository. This document
shows the dependencies and the selected existing Lean declarations;
a completed task must satisfy its full acceptance criteria, not only
compile one helper lemma.

{include 0 NcCubicBlueprint.Chapters.Foundations}
{include 0 NcCubicBlueprint.Chapters.LieTheory}
{include 0 NcCubicBlueprint.Chapters.Completion}

{blueprint_graph}

{blueprint_summary}
