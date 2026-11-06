import Verso
import VersoManual
import VersoBlueprint
import NcCubic

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Bilinear forms and Lie-theoretic normal form" =>

The decisive step is Lemma 3.2 of the source: a basepoint-free
linear system of symmetric bilinear forms compatible with a trivector
forces the trivector to split into disjoint three-dimensional volume
elements. Do not confuse the obstruction calculation with the
existence of the witnesses required to apply it.

:::lemma "L0"
A basepoint-free linear subspace of symmetric bilinear forms on
a finite-dimensional vector space over an infinite field contains
a nondegenerate form. The intended proof is the maximal-rank
determinant argument, rather than a general Bertini theorem.
:::

:::lemma "L1" (uses := "P0, L0")
Construct the Lie bracket from a trivector and a nondegenerate
compatible symmetric bilinear form on its support. Prove its
Jacobi identity, perfectness, and trivial center on the support.
:::

:::lemma "L2" (lean := "NcCubic.LieObstruction.no_highest_root_witness")
The four-term compatibility relation implies isotropy for a vector
admitting an explicit highest-root-type witness, and contradicts a
basepoint-free family. The radical-type witness is also implemented
as a separate Lean lemma. **The existence of the witnesses is not
proved here.**
:::

:::proof "L2"
The substitutions in Equation (3.2) of the manuscript are proved
in NcCubic/LieObstruction.lean. The corresponding contradiction
lemmas require explicitly supplied nonzero witnesses and are
conditional on those hypotheses.
:::

:::lemma "L3" (uses := "L1, L2")
Construct a nonzero radical-type witness from any nontrivial
solvable radical, using the representation of the semisimple
quotient, and conclude that the radical vanishes.
:::

:::lemma "L4" (uses := "L3, L2")
Exclude simple factors of rank at least two by constructing
a highest-root witness. Prove that the remaining simple factors
are three-dimensional and of type sl2.
:::

:::theorem "L5" (uses := "L4")
Recover the original trivector from the Cartan three-form and
split it as a sum of independent nonzero volume trivectors
on three-dimensional direct summands.
:::
