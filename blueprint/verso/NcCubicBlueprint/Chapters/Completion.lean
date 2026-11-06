import Verso
import VersoManual
import VersoBlueprint
import NcCubic

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Affine and projective classification" =>

The original theorem concerns every Poisson bivector section on the
smooth projective cubic. The polynomial calculation on the affine
cone alone is not sufficient: the geometric representation and
extension statements in Section 2 must be formalized too.

:::theorem "A" (uses := "P3, P4, L5, P5, P6b")
Prove the full affine polynomial classification, represented by
NcCubic.AffineClassificationStatement. The goal is a genuine
Lean theorem named `NcCubic.theorem113_affine`. The current declaration
AffineClassificationStatement is a definition of a proposition, not
the proof.
:::

:::lemma_ "G0" (uses := "P2, P0")
Prove the representation and uniqueness of projective bivector
fields on a smooth cubic in terms of constant trivectors.
This requires the Euler sequence, cohomological vanishings,
and the graded Koszul calculation from the source Section 2.
:::

:::lemma_ "G1" (uses := "G0, P2")
Show that a Poisson bivector on the cubic lifts to a
Poisson structure on the affine cone, not merely a tangent
bivector, by the divergence and Euler-field argument.
:::

:::lemma_ "G2" (uses := "G0, P0, P6b")
Connect projective smoothness and the geometric Poisson
section to the polynomial Lean model, and prove the
descent and inverse construction in the correct categories.
:::

:::theorem "T" (uses := "A, G0, G1, G2")
Formalize the actual Theorem 1.1(3) on smooth complex
projective cubic hypersurfaces, with the original hypotheses,
normal form, and converse. The final theorem must be named
NcCubic.theorem113; its type is to be independently reviewed
against the paper. All present classification goals remain open.
:::
