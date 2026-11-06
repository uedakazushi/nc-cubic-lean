import Verso
import VersoManual
import VersoBlueprint
import NcCubic

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Polynomial and Hessian foundations" =>

The affine model uses a homogeneous cubic F in N variables and a
constant alternating trivector P. Its coefficient bivector is
obtained by contraction with the gradient of F.

:::definition "P0"
Establish the correspondence between the alternating trilinear map used
by the Lean model, an element of the third exterior power, contraction,
and the change-of-basis formula. The current definitions compile, but
the required comparison theorems remain open.
:::

:::lemma_ "P1"
For homogeneous cubics, prove Euler's identity and the symmetry of the
Hessian, including the formula relating Hessian evaluation to the
differential of the cubic.
:::

:::lemma_ "P2" (uses := "P1")
Show that the gradient of a smooth projective cubic forms a regular
sequence and therefore has no syzygies with coefficients of degrees
zero or one. The Stacks Koszul adapter proves a conditional general
result, not this application.
:::

:::lemma_ "P3" (uses := "P0, P1, P2")
Prove that the Jacobi identity for the bracket induced by contraction
with the gradient is equivalent to every Hessian belonging to the
linear space K(P). Include the passage from generator Jacobi
to Jacobi for all polynomials.
:::

:::lemma_ "P4" (uses := "P1")
Use smoothness and the cubic Hessian identity to show that the Hessian
linear system is basepoint-free on projective space.
:::

:::lemma_ "P5" (uses := "P3, L5, L2")
Show that vanishing mixed Hessian entries between different active
blocks forces a decomposition of the cubic into terms using one active
block and the shared central variables.
:::

:::theorem "P6a" (lean := "NcCubic.Jacobian.jacobi")
The Jacobian bracket of one three-variable polynomial potential
satisfies the full Jacobi identity for all polynomials. The existing
Lean file also establishes skew-symmetry, Leibniz, the potential as
Casimir, and centrality of the other variables.
:::

:::proof "P6a"
Proved in NcCubic/Jacobian.lean, by expanding formal derivatives,
commuting mixed partial derivatives, and applying polynomial
normalization. This completes the single-block algebraic task only.
:::

:::lemma_ "P6b" (uses := "P6a, P0")
Prove that several independent active blocks with common central
variables define a Poisson bracket, and prove covariance under
the chosen linear coordinate transformation.
:::