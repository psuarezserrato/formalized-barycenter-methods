import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.MeasureTheory.Measure.Hausdorff
import DifferentialGeometry.Geometry.CenterOfMass.Basic
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BusemannHessian
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Busemann.Cocycle
import BCG.LinearAlgebra.TraceDet
import BCG.LinearAlgebra.BarycenterOperator
import BCG.Entropy.VolumeEntropy
import BCG.Hyperbolic.BarycenterFunctional
import BCG.Hyperbolic.NaturalMap
import BCG.Hyperbolic.JacobianBound
import BCG.Rigidity.EqualityCase
import BCG.RankOne.BusemannHessian
import BCG.RankOne.AssociativeCase
import BCG.RankOne.OctonionicCase
import BCG.MainTheorem

/-!
# Besson–Courtois–Gallot Barycenter Method (`formalized-barycenter-methods`)

Root module for the Lean 4 formalization of the Besson–Courtois–Gallot (1995), Souto (2008),
and Ruan (2024) barycenter method across smooth real hyperbolic manifolds, associative rank-one
locally symmetric spaces $\mathbb{K}\mathbf{H}^m$ ($\mathbb{K} \in \{\mathbb{R}, \mathbb{C}, \mathbb{H}\}$),
and the 16-dimensional Cayley hyperbolic plane $\mathbb{O}\mathbf{H}^2$.

Integrates Mathlib (`v4.35.0`) with the vendored `DifferentialGeometry.*` subset (`v0.1.5`).
Non-smooth $\mathsf{RCD}(K, N)$ and Alexandrov extensions live in the companion subrepositories
`rcd-entropy-degree-rigidity/` and `alexandrov-entropy-degree-applications/`.
-/
