import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Volume Entropy and Exponentially Weighted Measures (`μ_x^s`)

This file defines the volume entropy / critical exponent of a metric-measure space $(X, d, \mu)$
and the Besson–Courtois–Gallot family of exponentially weighted measures
$$d\mu_x^s(z) = e^{-s \, d(x, z)} \, d\mu(z),$$
together with their fundamental analytical properties.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BCG.Entropy

variable {X : Type*} [PseudoMetricSpace X]

/-- The exponential distance weight $w_x^s(z) = e^{-s \, d(x, z)}$. -/
def exponentialWeight (s : ℝ) (x z : X) : ℝ :=
  Real.exp (-s * dist x z)

/-- The exponential distance weight is continuous in the second variable. -/
theorem continuous_exponentialWeight (s : ℝ) (x : X) :
    Continuous (exponentialWeight s x) :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_const.dist continuous_id))

/-- The exponential distance weight is strictly positive everywhere. -/
theorem exponentialWeight_pos (s : ℝ) (x z : X) : 0 < exponentialWeight s x z :=
  Real.exp_pos _

/-- The exponential distance weight is nonnegative everywhere. -/
theorem exponentialWeight_nonneg (s : ℝ) (x z : X) : 0 ≤ exponentialWeight s x z :=
  (exponentialWeight_pos s x z).le

/-- At the basepoint $z = x$, the exponential distance weight equals $1$. -/
@[simp]
theorem exponentialWeight_self (s : ℝ) (x : X) : exponentialWeight s x x = 1 := by
  simp [exponentialWeight]

/-- Triangle inequality ratio bound for the exponential distance weight ($s \ge 0$):
$$e^{-s \, d(x, y)} \, e^{-s \, d(y, z)} \le e^{-s \, d(x, z)}.$$ -/
theorem exponentialWeight_mul_le {s : ℝ} (hs : 0 ≤ s) (x y z : X) :
    exponentialWeight s x y * exponentialWeight s y z ≤ exponentialWeight s x z := by
  dsimp [exponentialWeight]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have htri : dist x z ≤ dist x y + dist y z := dist_triangle x y z
  nlinarith

/-- Basepoint comparison for the exponential distance weight ($s \ge 0$):
$$e^{-s \, d(y, z)} \le e^{s \, d(x, y)} \, e^{-s \, d(x, z)}.$$ -/
theorem exponentialWeight_le_mul_exp_dist {s : ℝ} (hs : 0 ≤ s) (x y z : X) :
    exponentialWeight s y z ≤ Real.exp (s * dist x y) * exponentialWeight s x z := by
  dsimp [exponentialWeight]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have htri : dist x z ≤ dist x y + dist y z := dist_triangle x y z
  nlinarith

variable [MeasurableSpace X]

/-- The critical exponent (or Poincaré exponent) of a metric-measure space $(X, d, \mu)$ with
respect to a basepoint $x_0 \in X$:
$$h_{\mathrm{crit}}(X, \mu, x_0) = \inf \left\{ s \ge 0 \;\middle|\;
  \int_X e^{-s \, d(x_0, z)} \, d\mu(z) < \infty \right\}.$$ -/
def criticalExponent (μ : Measure X) (x₀ : X) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ Integrable (fun z => Real.exp (-s * dist x₀ z)) μ}

/-- Integrability of `exponentialWeight s x` is independent of the basepoint `x` when `s ≥ 0`. -/
theorem integrable_exponentialWeight_of_integrable [OpensMeasurableSpace X]
    {μ : Measure X} {s : ℝ} (hs : 0 ≤ s) {x : X} (hx : Integrable (exponentialWeight s x) μ)
    (y : X) : Integrable (exponentialWeight s y) μ := by
  refine (hx.const_mul (Real.exp (s * dist x y))).mono'
    (continuous_exponentialWeight s y).aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_of_nonneg (exponentialWeight_nonneg s y z)]
  exact exponentialWeight_le_mul_exp_dist hs x y z

/-- Equivalence of integrability of `exponentialWeight s` across basepoints `x, y : X`. -/
theorem integrable_exponentialWeight_iff [OpensMeasurableSpace X]
    {μ : Measure X} {s : ℝ} (hs : 0 ≤ s) (x y : X) :
    Integrable (exponentialWeight s x) μ ↔ Integrable (exponentialWeight s y) μ :=
  ⟨fun hx => integrable_exponentialWeight_of_integrable hs hx y,
   fun hy => integrable_exponentialWeight_of_integrable hs hy x⟩

/-- The critical exponent is independent of the choice of basepoint $x_0 \in X$. -/
theorem criticalExponent_eq [OpensMeasurableSpace X] (μ : Measure X) (x y : X) :
    criticalExponent μ x = criticalExponent μ y := by
  dsimp [criticalExponent, exponentialWeight]
  congr 1
  ext s
  simp only [mem_ofPred_eq, and_congr_right_iff]
  intro hs
  exact integrable_exponentialWeight_iff hs x y

/-- The BCG exponentially weighted measure $\mu_x^s = e^{-s \, d(x, \cdot)} \mu$. -/
def exponentialMeasure (μ : Measure X) (s : ℝ) (x : X) : Measure X :=
  μ.withDensity (fun z => ENNReal.ofReal (exponentialWeight s x z))

end BCG.Entropy
