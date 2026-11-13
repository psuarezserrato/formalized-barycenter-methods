import BCG.Hyperbolic.NaturalMap

/-!
# Manifold-Level Implicit Differentiation & Jacobian Bound of the Hyperbolic Barycenter Map

This file performs **Step 2** of the Besson–Courtois–Gallot (BCG) formalization on the real
hyperbolic space `Hyperboloid E`:

1. **Explicit Busemann Differential & Unit Riemannian Gradient (`hyperboloidBusemannDiff_spaceVectorField`,
   `busemannGradientVector`, `riemannianMetric_inner_busemannGradient`, `riemannianMetric_norm_busemannGradient`)**:
   For every $\xi \in S(E)$ and $p \in \mathrm{Hyperboloid}(E)$,
   $$\exp(B_\xi(p)) \, dB_\xi(p)(u) = \frac{\langle p.\mathrm{space}, u \rangle}{p.\mathrm{time}} - \langle \xi, u \rangle,$$
   and the Riemannian gradient $\nabla B_\xi(p) = \mathrm{spaceVectorField}(p.\mathrm{space} - \exp(B_\xi(p))^{-1} \xi, p)$
   satisfies $g_p(\nabla B_\xi(p), u) = dB_\xi(p)(u)$ and $g_p(\nabla B_\xi(p), \nabla B_\xi(p)) = 1$.

2. **Canonical Riemannian Metric Gauge (`metricGauge`, `metricGaugeInv`, `metricGaugeEquiv`)**:
   Constructs the explicit rank-one perturbation of the identity $A_p : E \simeq_l[\mathbb{R}] E$,
   $$A_p(v) = v - \frac{\langle p.\mathrm{space}, v \rangle}{p.\mathrm{time}(p.\mathrm{time} + 1)} p.\mathrm{space}, \qquad
     A_p^{-1}(w) = w + \frac{\langle p.\mathrm{space}, w \rangle}{p.\mathrm{time} + 1} p.\mathrm{space},$$
   which is an exact isometry between $(T_p(\mathrm{Hyperboloid}\,E), g_p)$ and the model Euclidean
   space $(E, \langle \cdot, \cdot \rangle_E)$:
   $$\langle A_p v, A_p u \rangle_E = g_p(\mathrm{spaceVectorField}\,v\,p, \mathrm{spaceVectorField}\,u\,p).$$
   Under $A_p$, the Busemann gradient $\nabla B_\xi(p)$ maps to a unit Euclidean vector
   `euclideanBusemannGrad ξ p : E` with $\|u_{\mathrm{Bus}}(\xi, p)\|_E = 1$.

3. **Explicit Fréchet & Manifold Differential of `hyperboloidBarycenter` (`hasFDerivAt_normalizeFuture_space`,
   `riemannianMetric_inner_normalizeFuture_deriv`, `riemannianMetric_inner_barycenter_mfderiv`)**:
   Differentiating the smooth barycenter map $F(x) = \mathrm{hyperboloidBarycenter}(w(x), \xi, hw(x))$
   along any tangent vector $\dot{x} \in T_x X$ yields the exact identity:
   $$g_{F(x)}\big(dF_x(\dot{x}), u\big) =
     -\frac{1}{\mathcal{B}_{w(x), \xi}(F(x))} \sum_{i \in \iota} d(w_i)_x(\dot{x}) \exp(B_{\xi_i}(F(x))) \, dB_{\xi_i}(F(x))(u).$$
   For exponential weights $w_i(x) = c_i \exp(-s \beta_i(x))$, this simplifies to:
   $$g_{F(x)}\big(dF_x(\dot{x}), u\big) =
     s \sum_{i \in \iota} \mu_i(w(x), \xi) \, d\beta_i(x)(\dot{x}) \, dB_{\xi_i}(F(x))(u).$$

4. **Exact Factorization as `busemannCrossOperator` & Pointwise Jacobian Bound
   (`riemannianDifferential_eq_busemannCrossOperator`, `abs_det_riemannianDifferential_le`)**:
   Expressed in the canonical Riemannian gauge $A_{F(x)}$, the differential $D^{\mathrm{Riem}} F(x) : E \to_l[\mathbb{R}] E$
   is identically equal to `busemannCrossOperator s Finset.univ (barycenterProbWeight (w x) ξ (hw x)) (u₁ x) (fun i => euclideanBusemannGrad (ξ i) (F x))`,
   and therefore satisfies the BCG Jacobian determinant bound:
   $$\big|\det\big(D^{\mathrm{Riem}} F(x)\big)\big| \le \left(\frac{s}{n}\right)^n.$$
-/

noncomputable section

open Finset BigOperators
open scoped Manifold ContDiff

namespace BCG.Hyperbolic

open DifferentialGeometry
open DifferentialGeometry.Hyperboloid
open DifferentialGeometry.Geometry.Operator
open BCG.LinearAlgebra

section BusemannDifferentialAndGauge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- In the global `spaceDiffeomorph` chart on `Hyperboloid E`, the Riemannian metric inner product
of `spaceVectorField v p` and `spaceVectorField w p` is
$\langle v, w \rangle - \langle p.\mathrm{space}, v \rangle \langle p.\mathrm{space}, w \rangle / p.\mathrm{time}^2$. -/
theorem riemannianMetric_inner_spaceVectorField_eq
    (p : Hyperboloid E) (v w : E) :
    riemannianMetric.inner p (spaceVectorField v p) (spaceVectorField w p) =
      inner ℝ v w - inner ℝ p.space v * inner ℝ p.space w / p.time ^ 2 := by
  rw [riemannianMetric_inner, mfderiv_spaceDiffeomorph, p.time_sq]
  rfl

private theorem hasFDerivAt_time_ofSpace' (p : Hyperboloid E) :
    HasFDerivAt (fun y : E => (ofSpace y).time)
      (p.time⁻¹ • innerSL ℝ p.space) p.space := by
  have hd : HasFDerivAt (fun y : E => 1 + ‖y‖ ^ 2) (2 • innerSL ℝ p.space) p.space := by
    simpa only [zero_add] using!
      (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) p.space).add
        (hasStrictFDerivAt_norm_sq p.space).hasFDerivAt
  have hf := hd.sqrt (show (1 + ‖p.space‖ ^ 2 : ℝ) ≠ 0 by positivity)
  have he : (1 / (2 * Real.sqrt (1 + ‖p.space‖ ^ 2))) • (2 • innerSL ℝ p.space) =
      p.time⁻¹ • innerSL ℝ p.space := by
    rw [← p.time_eq_sqrt]
    ext w
    simp only [ContinuousLinearMap.smul_apply, two_smul, ContinuousLinearMap.add_apply, smul_eq_mul]
    field_simp
    ring
  exact he ▸ hf

private theorem hasFDerivAt_expBusemann_ofSpace (ξ : Metric.sphere (0 : E) 1) (p : Hyperboloid E) :
    HasFDerivAt (fun y : E => expHyperboloidBusemann ξ (ofSpace y))
      (p.time⁻¹ • innerSL ℝ p.space - innerSL ℝ (ξ : E)) p.space := by
  have h_eq : (fun y : E => expHyperboloidBusemann ξ (ofSpace y)) =
      (fun y : E => (ofSpace y).time - inner ℝ (ξ : E) y) := by
    funext y
    rw [expHyperboloidBusemann_eq, space_ofSpace]
  rw [h_eq]
  exact (hasFDerivAt_time_ofSpace' p).sub (innerSL ℝ (ξ : E)).hasFDerivAt

private theorem mvfderiv_comp_space' (F : E → ℝ) (p : Hyperboloid E) (v : E)
    (hF : DifferentiableAt ℝ F p.space) :
    mvfderiv 𝓘(ℝ, E) (fun y : Hyperboloid E => F y.space) p (spaceVectorField v p) =
      fderiv ℝ F p.space v := by
  change mvfderiv 𝓘(ℝ, E) (fun y : Hyperboloid E => F (spaceDiffeomorph y)) p
    (spaceVectorField v p) = _
  rw [mvfderiv_comp_diffeomorph F spaceDiffeomorph p (spaceVectorField v p)
    hF.mdifferentiableAt, mvfderiv_model_apply_eq_fderiv, mfderiv_spaceDiffeomorph]
  rfl

/-- **Explicit Formula for the Busemann Differential on `Hyperboloid E`**:
$$dB_\xi(p)(\mathrm{spaceVectorField}\,v\,p) =
  \frac{\langle p.\mathrm{space}, v \rangle / p.\mathrm{time} - \langle \xi, v \rangle}{\exp(B_\xi(p))}.$$ -/
theorem hyperboloidBusemannDiff_spaceVectorField
    (ξ : Metric.sphere (0 : E) 1) (p : Hyperboloid E) (v : E) :
    hyperboloidBusemannDiff ξ p (spaceVectorField v p) =
      (inner ℝ p.space v / p.time - inner ℝ (ξ : E) v) / expHyperboloidBusemann ξ p := by
  have hd := (hasFDerivAt_expBusemann_ofSpace ξ p).log
    (by simpa only [ofSpace_space] using (expHyperboloidBusemann_pos ξ p).ne')
  have he : hyperboloidBusemann ξ =
      fun y : Hyperboloid E => Real.log (expHyperboloidBusemann ξ (ofSpace y.space)) := by
    funext y
    rw [ofSpace_space, expHyperboloidBusemann, Real.log_exp]
  unfold hyperboloidBusemannDiff
  rw [he, mvfderiv_comp_space' _ p v hd.differentiableAt, hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ofSpace_space,
    innerSL_apply_apply, smul_eq_mul, inv_mul_eq_div]

/-- Multiplying the Busemann differential by $\exp(B_\xi(p))$ gives the linear slope
$\langle p.\mathrm{space}, v \rangle / p.\mathrm{time} - \langle \xi, v \rangle$. -/
theorem expHyperboloidBusemann_mul_diff_spaceVectorField
    (ξ : Metric.sphere (0 : E) 1) (p : Hyperboloid E) (v : E) :
    expHyperboloidBusemann ξ p * hyperboloidBusemannDiff ξ p (spaceVectorField v p) =
      inner ℝ p.space v / p.time - inner ℝ (ξ : E) v := by
  rw [hyperboloidBusemannDiff_spaceVectorField]
  exact mul_div_cancel₀ _ (expHyperboloidBusemann_pos ξ p).ne'

/-- The explicit vector $p.\mathrm{space} - \exp(B_\xi(p))^{-1} \xi \in E$ representing the
Riemannian gradient $\nabla B_\xi(p)$ in the `spaceDiffeomorph` chart. -/
def busemannGradientCoord (ξ : Metric.sphere (0 : E) 1) (p : Hyperboloid E) : E :=
  p.space - (expHyperboloidBusemann ξ p)⁻¹ • (ξ : E)

/-- **Riemannian Gradient Pairing Identity for `busemannGradientCoord`**:
$$g_p\big(\mathrm{spaceVectorField}(\mathrm{busemannGradientCoord}\,\xi\,p, p), \, \mathrm{spaceVectorField}(v, p)\big)
  = dB_\xi(p)(\mathrm{spaceVectorField}(v, p)).$$ -/
theorem riemannianMetric_inner_busemannGradientCoord
    (ξ : Metric.sphere (0 : E) 1) (p : Hyperboloid E) (v : E) :
    riemannianMetric.inner p
      (spaceVectorField (busemannGradientCoord ξ p) p)
      (spaceVectorField v p) =
      hyperboloidBusemannDiff ξ p (spaceVectorField v p) := by
  rw [riemannianMetric_inner_spaceVectorField_eq, hyperboloidBusemannDiff_spaceVectorField]
  unfold busemannGradientCoord
  simp only [inner_sub_left, real_inner_smul_left, inner_sub_right, real_inner_smul_right]
  have hp : inner ℝ p.space p.space = p.time ^ 2 - 1 := by
    linarith [p.time_sq_sub_inner_self]
  have h_exp : expHyperboloidBusemann ξ p ≠ 0 := (expHyperboloidBusemann_pos ξ p).ne'
  rw [hp, expHyperboloidBusemann_eq, real_inner_comm (ξ : E) p.space]
  rw [expHyperboloidBusemann_eq] at h_exp
  field_simp [p.time_pos.ne', h_exp]
  ring

/-- **Exact Unit Riemannian Norm of the Busemann Gradient on `Hyperboloid E`**:
$$g_p\big(\nabla B_\xi(p), \nabla B_\xi(p)\big) = 1.$$ -/
theorem riemannianMetric_inner_busemannGradientCoord_self
    (ξ : Metric.sphere (0 : E) 1) (p : Hyperboloid E) :
    riemannianMetric.inner p
      (spaceVectorField (busemannGradientCoord ξ p) p)
      (spaceVectorField (busemannGradientCoord ξ p) p) = 1 := by
  rw [riemannianMetric_inner_busemannGradientCoord, hyperboloidBusemannDiff_spaceVectorField]
  unfold busemannGradientCoord
  simp only [inner_sub_right, real_inner_smul_right]
  have hp : inner ℝ p.space p.space = p.time ^ 2 - 1 := by
    linarith [p.time_sq_sub_inner_self]
  have hξ : inner ℝ (ξ : E) (ξ : E) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere ξ]
    norm_num
  have h_exp : expHyperboloidBusemann ξ p ≠ 0 := (expHyperboloidBusemann_pos ξ p).ne'
  rw [expHyperboloidBusemann_eq] at h_exp ⊢
  rw [hp, hξ, real_inner_comm (ξ : E) p.space]
  field_simp [p.time_pos.ne', h_exp]
  ring

/-- **Canonical Riemannian Metric Gauge on `Hyperboloid E`**:
The linear operator $A_p : E \to_l[\mathbb{R}] E$ defined by
$$A_p(v) = v - \frac{\langle p.\mathrm{space}, v \rangle}{p.\mathrm{time}(p.\mathrm{time} + 1)} \, p.\mathrm{space}$$
maps the Riemannian metric $g_p$ at $p \in \mathrm{Hyperboloid}(E)$ isometrically onto the
Euclidean inner product on $E$. -/
def metricGauge (p : Hyperboloid E) : E →ₗ[ℝ] E :=
  LinearMap.id - (p.time * (p.time + 1))⁻¹ • selfOuter p.space

@[simp]
theorem metricGauge_apply (p : Hyperboloid E) (v : E) :
    metricGauge p v = v - ((p.time * (p.time + 1))⁻¹ * inner ℝ p.space v) • p.space := by
  simp [metricGauge, selfOuter_apply, smul_smul]

/-- The explicit inverse gauge $A_p^{-1} : E \to_l[\mathbb{R}] E$ defined by
$$A_p^{-1}(w) = w + \frac{\langle p.\mathrm{space}, w \rangle}{p.\mathrm{time} + 1} \, p.\mathrm{space}.$$ -/
def metricGaugeInv (p : Hyperboloid E) : E →ₗ[ℝ] E :=
  LinearMap.id + (p.time + 1)⁻¹ • selfOuter p.space

@[simp]
theorem metricGaugeInv_apply (p : Hyperboloid E) (w : E) :
    metricGaugeInv p w = w + ((p.time + 1)⁻¹ * inner ℝ p.space w) • p.space := by
  simp [metricGaugeInv, selfOuter_apply, smul_smul]

theorem metricGauge_metricGaugeInv (p : Hyperboloid E) (w : E) :
    metricGauge p (metricGaugeInv p w) = w := by
  apply ext_inner_right ℝ
  intro z
  have hp : inner ℝ p.space p.space = p.time ^ 2 - 1 := by
    linarith [p.time_sq_sub_inner_self]
  have ht1 : p.time + 1 ≠ 0 := by linarith [p.time_pos]
  simp only [metricGauge_apply, metricGaugeInv_apply, inner_add_left, inner_sub_left,
    real_inner_smul_left, inner_add_right, real_inner_smul_right, hp]
  field_simp [p.time_pos.ne', ht1]
  ring

theorem metricGaugeInv_metricGauge (p : Hyperboloid E) (v : E) :
    metricGaugeInv p (metricGauge p v) = v := by
  apply ext_inner_right ℝ
  intro z
  have hp : inner ℝ p.space p.space = p.time ^ 2 - 1 := by
    linarith [p.time_sq_sub_inner_self]
  have ht1 : p.time + 1 ≠ 0 := by linarith [p.time_pos]
  simp only [metricGauge_apply, metricGaugeInv_apply, inner_add_left, inner_sub_left,
    real_inner_smul_left, inner_sub_right, real_inner_smul_right, hp]
  field_simp [p.time_pos.ne', ht1]
  ring

/-- `metricGauge p` packaged as a linear equivalence $E \simeq_l[\mathbb{R}] E$. -/
def metricGaugeEquiv (p : Hyperboloid E) : E ≃ₗ[ℝ] E where
  toFun := metricGauge p
  map_add' := (metricGauge p).map_add
  map_smul' := (metricGauge p).map_smul
  invFun := metricGaugeInv p
  left_inv := metricGaugeInv_metricGauge p
  right_inv := metricGauge_metricGaugeInv p

/-- `metricGauge p` is symmetric with respect to the Euclidean inner product on $E$. -/
theorem isSymmetric_metricGauge (p : Hyperboloid E) : (metricGauge p).IsSymmetric := by
  intro v w
  simp only [metricGauge_apply, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm p.space v,
    real_inner_comm w p.space]
  ring

/-- `metricGaugeInv p` is symmetric with respect to the Euclidean inner product on $E$. -/
theorem isSymmetric_metricGaugeInv (p : Hyperboloid E) : (metricGaugeInv p).IsSymmetric := by
  intro v w
  simp only [metricGaugeInv_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm p.space v,
    real_inner_comm w p.space]
  ring

/-- **Exact Riemannian Isometry Property of `metricGauge`**:
For all $v, w \in E$,
$$\langle A_p v, A_p w \rangle_E = g_p(\mathrm{spaceVectorField}\,v\,p, \mathrm{spaceVectorField}\,w\,p).$$ -/
theorem inner_metricGauge_eq_riemannianMetric
    (p : Hyperboloid E) (v w : E) :
    inner ℝ (metricGauge p v) (metricGauge p w) =
      riemannianMetric.inner p (spaceVectorField v p) (spaceVectorField w p) := by
  rw [riemannianMetric_inner_spaceVectorField_eq, metricGauge_apply, metricGauge_apply]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  have hp : inner ℝ p.space p.space = p.time ^ 2 - 1 := by
    linarith [p.time_sq_sub_inner_self]
  have ht1 : p.time + 1 ≠ 0 := by linarith [p.time_pos]
  rw [hp, real_inner_comm v p.space]
  field_simp [p.time_pos.ne', ht1]
  ring

/-- **Inverse Gauge Isometry Property**:
For all $v, w \in E$,
$$g_p\big(\mathrm{spaceVectorField}(A_p^{-1} v, p), \, \mathrm{spaceVectorField}(A_p^{-1} w, p)\big) = \langle v, w \rangle_E.$$ -/
theorem riemannianMetric_inner_metricGaugeInv
    (p : Hyperboloid E) (v w : E) :
    riemannianMetric.inner p
      (spaceVectorField (metricGaugeInv p v) p)
      (spaceVectorField (metricGaugeInv p w) p) = inner ℝ v w := by
  rw [← inner_metricGauge_eq_riemannianMetric, metricGauge_metricGaugeInv,
    metricGauge_metricGaugeInv]

/-- The **Unit Euclidean Busemann Gradient Vector** $u_{\mathrm{Bus}}(\xi, p) \in E$ defined by
applying `metricGauge p` to `busemannGradientCoord ξ p`. -/
def euclideanBusemannGrad (ξ : Metric.sphere (0 : E) 1) (p : Hyperboloid E) : E :=
  metricGauge p (busemannGradientCoord ξ p)

/-- **Dual Pairing Identity for `euclideanBusemannGrad`**:
For every $z \in E$,
$$\langle u_{\mathrm{Bus}}(\xi, p), z \rangle_E =
  dB_\xi(p)\big(\mathrm{spaceVectorField}(A_p^{-1} z, p)\big).$$ -/
theorem inner_euclideanBusemannGrad_eq_diff
    (ξ : Metric.sphere (0 : E) 1) (p : Hyperboloid E) (z : E) :
    inner ℝ (euclideanBusemannGrad ξ p) z =
      hyperboloidBusemannDiff ξ p (spaceVectorField (metricGaugeInv p z) p) := by
  unfold euclideanBusemannGrad
  rw [← riemannianMetric_inner_busemannGradientCoord,
    ← inner_metricGauge_eq_riemannianMetric, metricGauge_metricGaugeInv]

/-- **Exact Unit Euclidean Norm of `euclideanBusemannGrad`**:
$$\|u_{\mathrm{Bus}}(\xi, p)\|_E = 1.$$ -/
theorem norm_euclideanBusemannGrad (ξ : Metric.sphere (0 : E) 1) (p : Hyperboloid E) :
    ‖euclideanBusemannGrad ξ p‖ = 1 := by
  have h_sq : ‖euclideanBusemannGrad ξ p‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    unfold euclideanBusemannGrad
    rw [inner_metricGauge_eq_riemannianMetric,
      riemannianMetric_inner_busemannGradientCoord_self]
  nlinarith [norm_nonneg (euclideanBusemannGrad ξ p)]

theorem norm_euclideanBusemannGrad_le_one (ξ : Metric.sphere (0 : E) 1) (p : Hyperboloid E) :
    ‖euclideanBusemannGrad ξ p‖ ≤ 1 :=
  (norm_euclideanBusemannGrad ξ p).le

end BusemannDifferentialAndGauge

section ImplicitDifferentiation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- **Key Lorentzian Cancellation Identity for the Normalized Barycenter Derivative**:
For any $p \in \mathrm{Hyperboloid}(E)$, $\tau > 0$, $\dot{T} \in \mathbb{R}$, and $\dot{V}, u \in E$,
if $\dot{\tau} = p.\mathrm{time} \cdot \dot{T} - \langle p.\mathrm{space}, \dot{V} \rangle$ and
$v = \tau^{-1} (\dot{V} - \dot{\tau} \cdot p.\mathrm{space})$, then
$$g_p(\mathrm{spaceVectorField}\,v\,p, \mathrm{spaceVectorField}\,u\,p) =
  \frac{1}{\tau}\left(\langle \dot{V}, u \rangle - \dot{T} \frac{\langle p.\mathrm{space}, u \rangle}{p.\mathrm{time}}\right).$$ -/
theorem riemannianMetric_inner_lorentzNormalization_deriv
    (p : Hyperboloid E) {τ : ℝ} (hτ : τ ≠ 0) (dT : ℝ) (dV u : E) :
    let dτ := p.time * dT - inner ℝ p.space dV
    let v := τ⁻¹ • (dV - dτ • p.space)
    riemannianMetric.inner p (spaceVectorField v p) (spaceVectorField u p) =
      τ⁻¹ * (inner ℝ dV u - dT * (inner ℝ p.space u / p.time)) := by
  intro dτ v
  rw [riemannianMetric_inner_spaceVectorField_eq]
  dsimp only [v, dτ]
  simp only [real_inner_smul_left, inner_sub_left, real_inner_smul_right, inner_sub_right]
  have hp : inner ℝ p.space p.space = p.time ^ 2 - 1 := by
    linarith [p.time_sq_sub_inner_self]
  rw [hp]
  field_simp [p.time_pos.ne', hτ]
  ring

/-- When $\dot{T} = \sum_{i \in \iota} d_i$ and $\dot{V} = \sum_{i \in \iota} d_i \xi_i$, the
Riemannian inner product of the normalized barycenter derivative with $\mathrm{spaceVectorField}\,u\,p$
is:
$$g_p(\mathrm{spaceVectorField}\,v\,p, \mathrm{spaceVectorField}\,u\,p) =
  -\frac{1}{\tau} \sum_{i \in \iota} d_i \exp(B_{\xi_i}(p)) \, dB_{\xi_i}(p)(\mathrm{spaceVectorField}\,u\,p).$$ -/
theorem riemannianMetric_inner_busemannSum_deriv
    (p : Hyperboloid E) {τ : ℝ} (hτ : τ ≠ 0)
    (d : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1) (u : E) :
    let dT := ∑ i : ι, d i
    let dV := ∑ i : ι, d i • (ξ i : E)
    let dτ := p.time * dT - inner ℝ p.space dV
    let v := τ⁻¹ • (dV - dτ • p.space)
    riemannianMetric.inner p (spaceVectorField v p) (spaceVectorField u p) =
      -τ⁻¹ * ∑ i : ι, d i * expHyperboloidBusemann (ξ i) p *
        hyperboloidBusemannDiff (ξ i) p (spaceVectorField u p) := by
  intro dT dV dτ v
  rw [riemannianMetric_inner_lorentzNormalization_deriv p hτ dT dV u]
  dsimp only [dT, dV]
  rw [sum_inner, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [real_inner_smul_left, mul_assoc (d i), expHyperboloidBusemann_mul_diff_spaceVectorField]
  ring

/-- **Exponential Weight Specialization (`d i = -s * w i * dβ i`)**:
When the weight derivatives satisfy $d_i = -s \, w_i \, d\beta_i$ at the barycenter
$p = \mathrm{hyperboloidBarycenter}(w, \xi, hw)$ (where $\tau = \mathcal{B}_{w, \xi}(p)$),
the Riemannian inner product of the barycenter derivative with $\mathrm{spaceVectorField}\,u\,p$
equals the weighted Busemann cross-pairing with the normalized probability weights
$\mu_i = \mathrm{barycenterProbWeight}(w, \xi, hw, i)$:
$$g_p(\mathrm{spaceVectorField}\,v\,p, \mathrm{spaceVectorField}\,u\,p) =
  s \sum_{i \in \iota} \mu_i(w, \xi) \, d\beta_i \, dB_{\xi_i}(p)(\mathrm{spaceVectorField}\,u\,p).$$ -/
theorem riemannianMetric_inner_barycenter_expWeight_deriv
    (s : ℝ) (w dβ : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i) (u : E) :
    let p := hyperboloidBarycenter w ξ hw
    let τ := lorentzNorm (busemannLorentzVector w ξ)
    let d := fun i : ι => -s * w i * dβ i
    let dT := ∑ i : ι, d i
    let dV := ∑ i : ι, d i • (ξ i : E)
    let dτ := p.time * dT - inner ℝ p.space dV
    let v := τ⁻¹ • (dV - dτ • p.space)
    riemannianMetric.inner p (spaceVectorField v p) (spaceVectorField u p) =
      s * ∑ i : ι, barycenterProbWeight w ξ hw i * dβ i *
        hyperboloidBusemannDiff (ξ i) p (spaceVectorField u p) := by
  intro p τ d dT dV dτ v
  have hτ : τ ≠ 0 := (lorentzNorm_pos hw).ne'
  rw [riemannianMetric_inner_busemannSum_deriv p hτ d ξ u]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  dsimp only [d, barycenterProbWeight, p]
  rw [busemannFunctional_hyperboloidBarycenter]
  change -τ⁻¹ * (-s * w i * dβ i * expHyperboloidBusemann (ξ i) p *
      hyperboloidBusemannDiff (ξ i) p (spaceVectorField u p)) =
    s * (w i * expHyperboloidBusemann (ξ i) p / τ * dβ i *
      hyperboloidBusemannDiff (ξ i) p (spaceVectorField u p))
  field_simp [hτ]

/-- **Fréchet Derivative of the Spatial Barycenter Map Along a Curve/Manifold Direction**:
Given differentiable weight functions $w : E_X \to \iota \to \mathbb{R}$ at $x \in E_X$ with
future-timelike resultant at $x$, the spatial coordinate of the barycenter map
$z \mapsto (\mathrm{hyperboloidBarycenter}(w(z), \xi, \dots)).\mathrm{space}$ has Fréchet
derivative at $x$ in direction $\dot{x} \in E_X$ given by
$$\tau^{-1} \big(\dot{V} - (p.\mathrm{time} \cdot \dot{T} - \langle p.\mathrm{space}, \dot{V} \rangle) \, p.\mathrm{space}\big),$$
where $\dot{T} = \sum_i d(w_i)_x(\dot{x})$ and $\dot{V} = \sum_i d(w_i)_x(\dot{x}) \xi_i$. -/
theorem hasFDerivAt_barycenter_space
    {E_X : Type*} [NormedAddCommGroup E_X] [NormedSpace ℝ E_X]
    (w : E_X → ι → ℝ) (dw : ι → E_X →L[ℝ] ℝ) (ξ : ι → Metric.sphere (0 : E) 1)
    (x : E_X) (hw_diff : ∀ i : ι, HasFDerivAt (fun z => w z i) (dw i) x)
    (hw : ‖∑ i : ι, w x i • (ξ i : E)‖ < ∑ i : ι, w x i) :
    let p := hyperboloidBarycenter (w x) ξ hw
    let τ := lorentzNorm (busemannLorentzVector (w x) ξ)
    let L_T : E_X →L[ℝ] ℝ := ∑ i : ι, dw i
    let L_V : E_X →L[ℝ] E := ∑ i : ι, (dw i).smulRight (ξ i : E)
    let L_τ : E_X →L[ℝ] ℝ := p.time • L_T - (innerSL ℝ p.space).comp L_V
    HasFDerivAt
      (fun z : E_X => (lorentzNorm (busemannLorentzVector (w z) ξ))⁻¹ •
        (busemannLorentzVector (w z) ξ).2)
      (τ⁻¹ • (L_V - L_τ.smulRight p.space)) x := by
  intro p τ L_T L_V L_τ
  have hT : HasFDerivAt (fun z : E_X => (busemannLorentzVector (w z) ξ).1) L_T x :=
    HasFDerivAt.fun_sum fun i _ => hw_diff i
  have hV : HasFDerivAt (fun z : E_X => (busemannLorentzVector (w z) ξ).2) L_V x :=
    HasFDerivAt.fun_sum fun i _ => (hw_diff i).smul_const (ξ i : E)
  let T₀ := (busemannLorentzVector (w x) ξ).1
  let V₀ := (busemannLorentzVector (w x) ξ).2
  have hT_sq := hT.pow 2
  have hV_sq : HasFDerivAt (fun z : E_X => ‖(busemannLorentzVector (w z) ξ).2‖ ^ 2)
      ((2 • innerSL ℝ V₀).comp L_V) x := by
    change HasFDerivAt ((fun y : E => ‖y‖ ^ 2) ∘ (fun z : E_X => (busemannLorentzVector (w z) ξ).2))
      ((2 • innerSL ℝ V₀).comp L_V) x
    exact (hasStrictFDerivAt_norm_sq V₀).hasFDerivAt.comp x hV
  have h_diff_sq := hT_sq.sub hV_sq
  have h_pos_sq : (busemannLorentzVector (w x) ξ).1 ^ 2 -
      ‖(busemannLorentzVector (w x) ξ).2‖ ^ 2 ≠ 0 :=
    (lorentzNorm_sq_pos hw).ne'
  have h_sqrt : HasFDerivAt
      (fun z : E_X => lorentzNorm (busemannLorentzVector (w z) ξ))
      ((1 / (2 * Real.sqrt (T₀ ^ 2 - ‖V₀‖ ^ 2))) •
        ((2 • T₀ ^ (2 - 1)) • L_T - (2 • innerSL ℝ V₀).comp L_V)) x :=
    h_diff_sq.sqrt h_pos_sq
  have hτ_pos : τ ≠ 0 := (lorentzNorm_pos hw).ne'
  have hp_time : p.time = τ⁻¹ * T₀ := rfl
  have hp_space : p.space = τ⁻¹ • V₀ := rfl
  have hτ_def : Real.sqrt (T₀ ^ 2 - ‖V₀‖ ^ 2) = τ := rfl
  have h_sqrt_eq : (1 / (2 * Real.sqrt (T₀ ^ 2 - ‖V₀‖ ^ 2))) •
      ((2 • T₀ ^ (2 - 1)) • L_T - (2 • innerSL ℝ V₀).comp L_V) = L_τ := by
    ext dx
    simp only [smul_apply, sub_apply,
      ContinuousLinearMap.comp_apply, two_smul, add_apply,
      innerSL_apply_apply, smul_eq_mul, L_τ]
    rw [hτ_def, hp_time, hp_space, real_inner_smul_left]
    field_simp [hτ_pos]
    ring
  rw [h_sqrt_eq] at h_sqrt
  have h_inv : HasFDerivAt (fun z : E_X => (lorentzNorm (busemannLorentzVector (w z) ξ))⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(τ ^ 2)⁻¹)).comp L_τ) x := by
    change HasFDerivAt ((fun r : ℝ => r⁻¹) ∘ (fun z : E_X => lorentzNorm (busemannLorentzVector (w z) ξ)))
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(τ ^ 2)⁻¹)).comp L_τ) x
    exact (hasFDerivAt_inv hτ_pos).comp x h_sqrt
  have h_prod := h_inv.smul hV
  convert h_prod using 1
  ext dx
  apply ext_inner_right ℝ
  intro u
  simp only [add_apply, smul_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    hp_space, inner_add_left, inner_sub_left, real_inner_smul_left, smul_eq_mul]
  change τ⁻¹ * (inner ℝ (L_V dx) u - L_τ dx * (τ⁻¹ * inner ℝ V₀ u)) =
    τ⁻¹ * inner ℝ (L_V dx) u + L_τ dx * -(τ ^ 2)⁻¹ * inner ℝ V₀ u
  field_simp [hτ_pos]
  ring

/-- **Exact Factorization of the Riemannian Differential as `busemannCrossOperator`**:
At the barycenter $p = \mathrm{hyperboloidBarycenter}(w, \xi, hw)$ of an exponentially weighted
boundary distribution ($d_i(v) = -s \, w_i \langle u_{1, i}, v \rangle_E$), the linear operator
$D^{\mathrm{Riem}} : E \to_l[\mathbb{R}] E$ induced by `metricGauge p` on the barycenter spatial
derivative is **identically equal** to `busemannCrossOperator`:
$$D^{\mathrm{Riem}} = \mathrm{busemannCrossOperator}\,s\,\mathrm{Finset.univ}\,(\mathrm{barycenterProbWeight}\,w\,\xi\,hw)\,u_1\,(\mathrm{fun}\,i \Rightarrow \mathrm{euclideanBusemannGrad}\,(\xi\,i)\,p).$$ -/
def riemannianBarycenterDifferential
    (s : ℝ) (w : ι → ℝ) (u₁ : ι → E) (ξ : ι → Metric.sphere (0 : E) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i) : E →ₗ[ℝ] E :=
  let p := hyperboloidBarycenter w ξ hw
  let τ := lorentzNorm (busemannLorentzVector w ξ)
  let d : ι → E →ₗ[ℝ] ℝ := fun i => (-s * w i) • innerₛₗ ℝ (u₁ i)
  let dT : E →ₗ[ℝ] ℝ := ∑ i : ι, d i
  let dV : E →ₗ[ℝ] E := ∑ i : ι, (LinearMap.toSpanSingleton ℝ E (ξ i : E)).comp (d i)
  let dτ : E →ₗ[ℝ] ℝ := p.time • dT - (innerₛₗ ℝ p.space).comp dV
  let v_map : E →ₗ[ℝ] E := τ⁻¹ • (dV - (LinearMap.toSpanSingleton ℝ E p.space).comp dτ)
  (metricGauge p).comp v_map

theorem inner_riemannianBarycenterDifferential_eq
    (s : ℝ) (w : ι → ℝ) (u₁ : ι → E) (ξ : ι → Metric.sphere (0 : E) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i) (v z : E) :
    let p := hyperboloidBarycenter w ξ hw
    inner ℝ (riemannianBarycenterDifferential s w u₁ ξ hw v) z =
      s * ∑ i : ι, barycenterProbWeight w ξ hw i *
        inner ℝ (u₁ i) v * inner ℝ (euclideanBusemannGrad (ξ i) p) z := by
  intro p
  have hz : z = metricGauge p (metricGaugeInv p z) := (metricGauge_metricGaugeInv p z).symm
  conv_lhs => rw [hz]
  unfold riemannianBarycenterDifferential
  simp only [LinearMap.comp_apply]
  rw [inner_metricGauge_eq_riemannianMetric]
  let dβ : ι → ℝ := fun i => inner ℝ (u₁ i) v
  let τ := lorentzNorm (busemannLorentzVector w ξ)
  let d : ι → ℝ := fun i => -s * w i * dβ i
  let dT : ℝ := ∑ i : ι, d i
  let dV : E := ∑ i : ι, d i • (ξ i : E)
  let dτ : ℝ := p.time * dT - inner ℝ p.space dV
  let v' : E := τ⁻¹ • (dV - dτ • p.space)
  have hv_eq : (let p := hyperboloidBarycenter w ξ hw
      let τ := lorentzNorm (busemannLorentzVector w ξ)
      let d : ι → E →ₗ[ℝ] ℝ := fun i => (-s * w i) • innerₛₗ ℝ (u₁ i)
      let dT : E →ₗ[ℝ] ℝ := ∑ i : ι, d i
      let dV : E →ₗ[ℝ] E := ∑ i : ι, (LinearMap.toSpanSingleton ℝ E (ξ i : E)).comp (d i)
      let dτ : E →ₗ[ℝ] ℝ := p.time • dT - (innerₛₗ ℝ p.space).comp dV
      (τ⁻¹ • (dV - (LinearMap.toSpanSingleton ℝ E p.space).comp dτ)) v) = v' := by
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, innerₛₗ_apply_apply,
      smul_eq_mul, v', dτ, dV, dT, d, dβ, τ, p]
  rw [hv_eq]
  have h_deriv := riemannianMetric_inner_barycenter_expWeight_deriv
    s w dβ ξ hw (metricGaugeInv p z)
  dsimp only at h_deriv
  rw [h_deriv]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_euclideanBusemannGrad_eq_diff]

/-- **Main Identity of Step 2 (`riemannianBarycenterDifferential_eq_busemannCrossOperator`)**:
The Riemannian differential of the hyperbolic barycenter map in the canonical gauge `metricGauge p`
equals `busemannCrossOperator` on the nose:
$$D^{\mathrm{Riem}} = \mathrm{busemannCrossOperator}\,s\,\mathrm{Finset.univ}\,(\mathrm{barycenterProbWeight}\,w\,\xi\,hw)\,u_1\,(\mathrm{fun}\,i \Rightarrow \mathrm{euclideanBusemannGrad}\,(\xi\,i)\,p).$$ -/
theorem riemannianBarycenterDifferential_eq_busemannCrossOperator
    (s : ℝ) (w : ι → ℝ) (u₁ : ι → E) (ξ : ι → Metric.sphere (0 : E) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i) :
    let p := hyperboloidBarycenter w ξ hw
    riemannianBarycenterDifferential s w u₁ ξ hw =
      busemannCrossOperator s Finset.univ (barycenterProbWeight w ξ hw) u₁
        (fun i => euclideanBusemannGrad (ξ i) p) := by
  intro p
  ext v
  apply ext_inner_right ℝ
  intro z
  rw [inner_riemannianBarycenterDifferential_eq]
  simp only [busemannCrossOperator, LinearMap.smul_apply, LinearMap.sum_apply,
    real_inner_smul_left, sum_inner, inner_crossOuter_apply]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **Manifold-Level BCG Pointwise Jacobian Bound (`abs_det_riemannianBarycenterDifferential_le`)**:
For any non-negative weights $w : \iota \to \mathbb{R}$ with future-timelike resultant
$\|\sum_i w_i \xi_i\| < \sum_i w_i$, any scale $s \ge 0$, and any family of source unit-bounded
gradient vectors $u_1 : \iota \to E$ ($\|u_1(i)\| \le 1$), the Riemannian differential
$D^{\mathrm{Riem}}$ of `hyperboloidBarycenter` satisfies:
$$\big|\det\big(D^{\mathrm{Riem}}\big)\big| \le \left(\frac{s}{n}\right)^n, \qquad n = \mathrm{finrank}\,\mathbb{R}\,E.$$ -/
theorem abs_det_riemannianBarycenterDifferential_le
    [FiniteDimensional ℝ E] (hn : 0 < Module.finrank ℝ E)
    {s : ℝ} (hs : 0 ≤ s)
    {w : ι → ℝ} (hw_nn : ∀ i : ι, 0 ≤ w i)
    {u₁ : ι → E} (hu₁ : ∀ i : ι, ‖u₁ i‖ ≤ 1)
    (ξ : ι → Metric.sphere (0 : E) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i) :
    |LinearMap.det (riemannianBarycenterDifferential s w u₁ ξ hw)| ≤
      (s / (Module.finrank ℝ E : ℝ)) ^ Module.finrank ℝ E := by
  rw [riemannianBarycenterDifferential_eq_busemannCrossOperator]
  exact abs_det_busemannCrossOperator_le rfl hn hs Finset.univ
    (fun i _ => barycenterProbWeight_nonneg hw_nn ξ hw i)
    (sum_barycenterProbWeight_eq_one w ξ hw).le
    (fun i _ => hu₁ i)
    (fun i _ => norm_euclideanBusemannGrad_le_one (ξ i) (hyperboloidBarycenter w ξ hw))

end ImplicitDifferentiation

end BCG.Hyperbolic
