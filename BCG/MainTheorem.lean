import BCG.LinearAlgebra.TraceDet
import BCG.LinearAlgebra.BarycenterOperator
import BCG.Entropy.VolumeEntropy
import BCG.Hyperbolic.BarycenterFunctional
import BCG.Hyperbolic.JacobianBound
import BCG.Rigidity.EqualityCase
import BCG.RankOne.BusemannHessian
import BCG.RankOne.AssociativeCase
import BCG.RankOne.OctonionicCase

/-!
# Main Theorem: Besson–Courtois–Gallot Volume-Entropy Inequality

This file combines the four components of the Besson–Courtois–Gallot (1995) and Souto (2008)
barycenter method formalized in `BCG`:
1. `BCG.LinearAlgebra.TraceDet`: Spectral AM–GM trace-determinant inequalities
   ($\det H \le (\operatorname{Tr}(H)/n)^n$).
2. `BCG.LinearAlgebra.BarycenterOperator`: Gram operator and bilinear Cauchy–Schwarz determinant
   bound ($|\det L| \le c^n \sqrt{\det H_1}\sqrt{\det H_2} \le (c/n)^n$).
3. `BCG.Entropy.VolumeEntropy`: Critical exponent / volume entropy $h(X)$ and exponential distance
   measures $\mu_x^s = e^{-s d(x,\cdot)}\mu$.
4. `BCG.Hyperbolic.BarycenterFunctional`: Exact Busemann Hessian identity
   $\operatorname{Hess} B_\xi = g - dB_\xi \otimes dB_\xi$ on `Hyperboloid E` and rank-one
   covariance trace identity $\operatorname{Tr}(\nabla B_\xi \otimes dB_\xi) = \|\nabla B_\xi\|^2 = 1$.

## Main Results
- `bcg_volume_inequality_at_scale`: At each fixed scale $s > h(X)$, integrating the pointwise
  barycenter Jacobian bound $|\det(d_x F_s)| \le (s / h_Y)^n$ over a finite-measure space $(X, \mu_X)$
  yields
  $$|\deg(f)| \cdot h_Y^n \, \mathrm{Vol}(Y) \le s^n \, \mathrm{Vol}(X).$$
- `bcg_volume_entropy_inequality`: Passing to the infimum / limit $s \searrow h_X$ yields the
  global Besson–Courtois–Gallot volume-entropy inequality:
  $$|\deg(f)| \cdot h_Y^n \, \mathrm{Vol}(Y) \le h_X^n \, \mathrm{Vol}(X).$$
-/

noncomputable section

open MeasureTheory Filter Set Topology

namespace BCG

variable {X : Type*} [MeasurableSpace X]

/-- **BCG Volume Inequality at Fixed Scale $s$**:
Suppose $(X, \mu_X)$ is a finite-measure space, $J_s : X \to \mathbb{R}$ is an integrable Jacobian
function bounded pointwise almost everywhere by $(s / h_Y)^n$ ($h_Y > 0$), and the degree-area
formula gives $\mathrm{degAbs} \cdot \mathrm{volY} \le \int_X J_s(x)\,d\mu_X(x)$. Then
$$\mathrm{degAbs} \cdot h_Y^n \cdot \mathrm{volY} \le s^n \cdot \mu_X(\mathrm{univ}).\mathrm{toReal}.$$ -/
theorem bcg_volume_inequality_at_scale
    (μ_X : Measure X) [IsFiniteMeasure μ_X]
    {n : ℕ} {s h_Y degAbs volY : ℝ} (hh_Y : 0 < h_Y)
    {J_s : X → ℝ} (hJ_int : Integrable J_s μ_X)
    (hJ_bound : ∀ᵐ x ∂μ_X, J_s x ≤ (s / h_Y) ^ n)
    (h_deg_area : degAbs * volY ≤ ∫ x, J_s x ∂μ_X) :
    degAbs * h_Y ^ n * volY ≤ s ^ n * (μ_X univ).toReal := by
  have h_int_le : ∫ x, J_s x ∂μ_X ≤ (s / h_Y) ^ n * (μ_X univ).toReal := by
    calc
      ∫ x, J_s x ∂μ_X ≤ ∫ _ : X, (s / h_Y) ^ n ∂μ_X :=
        integral_mono_ae hJ_int (integrable_const _) hJ_bound
      _ = (s / h_Y) ^ n * (μ_X univ).toReal := by
        rw [integral_const, measureReal_def, smul_eq_mul, mul_comm]
  have h_step : degAbs * volY ≤ (s / h_Y) ^ n * (μ_X univ).toReal :=
    h_deg_area.trans h_int_le
  have hh_Y_pow : 0 < h_Y ^ n := pow_pos hh_Y n
  have h_mul := mul_le_mul_of_nonneg_right h_step hh_Y_pow.le
  rw [div_pow, div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt hh_Y_pow)] at h_mul
  linarith

/-- **Global Besson–Courtois–Gallot Volume-Entropy Inequality**:
If for every $s > h_X$ ($h_X \ge 0$), the natural map $F_s$ satisfies the fixed-scale BCG
estimate $\mathrm{degAbs} \cdot h_Y^n \cdot \mathrm{volY} \le s^n \cdot \mathrm{volX}$, then
passing to the limit $s \searrow h_X$ yields
$$\mathrm{degAbs} \cdot h_Y^n \cdot \mathrm{volY} \le h_X^n \cdot \mathrm{volX}.$$ -/
theorem bcg_volume_entropy_inequality
    {n : ℕ} {h_X h_Y degAbs volX volY : ℝ}
    (h_at_scale : ∀ s > h_X, degAbs * h_Y ^ n * volY ≤ s ^ n * volX) :
    degAbs * h_Y ^ n * volY ≤ h_X ^ n * volX := by
  have h_cont : Continuous (fun s : ℝ => s ^ n * volX) :=
    (continuous_pow n).mul continuous_const
  have h_tendsto : Tendsto (fun s : ℝ => s ^ n * volX) (𝓝[>] h_X) (𝓝 (h_X ^ n * volX)) :=
    h_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto h_tendsto (eventually_nhdsWithin_iff.mpr (Eventually.of_forall h_at_scale))

/-- **End-to-End Smooth Hyperbolic BCG Theorem**:
Combines the pointwise Busemann Cauchy–Schwarz operator bound
`BCG.LinearAlgebra.abs_det_le_div_dim_pow_of_abs_inner_le` on the tangent spaces $E_x$ ($\dim E_x = n \ge 1$)
with the integral degree bound to conclude:
$$|\deg(f)| \cdot n^n \cdot \mathrm{Vol}(Y) \le c_X^n \cdot \mathrm{Vol}(X).$$ -/
theorem hyperbolic_bcg_main_theorem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (μ_X : Measure X) [IsFiniteMeasure μ_X]
    {n : ℕ} (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n)
    {c_X degAbs volY : ℝ} (hc_X : 0 ≤ c_X)
    (L H₁ H₂ : ℝ → X → (E →ₗ[ℝ] E))
    (hH₁_symm : ∀ s > c_X, ∀ x, (H₁ s x).IsSymmetric)
    (hH₂_symm : ∀ s > c_X, ∀ x, (H₂ s x).IsSymmetric)
    (hH₁_pos : ∀ s > c_X, ∀ x u, 0 ≤ inner ℝ u (H₁ s x u))
    (hH₂_pos : ∀ s > c_X, ∀ x w, 0 ≤ inner ℝ w (H₂ s x w))
    (hH₁_tr : ∀ s > c_X, ∀ x, LinearMap.trace ℝ E (H₁ s x) ≤ 1)
    (hH₂_tr : ∀ s > c_X, ∀ x, LinearMap.trace ℝ E (H₂ s x) ≤ 1)
    (hCS : ∀ s > c_X, ∀ x u w,
      |inner ℝ (L s x u) w| ≤
        s * Real.sqrt (inner ℝ u (H₁ s x u)) * Real.sqrt (inner ℝ w (H₂ s x w)))
    (hL_int : ∀ s > c_X, Integrable (fun x => |(L s x).det|) μ_X)
    (h_deg_area : ∀ s > c_X, degAbs * volY ≤ ∫ x, |(L s x).det| ∂μ_X) :
    degAbs * (n : ℝ) ^ n * volY ≤ c_X ^ n * (μ_X univ).toReal := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  apply bcg_volume_entropy_inequality
  intro s hs
  have hs_nn : 0 ≤ s := le_trans hc_X hs.le
  apply bcg_volume_inequality_at_scale μ_X hnR (hL_int s hs)
  · exact Eventually.of_forall fun x =>
      BCG.LinearAlgebra.abs_det_le_div_dim_pow_of_abs_inner_le
        (hH₁_symm s hs x) (hH₂_symm s hs x) hn hn_pos
        (hH₁_pos s hs x) (hH₂_pos s hs x)
        (hH₁_tr s hs x) (hH₂_tr s hs x) hs_nn (hCS s hs x)
  · exact h_deg_area s hs

/-- **Smooth Hyperbolic BCG Theorem for Explicit Busemann Cross-Operators**:
When the differential of the natural map $F_s$ at scale $s > c_X$ is represented by the
weighted Busemann cross-operator `BCG.Hyperbolic.busemannCrossOperator s I (w s x) (u₁ s x) (u₂ s x)`
for unit Busemann gradients $\|u_1(s,x,a)\| \le 1$, $\|u_2(s,x,a)\| \le 1$ and probability weights
$w(s,x,a) \ge 0$, $\sum_{a \in I} w(s,x,a) \le 1$, we obtain directly:
$$|\deg(f)| \cdot n^n \cdot \mathrm{Vol}(Y) \le c_X^n \cdot \mathrm{Vol}(X).$$ -/
theorem hyperbolic_bcg_busemann_main_theorem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (μ_X : Measure X) [IsFiniteMeasure μ_X]
    {n : ℕ} (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n)
    {c_X degAbs volY : ℝ} (hc_X : 0 ≤ c_X)
    {α : Type*} (I : Finset α)
    (w : ℝ → X → α → ℝ)
    (u₁ u₂ : ℝ → X → α → E)
    (hw : ∀ s > c_X, ∀ x, ∀ a ∈ I, 0 ≤ w s x a)
    (hw_sum : ∀ s > c_X, ∀ x, ∑ a ∈ I, w s x a ≤ 1)
    (hu₁ : ∀ s > c_X, ∀ x, ∀ a ∈ I, ‖u₁ s x a‖ ≤ 1)
    (hu₂ : ∀ s > c_X, ∀ x, ∀ a ∈ I, ‖u₂ s x a‖ ≤ 1)
    (hL_int : ∀ s > c_X, Integrable
      (fun x => |(BCG.Hyperbolic.busemannCrossOperator s I (w s x) (u₁ s x) (u₂ s x)).det|) μ_X)
    (h_deg_area : ∀ s > c_X, degAbs * volY ≤
      ∫ x, |(BCG.Hyperbolic.busemannCrossOperator s I (w s x) (u₁ s x) (u₂ s x)).det| ∂μ_X) :
    degAbs * (n : ℝ) ^ n * volY ≤ c_X ^ n * (μ_X univ).toReal :=
  hyperbolic_bcg_main_theorem μ_X hn hn_pos hc_X
    (fun s x => BCG.Hyperbolic.busemannCrossOperator s I (w s x) (u₁ s x) (u₂ s x))
    (fun s x => BCG.Hyperbolic.busemannCovariance I (w s x) (u₁ s x))
    (fun s x => BCG.Hyperbolic.busemannCovariance I (w s x) (u₂ s x))
    (fun s _ x => BCG.Hyperbolic.isSymmetric_busemannCovariance I (w s x) (u₁ s x))
    (fun s _ x => BCG.Hyperbolic.isSymmetric_busemannCovariance I (w s x) (u₂ s x))
    (fun s hs x => BCG.Hyperbolic.inner_busemannCovariance_nonneg I (hw s hs x) (u₁ s x))
    (fun s hs x => BCG.Hyperbolic.inner_busemannCovariance_nonneg I (hw s hs x) (u₂ s x))
    (fun s hs x => BCG.Hyperbolic.trace_busemannCovariance_le_one I (hw s hs x) (hw_sum s hs x) (hu₁ s hs x))
    (fun s hs x => BCG.Hyperbolic.trace_busemannCovariance_le_one I (hw s hs x) (hw_sum s hs x) (hu₂ s hs x))
    (fun s hs x => BCG.Hyperbolic.abs_inner_busemannCrossOperator_le (le_trans hc_X hs.le) I (hw s hs x) (u₁ s x) (u₂ s x))
    hL_int h_deg_area

open BigOperators in
/-- **Smooth Hyperbolic BCG Theorem for the Explicit `hyperboloidBarycenter` Natural Map**:
For any boundary points $\xi : \iota \to S(E)$, non-negative weights $w(s, x) : \iota \to \mathbb{R}$
with future-timelike resultant $\|\sum_i w(s, x, i) \xi_i\| < \sum_i w(s, x, i)$, and source
unit-bounded distance gradients $u_1(s, x, i) \in E$ ($\|u_1(s, x, i)\| \le 1$), the Riemannian
differential `riemannianBarycenterDifferential` of the smooth natural map
$F_s(x) = \mathrm{hyperboloidBarycenter}(w(s, x), \xi, hw(s, x))$ satisfies
$|\det(D^{\mathrm{Riem}} F_s(x))| \le (s / n)^n$ at every $x \in X$, yielding the global BCG
volume-entropy inequality:
$$|\deg(f)| \cdot n^n \cdot \mathrm{Vol}(Y) \le c_X^n \cdot \mathrm{Vol}(X).$$ -/
theorem hyperbolic_bcg_natural_map_main_theorem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (μ_X : Measure X) [IsFiniteMeasure μ_X]
    {n : ℕ} (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n)
    {c_X degAbs volY : ℝ} (hc_X : 0 ≤ c_X)
    {ι : Type*} [Fintype ι]
    (ξ : ι → Metric.sphere (0 : E) 1)
    (w : ℝ → X → ι → ℝ)
    (u₁ : ℝ → X → ι → E)
    (hw_nn : ∀ s > c_X, ∀ x i, 0 ≤ w s x i)
    (hw : ∀ s x, ‖∑ i : ι, w s x i • (ξ i : E)‖ < ∑ i : ι, w s x i)
    (hu₁ : ∀ s > c_X, ∀ x i, ‖u₁ s x i‖ ≤ 1)
    (hL_int : ∀ s > c_X, Integrable
      (fun x => |(BCG.Hyperbolic.riemannianBarycenterDifferential s (w s x) (u₁ s x) ξ (hw s x)).det|) μ_X)
    (h_deg_area : ∀ s > c_X, degAbs * volY ≤
      ∫ x, |(BCG.Hyperbolic.riemannianBarycenterDifferential s (w s x) (u₁ s x) ξ (hw s x)).det| ∂μ_X) :
    degAbs * (n : ℝ) ^ n * volY ≤ c_X ^ n * (μ_X univ).toReal := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hfin_pos : 0 < Module.finrank ℝ E := hn.symm ▸ hn_pos
  apply bcg_volume_entropy_inequality
  intro s hs
  have hs_nn : 0 ≤ s := le_trans hc_X hs.le
  apply bcg_volume_inequality_at_scale μ_X hnR (hL_int s hs)
  · refine Eventually.of_forall fun x => ?_
    have hdet := BCG.Hyperbolic.abs_det_riemannianBarycenterDifferential_le
      hfin_pos hs_nn (hw_nn s hs x) (hu₁ s hs x) ξ (hw s x)
    rwa [hn] at hdet
  · exact h_deg_area s hs

open BigOperators in
/-- **Smooth Hyperbolic BCG Rigidity Theorem for `hyperboloidBarycenter` at Scale $s > 0$**:
If equality $\mathrm{degAbs} \cdot n^n \cdot \mathrm{volY} = s^n \cdot \mathrm{Vol}(X)$ holds at
scale $s > 0$ (in particular at the critical scale $s = n$), then for $\mu_X$-almost every $x \in X$:
1. $|\det(D^{\mathrm{Riem}} F_s(x))| = (s / n)^n$,
2. The source Busemann covariance tensor is isotropic:
   `busemannCovariance Finset.univ (barycenterProbWeight (w x) ξ (hw x)) (u₁ x) = (1 / (n : ℝ)) • LinearMap.id`,
3. The target Busemann covariance tensor at $F_s(x)$ is isotropic:
   `busemannCovariance Finset.univ (barycenterProbWeight (w x) ξ (hw x)) (fun i => euclideanBusemannGrad (ξ i) (F_s x)) = (1 / (n : ℝ)) • LinearMap.id`,
4. $D^{\mathrm{Riem}} F_s(x)$ is a scaled linear isometry with scale factor $s / n$:
   $\forall v \in E, \|D^{\mathrm{Riem}} F_s(x) v\| = (s / n) \|v\|$ (and an exact Riemannian
   linear isometry when $s = n$). -/
theorem hyperbolic_bcg_natural_map_rigidity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (μ_X : Measure X) [IsFiniteMeasure μ_X]
    {n : ℕ} (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n)
    {s degAbs volY : ℝ} (hs : 0 < s)
    {ι : Type*} [Fintype ι]
    (ξ : ι → Metric.sphere (0 : E) 1)
    (w : X → ι → ℝ)
    (u₁ : X → ι → E)
    (hw_nn : ∀ x i, 0 ≤ w x i)
    (hw : ∀ x, ‖∑ i : ι, w x i • (ξ i : E)‖ < ∑ i : ι, w x i)
    (hu₁ : ∀ x i, ‖u₁ x i‖ ≤ 1)
    (hL_int : Integrable
      (fun x => |(BCG.Hyperbolic.riemannianBarycenterDifferential s (w x) (u₁ x) ξ (hw x)).det|) μ_X)
    (h_deg_area : degAbs * volY ≤
      ∫ x, |(BCG.Hyperbolic.riemannianBarycenterDifferential s (w x) (u₁ x) ξ (hw x)).det| ∂μ_X)
    (h_eq : degAbs * (n : ℝ) ^ n * volY = s ^ n * (μ_X univ).toReal) :
    ∀ᵐ x ∂μ_X,
      let p := BCG.Hyperbolic.hyperboloidBarycenter (w x) ξ (hw x)
      let pw := BCG.Hyperbolic.barycenterProbWeight (w x) ξ (hw x)
      let u₂ := fun i : ι => BCG.Hyperbolic.euclideanBusemannGrad (ξ i) p
      let D := BCG.Hyperbolic.riemannianBarycenterDifferential s (w x) (u₁ x) ξ (hw x)
      |D.det| = (s / (n : ℝ)) ^ n ∧
      BCG.Hyperbolic.busemannCovariance Finset.univ pw (u₁ x) = (1 / (n : ℝ)) • LinearMap.id ∧
      BCG.Hyperbolic.busemannCovariance Finset.univ pw u₂ = (1 / (n : ℝ)) • LinearMap.id ∧
      D.adjoint * D = (s / (n : ℝ)) ^ 2 • LinearMap.id ∧
      (∀ v : E, ‖D v‖ = (s / (n : ℝ)) * ‖v‖) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hfin_pos : 0 < Module.finrank ℝ E := hn.symm ▸ hn_pos
  have hJ_bound : ∀ᵐ x ∂μ_X,
      |(BCG.Hyperbolic.riemannianBarycenterDifferential s (w x) (u₁ x) ξ (hw x)).det| ≤
        (s / (n : ℝ)) ^ n := by
    refine Eventually.of_forall fun x => ?_
    have hdet := BCG.Hyperbolic.abs_det_riemannianBarycenterDifferential_le
      hfin_pos hs.le (hw_nn x) (hu₁ x) ξ (hw x)
    rwa [hn] at hdet
  have hae_det := BCG.Rigidity.ae_eq_of_bcg_volume_equality
    μ_X hnR hL_int hJ_bound h_deg_area h_eq
  filter_upwards [hae_det] with x hx_det
  refine ⟨hx_det, ?_⟩
  exact BCG.Rigidity.riemannianBarycenterDifferential_rigidity
    hn hn_pos hs (hw_nn x) (hu₁ x) ξ (hw x) hx_det

/-!
### 2. General Rank-One Symmetric Spaces ($\mathbb{K}\mathbf{H}^m$, $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}, \mathbb{H}, \mathbb{O}\}$)
-/

/-- **General Rank-One Symmetric Space BCG Volume-Entropy Theorem (`rankOne_bcg_main_theorem`)**:
Let $(Y, g_0)$ be a closed locally symmetric space of rank one modeled on $\mathbb{K}\mathbf{H}^m$
of real dimension $n = \dim_{\mathbb{R}} Y \ge 1$ and division-algebra fiber dimension
$d = \dim_{\mathbb{R}} \mathbb{K} \in \{1, 2, 4, 8\}$, with volume entropy
$$h_0 = h(g_0) = n + d - 2 > 0.$$
Suppose that at every scale $s > c_X \ge 0$ and every $x \in X$, the natural map differential
$D_F(s, x) : E \to_l[\mathbb{R}] E$ satisfies the implicit function theorem equation
$$(I - 2 H(s, x) + \widehat{H}(s, x)) \circ D_F(s, x) = s \cdot H_y(s, x)$$
and the rank-one Busemann Hessian determinant inequality
$$\frac{\sqrt{\det H(s, x)}}{\det(I - 2 H(s, x) + \widehat{H}(s, x))}
  \le \left(\frac{\sqrt{n}}{h_0}\right)^n$$
(proved via `BCG.RankOne.associative_rankOne_det_ineq` for $\mathbb{C}\mathbf{H}^m, \mathbb{H}\mathbf{H}^m$,
`BCG.RankOne.real_rankOne_det_ineq` for $\mathbb{R}\mathbf{H}^m$, and Ruan's perturbed log-concavity
theorem `BCG.RankOne.octonionic_rankOne_det_ineq` for the Cayley hyperbolic plane $\mathbb{O}\mathbf{H}^2$).
Then the global Besson–Courtois–Gallot volume-entropy inequality holds:
$$|\deg(f)| \cdot h_0^n \cdot \mathrm{Vol}(Y) \le c_X^n \cdot \mathrm{Vol}(X).$$ -/
theorem rankOne_bcg_main_theorem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (μ_X : Measure X) [IsFiniteMeasure μ_X]
    {n : ℕ} (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n)
    {c_X h₀ degAbs volY : ℝ} (hc_X : 0 ≤ c_X) (hh₀ : 0 < h₀)
    (D_F H_y H_X H H_hat : ℝ → X → (E →ₗ[ℝ] E))
    (h_ift : ∀ s > c_X, ∀ x,
      (BCG.RankOne.rankOneHessianOperator (H s x) (H_hat s x)).comp (D_F s x) = s • H_y s x)
    (hW_pos : ∀ s > c_X, ∀ x, 0 < (BCG.RankOne.rankOneHessianOperator (H s x) (H_hat s x)).det)
    (hH_X_symm : ∀ s > c_X, ∀ x, (H_X s x).IsSymmetric)
    (hH_symm : ∀ s > c_X, ∀ x, (H s x).IsSymmetric)
    (hH_X_pos : ∀ s > c_X, ∀ x u, 0 ≤ inner ℝ u (H_X s x u))
    (hH_pos : ∀ s > c_X, ∀ x v, 0 ≤ inner ℝ v (H s x v))
    (hH_X_tr : ∀ s > c_X, ∀ x, LinearMap.trace ℝ E (H_X s x) ≤ 1)
    (hCS : ∀ s > c_X, ∀ x u v,
      |inner ℝ (H_y s x u) v| ≤
        Real.sqrt (inner ℝ u (H_X s x u)) * Real.sqrt (inner ℝ v (H s x v)))
    (h_det_ineq : ∀ s > c_X, ∀ x,
      Real.sqrt (H s x).det / (BCG.RankOne.rankOneHessianOperator (H s x) (H_hat s x)).det ≤
        (Real.sqrt (n : ℝ) / h₀) ^ n)
    (hD_int : ∀ s > c_X, Integrable (fun x => |(D_F s x).det|) μ_X)
    (h_deg_area : ∀ s > c_X, degAbs * volY ≤ ∫ x, |(D_F s x).det| ∂μ_X) :
    degAbs * h₀ ^ n * volY ≤ c_X ^ n * (μ_X univ).toReal := by
  apply bcg_volume_entropy_inequality
  intro s hs
  have hs_nn : 0 ≤ s := le_trans hc_X hs.le
  apply bcg_volume_inequality_at_scale μ_X hh₀ (hD_int s hs)
  · exact Eventually.of_forall fun x =>
      BCG.RankOne.abs_det_le_div_entropy_pow_of_rankOne_det_ineq
        hn hn_pos hs_nn hh₀ (h_ift s hs x) (hW_pos s hs x)
        (hH_X_symm s hs x) (hH_symm s hs x)
        (hH_X_pos s hs x) (hH_pos s hs x)
        (hH_X_tr s hs x) (hCS s hs x) (h_det_ineq s hs x)
  · exact h_deg_area s hs

/-- **Cayley Hyperbolic Plane ($\mathbb{O}\mathbf{H}^2$) BCG Volume-Entropy Theorem
(`octonionic_bcg_main_theorem`, `[Ruan 2024, Theorem 1.1]`)**:
For the 16-dimensional Cayley hyperbolic plane $\mathbb{O}\mathbf{H}^2$ ($n = 16$, $d = 8$,
$h_0 = 22$), combining Ruan's perturbed log-concavity determinant bound
`BCG.RankOne.octonionic_rankOne_bcg_jacobian_bound` ($|\det D_F(s, x)| \le (s / 22)^{16}$)
with the integral degree estimate and the limit $s \searrow c_X$ yields:
$$|\deg(f)| \cdot 22^{16} \cdot \mathrm{Vol}(Y) \le c_X^{16} \cdot \mathrm{Vol}(X).$$ -/
theorem octonionic_bcg_main_theorem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (μ_X : Measure X) [IsFiniteMeasure μ_X]
    (hn16 : Module.finrank ℝ E = 16)
    {c_X degAbs volY : ℝ} (hc_X : 0 ≤ c_X)
    {α : Type*} (I : Finset α)
    (w : ℝ → X → α → ℝ)
    (u v : ℝ → X → α → E)
    (π : ℝ → X → α → (E →ₗ[ℝ] E))
    (D_F U_α : ℝ → X → (E →ₗ[ℝ] E))
    (hw : ∀ s > c_X, ∀ x, ∀ a ∈ I, 0 ≤ w s x a)
    (hw_sum : ∀ s > c_X, ∀ x, ∑ a ∈ I, w s x a = 1)
    (hv : ∀ s > c_X, ∀ x, ∀ a ∈ I, ‖v s x a‖ ≤ 1)
    (h_ift : ∀ s > c_X, ∀ x,
      (BCG.RankOne.rankOneHessianOperator
        (BCG.Hyperbolic.busemannCovariance I (w s x) (u s x))
        (BCG.RankOne.rankOneLineCovariance I (w s x) (π s x))).comp (D_F s x) =
      s • BCG.Hyperbolic.busemannCrossOperator 1 I (w s x) (v s x) (u s x))
    (hIHU_symm : ∀ s > c_X, ∀ x,
      ((LinearMap.id : E →ₗ[ℝ] E) - BCG.Hyperbolic.busemannCovariance I (w s x) (u s x) - U_α s x).IsSymmetric)
    (hHHU_symm : ∀ s > c_X, ∀ x,
      (BCG.RankOne.rankOneLineCovariance I (w s x) (π s x) -
        BCG.Hyperbolic.busemannCovariance I (w s x) (u s x) + U_α s x).IsSymmetric)
    (hIHU_pos : ∀ s > c_X, ∀ x z,
      0 ≤ inner ℝ z (((LinearMap.id : E →ₗ[ℝ] E) -
        BCG.Hyperbolic.busemannCovariance I (w s x) (u s x) - U_α s x) z))
    (hHHU_pos : ∀ s > c_X, ∀ x z,
      0 ≤ inner ℝ z ((BCG.RankOne.rankOneLineCovariance I (w s x) (π s x) -
        BCG.Hyperbolic.busemannCovariance I (w s x) (u s x) + U_α s x) z))
    (hdetH_pos : ∀ s > c_X, ∀ x, 0 < (BCG.Hyperbolic.busemannCovariance I (w s x) (u s x)).det)
    (h_ruan_23 : ∀ s > c_X, ∀ x,
      (Real.sqrt (16 : ℝ)) ^ (-((16 : ℝ) * ((16 : ℝ) + (8 : ℝ) - 2) / ((16 : ℝ) - 1))) *
        (BCG.Hyperbolic.busemannCovariance I (w s x) (u s x)).det ^
          (((16 : ℝ) - (8 : ℝ)) / (2 * ((16 : ℝ) - 1))) ≤
        ((1 / (15 : ℝ)) • (LinearMap.id -
          BCG.Hyperbolic.busemannCovariance I (w s x) (u s x) - U_α s x)).det)
    (h_ruan_21 : ∀ s > c_X, ∀ x,
      (BCG.Hyperbolic.busemannCovariance I (w s x) (u s x)).det ≤
        ((1 / (7 : ℝ)) • (BCG.RankOne.rankOneLineCovariance I (w s x) (π s x) -
          BCG.Hyperbolic.busemannCovariance I (w s x) (u s x) + U_α s x)).det)
    (hD_int : ∀ s > c_X, Integrable (fun x => |(D_F s x).det|) μ_X)
    (h_deg_area : ∀ s > c_X, degAbs * volY ≤ ∫ x, |(D_F s x).det| ∂μ_X) :
    degAbs * (22 : ℝ) ^ 16 * volY ≤ c_X ^ 16 * (μ_X univ).toReal := by
  apply bcg_volume_entropy_inequality
  intro s hs
  have hs_nn : 0 ≤ s := le_trans hc_X hs.le
  apply bcg_volume_inequality_at_scale μ_X (by norm_num : (0 : ℝ) < 22) (hD_int s hs)
  · exact Eventually.of_forall fun x =>
      BCG.RankOne.octonionic_rankOne_bcg_jacobian_bound
        hn16 I (hw s hs x) (hw_sum s hs x) (hv s hs x) hs_nn
        (h_ift s hs x) (hIHU_symm s hs x) (hHHU_symm s hs x)
        (hIHU_pos s hs x) (hHHU_pos s hs x) (hdetH_pos s hs x)
        (h_ruan_23 s hs x) (h_ruan_21 s hs x)
  · exact h_deg_area s hs

end BCG
