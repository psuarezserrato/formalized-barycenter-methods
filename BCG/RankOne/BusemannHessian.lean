import BCG.LinearAlgebra.TraceDet
import BCG.LinearAlgebra.BarycenterOperator
import BCG.Hyperbolic.BarycenterFunctional
import BCG.Rigidity.EqualityCase

/-!
# Step 4A: Unified Rank-One Symmetric Space Busemann Hessian & BCG Jacobian Reduction

This file formalizes the geometric and operator-theoretic framework for the Besson–Courtois–Gallot
barycenter method on general rank-one symmetric spaces of non-compact type
$\widetilde{M} = \mathbb{K}\mathbf{H}^m$ ($\mathbb{K} \in \{\mathbb{R}, \mathbb{C}, \mathbb{H}, \mathbb{O}\}$),
faithfully following:
- **G. Besson, G. Courtois, S. Gallot (1995)**, *Entropies et rigidités des espaces localement
  symétriques de courbure strictement négative*, *Geom. Funct. Anal.* **5** (1995), §3–§5 &
  Appendix B (`[BCG1]`); and
- **Y. Ruan (2022/2024)**, *The Cayley hyperbolic space and volume entropy rigidity*,
  *Mathematische Zeitschrift* **306**, article 4 (2024), `arXiv:2203.14418`, §2 & §3.1–§3.2.

## Main Definitions and Results

1. **Rank-One Symmetric Space Division-Algebra Data (`DivisionAlgebraType`, `rankOneDim`, `rankOneEntropy`)**:
   For $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}, \mathbb{H}, \mathbb{O}\}$ with real dimension
   $d = \dim_{\mathbb{R}} \mathbb{K} \in \{1, 2, 4, 8\}$ and $\mathbb{K}$-hyperbolic dimension $m$,
   the real manifold dimension is $n = d m$ and the volume growth entropy under sectional curvature
   normalization $[-4, -1]$ ($-1$ for $\mathbb{R}\mathbf{H}^n$) is
   $$h(\mathbb{K}\mathbf{H}^m) = n + d - 2.$$

2. **Jacobi Curvature Operator & Busemann Hessian Square-Root Identity (`IsKLineProjection`,
   `rankOneJacobiOperator`, `rankOneSingleHessian`, `sq_rankOneSingleHessian_eq_jacobi`)**:
   Along a geodesic ray with unit tangent $u = \nabla B_\theta(x)$ and orthogonal projection
   $\pi_{x,\theta}$ onto the $d$-dimensional $\mathbb{K}$-line $\mathbb{K} \cdot u$ (where sectional
   curvatures are $-4$ inside $\mathbb{K} \cdot u$ and $-1$ on $(\mathbb{K} \cdot u)^\perp$), the
   negative Jacobi curvature operator $-R(u, \cdot, u, \cdot)$ is
   $$\mathcal{R}_{u,\pi} = I - 4(u \otimes u^*) + 3\pi,$$
   and its unique positive-semidefinite square root $\operatorname{Hess} B_\theta(x) = \sqrt{-R(\nabla B_\theta, \cdot, \nabla B_\theta, \cdot)}$
   ([Ruan 2024, Eq. (8) & p. 9]) is
   $$\operatorname{Hess} B_\theta(x) = I - 2(u \otimes u^*) + \pi, \qquad
     (I - 2(u \otimes u^*) + \pi)^2 = I - 4(u \otimes u^*) + 3\pi,$$
   with mean curvature (Laplacian of the Busemann function)
   $$\Delta B_\theta(x) = \operatorname{Tr}(\operatorname{Hess} B_\theta(x)) = n + d - 2 = h(\mathbb{K}\mathbf{H}^m).$$

3. **Integrated Operators $H$, $\widehat{H}$, and $W_y = I - 2H + \widehat{H}$
   (`rankOneLineCovariance`, `rankOneHessianOperator`)**:
   Integrating against a boundary probability distribution $w$ yields the pair of symmetric
   positive-semidefinite operators
   $$H = \int_{\partial_\infty \widetilde{M}} dB_\theta \otimes dB_\theta \, d\sigma_y^s(\theta), \qquad
     \widehat{H} = \int_{\partial_\infty \widetilde{M}} \pi_{x,\theta} \, d\sigma_y^s(\theta),$$
   satisfying $\operatorname{Tr}(H) = 1$, $\operatorname{Tr}(\widehat{H}) = d$, $\widehat{H} \ge H \ge 0$,
   and
   $$W_y = \int_{\partial_\infty \widetilde{M}} \operatorname{Hess} B_\theta \, d\sigma_y^s(\theta)
         = I - 2H + \widehat{H} = (I - H) + (\widehat{H} - H).$$

4. **Implicit Differentiation & BCG Determinant Reduction (`abs_det_cross_le_inv_sqrt_dim_pow_mul_sqrt_det`,
   `abs_det_of_hessian_comp_eq_smul`, `abs_det_le_div_entropy_pow_of_rankOne_det_ineq`,
   `abs_det_le_div_entropy_pow_mul_defect`)**:
   Faithfully formalizes [Ruan 2024, Eqs. (2)–(7), (12)–(13)] and [BCG 1995, Lemma 5.4 & Prop. B.5]:
   - From $W_y \circ D_y \widetilde{F}_s = s \, H_y$ and H\"older/Cauchy–Schwarz,
     $$|\det H_y| \le \left(\frac{1}{\sqrt{n}}\right)^n (\det H)^{1/2},$$
     $$|\det D_y \widetilde{F}_s| \le \left(\frac{s}{\sqrt{n}}\right)^n
       \frac{(\det H)^{1/2}}{\det(I - 2H + \widehat{H})}.$$
   - Consequently, the rank-one determinant inequality
     $$\frac{(\det H)^{1/2}}{\det(I - 2H + \widehat{H})} \le \left(\frac{\sqrt{n}}{n + d - 2}\right)^n$$
     directly implies the pointwise BCG Jacobian bound
     $$|\det D_y \widetilde{F}_s| \le \left(\frac{s}{n + d - 2}\right)^n = \left(\frac{s}{h(g_0)}\right)^n,$$
     as well as the quantitative eigenvalue-defect version ([Ruan 2024, Eq. (7) & Cor. 3.8]).
-/

noncomputable section

open Finset BigOperators

namespace BCG.RankOne

open BCG.LinearAlgebra BCG.Hyperbolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-!
### 1. Classification Data of Rank-One Symmetric Spaces of Non-Compact Type
-/

/-- The four real normed division algebras $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}, \mathbb{H}, \mathbb{O}\}$
underlying the rank-one symmetric spaces of non-compact type $\mathbb{K}\mathbf{H}^m$. -/
inductive DivisionAlgebraType : Type
  | real : DivisionAlgebraType
  | complex : DivisionAlgebraType
  | quaternionic : DivisionAlgebraType
  | octonionic : DivisionAlgebraType
  deriving DecidableEq, Repr

namespace DivisionAlgebraType

/-- Real dimension $d = \dim_{\mathbb{R}} \mathbb{K} \in \{1, 2, 4, 8\}$ of the division algebra $\mathbb{K}$. -/
def fiberDim : DivisionAlgebraType → ℕ
  | .real => 1
  | .complex => 2
  | .quaternionic => 4
  | .octonionic => 8

theorem fiberDim_pos (K : DivisionAlgebraType) : 0 < K.fiberDim := by
  cases K <;> decide

theorem one_le_fiberDim (K : DivisionAlgebraType) : 1 ≤ K.fiberDim :=
  K.fiberDim_pos

/-- Real manifold dimension $n = d m$ of the $\mathbb{K}$-hyperbolic space $\mathbb{K}\mathbf{H}^m$. -/
def manifoldDim (K : DivisionAlgebraType) (m : ℕ) : ℕ :=
  K.fiberDim * m

/-- Volume growth entropy $h(\mathbb{K}\mathbf{H}^m) = n + d - 2$ under the standard curvature
normalization $K \in [-4, -1]$ ($K \equiv -1$ for $\mathbb{R}\mathbf{H}^m$). -/
def volumeEntropy (K : DivisionAlgebraType) (m : ℕ) : ℝ :=
  (K.manifoldDim m : ℝ) + (K.fiberDim : ℝ) - 2

@[simp]
theorem volumeEntropy_real (n : ℕ) :
    DivisionAlgebraType.real.volumeEntropy n = (n : ℝ) - 1 := by
  simp [volumeEntropy, manifoldDim, fiberDim]
  ring

@[simp]
theorem volumeEntropy_complex (m : ℕ) :
    DivisionAlgebraType.complex.volumeEntropy m = (2 * m : ℕ) := by
  simp [volumeEntropy, manifoldDim, fiberDim]

@[simp]
theorem volumeEntropy_quaternionic (m : ℕ) :
    DivisionAlgebraType.quaternionic.volumeEntropy m = (4 * m : ℕ) + 2 := by
  simp [volumeEntropy, manifoldDim, fiberDim]
  ring

@[simp]
theorem volumeEntropy_octonionic_two :
    DivisionAlgebraType.octonionic.volumeEntropy 2 = 22 := by
  simp [volumeEntropy, manifoldDim, fiberDim]
  norm_num

end DivisionAlgebraType

/-- General rank-one volume growth entropy formula $h_0(n, d) = n + d - 2$ for a space of real
dimension $n$ and $\mathbb{K}$-line dimension $d$. -/
def rankOneEntropy (n d : ℕ) : ℝ :=
  (n : ℝ) + (d : ℝ) - 2

/-!
### 2. Pointwise $\mathbb{K}$-Line Projections, Jacobi Operator, and Busemann Hessian Square Root
-/

/-- `IsKLineProjection d u π` states that for a unit tangent vector $u \in E$ ($\|u\| = 1$),
$\pi : E \to_l[\mathbb{R}] E$ is the orthogonal projection onto a $d$-dimensional subspace
(the $\mathbb{K}$-line $\mathbb{K} \cdot u$, e.g. $\mathcal{C}ay(u)$ in [Ruan 2024, §1–§3])
containing $u$:
1. $\pi$ is symmetric ($\langle \pi v, w \rangle = \langle v, \pi w \rangle$),
2. $\pi$ is idempotent ($\pi \circ \pi = \pi$),
3. $\pi(u) = u$, and
4. $\operatorname{Tr}(\pi) = d$. -/
structure IsKLineProjection [FiniteDimensional ℝ E] (d : ℕ) (u : E) (π : E →ₗ[ℝ] E) : Prop where
  norm_u : ‖u‖ = 1
  isSymmetric : π.IsSymmetric
  idempotent : π * π = π
  apply_u : π u = u
  trace_eq : LinearMap.trace ℝ E π = d

namespace IsKLineProjection

variable [FiniteDimensional ℝ E] {d : ℕ} {u : E} {π : E →ₗ[ℝ] E}

/-- For any $\mathbb{K}$-line orthogonal projection $\pi$, $0 \le \langle v, \pi v \rangle = \|\pi v\|^2 \le \|v\|^2$. -/
theorem inner_eq_norm_sq (hπ : IsKLineProjection d u π) (v : E) :
    inner ℝ v (π v) = ‖π v‖ ^ 2 := by
  calc
    inner ℝ v (π v) = inner ℝ v ((π * π) v) := by rw [hπ.idempotent]
    _ = inner ℝ (π v) (π v) := by
      rw [Module.End.mul_apply, ← hπ.isSymmetric v (π v)]
    _ = ‖π v‖ ^ 2 := real_inner_self_eq_norm_sq (π v)

theorem inner_nonneg (hπ : IsKLineProjection d u π) (v : E) :
    0 ≤ inner ℝ v (π v) := by
  rw [hπ.inner_eq_norm_sq v]
  exact sq_nonneg _

theorem comp_selfOuter (hπ : IsKLineProjection d u π) :
    π * selfOuter u = selfOuter u := by
  ext v
  simp [Module.End.mul_apply, selfOuter_apply, map_smul, hπ.apply_u]

theorem selfOuter_comp (hπ : IsKLineProjection d u π) :
    selfOuter u * π = selfOuter u := by
  ext v
  simp only [Module.End.mul_apply, selfOuter_apply]
  rw [← hπ.isSymmetric u v, hπ.apply_u]

/-- The orthogonal projection $\pi$ onto $\mathbb{K} \cdot u$ dominates the rank-one projection
$P_u = u \otimes u^*$: $\langle v, (\pi - P_u) v \rangle = \|\pi v - \langle u, v \rangle u\|^2 \ge 0$. -/
theorem inner_sub_selfOuter_eq_norm_sq (hπ : IsKLineProjection d u π) (v : E) :
    inner ℝ v ((π - selfOuter u) v) = ‖π v - inner ℝ u v • u‖ ^ 2 := by
  have hπu : inner ℝ u (π v) = inner ℝ u v := by
    rw [← hπ.isSymmetric u v, hπ.apply_u]
  rw [LinearMap.sub_apply, inner_sub_right, hπ.inner_eq_norm_sq v, selfOuter_apply,
    real_inner_smul_right,
    norm_sub_sq_real, norm_smul, Real.norm_eq_abs, hπ.norm_u, mul_one, sq_abs,
    real_inner_smul_right, real_inner_comm u (π v), hπu, real_inner_comm u v]
  ring

theorem sub_selfOuter_nonneg (hπ : IsKLineProjection d u π) (v : E) :
    0 ≤ inner ℝ v ((π - selfOuter u) v) := by
  rw [hπ.inner_sub_selfOuter_eq_norm_sq v]
  exact sq_nonneg _

/-- And $I - \pi$ is also a symmetric idempotent projection, so $\langle v, (I - \pi) v \rangle = \|v - \pi v\|^2 \ge 0$. -/
theorem inner_id_sub_eq_norm_sq (hπ : IsKLineProjection d u π) (v : E) :
    inner ℝ v (((LinearMap.id : E →ₗ[ℝ] E) - π) v) = ‖v - π v‖ ^ 2 := by
  rw [LinearMap.sub_apply, LinearMap.id_apply, inner_sub_right, real_inner_self_eq_norm_sq,
    norm_sub_sq_real, hπ.inner_eq_norm_sq v]
  ring

theorem id_sub_nonneg (hπ : IsKLineProjection d u π) (v : E) :
    0 ≤ inner ℝ v (((LinearMap.id : E →ₗ[ℝ] E) - π) v) := by
  rw [hπ.inner_id_sub_eq_norm_sq v]
  exact sq_nonneg _

end IsKLineProjection

/-- The negative Jacobi curvature operator $\mathcal{R}_{u,\pi} = -R(u, \cdot, u, \cdot)$ along a
unit vector $u$ with $\mathbb{K}$-line projection $\pi$ in a rank-one symmetric space with
sectional curvatures $-4$ on $\mathbb{K} \cdot u$ and $-1$ on $(\mathbb{K} \cdot u)^\perp$:
$$\mathcal{R}_{u,\pi} = I - 4(u \otimes u^*) + 3\pi = 4(\pi - u \otimes u^*) + (I - \pi).$$ -/
def rankOneJacobiOperator (u : E) (π : E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  LinearMap.id - (4 : ℝ) • selfOuter u + (3 : ℝ) • π

/-- The pointwise Busemann Hessian operator ([Ruan 2024, p. 9, line 663]):
$$\operatorname{Hess} B_\theta(x) = I - 2(u \otimes u^*) + \pi = 2(\pi - u \otimes u^*) + (I - \pi).$$ -/
def rankOneSingleHessian (u : E) (π : E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  LinearMap.id - (2 : ℝ) • selfOuter u + π

/-- Decomposition of `rankOneSingleHessian` into orthogonal eigenspace projections with eigenvalues
$2$ (on $\mathbb{K} u \ominus \mathbb{R} u$), $1$ (on $(\mathbb{K} u)^\perp$), and $0$ (on $\mathbb{R} u$). -/
theorem rankOneSingleHessian_eq_two_smul_sub_add_id_sub (u : E) (π : E →ₗ[ℝ] E) :
    rankOneSingleHessian u π =
      (2 : ℝ) • (π - selfOuter u) + (LinearMap.id - π) := by
  ext v
  simp only [rankOneSingleHessian, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply]
  module

/-- **Operator Square-Root Identity (`sq_rankOneSingleHessian_eq_jacobi`)**:
Faithfully formalizes [Ruan 2024, Eq. (8) & p. 9]: for any unit vector $u$ and $\mathbb{K}$-line
orthogonal projection $\pi$ containing $u$, the Busemann Hessian operator
$B_{u,\pi} = I - 2(u \otimes u^*) + \pi$ is symmetric positive-semidefinite and its square equals
the negative Jacobi curvature operator $\mathcal{R}_{u,\pi} = -R(u, \cdot, u, \cdot)$:
$$(I - 2(u \otimes u^*) + \pi)^2 = I - 4(u \otimes u^*) + 3\pi.$$ -/
theorem sq_rankOneSingleHessian_eq_jacobi [FiniteDimensional ℝ E]
    {d : ℕ} {u : E} {π : E →ₗ[ℝ] E} (hπ : IsKLineProjection d u π) :
    rankOneSingleHessian u π * rankOneSingleHessian u π = rankOneJacobiOperator u π := by
  have hu_sq : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hπ.norm_u, one_pow]
  ext v
  have hπu : inner ℝ u (π v) = inner ℝ u v := by
    rw [← hπ.isSymmetric u v, hπ.apply_u]
  have hπ2 : π (π v) = π v := LinearMap.congr_fun hπ.idempotent v
  change (rankOneSingleHessian u π) ((rankOneSingleHessian u π) v) =
    rankOneJacobiOperator u π v
  dsimp [rankOneSingleHessian, rankOneJacobiOperator]
  simp only [map_add, map_sub, map_smul,
    inner_add_right, inner_sub_right, real_inner_smul_right,
    hu_sq, hπu, hπ.apply_u, hπ2, mul_one, smul_smul]
  module

theorem isSymmetric_rankOneSingleHessian [FiniteDimensional ℝ E]
    {d : ℕ} {u : E} {π : E →ₗ[ℝ] E} (hπ : IsKLineProjection d u π) :
    (rankOneSingleHessian u π).IsSymmetric := by
  intro v w
  unfold rankOneSingleHessian
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [isSymmetric_selfOuter u v w, hπ.isSymmetric v w]

theorem inner_rankOneSingleHessian_nonneg [FiniteDimensional ℝ E]
    {d : ℕ} {u : E} {π : E →ₗ[ℝ] E} (hπ : IsKLineProjection d u π) (v : E) :
    0 ≤ inner ℝ v (rankOneSingleHessian u π v) := by
  have h1 := hπ.sub_selfOuter_nonneg v
  have h2 := hπ.id_sub_nonneg v
  rw [rankOneSingleHessian_eq_two_smul_sub_add_id_sub, LinearMap.add_apply,
    LinearMap.smul_apply, inner_add_right, real_inner_smul_right]
  linarith

/-- **Mean Curvature of Horospheres (`trace_rankOneSingleHessian`)**:
For any $\mathbb{K}$-line projection $\pi$ of rank $d$ on an $n$-dimensional space $E$,
the trace of the Busemann Hessian $\operatorname{Hess} B_\theta(x) = I - 2(u \otimes u^*) + \pi$
equals the volume growth entropy $h_0(n, d) = n + d - 2$. -/
theorem trace_rankOneSingleHessian [FiniteDimensional ℝ E]
    {n d : ℕ} (hn : Module.finrank ℝ E = n)
    {u : E} {π : E →ₗ[ℝ] E} (hπ : IsKLineProjection d u π) :
    LinearMap.trace ℝ E (rankOneSingleHessian u π) = rankOneEntropy n d := by
  unfold rankOneSingleHessian rankOneEntropy
  rw [map_add, map_sub, map_smul, LinearMap.trace_id, hn, trace_selfOuter,
    hπ.norm_u, one_pow, hπ.trace_eq, smul_eq_mul, mul_one]
  ring

/-!
### 3. Integrated Operators $H$, $\widehat{H}$, and $W_y = I - 2H + \widehat{H}$
-/

/-- The $\mu$-weighted average $\widehat{H} = \sum_{a \in s} w_a \pi_a$ of $\mathbb{K}$-line
orthogonal projections ([Ruan 2024, p. 9, line 669]). -/
def rankOneLineCovariance {α : Type*} (s : Finset α) (w : α → ℝ)
    (π : α → (E →ₗ[ℝ] E)) : E →ₗ[ℝ] E :=
  ∑ a ∈ s, w a • π a

/-- The integrated Busemann Hessian operator $W_y = I - 2H + \widehat{H}$
([Ruan 2024, Eq. (2), p. 8 & Eq. (13), p. 9]):
$$W_y = \int_{\partial_\infty \widetilde{M}} \operatorname{Hess} B_\theta \, d\sigma_y^s(\theta)
      = I - 2H + \widehat{H} = (I - H) + (\widehat{H} - H).$$ -/
def rankOneHessianOperator (H H_hat : E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  LinearMap.id - (2 : ℝ) • H + H_hat

/-- Decomposition $I - 2H + \widehat{H} = (I - H) + (\widehat{H} - H)$ used in the log-concavity
argument ([Ruan 2024, Eq. (13) & Eq. (15)] / `[BCG1, Lemme B.3]`). -/
theorem rankOneHessianOperator_eq_add_sub (H H_hat : E →ₗ[ℝ] E) :
    rankOneHessianOperator H H_hat = (LinearMap.id - H) + (H_hat - H) := by
  ext v
  simp only [rankOneHessianOperator, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply]
  module

/-- When $d = 1$ (real hyperbolic space $\mathbb{R}\mathbf{H}^n$), $\widehat{H} = H$ and
`rankOneHessianOperator H H = I - H`. -/
@[simp]
theorem rankOneHessianOperator_self (H : E →ₗ[ℝ] E) :
    rankOneHessianOperator H H = LinearMap.id - H := by
  rw [rankOneHessianOperator_eq_add_sub, sub_self, add_zero]

/-- For a probability distribution $w$ ($\sum_{a \in s} w_a = 1$), the weighted average of the
pointwise Busemann Hessians `rankOneSingleHessian (u a) (π a)` equals
`rankOneHessianOperator (busemannCovariance s w u) (rankOneLineCovariance s w π)`. -/
theorem sum_rankOneSingleHessian_eq_rankOneHessianOperator
    {α : Type*} (s : Finset α) (w : α → ℝ) (hw_sum : ∑ a ∈ s, w a = 1)
    (u : α → E) (π : α → (E →ₗ[ℝ] E)) :
    (∑ a ∈ s, w a • rankOneSingleHessian (u a) (π a)) =
      rankOneHessianOperator (busemannCovariance s w u) (rankOneLineCovariance s w π) := by
  ext v
  simp only [rankOneSingleHessian, rankOneHessianOperator, busemannCovariance,
    rankOneLineCovariance, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, smul_add, smul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_smul, hw_sum, one_smul]
  congr 2
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_comm]

theorem isSymmetric_rankOneLineCovariance [FiniteDimensional ℝ E]
    {α : Type*} (s : Finset α) (w : α → ℝ) {d : ℕ} {u : α → E} {π : α → (E →ₗ[ℝ] E)}
    (hπ : ∀ a ∈ s, IsKLineProjection d (u a) (π a)) :
    (rankOneLineCovariance s w π).IsSymmetric := by
  intro v z
  unfold rankOneLineCovariance
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [(hπ a ha).isSymmetric v z]

theorem trace_rankOneLineCovariance [FiniteDimensional ℝ E]
    {α : Type*} (s : Finset α) (w : α → ℝ) (hw_sum : ∑ a ∈ s, w a = 1)
    {d : ℕ} {u : α → E} {π : α → (E →ₗ[ℝ] E)}
    (hπ : ∀ a ∈ s, IsKLineProjection d (u a) (π a)) :
    LinearMap.trace ℝ E (rankOneLineCovariance s w π) = d := by
  unfold rankOneLineCovariance
  rw [map_sum]
  have h_term : ∀ a ∈ s, LinearMap.trace ℝ E (w a • π a) = w a * (d : ℝ) := by
    intro a ha
    rw [map_smul, (hπ a ha).trace_eq, smul_eq_mul]
  rw [Finset.sum_congr rfl h_term, ← Finset.sum_mul, hw_sum, one_mul]

theorem sub_busemannCovariance_nonneg [FiniteDimensional ℝ E]
    {α : Type*} (s : Finset α) {w : α → ℝ} (hw : ∀ a ∈ s, 0 ≤ w a)
    {d : ℕ} {u : α → E} {π : α → (E →ₗ[ℝ] E)}
    (hπ : ∀ a ∈ s, IsKLineProjection d (u a) (π a)) (v : E) :
    0 ≤ inner ℝ v ((rankOneLineCovariance s w π - busemannCovariance s w u) v) := by
  have h_eq : (rankOneLineCovariance s w π - busemannCovariance s w u) v =
      ∑ a ∈ s, w a • ((π a - selfOuter (u a)) v) := by
    simp only [rankOneLineCovariance, busemannCovariance, LinearMap.sub_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_sub, Finset.sum_sub_distrib]
  rw [h_eq, inner_sum]
  refine Finset.sum_nonneg fun a ha => ?_
  rw [real_inner_smul_right]
  exact mul_nonneg (hw a ha) ((hπ a ha).sub_selfOuter_nonneg v)

/-!
### 4. Implicit Differentiation & BCG Determinant Reduction ([Ruan 2024, Eqs. (2)–(7)])
-/

/-- **Source-Target Cross-Operator Determinant Bound ([Ruan 2024, Eq. (4)] / `[BCG1, Lemme 5.4]`)**:
If $H_y : E \to_l[\mathbb{R}] E$ satisfies the Cauchy–Schwarz inequality
$$|\langle H_y u, v \rangle| \le \sqrt{\langle u, H_X u \rangle} \sqrt{\langle v, H v \rangle}$$
for symmetric positive-semidefinite operators $H_X, H : E \to_l[\mathbb{R}] E$ on an
$n$-dimensional space $E$ ($n \ge 1$) with $\operatorname{Tr}(H_X) \le 1$, then
$$|\det H_y| \le \left(\frac{1}{\sqrt{n}}\right)^n \sqrt{\det H}.$$ -/
theorem abs_det_cross_le_inv_sqrt_dim_pow_mul_sqrt_det [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n)
    {H_y H_X H : E →ₗ[ℝ] E}
    (hH_X : H_X.IsSymmetric) (hH : H.IsSymmetric)
    (hpos_X : ∀ u : E, 0 ≤ inner ℝ u (H_X u))
    (hpos_H : ∀ v : E, 0 ≤ inner ℝ v (H v))
    (htr_X : LinearMap.trace ℝ E H_X ≤ 1)
    (hCS : ∀ u v : E, |inner ℝ (H_y u) v| ≤
      Real.sqrt (inner ℝ u (H_X u)) * Real.sqrt (inner ℝ v (H v))) :
    |H_y.det| ≤ (1 / Real.sqrt (n : ℝ)) ^ n * Real.sqrt H.det := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hCS1 : ∀ u v : E, |inner ℝ (H_y u) v| ≤
      1 * Real.sqrt (inner ℝ u (H_X u)) * Real.sqrt (inner ℝ v (H v)) := by
    intro u v
    simpa using hCS u v
  have h1 := abs_det_le_of_abs_inner_le hH_X hH hn hn_pos hpos_X hpos_H zero_le_one hCS1
  rw [one_pow, one_mul] at h1
  have hd_X := det_le_one_div_dim_pow_of_trace_le_one hH_X hn hn_pos hpos_X htr_X
  have h_sqrt_X : Real.sqrt H_X.det ≤ (1 / Real.sqrt (n : ℝ)) ^ n := by
    calc
      Real.sqrt H_X.det ≤ Real.sqrt ((1 / (n : ℝ)) ^ n) := Real.sqrt_le_sqrt hd_X
      _ = (1 / Real.sqrt (n : ℝ)) ^ n := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ (1 / Real.sqrt (n : ℝ)) ^ n)]
        congr 1
        rw [← pow_mul, mul_comm n 2, pow_mul]
        congr 1
        rw [div_pow, one_pow, Real.sq_sqrt hnR.le]
  calc
    |H_y.det| ≤ Real.sqrt H_X.det * Real.sqrt H.det := h1
    _ ≤ (1 / Real.sqrt (n : ℝ)) ^ n * Real.sqrt H.det :=
      mul_le_mul_of_nonneg_right h_sqrt_X (Real.sqrt_nonneg _)

/-- **Implicit Differentiation Jacobian Estimate ([Ruan 2024, Eqs. (2) & (5)])**:
Suppose the differential $D_F : E \to_l[\mathbb{R}] E$ of the natural map $\widetilde{F}_s$ at $y$
satisfies the implicit differentiation equation
$$W_y \circ_l D_F = s \bullet H_y$$
with $\det W_y > 0$, where $H_y$ satisfies the Cauchy–Schwarz bound against $H_X$ ($\operatorname{Tr}(H_X) \le 1$)
and $H$. Then:
$$|\det D_F| = s^n \frac{|\det H_y|}{\det W_y} \le
  \left(\frac{s}{\sqrt{n}}\right)^n \frac{\sqrt{\det H}}{\det W_y}.$$ -/
theorem abs_det_of_hessian_comp_eq_smul [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n)
    {s : ℝ} (hs : 0 ≤ s)
    {D_F W_y H_y H_X H : E →ₗ[ℝ] E}
    (h_imp : W_y.comp D_F = s • H_y)
    (hW_pos : 0 < W_y.det)
    (hH_X : H_X.IsSymmetric) (hH : H.IsSymmetric)
    (hpos_X : ∀ u : E, 0 ≤ inner ℝ u (H_X u))
    (hpos_H : ∀ v : E, 0 ≤ inner ℝ v (H v))
    (htr_X : LinearMap.trace ℝ E H_X ≤ 1)
    (hCS : ∀ u v : E, |inner ℝ (H_y u) v| ≤
      Real.sqrt (inner ℝ u (H_X u)) * Real.sqrt (inner ℝ v (H v))) :
    |D_F.det| = s ^ n * |H_y.det| / W_y.det ∧
    |D_F.det| ≤ (s / Real.sqrt (n : ℝ)) ^ n * (Real.sqrt H.det / W_y.det) := by
  have h_det_comp : W_y.det * |D_F.det| = s ^ n * |H_y.det| := by
    have h1 := congr_arg (fun A : E →ₗ[ℝ] E => |A.det|) h_imp
    rw [LinearMap.det_comp, abs_mul, abs_of_pos hW_pos,
      LinearMap.det_smul, hn, abs_mul, abs_of_nonneg (pow_nonneg hs n)] at h1
    exact h1
  have h_eq : |D_F.det| = s ^ n * |H_y.det| / W_y.det := by
    rw [eq_div_iff hW_pos.ne', mul_comm, h_det_comp]
  refine ⟨h_eq, ?_⟩
  have hHy := abs_det_cross_le_inv_sqrt_dim_pow_mul_sqrt_det
    hn hn_pos hH_X hH hpos_X hpos_H htr_X hCS
  rw [h_eq]
  calc
    s ^ n * |H_y.det| / W_y.det
      ≤ s ^ n * ((1 / Real.sqrt (n : ℝ)) ^ n * Real.sqrt H.det) / W_y.det := by
        apply div_le_div_of_nonneg_right _ hW_pos.le
        exact mul_le_mul_of_nonneg_left hHy (pow_nonneg hs n)
    _ = (s * (1 / Real.sqrt (n : ℝ))) ^ n * (Real.sqrt H.det / W_y.det) := by
        rw [mul_pow]
        ring
    _ = (s / Real.sqrt (n : ℝ)) ^ n * (Real.sqrt H.det / W_y.det) := by
        rw [mul_one_div]

/-- **Rank-One BCG Jacobian Bound from the Determinant Inequality
([Ruan 2024, Eqs. (5) & (13)] / `[BCG1, Lemme 5.4]`)**:
If $W_y = I - 2H + \widehat{H}$ satisfies $\det W_y > 0$ and the rank-one determinant inequality
$$\frac{\sqrt{\det H}}{\det(I - 2H + \widehat{H})} \le \left(\frac{\sqrt{n}}{h_0}\right)^n$$
for $h_0 > 0$ (specifically $h_0 = n + d - 2$), then the differential $D_F$ satisfying
$W_y \circ_l D_F = s \bullet H_y$ obeys the pointwise BCG Jacobian bound:
$$|\det D_F| \le \left(\frac{s}{h_0}\right)^n.$$ -/
theorem abs_det_le_div_entropy_pow_of_rankOne_det_ineq [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n)
    {s h₀ : ℝ} (hs : 0 ≤ s) (hh₀ : 0 < h₀)
    {D_F H_y H_X H H_hat : E →ₗ[ℝ] E}
    (h_imp : (rankOneHessianOperator H H_hat).comp D_F = s • H_y)
    (hW_pos : 0 < (rankOneHessianOperator H H_hat).det)
    (hH_X : H_X.IsSymmetric) (hH : H.IsSymmetric)
    (hpos_X : ∀ u : E, 0 ≤ inner ℝ u (H_X u))
    (hpos_H : ∀ v : E, 0 ≤ inner ℝ v (H v))
    (htr_X : LinearMap.trace ℝ E H_X ≤ 1)
    (hCS : ∀ u v : E, |inner ℝ (H_y u) v| ≤
      Real.sqrt (inner ℝ u (H_X u)) * Real.sqrt (inner ℝ v (H v)))
    (h_rankOne_ineq :
      Real.sqrt H.det / (rankOneHessianOperator H H_hat).det ≤
        (Real.sqrt (n : ℝ) / h₀) ^ n) :
    |D_F.det| ≤ (s / h₀) ^ n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  obtain ⟨_, h_est⟩ := abs_det_of_hessian_comp_eq_smul
    hn hn_pos hs h_imp hW_pos hH_X hH hpos_X hpos_H htr_X hCS
  calc
    |D_F.det|
      ≤ (s / Real.sqrt (n : ℝ)) ^ n *
          (Real.sqrt H.det / (rankOneHessianOperator H H_hat).det) := h_est
    _ ≤ (s / Real.sqrt (n : ℝ)) ^ n * (Real.sqrt (n : ℝ) / h₀) ^ n :=
        mul_le_mul_of_nonneg_left h_rankOne_ineq (by positivity)
    _ = (s / Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) / h₀)) ^ n :=
        (mul_pow _ _ n).symm
    _ = (s / h₀) ^ n := by
        congr 1
        field_simp [hsqrt_ne, hh₀.ne']

/-- **Quantitative Eigenvalue-Defect Rank-One BCG Bound ([Ruan 2024, Eq. (7) & Cor. 3.8] /
`[BCG1, Prop. B.5]`)**:
If $(H, \widehat{H})$ satisfies the sharp quantitative stability estimate
$$\frac{\sqrt{\det H}}{\det(I - 2H + \widehat{H})} \le
  \left(\frac{\sqrt{n}}{h_0}\right)^n \left(1 - K \sum_{i=1}^n \left(\nu_i - \frac{1}{n}\right)^2\right)$$
where $\nu_i$ are the eigenvalues of $H$, then:
1. $|\det D_F| \le \left(\frac{s}{h_0}\right)^n \left(1 - K \sum_{i=1}^n \left(\nu_i - \frac{1}{n}\right)^2\right)$, and
2. Whenever $s > 0$, $K > 0$, and equality $|\det D_F| = (s / h_0)^n$ holds at $y$, every
   eigenvalue $\nu_i$ of $H$ equals $1/n$ and $H = (1 / (n : \mathbb{R})) \bullet \mathrm{LinearMap.id}$. -/
theorem abs_det_le_div_entropy_pow_mul_defect [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n)
    {s h₀ K : ℝ} (hs : 0 ≤ s) (hh₀ : 0 < h₀)
    {D_F H_y H_X H H_hat : E →ₗ[ℝ] E}
    (h_imp : (rankOneHessianOperator H H_hat).comp D_F = s • H_y)
    (hW_pos : 0 < (rankOneHessianOperator H H_hat).det)
    (hH_X : H_X.IsSymmetric) (hH : H.IsSymmetric)
    (hpos_X : ∀ u : E, 0 ≤ inner ℝ u (H_X u))
    (hpos_H : ∀ v : E, 0 ≤ inner ℝ v (H v))
    (htr_X : LinearMap.trace ℝ E H_X ≤ 1)
    (hCS : ∀ u v : E, |inner ℝ (H_y u) v| ≤
      Real.sqrt (inner ℝ u (H_X u)) * Real.sqrt (inner ℝ v (H v)))
    (h_sharp_ineq :
      Real.sqrt H.det / (rankOneHessianOperator H H_hat).det ≤
        (Real.sqrt (n : ℝ) / h₀) ^ n *
          (1 - K * ∑ i : Fin n, (hH.eigenvalues hn i - 1 / (n : ℝ)) ^ 2)) :
    |D_F.det| ≤ (s / h₀) ^ n *
      (1 - K * ∑ i : Fin n, (hH.eigenvalues hn i - 1 / (n : ℝ)) ^ 2) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  obtain ⟨_, h_est⟩ := abs_det_of_hessian_comp_eq_smul
    hn hn_pos hs h_imp hW_pos hH_X hH hpos_X hpos_H htr_X hCS
  calc
    |D_F.det|
      ≤ (s / Real.sqrt (n : ℝ)) ^ n *
          (Real.sqrt H.det / (rankOneHessianOperator H H_hat).det) := h_est
    _ ≤ (s / Real.sqrt (n : ℝ)) ^ n *
          ((Real.sqrt (n : ℝ) / h₀) ^ n *
            (1 - K * ∑ i : Fin n, (hH.eigenvalues hn i - 1 / (n : ℝ)) ^ 2)) :=
        mul_le_mul_of_nonneg_left h_sharp_ineq (by positivity)
    _ = ((s / Real.sqrt (n : ℝ)) * (Real.sqrt (n : ℝ) / h₀)) ^ n *
          (1 - K * ∑ i : Fin n, (hH.eigenvalues hn i - 1 / (n : ℝ)) ^ 2) := by
        rw [← mul_assoc, ← mul_pow]
    _ = (s / h₀) ^ n *
          (1 - K * ∑ i : Fin n, (hH.eigenvalues hn i - 1 / (n : ℝ)) ^ 2) := by
        congr 2
        field_simp [hsqrt_ne, hh₀.ne']

/-- **Isotropy of $H$ from Saturation of the Quantitative Defect Bound**:
If $|\det D_F| = (s / h_0)^n$ with $s > 0$, $h_0 > 0$, and $K > 0$ in
`abs_det_le_div_entropy_pow_mul_defect`, then $\sum_{i=1}^n (\nu_i - 1/n)^2 = 0$, every eigenvalue
of $H$ equals $1/n$, and $H = (1 / (n : \mathbb{R})) \bullet \mathrm{LinearMap.id}$. -/
theorem isotropic_of_abs_det_eq_div_entropy_pow [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E = n)
    {s h₀ K : ℝ} (hs : 0 < s) (hh₀ : 0 < h₀) (hK : 0 < K)
    {D_F H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (h_defect_bound : |D_F.det| ≤ (s / h₀) ^ n *
      (1 - K * ∑ i : Fin n, (hH.eigenvalues hn i - 1 / (n : ℝ)) ^ 2))
    (h_eq : |D_F.det| = (s / h₀) ^ n) :
    (∀ i : Fin n, hH.eigenvalues hn i = 1 / (n : ℝ)) ∧
    H = (1 / (n : ℝ)) • LinearMap.id := by
  have hsh_pos : 0 < (s / h₀) ^ n := by positivity
  rw [h_eq] at h_defect_bound
  have h_one_le : 1 ≤ 1 - K * ∑ i : Fin n, (hH.eigenvalues hn i - 1 / (n : ℝ)) ^ 2 := by
    have h1 : (s / h₀) ^ n * 1 ≤ (s / h₀) ^ n *
        (1 - K * ∑ i : Fin n, (hH.eigenvalues hn i - 1 / (n : ℝ)) ^ 2) := by
      simpa using h_defect_bound
    exact le_of_mul_le_mul_left h1 hsh_pos
  have h_sum_nonpos : ∑ i : Fin n, (hH.eigenvalues hn i - 1 / (n : ℝ)) ^ 2 ≤ 0 := by
    nlinarith
  have h_sum_nonneg : 0 ≤ ∑ i : Fin n, (hH.eigenvalues hn i - 1 / (n : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have h_sum_zero : ∑ i : Fin n, (hH.eigenvalues hn i - 1 / (n : ℝ)) ^ 2 = 0 :=
    le_antisymm h_sum_nonpos h_sum_nonneg
  have h_all_zero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp h_sum_zero
  have heig : ∀ i : Fin n, hH.eigenvalues hn i = 1 / (n : ℝ) := by
    intro i
    have hi := sq_eq_zero_iff.mp (h_all_zero i (Finset.mem_univ i))
    linarith
  refine ⟨heig, ?_⟩
  apply (hH.eigenvectorBasis hn).toBasis.ext
  intro i
  change H (hH.eigenvectorBasis hn i) = ((1 / (n : ℝ)) • LinearMap.id) (hH.eigenvectorBasis hn i)
  rw [hH.apply_eigenvectorBasis hn i, heig i, LinearMap.smul_apply, LinearMap.id_apply]
  rfl

end BCG.RankOne
