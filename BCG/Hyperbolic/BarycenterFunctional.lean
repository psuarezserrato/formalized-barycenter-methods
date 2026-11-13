import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BusemannHessian
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Busemann.Cocycle
import DifferentialGeometry.Geometry.CenterOfMass.Basic
import BCG.LinearAlgebra.BarycenterOperator

/-!
# Hyperbolic Busemann Functions, Rank-One Covariance Tensors, and Barycenter Functional

This file connects the hyperboloid Busemann Hessian identities from
`DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BusemannHessian` and the Lorentz-model
Busemann cocycle from `DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Busemann.Cocycle`
to the linear-algebraic Jacobian machinery in `BCG.LinearAlgebra.BarycenterOperator`.

## Main Results
1. **Hyperboloid Busemann Hessian & Gradient Norm** (`hyperboloidBusemann_hessian`,
   `hyperboloidBusemann_diff_sq_le`, `hyperboloidBusemann_hessian_nonneg`):
   For every boundary direction $\xi \in S(E)$ and point $y \in \mathrm{Hyperboloid}(E)$,
   $$\operatorname{Hess}_y B_\xi(v, w) = g_y(v, w) - dB_\xi(y)(v)\,dB_\xi(y)(w) \ge 0,$$
   and $(dB_\xi(y)(v))^2 \le g_y(v, v)$.
2. **Rank-One Busemann Tensor (`selfOuter`)** (`isSymmetric_selfOuter`, `inner_selfOuter_eq_sq`,
   `trace_selfOuter`):
   For any vector $u \in E$ (representing $\nabla B_\xi$), the rank-one endomorphism
   $v \mapsto \langle u, v \rangle u$ is symmetric, positive-semidefinite, and has trace $\|u\|^2$.
3. **Weighted Busemann Covariance Operators (`busemannCovariance`, `busemannCrossOperator`)**:
   For any probability distribution of unit gradients ($w_a \ge 0$, $\sum_a w_a = 1$,
   $\|u_a\| \le 1$, $\|u'_a\| \le 1$), the covariance operators $H_1, H_2$ are symmetric,
   positive-semidefinite, satisfy $\operatorname{Tr}(H_1) \le 1$ and $\operatorname{Tr}(H_2) \le 1$,
   and the cross-differential $L = c \sum_a w_a \langle u'_a, \cdot \rangle u_a$ satisfies
   $$|\langle L v, w \rangle| \le c \sqrt{\langle v, H_1 v \rangle} \sqrt{\langle w, H_2 w \rangle}$$
   and hence by `abs_det_le_div_dim_pow_of_abs_inner_le`:
   $$|\det L| \le \left(\frac{c}{n}\right)^n.$$
-/

noncomputable section

open Finset BigOperators
open scoped Manifold ContDiff

namespace BCG.Hyperbolic

open DifferentialGeometry
open DifferentialGeometry.Hyperboloid
open BCG.LinearAlgebra

section HyperboloidBusemann

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The standard Busemann function on the hyperboloid model `Hyperboloid E` centered at
$\xi \in S(E)$:
$$B_\xi(y) = \log(y.\mathrm{time} - \langle \xi, y.\mathrm{space} \rangle).$$ -/
def hyperboloidBusemann (ξ : Metric.sphere (0 : E) 1) (y : Hyperboloid E) : ℝ :=
  Real.log (y.time - inner ℝ (ξ : E) y.space)

/-- The Busemann function `hyperboloidBusemann ξ` is $C^\infty$ smooth on `Hyperboloid E`. -/
theorem contMDiff_hyperboloidBusemann (ξ : Metric.sphere (0 : E) 1) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (hyperboloidBusemann ξ) :=
  contMDiff_log_time_sub_inner ξ

/-- The Riemannian differential $dB_\xi(y) : T_y(\mathrm{Hyperboloid}\, E) \to_L[\mathbb{R}] \mathbb{R}$
of the Busemann function at $y$. -/
def hyperboloidBusemannDiff (ξ : Metric.sphere (0 : E) 1) (y : Hyperboloid E) :
    TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ :=
  mvfderiv 𝓘(ℝ, E) (hyperboloidBusemann ξ) y

/-- **Exact Busemann Hessian Identity on $\mathbb{H}^n$**:
$$\operatorname{Hess}_y B_\xi(v, w) = g_y(v, w) - dB_\xi(y)(v)\,dB_\xi(y)(w).$$ -/
theorem hyperboloidBusemann_hessian [FiniteDimensional ℝ E]
    (ξ : Metric.sphere (0 : E) 1) (y : Hyperboloid E)
    (v w : TangentSpace 𝓘(ℝ, E) y) :
    Geometry.Operator.hessFun riemannianMetric (hyperboloidBusemann ξ) y v w =
      riemannianMetric.inner y v w -
        hyperboloidBusemannDiff ξ y v * hyperboloidBusemannDiff ξ y w :=
  hessFun_log_time_sub_inner ξ y v w

/-- **Unit Gradient Bound for the Busemann Differential on $\mathbb{H}^n$**:
$$(dB_\xi(y)(v))^2 \le g_y(v, v).$$ -/
theorem hyperboloidBusemann_diff_sq_le (ξ : Metric.sphere (0 : E) 1) (y : Hyperboloid E)
    (v : TangentSpace 𝓘(ℝ, E) y) :
    (hyperboloidBusemannDiff ξ y v) ^ 2 ≤ riemannianMetric.inner y v v :=
  sq_mvfderiv_log_time_sub_inner_le ξ y v

/-- **Convexity of Busemann Functions on $\mathbb{H}^n$**:
The Riemannian Hessian of $B_\xi$ is positive-semidefinite everywhere on `Hyperboloid E`. -/
theorem hyperboloidBusemann_hessian_nonneg [FiniteDimensional ℝ E]
    (ξ : Metric.sphere (0 : E) 1) (y : Hyperboloid E)
    (v : TangentSpace 𝓘(ℝ, E) y) :
    0 ≤ Geometry.Operator.hessFun riemannianMetric (hyperboloidBusemann ξ) y v v := by
  rw [hyperboloidBusemann_hessian, sub_nonneg, ← sq]
  exact hyperboloidBusemann_diff_sq_le ξ y v

/-- Exponential Busemann height $\exp(B_\xi(y)) = y.\mathrm{time} - \langle \xi, y.\mathrm{space} \rangle$
used in Souto's natural map functional $\mathcal{B}_x(y) = \int \exp(B_\xi(y))\,d\mu_x(\xi)$. -/
def expHyperboloidBusemann (ξ : Metric.sphere (0 : E) 1) (y : Hyperboloid E) : ℝ :=
  Real.exp (hyperboloidBusemann ξ y)

end HyperboloidBusemann

section RankOneCovariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The rank-one self-adjoint tensor $u \otimes u^\flat : E \to_l[\mathbb{R}] E$ given by
$v \mapsto \langle u, v \rangle u$. -/
def selfOuter (u : E) : E →ₗ[ℝ] E :=
  (LinearMap.toSpanSingleton ℝ E u).comp (innerₛₗ ℝ u)

@[simp]
theorem selfOuter_apply (u v : E) : selfOuter u v = inner ℝ u v • u :=
  rfl

/-- `selfOuter u` is a symmetric linear endomorphism. -/
theorem isSymmetric_selfOuter (u : E) : (selfOuter u).IsSymmetric := by
  intro v w
  simp only [selfOuter_apply, real_inner_smul_left, real_inner_smul_right, real_inner_comm u]
  ring

/-- The quadratic form of `selfOuter u` is $\langle v, (u \otimes u^\flat) v \rangle = \langle u, v \rangle^2$. -/
theorem inner_selfOuter_eq_sq (u v : E) :
    inner ℝ v (selfOuter u v) = (inner ℝ u v) ^ 2 := by
  rw [selfOuter_apply, real_inner_smul_right, real_inner_comm v u, sq]

/-- `selfOuter u` is positive-semidefinite. -/
theorem inner_selfOuter_nonneg (u v : E) : 0 ≤ inner ℝ v (selfOuter u v) := by
  rw [inner_selfOuter_eq_sq]
  exact sq_nonneg _

/-- **Trace Identity for Rank-One Busemann Gradient Tensors**:
$$\operatorname{Tr}(u \otimes u^\flat) = \|u\|^2.$$ -/
theorem trace_selfOuter [FiniteDimensional ℝ E] (u : E) :
    LinearMap.trace ℝ E (selfOuter u) = ‖u‖ ^ 2 := by
  let b := stdOrthonormalBasis ℝ E
  rw [trace_eq_sum_orthonormalBasis b (selfOuter u)]
  have h : ∀ i, inner ℝ (b i) (selfOuter u (b i)) = inner ℝ u (b i) * inner ℝ (b i) u := by
    intro i
    rw [inner_selfOuter_eq_sq, sq, real_inner_comm (b i) u]
  simp_rw [h]
  rw [b.sum_inner_mul_inner u u, real_inner_self_eq_norm_sq]

/-- The rank-one cross-operator $u_2 \otimes u_1^\flat : E \to_l[\mathbb{R}] E$ given by
$v \mapsto \langle u_1, v \rangle u_2$. -/
def crossOuter (u₁ u₂ : E) : E →ₗ[ℝ] E :=
  (LinearMap.toSpanSingleton ℝ E u₂).comp (innerₛₗ ℝ u₁)

@[simp]
theorem crossOuter_apply (u₁ u₂ v : E) : crossOuter u₁ u₂ v = inner ℝ u₁ v • u₂ :=
  rfl

theorem inner_crossOuter_apply (u₁ u₂ v w : E) :
    inner ℝ (crossOuter u₁ u₂ v) w = inner ℝ u₁ v * inner ℝ u₂ w := by
  rw [crossOuter_apply, real_inner_smul_left]

end RankOneCovariance

section WeightedBusemannCovariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The weighted Busemann covariance operator
$$H = \sum_{a \in s} w_a (u_a \otimes u_a^\flat) : E \to_l[\mathbb{R}] E$$
associated to a family of Busemann gradient vectors $u_a$ and weights $w_a$. -/
def busemannCovariance {α : Type*} (s : Finset α) (w : α → ℝ) (u : α → E) : E →ₗ[ℝ] E :=
  ∑ a ∈ s, w a • selfOuter (u a)

/-- `busemannCovariance` is a symmetric linear endomorphism. -/
theorem isSymmetric_busemannCovariance {α : Type*} (s : Finset α) (w : α → ℝ) (u : α → E) :
    (busemannCovariance s w u).IsSymmetric := by
  intro v z
  simp only [busemannCovariance, LinearMap.sum_apply, LinearMap.smul_apply,
    inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [isSymmetric_selfOuter (u a) v z]

/-- The quadratic form of `busemannCovariance` is $\sum_{a \in s} w_a \langle u_a, v \rangle^2$. -/
theorem inner_busemannCovariance_eq_sum {α : Type*} (s : Finset α) (w : α → ℝ) (u : α → E) (v : E) :
    inner ℝ v (busemannCovariance s w u v) = ∑ a ∈ s, w a * (inner ℝ (u a) v) ^ 2 := by
  simp only [busemannCovariance, LinearMap.sum_apply, LinearMap.smul_apply, inner_sum,
    real_inner_smul_right, inner_selfOuter_eq_sq]

/-- For non-negative weights $w_a \ge 0$, `busemannCovariance` is positive-semidefinite. -/
theorem inner_busemannCovariance_nonneg {α : Type*} (s : Finset α) {w : α → ℝ}
    (hw : ∀ a ∈ s, 0 ≤ w a) (u : α → E) (v : E) :
    0 ≤ inner ℝ v (busemannCovariance s w u v) := by
  rw [inner_busemannCovariance_eq_sum]
  exact Finset.sum_nonneg (fun a ha => mul_nonneg (hw a ha) (sq_nonneg _))

/-- **Trace Bound for Busemann Covariance Operators**:
When $w_a \ge 0$, $\sum_{a \in s} w_a \le 1$, and $\|u_a\| \le 1$ (since $\|\nabla B_\xi\| \le 1$),
we have $\operatorname{Tr}(H) \le 1$. -/
theorem trace_busemannCovariance_le_one [FiniteDimensional ℝ E] {α : Type*} (s : Finset α)
    {w : α → ℝ} (hw : ∀ a ∈ s, 0 ≤ w a) (hw_sum : ∑ a ∈ s, w a ≤ 1)
    {u : α → E} (hu : ∀ a ∈ s, ‖u a‖ ≤ 1) :
    LinearMap.trace ℝ E (busemannCovariance s w u) ≤ 1 := by
  unfold busemannCovariance
  rw [map_sum]
  calc
    ∑ a ∈ s, (LinearMap.trace ℝ E) (w a • selfOuter (u a))
      = ∑ a ∈ s, w a * ‖u a‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [LinearMap.map_smul, smul_eq_mul, trace_selfOuter]
    _ ≤ ∑ a ∈ s, w a * 1 := by
        refine Finset.sum_le_sum (fun a ha => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (hw a ha)
        nlinarith [hu a ha, norm_nonneg (u a)]
    _ ≤ 1 := by simpa using hw_sum

/-- The weighted Busemann cross-operator
$$L = c \sum_{a \in s} w_a (u_2(a) \otimes u_1(a)^\flat) : E \to_l[\mathbb{R}] E$$
appearing in the implicit-function differentiation of the barycenter equation. -/
def busemannCrossOperator {α : Type*} (c : ℝ) (s : Finset α) (w : α → ℝ) (u₁ u₂ : α → E) :
    E →ₗ[ℝ] E :=
  c • ∑ a ∈ s, w a • crossOuter (u₁ a) (u₂ a)

/-- **Cauchy–Schwarz Inequality for Busemann Cross-Operators**:
$$|\langle L v, z \rangle| \le c \sqrt{\langle v, H_1 v \rangle} \sqrt{\langle z, H_2 z \rangle}.$$ -/
theorem abs_inner_busemannCrossOperator_le {α : Type*} {c : ℝ} (hc : 0 ≤ c)
    (s : Finset α) {w : α → ℝ} (hw : ∀ a ∈ s, 0 ≤ w a) (u₁ u₂ : α → E) (v z : E) :
    |inner ℝ (busemannCrossOperator c s w u₁ u₂ v) z| ≤
      c * Real.sqrt (inner ℝ v (busemannCovariance s w u₁ v)) *
        Real.sqrt (inner ℝ z (busemannCovariance s w u₂ z)) := by
  have h_expand : inner ℝ (busemannCrossOperator c s w u₁ u₂ v) z =
      c * ∑ a ∈ s, (Real.sqrt (w a) * inner ℝ (u₁ a) v) *
        (Real.sqrt (w a) * inner ℝ (u₂ a) z) := by
    simp only [busemannCrossOperator, LinearMap.smul_apply, LinearMap.sum_apply,
      real_inner_smul_left, sum_inner, inner_crossOuter_apply]
    congr 1
    refine Finset.sum_congr rfl (fun a ha => ?_)
    have hwa : Real.sqrt (w a) * Real.sqrt (w a) = w a := Real.mul_self_sqrt (hw a ha)
    calc
      w a * (inner ℝ (u₁ a) v * inner ℝ (u₂ a) z)
        = (Real.sqrt (w a) * Real.sqrt (w a)) * (inner ℝ (u₁ a) v * inner ℝ (u₂ a) z) := by
          rw [hwa]
      _ = (Real.sqrt (w a) * inner ℝ (u₁ a) v) * (Real.sqrt (w a) * inner ℝ (u₂ a) z) := by
          ring
  rw [h_expand, abs_mul, abs_of_nonneg hc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  have h_cs := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun a => |Real.sqrt (w a) * inner ℝ (u₁ a) v|)
    (fun a => |Real.sqrt (w a) * inner ℝ (u₂ a) z|)
  have h_abs_sum : |∑ a ∈ s, (Real.sqrt (w a) * inner ℝ (u₁ a) v) *
      (Real.sqrt (w a) * inner ℝ (u₂ a) z)| ≤
      ∑ a ∈ s, |Real.sqrt (w a) * inner ℝ (u₁ a) v| *
        |Real.sqrt (w a) * inner ℝ (u₂ a) z| := by
    simpa [abs_mul] using Finset.abs_sum_le_sum_abs
      (fun a => (Real.sqrt (w a) * inner ℝ (u₁ a) v) * (Real.sqrt (w a) * inner ℝ (u₂ a) z)) s
  have h_sq₁ : ∑ a ∈ s, |Real.sqrt (w a) * inner ℝ (u₁ a) v| ^ 2 =
      inner ℝ v (busemannCovariance s w u₁ v) := by
    rw [inner_busemannCovariance_eq_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [sq_abs, mul_pow, Real.sq_sqrt (hw a ha)]
  have h_sq₂ : ∑ a ∈ s, |Real.sqrt (w a) * inner ℝ (u₂ a) z| ^ 2 =
      inner ℝ z (busemannCovariance s w u₂ z) := by
    rw [inner_busemannCovariance_eq_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [sq_abs, mul_pow, Real.sq_sqrt (hw a ha)]
  rw [h_sq₁, h_sq₂] at h_cs
  exact le_trans h_abs_sum h_cs

/-- **Determinant Bound for Weighted Busemann Cross-Operators**:
For any sub-probability distribution of unit Busemann gradient vectors ($w_a \ge 0$,
$\sum_{a \in s} w_a \le 1$, $\|u_1(a)\| \le 1$, $\|u_2(a)\| \le 1$) and scale factor $c \ge 0$,
$$|\det L| \le \left(\frac{c}{n}\right)^n.$$ -/
theorem abs_det_busemannCrossOperator_le [FiniteDimensional ℝ E] {n : ℕ}
    (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n)
    {α : Type*} {c : ℝ} (hc : 0 ≤ c) (s : Finset α)
    {w : α → ℝ} (hw : ∀ a ∈ s, 0 ≤ w a) (hw_sum : ∑ a ∈ s, w a ≤ 1)
    {u₁ u₂ : α → E} (hu₁ : ∀ a ∈ s, ‖u₁ a‖ ≤ 1) (hu₂ : ∀ a ∈ s, ‖u₂ a‖ ≤ 1) :
    |(busemannCrossOperator c s w u₁ u₂).det| ≤ (c / (n : ℝ)) ^ n :=
  abs_det_le_div_dim_pow_of_abs_inner_le
    (isSymmetric_busemannCovariance s w u₁)
    (isSymmetric_busemannCovariance s w u₂)
    hn hn_pos
    (inner_busemannCovariance_nonneg s hw u₁)
    (inner_busemannCovariance_nonneg s hw u₂)
    (trace_busemannCovariance_le_one s hw hw_sum hu₁)
    (trace_busemannCovariance_le_one s hw hw_sum hu₂)
    hc
    (abs_inner_busemannCrossOperator_le hc s hw u₁ u₂)

end WeightedBusemannCovariance

end BCG.Hyperbolic
