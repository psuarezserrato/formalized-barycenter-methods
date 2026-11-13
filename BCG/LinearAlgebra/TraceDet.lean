import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.LinearAlgebra.Trace

/-!
# Trace-Determinant Inequalities for the Barycenter Method

This file formalizes the core linear algebra trace-determinant inequalities underlying the
Besson–Courtois–Gallot (1995) and Souto (2008) barycenter method on an $n$-dimensional real inner
product space $E$:

1. **Spectral trace and determinant formulas** for symmetric endomorphisms `T : E →ₗ[ℝ] E`:
   - `LinearMap.IsSymmetric.trace_eq_sum_eigenvalues`: $\operatorname{Tr}(T) = \sum_i \lambda_i(T)$
   - `LinearMap.IsSymmetric.det_one_sub_eq_prod_eigenvalues`:
     $\det(I - T) = \prod_i (1 - \lambda_i(T))$
2. **Sharp AM–GM determinant bound** (`LinearMap.IsSymmetric.det_le_trace_div_finrank_pow`):
   For any symmetric positive-semidefinite endomorphism $T : E \to_l[\mathbb{R}] E$
   ($\forall v, 0 \le \langle v, T v \rangle$) on an $n$-dimensional real inner product space,
   $$\det(T) \le \left(\frac{\operatorname{Tr}(T)}{n}\right)^n.$$
3. **Normalized trace-one coroutine** (`LinearMap.IsSymmetric.det_le_inv_finrank_pow_of_trace_le_one`):
   When $\operatorname{Tr}(T) \le 1$, $\det(T) \le n^{-n}$, and for two such operators $H_1, H_2$,
   $$\sqrt{\det(H_1)} \sqrt{\det(H_2)} \le n^{-n}.$$
-/

noncomputable section

open Finset BigOperators

namespace BCG.LinearAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ}

/-- Arithmetic-Geometric Mean inequality in product-power form on `Fin n`:
for $n \ge 1$ and $z_i \ge 0$, $\prod_{i=1}^n z_i \le \left(\frac{1}{n}\sum_{i=1}^n z_i\right)^n$. -/
theorem prod_le_arith_mean_pow (hn : 0 < n) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∏ i : Fin n, z i ≤ ((∑ i : Fin n, z i) / n) ^ n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  let w : Fin n → ℝ := fun _ => (n : ℝ)⁻¹
  have hw : ∀ i ∈ (univ : Finset (Fin n)), 0 ≤ w i := fun _ _ => inv_nonneg.mpr hnR.le
  have hw' : ∑ i ∈ (univ : Finset (Fin n)), w i = 1 := by
    simp [w, hn_ne]
  have h_amgm := Real.geom_mean_le_arith_mean_weighted univ w z hw hw' (fun i _ => hz i)
  have h_lhs_nonneg : 0 ≤ ∏ i ∈ (univ : Finset (Fin n)), z i ^ w i :=
    prod_nonneg fun i _ => Real.rpow_nonneg (hz i) _
  have h_pow := pow_le_pow_left₀ h_lhs_nonneg h_amgm n
  have h_lhs_eq : (∏ i ∈ (univ : Finset (Fin n)), z i ^ w i) ^ n = ∏ i : Fin n, z i := by
    rw [← prod_pow]
    refine prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_natCast (z i ^ w i) n, ← Real.rpow_mul (hz i), inv_mul_cancel₀ hn_ne,
      Real.rpow_one]
  have h_rhs_eq : (∑ i ∈ (univ : Finset (Fin n)), w i * z i) = (∑ i : Fin n, z i) / n := by
    simp only [w, ← mul_sum, div_eq_inv_mul]
  rwa [h_lhs_eq, h_rhs_eq] at h_pow

/-- The trace of a symmetric linear endomorphism on a finite-dimensional real inner product space
equals the sum of its eigenvalues. -/
theorem trace_eq_sum_eigenvalues {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) :
    LinearMap.trace ℝ E T = ∑ i : Fin n, hT.eigenvalues hn i := by
  let b := (hT.eigenvectorBasis hn).toBasis
  rw [LinearMap.trace_eq_matrix_trace ℝ b, hT.toMatrix_eigenvectorBasis hn, Matrix.trace_diagonal]
  simp

/-- The determinant of `1 - T` for a symmetric linear endomorphism `T` equals the product of
`1 - λ_i`, where `λ_i` are the eigenvalues of `T`. -/
theorem det_one_sub_eq_prod_eigenvalues {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) :
    LinearMap.det (1 - T) = ∏ i : Fin n, (1 - hT.eigenvalues hn i) := by
  let b := (hT.eigenvectorBasis hn).toBasis
  rw [← LinearMap.det_toMatrix b (1 - T), map_sub, LinearMap.toMatrix_one,
    hT.toMatrix_eigenvectorBasis hn]
  have hdiag : (1 : Matrix (Fin n) (Fin n) ℝ) -
      Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues hn) =
      Matrix.diagonal (fun i => 1 - hT.eigenvalues hn i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
  rw [hdiag, Matrix.det_diagonal]

/-- Every eigenvalue of a symmetric positive-semidefinite operator is nonnegative. -/
theorem eigenvalues_nonneg_of_inner_nonneg {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (hpos : ∀ v : E, 0 ≤ inner ℝ v (T v)) (i : Fin n) :
    0 ≤ hT.eigenvalues hn i :=
  eigenvalue_nonneg_of_nonneg (hT.hasEigenvalue_eigenvalues hn i) hpos

/-- Every eigenvalue of a symmetric positive-definite operator is strictly positive. -/
theorem eigenvalues_pos_of_inner_pos {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (T v)) (i : Fin n) :
    0 < hT.eigenvalues hn i :=
  eigenvalue_pos_of_pos (hT.hasEigenvalue_eigenvalues hn i) hpos

/-- The determinant of a symmetric positive-semidefinite operator is nonnegative. -/
theorem det_nonneg_of_inner_nonneg {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (hpos : ∀ v : E, 0 ≤ inner ℝ v (T v)) :
    0 ≤ LinearMap.det T := by
  rw [hT.det_eq_prod_eigenvalues hn]
  exact prod_nonneg fun i _ => eigenvalues_nonneg_of_inner_nonneg hT hn hpos i

/-- **BCG Trace-Determinant Inequality**:
For any symmetric positive-semidefinite endomorphism `T : E →ₗ[ℝ] E` on an $n$-dimensional real
inner product space ($n \ge 1$),
$$\det(T) \le \left(\frac{\operatorname{Tr}(T)}{n}\right)^n.$$ -/
theorem det_le_trace_div_dim_pow {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n) (hpos : ∀ v : E, 0 ≤ inner ℝ v (T v)) :
    LinearMap.det T ≤ (LinearMap.trace ℝ E T / n) ^ n := by
  rw [hT.det_eq_prod_eigenvalues hn, trace_eq_sum_eigenvalues hT hn]
  simpa using prod_le_arith_mean_pow hn_pos (hT.eigenvalues hn)
    (eigenvalues_nonneg_of_inner_nonneg hT hn hpos)

/-- Corollary for symmetric positive-semidefinite endomorphisms with $\operatorname{Tr}(T) \le 1$:
$$\det(T) \le \left(\frac{1}{n}\right)^n.$$ -/
theorem det_le_one_div_dim_pow_of_trace_le_one {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n) (hpos : ∀ v : E, 0 ≤ inner ℝ v (T v))
    (htr : LinearMap.trace ℝ E T ≤ 1) :
    LinearMap.det T ≤ (1 / (n : ℝ)) ^ n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have htr_nonneg : 0 ≤ LinearMap.trace ℝ E T := by
    rw [trace_eq_sum_eigenvalues hT hn]
    exact sum_nonneg fun i _ => eigenvalues_nonneg_of_inner_nonneg hT hn hpos i
  calc
    LinearMap.det T ≤ (LinearMap.trace ℝ E T / n) ^ n :=
      det_le_trace_div_dim_pow hT hn hn_pos hpos
    _ ≤ (1 / (n : ℝ)) ^ n := by
      apply pow_le_pow_left₀ (div_nonneg htr_nonneg hnR.le)
      exact div_le_div_of_nonneg_right htr hnR.le

/-- **Souto's Two-Operator Determinant Bound** (Souto 2008, Proof of Proposition 5):
If $H_1, H_2$ are symmetric positive-semidefinite endomorphisms on $n$-dimensional real inner
product spaces $E_1, E_2$ with $\operatorname{Tr}(H_1) \le 1$ and $\operatorname{Tr}(H_2) \le 1$,
then for any factor $c \ge 0$,
$$c^n \sqrt{\det(H_1)} \sqrt{\det(H_2)} \le \left(\frac{c}{n}\right)^n.$$ -/
theorem mul_sqrt_det_le_of_trace_le_one
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    {H₁ : E₁ →ₗ[ℝ] E₁} {H₂ : E₂ →ₗ[ℝ] E₂}
    (hH₁ : H₁.IsSymmetric) (hH₂ : H₂.IsSymmetric)
    (hn₁ : Module.finrank ℝ E₁ = n) (hn₂ : Module.finrank ℝ E₂ = n) (hn_pos : 0 < n)
    (hpos₁ : ∀ v : E₁, 0 ≤ inner ℝ v (H₁ v))
    (hpos₂ : ∀ v : E₂, 0 ≤ inner ℝ v (H₂ v))
    (htr₁ : LinearMap.trace ℝ E₁ H₁ ≤ 1)
    (htr₂ : LinearMap.trace ℝ E₂ H₂ ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) :
    c ^ n * Real.sqrt (LinearMap.det H₁) * Real.sqrt (LinearMap.det H₂) ≤ (c / n) ^ n := by
  have hd₁ := det_le_one_div_dim_pow_of_trace_le_one hH₁ hn₁ hn_pos hpos₁ htr₁
  have hd₂ := det_le_one_div_dim_pow_of_trace_le_one hH₂ hn₂ hn_pos hpos₂ htr₂
  have h1n_nonneg : 0 ≤ (1 / (n : ℝ)) ^ n := by positivity
  have h_sqrt_mul :
      Real.sqrt (LinearMap.det H₁) * Real.sqrt (LinearMap.det H₂) ≤ (1 / (n : ℝ)) ^ n := by
    calc
      Real.sqrt (LinearMap.det H₁) * Real.sqrt (LinearMap.det H₂)
        ≤ Real.sqrt ((1 / (n : ℝ)) ^ n) * Real.sqrt ((1 / (n : ℝ)) ^ n) :=
          mul_le_mul (Real.sqrt_le_sqrt hd₁) (Real.sqrt_le_sqrt hd₂)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = (1 / (n : ℝ)) ^ n := Real.mul_self_sqrt h1n_nonneg
  calc
    c ^ n * Real.sqrt (LinearMap.det H₁) * Real.sqrt (LinearMap.det H₂)
      = c ^ n * (Real.sqrt (LinearMap.det H₁) * Real.sqrt (LinearMap.det H₂)) := by ring
    _ ≤ c ^ n * (1 / (n : ℝ)) ^ n :=
      mul_le_mul_of_nonneg_left h_sqrt_mul (pow_nonneg hc n)
    _ = (c / n) ^ n := by rw [← mul_pow, mul_one_div]

end BCG.LinearAlgebra
