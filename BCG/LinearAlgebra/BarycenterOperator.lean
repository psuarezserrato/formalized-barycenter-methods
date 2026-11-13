import BCG.LinearAlgebra.TraceDet
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Barycenter Operator Determinant Bounds via Cauchy–Schwarz

This file formalizes the operator determinant estimates for the differential of the natural map in
the Besson–Courtois–Gallot (1995) and Souto (2008) barycenter method:

1. **Gram operator trace and determinant** (`det_adjoint`, `det_adjoint_mul_self`,
   `trace_eq_sum_orthonormalBasis`, `trace_adjoint_mul_self_eq_sum_norm_sq`):
   For any endomorphism $A : E \to_l[\mathbb{R}] E$ and orthonormal basis $\{v_i\}$,
   $$\det(A^* A) = (\det A)^2, \qquad \operatorname{Tr}(A^* A) = \sum_{i=1}^n \|A v_i\|^2.$$
2. **Contraction determinant bound** (`abs_det_le_pow_of_norm_le`):
   If $\|A u\| \le c \|u\|$ for all $u \in E$ ($c \ge 0$), then $|\det A| \le c^n$.
3. **Rescaled quadratic-form helper** (`exists_inv_sqrt_of_det_pos`):
   For any symmetric positive-definite operator $H$ on an $n$-dimensional real inner product space,
   there exists a symmetric operator $D$ (namely $H^{-1/2}$) such that
   $\langle D u, H(D u) \rangle = \|u\|^2$ for all $u \in E$ and
   $\det(D) \cdot \sqrt{\det(H)} = 1$.
4. **Bilinear Cauchy–Schwarz determinant bound** (`abs_det_le_of_abs_inner_le`):
   If $L : E \to_l[\mathbb{R}] E$ and symmetric positive-semidefinite operators $H_1, H_2$ satisfy
   $$|\langle L u, w \rangle| \le c \sqrt{\langle u, H_1 u \rangle} \sqrt{\langle w, H_2 w \rangle}$$
   for all $u, w \in E$, then
   $$|\det L| \le c^n \sqrt{\det H_1} \sqrt{\det H_2}.$$
   When $\operatorname{Tr}(H_1) \le 1$ and $\operatorname{Tr}(H_2) \le 1$, this yields Souto's
   Proposition 5 / BCG Jacobian bound:
   $$|\det L| \le \left(\frac{c}{n}\right)^n.$$
-/

noncomputable section

open Finset BigOperators

namespace BCG.LinearAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ}

/-- The determinant of the adjoint of a linear endomorphism on a finite-dimensional real inner
product space equals the determinant of the endomorphism. -/
theorem det_adjoint (A : E →ₗ[ℝ] E) : A.adjoint.det = A.det := by
  let v := stdOrthonormalBasis ℝ E
  rw [← LinearMap.det_toMatrix v.toBasis A.adjoint, LinearMap.toMatrix_adjoint v v,
    Matrix.det_conjTranspose, star_trivial, LinearMap.det_toMatrix]

/-- The determinant of the Gram operator $A^* A$ equals $(\det A)^2$. -/
theorem det_adjoint_mul_self (A : E →ₗ[ℝ] E) : (A.adjoint * A).det = A.det ^ 2 := by
  rw [map_mul, det_adjoint, sq]

/-- The trace of a linear endomorphism in any orthonormal basis equals the sum of its diagonal
inner products $\sum_i \langle v_i, T v_i \rangle$. -/
theorem trace_eq_sum_orthonormalBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E T = ∑ i : ι, inner ℝ (v i) (T (v i)) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ v.toBasis, Matrix.trace]
  refine sum_congr rfl fun i _ => ?_
  exact LinearMap.toMatrixOrthonormal_apply_apply v T i i

/-- The trace of the Gram operator $A^* A$ in any orthonormal basis $\{v_i\}$ equals
$\sum_i \|A v_i\|^2$. -/
theorem trace_adjoint_mul_self_eq_sum_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : OrthonormalBasis ι ℝ E) (A : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E (A.adjoint * A) = ∑ i : ι, ‖A (v i)‖ ^ 2 := by
  rw [trace_eq_sum_orthonormalBasis v (A.adjoint * A)]
  refine sum_congr rfl fun i _ => ?_
  rw [Module.End.mul_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

/-- **Contraction Determinant Bound**:
If $A : E \to_l[\mathbb{R}] E$ satisfies $\|A u\| \le c \|u\|$ for all $u \in E$ ($c \ge 0$),
then $|\det A| \le c^n$ where $n = \dim_{\mathbb{R}} E$. -/
theorem abs_det_le_pow_of_norm_le {A : E →ₗ[ℝ] E} (hn : Module.finrank ℝ E = n)
    (hn_pos : 0 < n) {c : ℝ} (hc : 0 ≤ c) (hA : ∀ u : E, ‖A u‖ ≤ c * ‖u‖) :
    |A.det| ≤ c ^ n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hQ_symm : (A.adjoint * A).IsSymmetric := LinearMap.isSymmetric_adjoint_mul_self A
  have hQ_pos : ∀ u : E, 0 ≤ inner ℝ u ((A.adjoint * A) u) :=
    LinearMap.re_inner_adjoint_mul_self_nonneg A
  let v := hQ_symm.eigenvectorBasis hn
  have htr_le : LinearMap.trace ℝ E (A.adjoint * A) ≤ n * c ^ 2 := by
    rw [trace_adjoint_mul_self_eq_sum_norm_sq v A]
    have hterm : ∀ i : Fin n, ‖A (v i)‖ ^ 2 ≤ c ^ 2 := by
      intro i
      have hvi : ‖v i‖ = 1 := v.orthonormal.1 i
      have h1 : ‖A (v i)‖ ≤ c := by simpa [hvi] using hA (v i)
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc
      ∑ i : Fin n, ‖A (v i)‖ ^ 2 ≤ ∑ _ : Fin n, c ^ 2 := sum_le_sum fun i _ => hterm i
      _ = n * c ^ 2 := by simp
  have hdet_sq : A.det ^ 2 ≤ (c ^ n) ^ 2 := by
    rw [← det_adjoint_mul_self]
    calc
      (A.adjoint * A).det ≤ (LinearMap.trace ℝ E (A.adjoint * A) / n) ^ n :=
        det_le_trace_div_dim_pow hQ_symm hn hn_pos hQ_pos
      _ ≤ (c ^ 2) ^ n := by
        have htr_nn : 0 ≤ LinearMap.trace ℝ E (A.adjoint * A) := by
          rw [trace_adjoint_mul_self_eq_sum_norm_sq v A]
          exact sum_nonneg fun i _ => sq_nonneg _
        apply pow_le_pow_left₀ (div_nonneg htr_nn hnR.le)
        rw [div_le_iff₀ hnR, mul_comm]
        exact htr_le
      _ = (c ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]
  have habs := Real.sqrt_le_sqrt hdet_sq
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (pow_nonneg hc n)] at habs

/-- If a symmetric positive-semidefinite operator $H$ has $\det H = 0$, then there exists a nonzero
eigenvector $v \ne 0$ with $\langle v, H v \rangle = 0$. -/
theorem exists_ne_zero_inner_eq_zero_of_det_eq_zero {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (hdet : H.det = 0) :
    ∃ v : E, v ≠ 0 ∧ inner ℝ v (H v) = 0 := by
  rw [hH.det_eq_prod_eigenvalues hn, prod_eq_zero_iff] at hdet
  rcases hdet with ⟨i, _, hi⟩
  refine ⟨hH.eigenvectorBasis hn i, (hH.eigenvectorBasis hn).toBasis.ne_zero i, ?_⟩
  rw [hH.apply_eigenvectorBasis hn i, real_inner_smul_right, hi, zero_mul]

/-- For a symmetric positive-semidefinite operator $H$ with $\det H > 0$, the inverse square root
$D = H^{-1/2}$ constructed in its orthonormal eigenbasis is symmetric and satisfies
$\langle D u, H(D u) \rangle = \|u\|^2$ and $\det(D) \cdot \sqrt{\det H} = 1$. -/
theorem exists_inv_sqrt_of_det_pos {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (hpos : ∀ u : E, 0 ≤ inner ℝ u (H u)) (hdet : 0 < H.det) :
    ∃ D : E →ₗ[ℝ] E, D.IsSymmetric ∧
      (∀ u : E, inner ℝ (D u) (H (D u)) = ‖u‖ ^ 2) ∧
      D.det * Real.sqrt H.det = 1 := by
  let b := hH.eigenvectorBasis hn
  let μ := hH.eigenvalues hn
  have hμ_pos : ∀ i : Fin n, 0 < μ i := by
    intro i
    have hμ_nn := eigenvalues_nonneg_of_inner_nonneg hH hn hpos i
    refine lt_of_le_of_ne hμ_nn fun hzero => ?_
    have hdet0 : H.det = 0 := by
      rw [hH.det_eq_prod_eigenvalues hn]
      exact prod_eq_zero (mem_univ i) hzero.symm
    linarith
  let d : Fin n → ℝ := fun i => (Real.sqrt (μ i))⁻¹
  let D : E →ₗ[ℝ] E := Matrix.toLin b.toBasis b.toBasis (Matrix.diagonal d)
  have hD_apply_basis : ∀ i : Fin n, D (b i) = d i • b i := by
    intro i
    change (Matrix.toLin b.toBasis b.toBasis (Matrix.diagonal d)) (b.toBasis i) = d i • b.toBasis i
    rw [Matrix.toLin_self]
    simp [Matrix.diagonal_apply]
  have hD_repr : ∀ (u : E) (i : Fin n), b.repr (D u) i = d i * b.repr u i := by
    intro u i
    conv_lhs => rw [b.repr_apply_apply, ← b.sum_repr u, map_sum, inner_sum]
    simp [hD_apply_basis, real_inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
    ring
  have hD_symm : D.IsSymmetric := by
    intro u w
    rw [← b.repr.inner_map_map (D u) w, ← b.repr.inner_map_map u (D w),
      EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial, dotProduct]
    refine sum_congr rfl fun i _ => ?_
    rw [hD_repr u i, hD_repr w i]
    ring
  have hD_quad : ∀ u : E, inner ℝ (D u) (H (D u)) = ‖u‖ ^ 2 := by
    intro u
    rw [← b.repr.inner_map_map (D u) (H (D u)), EuclideanSpace.inner_eq_star_dotProduct,
      ← b.repr.norm_map u, EuclideanSpace.norm_sq_eq]
    simp only [star_trivial, dotProduct, Real.norm_eq_abs, sq_abs]
    refine sum_congr rfl fun i _ => ?_
    rw [hH.eigenvectorBasis_apply_self_apply hn (D u) i, hD_repr u i]
    have hsq : Real.sqrt (μ i) * Real.sqrt (μ i) = μ i := Real.mul_self_sqrt (hμ_pos i).le
    have hinv : μ i * ((Real.sqrt (μ i))⁻¹ * (Real.sqrt (μ i))⁻¹) = 1 := by
      rw [← mul_inv, hsq, mul_inv_cancel₀ (ne_of_gt (hμ_pos i))]
    dsimp [d]
    calc
      μ i * ((Real.sqrt (μ i))⁻¹ * b.repr u i) * ((Real.sqrt (μ i))⁻¹ * b.repr u i)
        = (μ i * ((Real.sqrt (μ i))⁻¹ * (Real.sqrt (μ i))⁻¹)) * (b.repr u i) ^ 2 := by ring
      _ = (b.repr u i) ^ 2 := by rw [hinv, one_mul]
  have hD_det : D.det * Real.sqrt H.det = 1 := by
    have hdetD : D.det = ∏ i : Fin n, d i := by
      dsimp [D]
      rw [LinearMap.det_toLin, Matrix.det_diagonal]
    rw [hdetD, hH.det_eq_prod_eigenvalues hn]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [Real.sqrt_prod _ (fun i _ => (hμ_pos i).le), ← prod_mul_distrib]
    refine prod_eq_one fun i _ => ?_
    dsimp [d]
    exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (hμ_pos i)))
  exact ⟨D, hD_symm, hD_quad, hD_det⟩

/-- **Bilinear Cauchy–Schwarz Determinant Bound**:
If $L : E \to_l[\mathbb{R}] E$ and symmetric positive-semidefinite operators $H_1, H_2$ on an
$n$-dimensional real inner product space $E$ ($n \ge 1$) satisfy
$$|\langle L u, w \rangle| \le c \sqrt{\langle u, H_1 u \rangle} \sqrt{\langle w, H_2 w \rangle}$$
for all $u, w \in E$ ($c \ge 0$), then
$$|\det L| \le c^n \sqrt{\det H_1} \sqrt{\det H_2}.$$ -/
theorem abs_det_le_of_abs_inner_le
    {L H₁ H₂ : E →ₗ[ℝ] E} (hH₁ : H₁.IsSymmetric) (hH₂ : H₂.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n)
    (hpos₁ : ∀ u : E, 0 ≤ inner ℝ u (H₁ u))
    (hpos₂ : ∀ w : E, 0 ≤ inner ℝ w (H₂ w))
    {c : ℝ} (hc : 0 ≤ c)
    (hCS : ∀ u w : E, |inner ℝ (L u) w| ≤
      c * Real.sqrt (inner ℝ u (H₁ u)) * Real.sqrt (inner ℝ w (H₂ w))) :
    |L.det| ≤ c ^ n * Real.sqrt H₁.det * Real.sqrt H₂.det := by
  have hd₁_nn := det_nonneg_of_inner_nonneg hH₁ hn hpos₁
  have hd₂_nn := det_nonneg_of_inner_nonneg hH₂ hn hpos₂
  by_cases hd₁ : H₁.det = 0
  · obtain ⟨v, hv_ne, hv0⟩ := exists_ne_zero_inner_eq_zero_of_det_eq_zero hH₁ hn hd₁
    have hLv : L v = 0 := by
      have h0 : |inner ℝ (L v) (L v)| ≤ 0 := by
        simpa [hv0] using hCS v (L v)
      exact inner_self_eq_zero.mp (abs_nonpos_iff.mp h0)
    have hdetL : L.det = 0 := LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
      (fun hbot => hv_ne ((Submodule.eq_bot_iff _).mp hbot v (LinearMap.mem_ker.mpr hLv)))
    simp [hdetL, hd₁]
  · by_cases hd₂ : H₂.det = 0
    · obtain ⟨w, hw_ne, hw0⟩ := exists_ne_zero_inner_eq_zero_of_det_eq_zero hH₂ hn hd₂
      have hLad_w : L.adjoint w = 0 := by
        have h0 : |inner ℝ (L (L.adjoint w)) w| ≤ 0 := by
          simpa [hw0] using hCS (L.adjoint w) w
        rw [← LinearMap.adjoint_inner_right] at h0
        exact inner_self_eq_zero.mp (abs_nonpos_iff.mp h0)
      have hdetLad : L.adjoint.det = 0 := LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
        (fun hbot => hw_ne ((Submodule.eq_bot_iff _).mp hbot w (LinearMap.mem_ker.mpr hLad_w)))
      rw [det_adjoint] at hdetLad
      simp [hdetLad, hd₂]
    · have hd₁_pos : 0 < H₁.det := lt_of_le_of_ne hd₁_nn (Ne.symm hd₁)
      have hd₂_pos : 0 < H₂.det := lt_of_le_of_ne hd₂_nn (Ne.symm hd₂)
      obtain ⟨D₁, _, hD₁_quad, hD₁_det⟩ := exists_inv_sqrt_of_det_pos hH₁ hn hpos₁ hd₁_pos
      obtain ⟨D₂, hD₂_symm, hD₂_quad, hD₂_det⟩ := exists_inv_sqrt_of_det_pos hH₂ hn hpos₂ hd₂_pos
      let A : E →ₗ[ℝ] E := D₂ ∘ₗ L ∘ₗ D₁
      have hA_norm : ∀ u : E, ‖A u‖ ≤ c * ‖u‖ := by
        intro u
        by_cases hAu : ‖A u‖ = 0
        · rw [hAu]; exact mul_nonneg hc (norm_nonneg u)
        · have hAu_pos : 0 < ‖A u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hAu)
          have h_in : ‖A u‖ ^ 2 ≤ c * ‖u‖ * ‖A u‖ := by
            calc
              ‖A u‖ ^ 2 = |inner ℝ (A u) (A u)| := by
                rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
              _ = |inner ℝ (L (D₁ u)) (D₂ (A u))| := by
                change |inner ℝ (D₂ (L (D₁ u))) (A u)| = |inner ℝ (L (D₁ u)) (D₂ (A u))|
                rw [hD₂_symm (L (D₁ u)) (A u)]
              _ ≤ c * Real.sqrt (inner ℝ (D₁ u) (H₁ (D₁ u))) *
                    Real.sqrt (inner ℝ (D₂ (A u)) (H₂ (D₂ (A u)))) :=
                hCS (D₁ u) (D₂ (A u))
              _ = c * ‖u‖ * ‖A u‖ := by
                rw [hD₁_quad u, hD₂_quad (A u), Real.sqrt_sq (norm_nonneg u),
                  Real.sqrt_sq (norm_nonneg (A u))]
          nlinarith
      have hA_det_le := abs_det_le_pow_of_norm_le hn hn_pos hc hA_norm
      have hD₁_det_pos : 0 < D₁.det := by
        nlinarith [hD₁_det, Real.sqrt_pos.mpr hd₁_pos]
      have hD₂_det_pos : 0 < D₂.det := by
        nlinarith [hD₂_det, Real.sqrt_pos.mpr hd₂_pos]
      have hA_det_eq : |A.det| = D₂.det * |L.det| * D₁.det := by
        dsimp [A]
        rw [LinearMap.det_comp, LinearMap.det_comp, abs_mul, abs_mul,
          abs_of_pos hD₂_det_pos, abs_of_pos hD₁_det_pos]
        ring
      have hL_eq : |L.det| = |A.det| * Real.sqrt H₁.det * Real.sqrt H₂.det := by
        rw [hA_det_eq]
        calc
          |L.det| = |L.det| * (D₁.det * Real.sqrt H₁.det) * (D₂.det * Real.sqrt H₂.det) := by
            rw [hD₁_det, hD₂_det, mul_one, mul_one]
          _ = D₂.det * |L.det| * D₁.det * Real.sqrt H₁.det * Real.sqrt H₂.det := by ring
      calc
        |L.det| = |A.det| * Real.sqrt H₁.det * Real.sqrt H₂.det := hL_eq
        _ ≤ c ^ n * Real.sqrt H₁.det * Real.sqrt H₂.det := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right hA_det_le (Real.sqrt_nonneg _)
          · exact Real.sqrt_nonneg _

/-- **Souto / BCG Natural Map Jacobian Bound**:
If $L : E \to_l[\mathbb{R}] E$ and symmetric positive-semidefinite operators $H_1, H_2$ on an
$n$-dimensional real inner product space $E$ ($n \ge 1$) with $\operatorname{Tr}(H_1) \le 1$ and
$\operatorname{Tr}(H_2) \le 1$ satisfy
$$|\langle L u, w \rangle| \le c \sqrt{\langle u, H_1 u \rangle} \sqrt{\langle w, H_2 w \rangle}$$
for all $u, w \in E$ ($c \ge 0$), then
$$|\det L| \le \left(\frac{c}{n}\right)^n.$$ -/
theorem abs_det_le_div_dim_pow_of_abs_inner_le
    {L H₁ H₂ : E →ₗ[ℝ] E} (hH₁ : H₁.IsSymmetric) (hH₂ : H₂.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n)
    (hpos₁ : ∀ u : E, 0 ≤ inner ℝ u (H₁ u))
    (hpos₂ : ∀ w : E, 0 ≤ inner ℝ w (H₂ w))
    (htr₁ : LinearMap.trace ℝ E H₁ ≤ 1)
    (htr₂ : LinearMap.trace ℝ E H₂ ≤ 1)
    {c : ℝ} (hc : 0 ≤ c)
    (hCS : ∀ u w : E, |inner ℝ (L u) w| ≤
      c * Real.sqrt (inner ℝ u (H₁ u)) * Real.sqrt (inner ℝ w (H₂ w))) :
    |L.det| ≤ (c / n) ^ n :=
  (abs_det_le_of_abs_inner_le hH₁ hH₂ hn hn_pos hpos₁ hpos₂ hc hCS).trans
    (mul_sqrt_det_le_of_trace_le_one hH₁ hH₂ hn hn hn_pos hpos₁ hpos₂ htr₁ htr₂ hc)

end BCG.LinearAlgebra
