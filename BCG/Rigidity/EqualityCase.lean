import BCG.LinearAlgebra.TraceDet
import BCG.LinearAlgebra.BarycenterOperator
import BCG.Hyperbolic.BarycenterFunctional
import BCG.Hyperbolic.JacobianBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Step 3: Change-of-Variables, Equality in AM–GM / Cauchy–Schwarz, and BCG Rigidity

This file formalizes the third pillar of the Besson–Courtois–Gallot (1995) and Souto (2008)
barycenter method:

1. **Euclidean Change-of-Variables Formula** (`measureReal_image_eq_integral_abs_det_fderiv`):
   For an injective $C^1$ chart map $f : E \to E$ on a measurable set $s$, the volume of the image
   $f(s)$ equals $\int_{x \in s} |\det f'(x)| \, d\mu(x)$.
2. **Spectral AM–GM Equality Case & Isotropic Covariance**
   (`eq_one_of_prod_eq_one_of_sum_le`, `eq_one_div_dim_smul_id_of_det_eq`):
   If a symmetric positive-semidefinite operator $H : E \to_l[\mathbb{R}] E$ on an $n$-dimensional
   real inner product space ($n \ge 1$) satisfies $\operatorname{Tr}(H) \le 1$ and
   $\det H = (1/n)^n$, then $\operatorname{Tr}(H) = 1$, every eigenvalue of $H$ equals $1/n$, and
   $$H = \left(\frac{1}{n}\right) \bullet \mathrm{LinearMap.id}.$$
3. **Bilinear Cauchy–Schwarz Determinant Equality & Homothety / Scaled Isometry**
   (`isotropic_and_norm_eq_of_abs_det_eq_div_dim_pow`):
   If $L, H_1, H_2 : E \to_l[\mathbb{R}] E$ satisfy the BCG Cauchy–Schwarz hypotheses with $c > 0$
   and $|\det L| = (c/n)^n$, then:
   - $H_1 = (1/n) \bullet \mathrm{LinearMap.id}$ and $H_2 = (1/n) \bullet \mathrm{LinearMap.id}$,
   - $L^* \circ L = (c/n)^2 \bullet \mathrm{LinearMap.id}$, and
   - $\|L u\| = (c/n) \|u\|$ for all $u \in E$ (so $L$ is a linear isometry when $c = n$).
4. **Almost-Everywhere Equality & Mostow/BCG Infinitesimal Rigidity**
   (`ae_eq_of_bcg_volume_equality`, `riemannianBarycenterDifferential_rigidity`):
   Equality in the BCG volume inequality at scale $s > 0$ forces $|\det(D^{\mathrm{Riem}} F_s(x))| = (s/n)^n$
   almost everywhere, hence forces isotropic Busemann covariance tensors and a scaled Riemannian
   isometry differential almost everywhere.
-/

noncomputable section

open Finset BigOperators MeasureTheory Filter Set

namespace BCG.LinearAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ}

/-!
### 1. Equality Case of the Arithmetic–Geometric Mean Inequality on `Fin n`
-/

/-- **AM–GM Equality Lemma**:
If $z : \mathrm{Fin}\,n \to \mathbb{R}$ has strictly positive entries ($z_i > 0$), unit product
$\prod_i z_i = 1$, and sum $\sum_i z_i \le n$, then $z_i = 1$ for every $i$. -/
theorem eq_one_of_prod_eq_one_of_sum_le
    (z : Fin n → ℝ) (hz : ∀ i, 0 < z i)
    (hprod : ∏ i : Fin n, z i = 1) (hsum : ∑ i : Fin n, z i ≤ n) :
    ∀ i : Fin n, z i = 1 := by
  intro i₀
  by_contra hne
  have hlog_le : ∀ i : Fin n, Real.log (z i) ≤ z i - 1 :=
    fun i => Real.log_le_sub_one_of_pos (hz i)
  have hlog_lt : Real.log (z i₀) < z i₀ - 1 :=
    Real.log_lt_sub_one_of_pos (hz i₀) hne
  have hsum_lt : ∑ i : Fin n, Real.log (z i) < ∑ i : Fin n, (z i - 1) :=
    Finset.sum_lt_sum (fun i _ => hlog_le i) ⟨i₀, Finset.mem_univ i₀, hlog_lt⟩
  have hsum_log : ∑ i : Fin n, Real.log (z i) = 0 := by
    rw [← Real.log_prod (fun i _ => (hz i).ne'), hprod, Real.log_one]
  have hsum_sub : ∑ i : Fin n, (z i - 1) = (∑ i : Fin n, z i) - n := by
    simp [Finset.sum_sub_distrib]
  linarith

/-- **Rescaled AM–GM Equality Lemma**:
If $n > 0$ and $\lambda : \mathrm{Fin}\,n \to \mathbb{R}$ has non-negative entries ($\lambda_i \ge 0$)
with $\prod_i \lambda_i = (1 / (n : \mathbb{R}))^n$ and $\sum_i \lambda_i \le 1$, then
$\lambda_i = 1 / (n : \mathbb{R})$ for every $i$ and $\sum_i \lambda_i = 1$. -/
theorem eq_one_div_dim_of_prod_eq_of_sum_le
    (hn_pos : 0 < n) (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (hprod : ∏ i : Fin n, μ i = (1 / (n : ℝ)) ^ n) (hsum : ∑ i : Fin n, μ i ≤ 1) :
    (∀ i : Fin n, μ i = 1 / (n : ℝ)) ∧ ∑ i : Fin n, μ i = 1 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hprod_pos : 0 < ∏ i : Fin n, μ i := by
    rw [hprod]
    positivity
  have hμ_pos : ∀ i : Fin n, 0 < μ i := by
    intro i
    refine lt_of_le_of_ne (hμ i) fun h0 => ?_
    have hprod_zero : ∏ j : Fin n, μ j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) h0.symm
    linarith
  let z : Fin n → ℝ := fun i => (n : ℝ) * μ i
  have hz_pos : ∀ i : Fin n, 0 < z i := fun i => mul_pos hnR (hμ_pos i)
  have hz_prod : ∏ i : Fin n, z i = 1 := by
    dsimp [z]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      hprod, one_div, inv_pow, mul_inv_cancel₀ (pow_ne_zero n hn_ne)]
  have hz_sum : ∑ i : Fin n, z i ≤ n := by
    dsimp [z]
    rw [← Finset.mul_sum]
    nlinarith
  have hz_eq := eq_one_of_prod_eq_one_of_sum_le z hz_pos hz_prod hz_sum
  have hμ_eq : ∀ i : Fin n, μ i = 1 / (n : ℝ) := by
    intro i
    exact eq_one_div_of_mul_eq_one_right (hz_eq i)
  refine ⟨hμ_eq, ?_⟩
  simp [hμ_eq, hn_ne]

/-!
### 2. Spectral AM–GM Equality & Isotropic Covariance Operators
-/

/-- **Spectral AM–GM Rigidity (`eq_one_div_dim_smul_id_of_det_eq`)**:
If a symmetric positive-semidefinite endomorphism $H : E \to_l[\mathbb{R}] E$ on an $n$-dimensional
real inner product space ($n \ge 1$) satisfies $\operatorname{Tr}(H) \le 1$ and
$\det H = (1 / (n : \mathbb{R}))^n$, then:
1. $H = (1 / (n : \mathbb{R})) \bullet \mathrm{LinearMap.id}$,
2. $\operatorname{Tr}(H) = 1$, and
3. $\forall u \in E, \langle u, H u \rangle = (1 / (n : \mathbb{R})) \|u\|^2$. -/
theorem eq_one_div_dim_smul_id_of_det_eq
    {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n)
    (hpos : ∀ u : E, 0 ≤ inner ℝ u (H u))
    (htr : LinearMap.trace ℝ E H ≤ 1)
    (hdet : H.det = (1 / (n : ℝ)) ^ n) :
    H = (1 / (n : ℝ)) • LinearMap.id ∧
    LinearMap.trace ℝ E H = 1 ∧
    (∀ u : E, inner ℝ u (H u) = (1 / (n : ℝ)) * ‖u‖ ^ 2) := by
  have h_prod : ∏ i : Fin n, hH.eigenvalues hn i = (1 / (n : ℝ)) ^ n := by
    have hd := hH.det_eq_prod_eigenvalues hn
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hd
    linarith
  have h_sum : ∑ i : Fin n, hH.eigenvalues hn i ≤ 1 := by
    rwa [← trace_eq_sum_eigenvalues hH hn]
  obtain ⟨heig, hsum_eq⟩ := eq_one_div_dim_of_prod_eq_of_sum_le hn_pos
    (hH.eigenvalues hn) (eigenvalues_nonneg_of_inner_nonneg hH hn hpos) h_prod h_sum
  have hH_eq : H = (1 / (n : ℝ)) • LinearMap.id := by
    apply (hH.eigenvectorBasis hn).toBasis.ext
    intro i
    change H (hH.eigenvectorBasis hn i) = ((1 / (n : ℝ)) • LinearMap.id) (hH.eigenvectorBasis hn i)
    rw [hH.apply_eigenvectorBasis hn i, heig i, LinearMap.smul_apply, LinearMap.id_apply]
    rfl
  refine ⟨hH_eq, ?_, ?_⟩
  · rw [trace_eq_sum_eigenvalues hH hn, hsum_eq]
  · intro u
    rw [hH_eq, LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_right,
      real_inner_self_eq_norm_sq]

/-!
### 3. Bilinear Cauchy–Schwarz Determinant Equality & Scaled Isometries
-/

/-- **Bilinear Cauchy–Schwarz Determinant Equality (`isotropic_and_norm_eq_of_abs_det_eq_div_dim_pow`)**:
Suppose $L, H_1, H_2 : E \to_l[\mathbb{R}] E$ on an $n$-dimensional real inner product space ($n \ge 1$)
satisfy:
- $H_1, H_2$ are symmetric positive-semidefinite with $\operatorname{Tr}(H_1) \le 1$ and $\operatorname{Tr}(H_2) \le 1$,
- $c > 0$ and $|\langle L u, w \rangle| \le c \sqrt{\langle u, H_1 u \rangle} \sqrt{\langle w, H_2 w \rangle}$ for all $u, w \in E$,
- and equality holds in the BCG Jacobian bound: $|\det L| = (c / n)^n$.
Then:
1. $H_1 = (1 / (n : \mathbb{R})) \bullet \mathrm{LinearMap.id}$ and $H_2 = (1 / (n : \mathbb{R})) \bullet \mathrm{LinearMap.id}$,
2. $L^* * L = (c / (n : \mathbb{R}))^2 \bullet \mathrm{LinearMap.id}$, and
3. $\|L u\| = (c / (n : \mathbb{R})) \|u\|$ for every $u \in E$. -/
theorem isotropic_and_norm_eq_of_abs_det_eq_div_dim_pow
    {L H₁ H₂ : E →ₗ[ℝ] E} (hH₁ : H₁.IsSymmetric) (hH₂ : H₂.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n)
    (hpos₁ : ∀ u : E, 0 ≤ inner ℝ u (H₁ u))
    (hpos₂ : ∀ w : E, 0 ≤ inner ℝ w (H₂ w))
    (htr₁ : LinearMap.trace ℝ E H₁ ≤ 1)
    (htr₂ : LinearMap.trace ℝ E H₂ ≤ 1)
    {c : ℝ} (hc : 0 < c)
    (hCS : ∀ u w : E, |inner ℝ (L u) w| ≤
      c * Real.sqrt (inner ℝ u (H₁ u)) * Real.sqrt (inner ℝ w (H₂ w)))
    (hdet_eq : |L.det| = (c / (n : ℝ)) ^ n) :
    H₁ = (1 / (n : ℝ)) • LinearMap.id ∧
    H₂ = (1 / (n : ℝ)) • LinearMap.id ∧
    L.adjoint * L = (c / (n : ℝ)) ^ 2 • LinearMap.id ∧
    (∀ u : E, ‖L u‖ = (c / (n : ℝ)) * ‖u‖) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hd₁_le := det_le_one_div_dim_pow_of_trace_le_one hH₁ hn hn_pos hpos₁ htr₁
  have hd₂_le := det_le_one_div_dim_pow_of_trace_le_one hH₂ hn hn_pos hpos₂ htr₂
  have hd₁_nn := det_nonneg_of_inner_nonneg hH₁ hn hpos₁
  have hd₂_nn := det_nonneg_of_inner_nonneg hH₂ hn hpos₂
  have h_cs_det := abs_det_le_of_abs_inner_le hH₁ hH₂ hn hn_pos hpos₁ hpos₂ hc.le hCS
  have h1n_pos : 0 < (1 / (n : ℝ)) ^ n := by positivity
  have h_sqrt_le₁ : Real.sqrt H₁.det ≤ Real.sqrt ((1 / (n : ℝ)) ^ n) := Real.sqrt_le_sqrt hd₁_le
  have h_sqrt_le₂ : Real.sqrt H₂.det ≤ Real.sqrt ((1 / (n : ℝ)) ^ n) := Real.sqrt_le_sqrt hd₂_le
  have h_prod_sqrt_eq : Real.sqrt H₁.det * Real.sqrt H₂.det = (1 / (n : ℝ)) ^ n := by
    have h_upper : Real.sqrt H₁.det * Real.sqrt H₂.det ≤ (1 / (n : ℝ)) ^ n := by
      calc
        Real.sqrt H₁.det * Real.sqrt H₂.det
          ≤ Real.sqrt ((1 / (n : ℝ)) ^ n) * Real.sqrt ((1 / (n : ℝ)) ^ n) :=
            mul_le_mul h_sqrt_le₁ h_sqrt_le₂ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = (1 / (n : ℝ)) ^ n := Real.mul_self_sqrt h1n_pos.le
    have h_lower : (1 / (n : ℝ)) ^ n ≤ Real.sqrt H₁.det * Real.sqrt H₂.det := by
      have h_eq_pow : (c / (n : ℝ)) ^ n = c ^ n * (1 / (n : ℝ)) ^ n := by
        rw [← mul_pow, mul_one_div]
      rw [hdet_eq, h_eq_pow, mul_assoc] at h_cs_det
      exact le_of_mul_le_mul_left h_cs_det (pow_pos hc n)
    exact le_antisymm h_upper h_lower
  have h_sqrt_pos : 0 < Real.sqrt ((1 / (n : ℝ)) ^ n) := Real.sqrt_pos.mpr h1n_pos
  have h_sqrt_eq₁ : Real.sqrt H₁.det = Real.sqrt ((1 / (n : ℝ)) ^ n) := by
    by_contra hne
    have hlt : Real.sqrt H₁.det < Real.sqrt ((1 / (n : ℝ)) ^ n) := lt_of_le_of_ne h_sqrt_le₁ hne
    have hmul_lt : Real.sqrt H₁.det * Real.sqrt H₂.det < (1 / (n : ℝ)) ^ n := by
      calc
        Real.sqrt H₁.det * Real.sqrt H₂.det
          ≤ Real.sqrt H₁.det * Real.sqrt ((1 / (n : ℝ)) ^ n) :=
            mul_le_mul_of_nonneg_left h_sqrt_le₂ (Real.sqrt_nonneg _)
        _ < Real.sqrt ((1 / (n : ℝ)) ^ n) * Real.sqrt ((1 / (n : ℝ)) ^ n) :=
            mul_lt_mul_of_pos_right hlt h_sqrt_pos
        _ = (1 / (n : ℝ)) ^ n := Real.mul_self_sqrt h1n_pos.le
    linarith
  have h_sqrt_eq₂ : Real.sqrt H₂.det = Real.sqrt ((1 / (n : ℝ)) ^ n) := by
    by_contra hne
    have hlt : Real.sqrt H₂.det < Real.sqrt ((1 / (n : ℝ)) ^ n) := lt_of_le_of_ne h_sqrt_le₂ hne
    have hmul_lt : Real.sqrt H₁.det * Real.sqrt H₂.det < (1 / (n : ℝ)) ^ n := by
      calc
        Real.sqrt H₁.det * Real.sqrt H₂.det
          ≤ Real.sqrt ((1 / (n : ℝ)) ^ n) * Real.sqrt H₂.det :=
            mul_le_mul_of_nonneg_right h_sqrt_le₁ (Real.sqrt_nonneg _)
        _ < Real.sqrt ((1 / (n : ℝ)) ^ n) * Real.sqrt ((1 / (n : ℝ)) ^ n) :=
            mul_lt_mul_of_pos_left hlt h_sqrt_pos
        _ = (1 / (n : ℝ)) ^ n := Real.mul_self_sqrt h1n_pos.le
    linarith
  have hd₁_eq : H₁.det = (1 / (n : ℝ)) ^ n := by
    rw [← Real.mul_self_sqrt hd₁_nn, h_sqrt_eq₁, Real.mul_self_sqrt h1n_pos.le]
  have hd₂_eq : H₂.det = (1 / (n : ℝ)) ^ n := by
    rw [← Real.mul_self_sqrt hd₂_nn, h_sqrt_eq₂, Real.mul_self_sqrt h1n_pos.le]
  obtain ⟨hH₁_id, _, hH₁_quad⟩ := eq_one_div_dim_smul_id_of_det_eq hH₁ hn hn_pos hpos₁ htr₁ hd₁_eq
  obtain ⟨hH₂_id, _, hH₂_quad⟩ := eq_one_div_dim_smul_id_of_det_eq hH₂ hn hn_pos hpos₂ htr₂ hd₂_eq
  have hL_norm_le : ∀ u : E, ‖L u‖ ≤ (c / (n : ℝ)) * ‖u‖ := by
    intro u
    by_cases hLu : ‖L u‖ = 0
    · rw [hLu]; positivity
    · have hLu_pos : 0 < ‖L u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hLu)
      have h_in := hCS u (L u)
      rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _),
        hH₁_quad u, hH₂_quad (L u),
        Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_sq (norm_nonneg u), Real.sqrt_sq (norm_nonneg (L u))] at h_in
      have h_prod_sqrt :
          c * (Real.sqrt (1 / (n : ℝ)) * ‖u‖) * (Real.sqrt (1 / (n : ℝ)) * ‖L u‖) =
          (c / (n : ℝ)) * ‖u‖ * ‖L u‖ := by
        calc
          c * (Real.sqrt (1 / (n : ℝ)) * ‖u‖) * (Real.sqrt (1 / (n : ℝ)) * ‖L u‖)
            = c * (Real.sqrt (1 / (n : ℝ)) * Real.sqrt (1 / (n : ℝ))) * ‖u‖ * ‖L u‖ := by ring
          _ = c * (1 / (n : ℝ)) * ‖u‖ * ‖L u‖ := by
            rw [Real.mul_self_sqrt (by positivity)]
          _ = (c / (n : ℝ)) * ‖u‖ * ‖L u‖ := by ring
      rw [h_prod_sqrt] at h_in
      nlinarith
  -- Now apply spectral AM-GM rigidity to the normalized Gram operator T = (n * (c/n)^2)⁻¹ • (L^* * L)
  let α : ℝ := ((n : ℝ) * (c / (n : ℝ)) ^ 2)⁻¹
  have hα_pos : 0 < α := by positivity
  let T : E →ₗ[ℝ] E := α • (L.adjoint * L)
  have hT_symm : T.IsSymmetric := by
    intro u w
    change inner ℝ (α • ((L.adjoint * L) u)) w = inner ℝ u (α • ((L.adjoint * L) w))
    rw [real_inner_smul_left, real_inner_smul_right,
      (LinearMap.isSymmetric_adjoint_mul_self L) u w]
  have hT_pos : ∀ u : E, 0 ≤ inner ℝ u (T u) := by
    intro u
    change 0 ≤ inner ℝ u (α • ((L.adjoint * L) u))
    rw [real_inner_smul_right]
    exact mul_nonneg hα_pos.le (LinearMap.re_inner_adjoint_mul_self_nonneg L u)
  let v := stdOrthonormalBasis ℝ E
  have h_fin : Fintype.card (Fin (Module.finrank ℝ E)) = n := by rw [Fintype.card_fin, hn]
  have htr_gram : LinearMap.trace ℝ E (L.adjoint * L) ≤ (n : ℝ) * (c / (n : ℝ)) ^ 2 := by
    rw [trace_adjoint_mul_self_eq_sum_norm_sq v L]
    have h_term : ∀ i, ‖L (v i)‖ ^ 2 ≤ (c / (n : ℝ)) ^ 2 := by
      intro i
      have hvi : ‖v i‖ = 1 := v.orthonormal.1 i
      have h1 : ‖L (v i)‖ ≤ c / (n : ℝ) := by simpa [hvi] using hL_norm_le (v i)
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc
      ∑ i, ‖L (v i)‖ ^ 2 ≤ ∑ _i, (c / (n : ℝ)) ^ 2 := Finset.sum_le_sum fun i _ => h_term i
      _ = (n : ℝ) * (c / (n : ℝ)) ^ 2 := by
        simp [hn]
  have hT_tr : LinearMap.trace ℝ E T ≤ 1 := by
    dsimp [T]
    rw [map_smul, smul_eq_mul]
    calc
      α * LinearMap.trace ℝ E (L.adjoint * L)
        ≤ α * ((n : ℝ) * (c / (n : ℝ)) ^ 2) := mul_le_mul_of_nonneg_left htr_gram hα_pos.le
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have hT_det : T.det = (1 / (n : ℝ)) ^ n := by
    dsimp [T]
    rw [LinearMap.det_smul, hn, det_adjoint_mul_self, ← sq_abs, hdet_eq]
    dsimp [α]
    rw [← pow_mul, mul_comm n 2, pow_mul, inv_pow, mul_pow, mul_inv, mul_assoc,
      inv_mul_cancel₀ (by positivity), mul_one, one_div, inv_pow]
  obtain ⟨hT_id, _, hT_quad⟩ :=
    eq_one_div_dim_smul_id_of_det_eq hT_symm hn hn_pos hT_pos hT_tr hT_det
  have hGram_id : L.adjoint * L = (c / (n : ℝ)) ^ 2 • LinearMap.id := by
    have h1 := congr_arg (fun A : E →ₗ[ℝ] E => ((n : ℝ) * (c / (n : ℝ)) ^ 2) • A) hT_id
    dsimp [T, α] at h1
    rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul, smul_smul] at h1
    convert h1 using 2
    field_simp [hn_ne]
  have hL_norm_eq : ∀ u : E, ‖L u‖ = (c / (n : ℝ)) * ‖u‖ := by
    intro u
    have h_sq : ‖L u‖ ^ 2 = ((c / (n : ℝ)) * ‖u‖) ^ 2 := by
      calc
        ‖L u‖ ^ 2 = inner ℝ (L u) (L u) := (real_inner_self_eq_norm_sq (L u)).symm
        _ = inner ℝ u ((L.adjoint * L) u) := by
          rw [Module.End.mul_apply, LinearMap.adjoint_inner_right]
        _ = inner ℝ u (((c / (n : ℝ)) ^ 2 • LinearMap.id) u) := by rw [hGram_id]
        _ = ((c / (n : ℝ)) * ‖u‖) ^ 2 := by
          rw [LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_right,
            real_inner_self_eq_norm_sq, mul_pow]
    have h_sqrt := congr_arg Real.sqrt h_sq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h_sqrt
  exact ⟨hH₁_id, hH₂_id, hGram_id, hL_norm_eq⟩

end BCG.LinearAlgebra

namespace BCG.Rigidity

open BCG.LinearAlgebra BCG.Hyperbolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
### 4. Euclidean Change-of-Variables / Area Formula Bridge
-/

/-- **Euclidean Jacobian Change-of-Variables Volume Formula**
(`measureReal_image_eq_integral_abs_det_fderiv`):
For any measurable set $s \subseteq E$ on which $f : E \to E$ is injective and differentiable with
derivative $f'$, the volume of the image $f(s)$ equals the integral of $|\det f'(x)|$ over $s$. -/
theorem measureReal_image_eq_integral_abs_det_fderiv
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → E} {f' : E → (E →L[ℝ] E)} {s : Set E}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hinj : InjOn f s) :
    μ.real (f '' s) = ∫ x in s, |(f' x).det| ∂μ := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul μ hs hf' hinj (fun _ : E => (1 : ℝ))
  simpa [integral_const, smul_eq_mul, mul_one] using h

/-!
### 5. Measure-Theoretic Almost-Everywhere Equality in BCG
-/

/-- **Measure-Theoretic Equality Case of the BCG Volume Inequality**
(`ae_eq_of_bcg_volume_equality`):
Suppose $(X, \mu_X)$ is a finite-measure space, $J_s : X \to \mathbb{R}$ is integrable and satisfies
$J_s(x) \le (s / h_Y)^n$ almost everywhere ($h_Y > 0$), $\mathrm{degAbs} \cdot \mathrm{volY} \le \int_X J_s \, d\mu_X$,
and equality holds in the fixed-scale BCG inequality:
$$\mathrm{degAbs} \cdot h_Y^n \cdot \mathrm{volY} = s ^ n \cdot (\mu_X\,\mathrm{univ}).\mathrm{toReal}.$$
Then $J_s(x) = (s / h_Y)^n$ for $\mu_X$-almost every $x \in X$. -/
theorem ae_eq_of_bcg_volume_equality
    {X : Type*} [MeasurableSpace X] (μ_X : Measure X) [IsFiniteMeasure μ_X]
    {n : ℕ} {s h_Y degAbs volY : ℝ} (hh_Y : 0 < h_Y)
    {J_s : X → ℝ} (hJ_int : Integrable J_s μ_X)
    (hJ_bound : ∀ᵐ x ∂μ_X, J_s x ≤ (s / h_Y) ^ n)
    (h_deg_area : degAbs * volY ≤ ∫ x, J_s x ∂μ_X)
    (h_eq : degAbs * h_Y ^ n * volY = s ^ n * (μ_X univ).toReal) :
    ∀ᵐ x ∂μ_X, J_s x = (s / h_Y) ^ n := by
  have hh_Y_pow : 0 < h_Y ^ n := pow_pos hh_Y n
  have h_const_int : ∫ _ : X, (s / h_Y) ^ n ∂μ_X = (s / h_Y) ^ n * (μ_X univ).toReal := by
    rw [integral_const, measureReal_def, smul_eq_mul, mul_comm]
  have h_int_le : ∫ x, J_s x ∂μ_X ≤ ∫ _ : X, (s / h_Y) ^ n ∂μ_X :=
    integral_mono_ae hJ_int (integrable_const _) hJ_bound
  have h_int_ge : ∫ _ : X, (s / h_Y) ^ n ∂μ_X ≤ ∫ x, J_s x ∂μ_X := by
    rw [h_const_int, div_pow, div_mul_eq_mul_div, div_le_iff₀ hh_Y_pow]
    calc
      s ^ n * (μ_X univ).toReal = degAbs * h_Y ^ n * volY := h_eq.symm
      _ = (degAbs * volY) * h_Y ^ n := by ring
      _ ≤ (∫ x, J_s x ∂μ_X) * h_Y ^ n := mul_le_mul_of_nonneg_right h_deg_area hh_Y_pow.le
  have h_int_eq : ∫ x, J_s x ∂μ_X = ∫ _ : X, (s / h_Y) ^ n ∂μ_X :=
    le_antisymm h_int_le h_int_ge
  exact (integral_eq_iff_of_ae_le hJ_int (integrable_const _) hJ_bound).mp h_int_eq

/-!
### 6. Pointwise and Almost-Everywhere Rigidity of the Hyperbolic Barycenter Map
-/

/-- **Pointwise Infinitesimal Rigidity of `riemannianBarycenterDifferential`**
(`riemannianBarycenterDifferential_rigidity`):
If at a point $x$, the Riemannian differential `riemannianBarycenterDifferential s w u₁ ξ hw`
($s > 0$) attains the maximal BCG Jacobian determinant
$$\big|\det\big(D^{\mathrm{Riem}}\big)\big| = \left(\frac{s}{n}\right)^n,$$
then:
1. The source Busemann covariance tensor is isotropic:
   `busemannCovariance Finset.univ (barycenterProbWeight w ξ hw) u₁ = (1 / (n : ℝ)) • LinearMap.id`,
2. The target Busemann covariance tensor at $p = \mathrm{hyperboloidBarycenter}(w, \xi, hw)$ is isotropic:
   `busemannCovariance Finset.univ (barycenterProbWeight w ξ hw) (fun i => euclideanBusemannGrad (ξ i) p) = (1 / (n : ℝ)) • LinearMap.id`,
3. $D^{\mathrm{Riem}}$ is a scaled linear isometry with scale factor $s / n$:
   $\forall v \in E, \|D^{\mathrm{Riem}} v\| = (s / n) \|v\|$ (and a linear isometry when $s = n$). -/
theorem riemannianBarycenterDifferential_rigidity
    {n : ℕ} (hn : Module.finrank ℝ E = n) (hn_pos : 0 < n)
    {ι : Type*} [Fintype ι]
    {s : ℝ} (hs : 0 < s)
    {w : ι → ℝ} (hw_nn : ∀ i : ι, 0 ≤ w i)
    {u₁ : ι → E} (hu₁ : ∀ i : ι, ‖u₁ i‖ ≤ 1)
    (ξ : ι → Metric.sphere (0 : E) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i)
    (hdet : |LinearMap.det (riemannianBarycenterDifferential s w u₁ ξ hw)| = (s / (n : ℝ)) ^ n) :
    let p := hyperboloidBarycenter w ξ hw
    let pw := barycenterProbWeight w ξ hw
    let u₂ := fun i : ι => euclideanBusemannGrad (ξ i) p
    let D := riemannianBarycenterDifferential s w u₁ ξ hw
    busemannCovariance Finset.univ pw u₁ = (1 / (n : ℝ)) • LinearMap.id ∧
    busemannCovariance Finset.univ pw u₂ = (1 / (n : ℝ)) • LinearMap.id ∧
    D.adjoint * D = (s / (n : ℝ)) ^ 2 • LinearMap.id ∧
    (∀ v : E, ‖D v‖ = (s / (n : ℝ)) * ‖v‖) := by
  intro p pw u₂ D
  have hD_eq : D = busemannCrossOperator s Finset.univ pw u₁ u₂ :=
    riemannianBarycenterDifferential_eq_busemannCrossOperator s w u₁ ξ hw
  have hpw_nn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ pw i :=
    fun i _ => barycenterProbWeight_nonneg hw_nn ξ hw i
  have hpw_sum : ∑ i ∈ (Finset.univ : Finset ι), pw i ≤ 1 :=
    (sum_barycenterProbWeight_eq_one w ξ hw).le
  have hu₁' : ∀ i ∈ (Finset.univ : Finset ι), ‖u₁ i‖ ≤ 1 := fun i _ => hu₁ i
  have hu₂' : ∀ i ∈ (Finset.univ : Finset ι), ‖u₂ i‖ ≤ 1 :=
    fun i _ => norm_euclideanBusemannGrad_le_one (ξ i) p
  change |D.det| = (s / (n : ℝ)) ^ n at hdet
  rw [hD_eq] at hdet ⊢
  exact isotropic_and_norm_eq_of_abs_det_eq_div_dim_pow
    (isSymmetric_busemannCovariance Finset.univ pw u₁)
    (isSymmetric_busemannCovariance Finset.univ pw u₂)
    hn hn_pos
    (inner_busemannCovariance_nonneg Finset.univ hpw_nn u₁)
    (inner_busemannCovariance_nonneg Finset.univ hpw_nn u₂)
    (trace_busemannCovariance_le_one Finset.univ hpw_nn hpw_sum hu₁')
    (trace_busemannCovariance_le_one Finset.univ hpw_nn hpw_sum hu₂')
    hs
    (abs_inner_busemannCrossOperator_le hs.le Finset.univ hpw_nn u₁ u₂)
    hdet

end BCG.Rigidity
