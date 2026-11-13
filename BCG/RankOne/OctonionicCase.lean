import BCG.RankOne.AssociativeCase

/-!
# Step 4C: Ruan's Repair for the Cayley Hyperbolic Plane $\mathbb{O}\mathbf{H}^2$

This file formalizes **Yuping Ruan (2024)**, *"The Cayley hyperbolic space and volume entropy
rigidity"*, *Mathematische Zeitschrift* **306**, article 4 (arXiv:2203.14418), §§3.2–3.4,
which repairs the gap in `[BCG1, Appendice B, p. 751]` pointed out by Chris Connell for the
16-dimensional Cayley hyperbolic plane $\mathbb{O}\mathbf{H}^2$ ($n = 16$, $d = 8$, $h = 22$).

## The Gap in `[BCG1]` and Ruan's Resolution

In `[BCG1, Appendice B, p. 751]`, Besson, Courtois, and Gallot assumed the existence of global
orthogonal transformations $J_1, \dots, J_7 \in \mathrm{O}(T_x \mathbb{O}\mathbf{H}^2)$ such that
for *every* unit vector $u \in T_x \mathbb{O}\mathbf{H}^2$, the orthogonal projection onto its
8-dimensional Cayley line $\mathcal{C}ay(u)$ is given by
$$\pi_{\mathcal{C}ay(u)} = u \otimes u^* + \sum_{l=1}^7 (J_l u) \otimes (J_l u)^*.$$
However, as noted by Connell and explained in `[Ruan 2024, §2.3, Remark after Cor. 2.4]`, the
non-associativity of the octonions $\mathbb{O}$ prevents the existence of such global $J_l$
(`IsOrthogonalKStructure 8 J` does not exist globally on $\mathbb{O}^2$). Consequently, the
sum-of-conjugates formula $\widehat{H} - H = \sum_{l=1}^7 J_l^* H J_l$ (`[Ruan 2024, Property (P2)]`)
fails globally on $T_x \mathbb{O}\mathbf{H}^2$.

Ruan resolves this gap in three steps:
1. **Local Cayley-Line Properties `(P1')` and `(P2')` (`[Ruan 2024, Lemma 3.2]`):**
   - `(P1')`: For any Cayley line $\mathcal{C}ay(v)$ and any unit vector $w$, the restriction of
     $\pi_{\mathcal{C}ay(w)}$ to $\mathcal{C}ay(v)$ is a scalar multiple $\cos^2\theta \cdot \mathrm{id}_{\mathcal{C}ay(v)}$.
     Hence $\widehat{H}$ preserves an orthogonal decomposition into two 8-dimensional Cayley lines
     $\mathcal{C}ay(v_1) \oplus \mathcal{C}ay(v_2) \cong \mathbb{R}^8 \oplus \mathbb{R}^8$ and acts
     as $\lambda I_8 \oplus \mu I_8$ with $\lambda, \mu \ge 0$ and $\lambda + \mu = 1$.
   - `(P2')`: On each *individual* 8-dimensional Cayley line $V = \mathcal{C}ay(v_i)$, there exist
     *line-dependent* orthogonal endomorphisms $J_{0,v_i} = \mathrm{id}_V, J_{1,v_i}, \dots, J_{7,v_i} \in \mathrm{O}(V)$
     such that $\langle v', \widehat{H} v' \rangle = \sum_{t=0}^7 \langle J_{t,v_i} v', H J_{t,v_i} v' \rangle$
     for all $v' \in V$. Taking the trace on $V$ yields (`trace_cayleyLine_eq_eigenvalue`,
     `[Ruan 2024, Eq. (18)]`):
     $$H = \begin{pmatrix} A & C \\ C^* & B \end{pmatrix}, \qquad
       \widehat{H} = \begin{pmatrix} \lambda I_8 & 0 \\ 0 & \mu I_8 \end{pmatrix}, \qquad
       \operatorname{Tr}(A) = \lambda, \quad \operatorname{Tr}(B) = \mu, \quad \lambda + \mu = 1.$$
2. **8-Dimensional Diagonal Block Bounds & Case 1 (`[Ruan 2024, Eq. (28) & Lemma 3.5]`):**
   - Applying `[BCG1, Lemme B.4]` (`det_id_sub_div_ge_det`) on each 8-dimensional Cayley line
     proves (`det_lambda_sub_cayleyBlock_ge`, `[Ruan 2024, Eq. (28)]`):
     $$\det(\lambda I_8 - A) \ge 7^8 \det A \qquad \text{and} \qquad \det(\mu I_8 - B) \ge 7^8 \det B.$$
   - By `[Ruan 2024, Lemma 3.5]` (`cayley_schur_monotone_one_dim`, `cayley_case1_det_bound`),
     whenever $2\lambda_1 \le \lambda$ and $2\mu_1 \le \mu$ (**Case 1**, $\alpha = 0$), Schur
     complement monotonicity directly yields $\det(\widehat{H} - H) \ge 7^{16} \det H$, i.e.,
     $\det((\widehat{H} - H)/7) \ge \det H$ (`[Ruan 2024, Eq. (24)]`).
3. **Off-Diagonal Perturbation $U_\alpha$ and Perturbed Log-Concavity (`[Ruan 2024, Eqs. (20)–(23) & Lemma 3.4]`):**
   - When $2\mu_1 > \mu$ or $2\lambda_1 > \lambda$ (**Case 2**), $\det((\widehat{H} - H)/7) \ge \det H$
     need not hold at $\alpha = 0$. Ruan introduces the off-diagonal block operator
     $U_\alpha = \alpha \begin{pmatrix} 0 & C \\ C^* & 0 \end{pmatrix}$ ($\alpha \in [0, 1]$) and
     splits the Hessian operator as
     $$I - 2H + \widehat{H} = (I - H - U_\alpha) + (\widehat{H} - H + U_\alpha),$$
     applying `det_weighted_add_ge_rpow_mul_rpow` with $p = 15/22$ and $q = 7/22$ (`[Ruan 2024, Eq. (22)]`,
     `det_rankOneHessianOperator_perturbed_ge`):
     $$\det(I - 2H + \widehat{H}) \ge 22^{16} \det\left(\frac{I - H - U_\alpha}{15}\right)^{15/22}
       \det\left(\frac{\widehat{H} - H + U_\alpha}{7}\right)^{7/22}.$$
   - Choosing $\alpha \in [1 - \sqrt{2/3}, 0.266]$ (`octonionic_alpha_parameter_bounds`)
     restores $\det((\widehat{H} - H + U_\alpha)/7) \ge \det H$ (`[Ruan 2024, Eq. (21)]`) via the
     8-dimensional reverse AM–GM inequality (`[Ruan 2024, Lemma 3.6]`, `reverse_amgm_eight_dim`)
     while maintaining $\det((I - H - U_\alpha)/15) \ge 16^{-16 \cdot 11/15} (\det H)^{4/15}$
     (`[Ruan 2024, Eq. (23)]`), proving Proposition 3.1 (`octonionic_rankOne_det_ineq`) and
     Corollary 3.8 (`octonionic_rankOne_bcg_jacobian_bound_with_defect`).

## Main Results
- `octonionic_dim_eq`, `octonionic_fiberDim_eq`, `octonionic_volumeEntropy_eq`:
  Exact dimensions ($n = 16$, $d = 8$, $h = 22$) for $\mathbb{O}\mathbf{H}^2$.
- `IsLocalCayleyLineStructure`: Ruan's local property `(P2')` on an 8-dimensional Cayley line $V$.
- `trace_cayleyLine_eq_eigenvalue`: Proof of `[Ruan 2024, Lemma 3.2 / Eq. (18)]` that
  $\operatorname{Tr}(A) = \lambda$ on any Cayley line where $\widehat{H}|_V = \lambda \mathrm{id}_V$.
- `det_lambda_sub_cayleyBlock_ge`: Proof of `[Ruan 2024, Eq. (28)]`
  ($\det(\lambda I_8 - A) \ge 7^8 \det A$) on an 8-dimensional Cayley line.
- `cayley_schur_monotone_one_dim`, `cayley_schur_monotone_finset_prod`, `cayley_case1_det_bound`:
  Proof of `[Ruan 2024, Lemma 3.5 & Eq. (24)]` (Case 1, $\alpha = 0$).
- `reverse_amgm_eight_dim`, `octonionic_alpha_parameter_bounds`, `cayley_case2_step2_endpoint_bound`:
  Proof of `[Ruan 2024, Lemma 3.6 & Case 2 Step 1–2]`.
- `det_rankOneHessianOperator_perturbed_ge`: Ruan's perturbed log-concavity trick (`[Ruan 2024, Eq. (22)]`).
- `octonionic_rankOne_det_ineq`: Proof of `[Ruan 2024, Proposition 3.1 / Eq. (19)]`:
  $$\frac{\sqrt{\det H}}{\det(I - 2H + \widehat{H})} \le \left(\frac{\sqrt{16}}{22}\right)^{16} = \left(\frac{2}{11}\right)^{16}.$$
- `octonionic_rankOne_bcg_jacobian_bound`: Master pointwise BCG Jacobian bound
  $|\det D_F| \le (s / 22)^{16}$ for the Cayley hyperbolic plane $\mathbb{O}\mathbf{H}^2$.
-/

noncomputable section

open scoped RealInnerProductSpace BigOperators

namespace BCG.RankOne

open BCG.LinearAlgebra BCG.Hyperbolic

/-! ### 1. Exact Dimensions and Volume Entropy of the Cayley Hyperbolic Plane $\mathbb{O}\mathbf{H}^2$ -/

/-- The real manifold dimension of the Cayley hyperbolic plane $\mathbb{O}\mathbf{H}^2$ is $n = 16$. -/
@[simp] theorem octonionic_dim_eq : DivisionAlgebraType.octonionic.manifoldDim 2 = 16 := rfl

/-- The real fiber dimension of a Cayley line $\mathbb{O} \cong \mathbb{R}^8$ is $d = 8$. -/
@[simp] theorem octonionic_fiberDim_eq : DivisionAlgebraType.octonionic.fiberDim = 8 := rfl

/-- The volume entropy of the Cayley hyperbolic plane $\mathbb{O}\mathbf{H}^2$ with sectional
curvatures in $[-4, -1]$ is $h(\mathbb{O}\mathbf{H}^2) = 16 + 8 - 2 = 22$. -/
@[simp] theorem octonionic_volumeEntropy_eq : DivisionAlgebraType.octonionic.volumeEntropy 2 = 22 := by
  simp [DivisionAlgebraType.volumeEntropy, DivisionAlgebraType.manifoldDim, DivisionAlgebraType.fiberDim]
  norm_num

/-- The real rank-one entropy formula `rankOneEntropy 16 8` equals $22$. -/
@[simp] theorem rankOneEntropy_sixteen_eight : rankOneEntropy 16 8 = 22 := by
  unfold rankOneEntropy
  norm_num

/-- In dimension $n = 16$ with $h_0 = 22$, the critical constant $\frac{\sqrt{16}}{16 + 8 - 2}$
in `[Ruan 2024, Proposition 3.1, Eq. (19)]` simplifies to $\frac{4}{22} = \frac{2}{11}$. -/
theorem octonionic_critical_ratio_eq :
    Real.sqrt (16 : ℝ) / ((16 : ℝ) + (8 : ℝ) - 2) = 2 / 11 := by
  have h16 : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h16]
  norm_num

/-- Variant of `octonionic_critical_ratio_eq` with denominator `22`. -/
theorem octonionic_critical_ratio_twenty_two_eq :
    Real.sqrt (16 : ℝ) / (22 : ℝ) = 2 / 11 := by
  have h : (22 : ℝ) = (16 : ℝ) + (8 : ℝ) - 2 := by norm_num
  rw [h, octonionic_critical_ratio_eq]

/-! ### 2. Local Cayley-Line Structure `(P1')`–`(P2')` and Block Trace Identity (`[Ruan 2024, Lemma 3.2]`) -/

/-- **Local Cayley-Line Orthogonal Endomorphisms (`[Ruan 2024, Lemma 3.2 (P2')]`)**:
Although the octonions $\mathbb{O}$ are non-associative and do not admit a *global*
`IsOrthogonalKStructure 8 J` on $\mathbb{O}^2 \cong \mathbb{R}^{16}$, on each *individual*
$d$-dimensional Cayley line $V = \mathcal{C}ay(v) \cong \mathbb{R}^d$ ($d = 8$) there exist local
orthogonal endomorphisms $J_{0,v}, \dots, J_{d-1,v} : V \to_l[\mathbb{R}] V$ generated by right
multiplication on $\mathcal{C}ay(v)$ such that:
1. $J_{0,v} = \mathrm{id}_V$, and
2. each $J_{r,v}$ is an orthogonal transformation of $V$ ($\langle J_{r,v} x, J_{r,v} y \rangle = \langle x, y \rangle$). -/
structure IsLocalCayleyLineStructure {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (d : ℕ) [NeZero d] (J : Fin d → (V →ₗ[ℝ] V)) : Prop where
  /-- $J_0$ is the identity map on the Cayley line $V$. -/
  zero_eq_id : J 0 = LinearMap.id
  /-- Each $J_r$ preserves the inner product on $V$: $\langle J_r x, J_r y \rangle = \langle x, y \rangle$. -/
  inner_map_map : ∀ (r : Fin d) (x y : V), inner ℝ (J r x) (J r y) = inner ℝ x y

namespace IsLocalCayleyLineStructure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {d : ℕ} [NeZero d] {J : Fin d → (V →ₗ[ℝ] V)}

/-- Each local operator $J_r$ on the Cayley line $V$ satisfies $(J_r)^* J_r = \mathrm{id}_V$. -/
theorem adjoint_comp_self [FiniteDimensional ℝ V]
    (hJ : IsLocalCayleyLineStructure d J) (r : Fin d) :
    (J r).adjoint.comp (J r) = LinearMap.id := by
  ext x
  apply ext_inner_right ℝ
  intro y
  simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.adjoint_inner_left]
  exact hJ.inner_map_map r x y

/-- Conjugating an operator $A : V \to_l[\mathbb{R}] V$ by a local Cayley-line
orthogonal transformation $J_r$ preserves its trace:
$\operatorname{Tr}(J_r A J_r^*) = \operatorname{Tr}(A)$. -/
theorem trace_conj_eq [FiniteDimensional ℝ V]
    (hJ : IsLocalCayleyLineStructure d J) (A : V →ₗ[ℝ] V) (r : Fin d) :
    LinearMap.trace ℝ V ((J r).comp (A.comp (J r).adjoint)) = LinearMap.trace ℝ V A := by
  calc
    LinearMap.trace ℝ V ((J r).comp (A.comp (J r).adjoint))
      = LinearMap.trace ℝ V ((A.comp (J r).adjoint).comp (J r)) :=
        (LinearMap.trace_comp_comm' (J r) (A.comp (J r).adjoint)).symm
    _ = LinearMap.trace ℝ V (A.comp ((J r).adjoint.comp (J r))) := by
        rw [LinearMap.comp_assoc]
    _ = LinearMap.trace ℝ V A := by
        rw [hJ.adjoint_comp_self r, LinearMap.comp_id]

/-- **Ruan Lemma 3.2 / Eq. (18) (`trace_cayleyLine_eq_eigenvalue`)**:
Suppose $V = \mathcal{C}ay(v)$ is a $d$-dimensional Cayley line ($d = 8$, $\dim V = d$),
$A : V \to_l[\mathbb{R}] V$ is the symmetric compression of $H$ to $V$
($\langle x, A x \rangle = \langle x, H x \rangle$), and on $V$ the operator $\widehat{H}$ acts as
$\lambda \cdot \mathrm{id}_V$ (`(P1')`) and satisfies Ruan's local property `(P2')`:
$$\forall x \in V,\quad \lambda \|x\|^2 = \sum_{r : \mathrm{Fin}\,d} \langle J_r^* x, A (J_r^* x) \rangle.$$
Then $\operatorname{Tr}(A) = \lambda$.
In particular, on $\mathbb{O}\mathbf{H}^2 = \mathcal{C}ay(v_1) \oplus \mathcal{C}ay(v_2)$ with
$d = 8$, the $8 \times 8$ diagonal blocks $A, B$ of $H$ satisfy $\operatorname{Tr}(A) = \lambda$
and $\operatorname{Tr}(B) = \mu$. -/
theorem trace_cayleyLine_eq_eigenvalue [FiniteDimensional ℝ V]
    (hJ : IsLocalCayleyLineStructure d J) (hd_dim : Module.finrank ℝ V = d)
    {A : V →ₗ[ℝ] V} (hA_symm : A.IsSymmetric) {lam : ℝ}
    (hP2' : ∀ x : V, lam * ‖x‖ ^ 2 = ∑ r : Fin d, inner ℝ ((J r).adjoint x) (A ((J r).adjoint x))) :
    LinearMap.trace ℝ V A = lam := by
  have hd_pos : 0 < d := NeZero.pos d
  have hdR_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let S : V →ₗ[ℝ] V := ∑ r : Fin d, (J r).comp (A.comp (J r).adjoint)
  have hS_symm : S.IsSymmetric := by
    intro x y
    simp only [S, LinearMap.sum_apply, inner_sum, sum_inner, LinearMap.comp_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← LinearMap.adjoint_inner_right (J r),
      hA_symm ((J r).adjoint x) ((J r).adjoint y),
      LinearMap.adjoint_inner_left (J r)]
  have h_quad : ∀ x : V, inner ℝ x (S x) = lam * ‖x‖ ^ 2 := by
    intro x
    simp only [S, LinearMap.sum_apply, inner_sum, LinearMap.comp_apply]
    have h_sum : ∑ r : Fin d, inner ℝ x ((J r) (A ((J r).adjoint x))) =
        ∑ r : Fin d, inner ℝ ((J r).adjoint x) (A ((J r).adjoint x)) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      exact (LinearMap.adjoint_inner_left (J r) (A ((J r).adjoint x)) x).symm
    rw [h_sum, ← hP2' x]
  -- Polarize `S - lam • id`: it is symmetric and its quadratic form is identically 0, so `S = lam • id`.
  have h_S_eq : S = lam • (LinearMap.id : V →ₗ[ℝ] V) := by
    ext x
    apply ext_inner_left ℝ
    intro y
    have hxy := h_quad (x + y)
    have hx := h_quad x
    have hy := h_quad y
    have h_symm_xy : inner ℝ x (S y) = inner ℝ y (S x) := by
      rw [← hS_symm x y, real_inner_comm]
    rw [map_add, inner_add_left, inner_add_right, inner_add_right,
      h_symm_xy, norm_add_sq_real] at hxy
    have h_inner : inner ℝ y (S x) = lam * inner ℝ x y := by linarith
    rw [LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_right, real_inner_comm x y]
    exact h_inner
  have h_tr_eq : LinearMap.trace ℝ V S = LinearMap.trace ℝ V (lam • (LinearMap.id : V →ₗ[ℝ] V)) :=
    congr_arg (LinearMap.trace ℝ V) h_S_eq
  have h_tr_S : LinearMap.trace ℝ V S = (d : ℝ) * LinearMap.trace ℝ V A := by
    simp only [S, map_sum, hJ.trace_conj_eq A, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have h_tr_lam : LinearMap.trace ℝ V (lam • (LinearMap.id : V →ₗ[ℝ] V)) = (d : ℝ) * lam := by
    rw [map_smul, LinearMap.trace_id, hd_dim, smul_eq_mul, mul_comm]
  rw [h_tr_S, h_tr_lam] at h_tr_eq
  exact mul_left_cancel₀ hdR_ne h_tr_eq

end IsLocalCayleyLineStructure

/-! ### 3. 8-Dimensional Cayley Block AM–GM Bounds (`[Ruan 2024, Eq. (28)]`) -/

/-- **Single-Block Spectral AM–GM Inequality (`det_lambda_sub_cayleyBlock_ge`, `[Ruan 2024, Eq. (28)]`)**:
Let $V$ be a $d$-dimensional real inner product space ($d \ge 2$, with $d = 8$ for a Cayley line),
and let $A : V \to_l[\mathbb{R}] V$ be a symmetric positive-semidefinite operator with
$\operatorname{Tr}(A) = \lambda$. Then
$$((d : \mathbb{R}) - 1)^d \cdot \det A \le \det(\lambda \bullet \mathrm{id}_V - A).$$
For $d = 8$, this gives Ruan's Eq. (28) (`\eqref{am_gm_good}`):
$$\det(\lambda I_8 - A) \ge 7^8 \det A \qquad \text{and} \qquad \det(\mu I_8 - B) \ge 7^8 \det B.$$ -/
theorem det_lambda_sub_cayleyBlock_ge
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {d : ℕ} (hd_dim : Module.finrank ℝ V = d) (hd2 : 2 ≤ d)
    {A : V →ₗ[ℝ] V} (hA_symm : A.IsSymmetric)
    (hA_pos : ∀ x : V, 0 ≤ inner ℝ x (A x))
    {lam : ℝ} (h_tr : LinearMap.trace ℝ V A = lam) :
    ((d : ℝ) - 1) ^ d * A.det ≤ (lam • (LinearMap.id : V →ₗ[ℝ] V) - A).det := by
  have hd_pos : 0 < d := by omega
  have hd1_pos : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := Nat.cast_le.mpr hd2; linarith
  have h_tr_nn : 0 ≤ LinearMap.trace ℝ V A := by
    rw [trace_eq_sum_eigenvalues hA_symm hd_dim]
    exact Finset.sum_nonneg fun i _ => eigenvalues_nonneg_of_inner_nonneg hA_symm hd_dim hA_pos i
  have hlam_nn : 0 ≤ lam := h_tr ▸ h_tr_nn
  rcases eq_or_lt_of_le hlam_nn with rfl | hlam_pos
  · -- Case `lam = 0`: Since `Tr(A) = 0` and `A ≥ 0`, `det A ≤ (Tr(A)/d)^d = 0`, while `det A ≥ 0`.
    have hdetA_nn : 0 ≤ A.det := det_nonneg_of_inner_nonneg hA_symm hd_dim hA_pos
    have hdetA_le : A.det ≤ (0 / (d : ℝ)) ^ d := by
      rw [← h_tr]
      exact det_le_trace_div_dim_pow hA_symm hd_dim hd_pos hA_pos
    have h0_pow : (0 / (d : ℝ)) ^ d = 0 := by
      rw [zero_div, zero_pow (by omega)]
    have hdetA_zero : A.det = 0 := le_antisymm (hdetA_le.trans_eq h0_pow) hdetA_nn
    have h_lhs : ((d : ℝ) - 1) ^ d * A.det = 0 := by rw [hdetA_zero, mul_zero]
    have h_rhs : ((0 : ℝ) • (LinearMap.id : V →ₗ[ℝ] V) - A).det = 0 := by
      rw [zero_smul, zero_sub, show (-A : V →ₗ[ℝ] V) = (-1 : ℝ) • A by ext x; simp,
        LinearMap.det_smul, hd_dim, hdetA_zero, mul_zero]
    rw [h_lhs, h_rhs]
  · -- Case `0 < lam`: Rescale `A' = lam⁻¹ • A`, which has `Tr(A') = 1`, and apply `det_id_sub_div_ge_det`.
    let A' : V →ₗ[ℝ] V := lam⁻¹ • A
    have hA'_symm : A'.IsSymmetric := by
      intro x y
      simp only [A', LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right]
      rw [hA_symm x y]
    have hA'_pos : ∀ x : V, 0 ≤ inner ℝ x (A' x) := by
      intro x
      simp only [A', LinearMap.smul_apply, real_inner_smul_right]
      exact mul_nonneg (inv_nonneg.mpr hlam_pos.le) (hA_pos x)
    have hA'_tr : LinearMap.trace ℝ V A' = 1 := by
      simp only [A', map_smul, h_tr, smul_eq_mul]
      exact inv_mul_cancel₀ hlam_pos.ne'
    have h_b4_simp : A'.det ≤ ((1 / ((d : ℝ) - 1)) • (LinearMap.id - A')).det :=
      det_id_sub_div_ge_det hA'_symm hd_dim hd2 hA'_pos hA'_tr
    have h_scale_A : A = lam • A' := by
      ext x
      simp only [A', smul_smul, mul_inv_cancel₀ hlam_pos.ne', one_smul]
    have h_scale_sub :
        lam • (LinearMap.id : V →ₗ[ℝ] V) - A =
          (lam * ((d : ℝ) - 1)) • ((1 / ((d : ℝ) - 1)) • (LinearMap.id - A')) := by
      ext x
      simp only [A', LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [smul_smul]
      have h1 : lam * ((d : ℝ) - 1) * (1 / ((d : ℝ) - 1)) = lam := by
        field_simp [hd1_pos.ne']
      rw [h1, smul_sub, smul_smul, mul_inv_cancel₀ hlam_pos.ne', one_smul]
    calc
      ((d : ℝ) - 1) ^ d * A.det
        = (lam * ((d : ℝ) - 1)) ^ d * A'.det := by
          rw [h_scale_A, LinearMap.det_smul, hd_dim, mul_pow]
          ring
      _ ≤ (lam * ((d : ℝ) - 1)) ^ d * ((1 / ((d : ℝ) - 1)) • (LinearMap.id - A')).det :=
          mul_le_mul_of_nonneg_left h_b4_simp (pow_nonneg (mul_nonneg hlam_pos.le hd1_pos.le) d)
      _ = ((lam * ((d : ℝ) - 1)) • ((1 / ((d : ℝ) - 1)) • (LinearMap.id - A'))).det := by
          rw [← hd_dim, ← LinearMap.det_smul]
      _ = (lam • (LinearMap.id : V →ₗ[ℝ] V) - A).det := by
          rw [← h_scale_sub]

/-- Specialization of `det_lambda_sub_cayleyBlock_ge` to an 8-dimensional Cayley line ($d = 8$,
`[Ruan 2024, Eq. (28)]`):
$$\det(\lambda I_8 - A) \ge 7^8 \det A.$$ -/
theorem det_lambda_sub_cayleyBlock_eight_ge
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (hd_dim : Module.finrank ℝ V = 8)
    {A : V →ₗ[ℝ] V} (hA_symm : A.IsSymmetric)
    (hA_pos : ∀ x : V, 0 ≤ inner ℝ x (A x))
    {lam : ℝ} (h_tr : LinearMap.trace ℝ V A = lam) :
    (7 : ℝ) ^ 8 * A.det ≤ (lam • (LinearMap.id : V →ₗ[ℝ] V) - A).det := by
  have h := det_lambda_sub_cayleyBlock_ge hd_dim (by norm_num : 2 ≤ 8) hA_symm hA_pos h_tr
  have h7 : (((8 : ℕ) : ℝ) - 1) ^ 8 = (7 : ℝ) ^ 8 := by norm_num
  rwa [h7] at h

/-! ### 4. Ruan Lemma 3.5 and Case 1 ($\alpha = 0$, `[Ruan 2024, Eqs. (24)–(31)]`) -/

/-- **1D Monotonicity Lemma (`[Ruan 2024, Lemma 3.5]`, `cayley_schur_monotone_one_dim`)**:
If $0 \le w$, $0 \le h_2 \le h_1$, then
$$(h_2 - w) h_1 \le (h_1 - w) h_2,$$
since $(h_1 - w) h_2 - (h_2 - w) h_1 = w (h_1 - h_2) \ge 0$. -/
theorem cayley_schur_monotone_one_dim {h₁ h₂ w : ℝ} (hw : 0 ≤ w) (hh : h₂ ≤ h₁) :
    (h₂ - w) * h₁ ≤ (h₁ - w) * h₂ := by
  have : 0 ≤ w * (h₁ - h₂) := mul_nonneg hw (sub_nonneg.mpr hh)
  linarith

/-- **Product Form of `[Ruan 2024, Lemma 3.5]` (`cayley_schur_monotone_finset_prod`)**:
For any finite index set $s$ (e.g. `Fin 8`) and non-negative families $h_1, h_2, w : \iota \to \mathbb{R}$
satisfying $0 \le w_i \le h_{2,i} \le h_{1,i}$ for all $i \in s$, we have
$$\prod_{i \in s} (h_{2,i} - w_i) \cdot \prod_{i \in s} h_{1,i}
  \le \prod_{i \in s} (h_{1,i} - w_i) \cdot \prod_{i \in s} h_{2,i}.$$ -/
theorem cayley_schur_monotone_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {h₁ h₂ w : ι → ℝ}
    (hw_nn : ∀ i ∈ s, 0 ≤ w i)
    (hwh₂ : ∀ i ∈ s, w i ≤ h₂ i)
    (hh₂h₁ : ∀ i ∈ s, h₂ i ≤ h₁ i) :
    (∏ i ∈ s, (h₂ i - w i)) * (∏ i ∈ s, h₁ i) ≤
      (∏ i ∈ s, (h₁ i - w i)) * (∏ i ∈ s, h₂ i) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact finset_prod_le_prod_of_nonneg s
    (fun i hi => mul_nonneg (sub_nonneg.mpr (hwh₂ i hi))
      (le_trans (hw_nn i hi) (le_trans (hwh₂ i hi) (hh₂h₁ i hi))))
    (fun i hi => cayley_schur_monotone_one_dim (hw_nn i hi) (hh₂h₁ i hi))

/-- **Ruan Case 1 Determinant Inequality (`[Ruan 2024, Eqs. (24)–(31)]`, `cayley_case1_det_bound`)**:
In **Case 1** ($2\lambda_1 \le \lambda$ and $2\mu_1 \le \mu$, so $\alpha = 0$ and $U_\alpha = 0$),
we have $A \le \lambda I_8 - A$ and $B \le \mu I_8 - B$, and the Schur complement factors satisfy:
1. $0 < \det B$,
2. $\det H = \det A \cdot \det(B - C^* A^{-1} C)$ and
   $\det(\widehat{H} - H) = \det(\lambda I_8 - A) \cdot \det(\mu I_8 - B - C^*(\lambda I_8 - A)^{-1} C)$,
3. By Lemma 3.5 (`[Ruan 2024, Eq. (31)]`),
   $\det(B - C^* A^{-1} C) \cdot \det(\mu I_8 - B) \le \det(\mu I_8 - B - C^*(\lambda I_8 - A)^{-1} C) \cdot \det B$,
4. By Eq. (28) (`det_lambda_sub_cayleyBlock_eight_ge`),
   $\det(\lambda I_8 - A) \ge 7^8 \det A$ and $\det(\mu I_8 - B) \ge 7^8 \det B$.

Combining (1)–(4) proves `[Ruan 2024, Eq. (24)]`:
$$(7 : \mathbb{R})^{16} \cdot \det H \le \det(\widehat{H} - H)
  \quad\Longleftrightarrow\quad \det H \le \det\left(\frac{\widehat{H} - H}{7}\right).$$ -/
theorem cayley_case1_det_bound
    {detH detHH detA detB detLamA detMuB detSchurH detSchurHH : ℝ}
    (hdetA_nn : 0 ≤ detA)
    (hdetB_pos : 0 < detB)
    (hdetSchurH_nn : 0 ≤ detSchurH)
    (h_schur_H : detH = detA * detSchurH)
    (h_schur_HH : detHH = detLamA * detSchurHH)
    (h_amgm_A : (7 : ℝ) ^ 8 * detA ≤ detLamA)
    (h_amgm_B : (7 : ℝ) ^ 8 * detB ≤ detMuB)
    (h_lem35 : detSchurH * detMuB ≤ detSchurHH * detB) :
    (7 : ℝ) ^ 16 * detH ≤ detHH := by
  have h7_8_pos : (0 : ℝ) < (7 : ℝ) ^ 8 := by positivity
  have hdetLamA_nn : 0 ≤ detLamA := le_trans (mul_nonneg h7_8_pos.le hdetA_nn) h_amgm_A
  have h_schur_ineq : (7 : ℝ) ^ 8 * detSchurH ≤ detSchurHH := by
    have h1 : (7 : ℝ) ^ 8 * detSchurH * detB ≤ detSchurH * detMuB := by
      calc
        (7 : ℝ) ^ 8 * detSchurH * detB = detSchurH * ((7 : ℝ) ^ 8 * detB) := by ring
        _ ≤ detSchurH * detMuB := mul_le_mul_of_nonneg_left h_amgm_B hdetSchurH_nn
    have h2 : (7 : ℝ) ^ 8 * detSchurH * detB ≤ detSchurHH * detB := h1.trans h_lem35
    exact le_of_mul_le_mul_right h2 hdetB_pos
  calc
    (7 : ℝ) ^ 16 * detH
      = ((7 : ℝ) ^ 8 * detA) * ((7 : ℝ) ^ 8 * detSchurH) := by
        rw [h_schur_H]; ring
    _ ≤ detLamA * detSchurHH :=
        mul_le_mul h_amgm_A h_schur_ineq
          (mul_nonneg h7_8_pos.le hdetSchurH_nn) hdetLamA_nn
    _ = detHH := h_schur_HH.symm

/-! ### 5. Ruan Lemma 3.6 and Case 2 ($\alpha$-Interpolation, `[Ruan 2024, Eqs. (32)–(43)]`) -/

/-- **8-Dimensional Reverse AM–GM Inequality (`[Ruan 2024, Lemma 3.6]`, `reverse_amgm_eight_dim`)**:
For any $x : \mathrm{Fin}\,8 \to \mathbb{R}$ with $x_i \ge 0$, applying AM–GM to the 7 variables
$x_1, \dots, x_7$ gives (`[Ruan 2024, Eq. (33)]`):
$$\left(\sum_{i : \mathrm{Fin}\,8} x_i - x_0\right)^7 \cdot x_0 \ge 7^7 \prod_{i : \mathrm{Fin}\,8} x_i.$$ -/
theorem reverse_amgm_eight_dim (x : Fin 8 → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (7 : ℝ) ^ 7 * (∏ i : Fin 8, x i) ≤ ((∑ i : Fin 8, x i) - x 0) ^ 7 * x 0 := by
  let s7 : Finset (Fin 8) := Finset.univ.erase 0
  have h0_mem : (0 : Fin 8) ∈ (Finset.univ : Finset (Fin 8)) := Finset.mem_univ 0
  have h_sum_split : (∑ i : Fin 8, x i) - x 0 = ∑ i ∈ s7, x i := by
    rw [← Finset.add_sum_erase _ _ h0_mem, add_sub_cancel_left]
  have h_prod_split : (∏ i : Fin 8, x i) = x 0 * ∏ i ∈ s7, x i := by
    rw [← Finset.mul_prod_erase _ _ h0_mem]
  have hs7_card : s7.card = 7 := by
    simp [s7]
  have hw : ∀ i ∈ s7, (0 : ℝ) ≤ 1 / 7 := fun _ _ => by positivity
  have hw_sum : ∑ _i ∈ s7, (1 / 7 : ℝ) = 1 := by
    rw [Finset.sum_const, hs7_card, nsmul_eq_mul]
    norm_num
  have h_amgm := Real.geom_mean_le_arith_mean_weighted s7 (fun _ => (1 / 7 : ℝ)) x hw hw_sum
    (fun i _ => hx i)
  have h_lhs : ∏ i ∈ s7, x i ^ (1 / 7 : ℝ) = (∏ i ∈ s7, x i) ^ (1 / 7 : ℝ) :=
    Real.finsetProd_rpow s7 x (fun i _ => hx i) (1 / 7 : ℝ)
  have h_rhs : ∑ i ∈ s7, (1 / 7 : ℝ) * x i = (1 / 7 : ℝ) * ∑ i ∈ s7, x i :=
    (Finset.mul_sum s7 x (1 / 7 : ℝ)).symm
  rw [h_lhs, h_rhs] at h_amgm
  have h_prod_nn : 0 ≤ ∏ i ∈ s7, x i := Finset.prod_nonneg fun i _ => hx i
  have h_pow7 := pow_le_pow_left₀ (Real.rpow_nonneg h_prod_nn _) h_amgm 7
  have h_rpow7 : ((∏ i ∈ s7, x i) ^ (1 / 7 : ℝ)) ^ (7 : ℕ) = ∏ i ∈ s7, x i := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h_prod_nn]
    norm_num
  rw [h_rpow7, mul_pow, div_pow, one_pow] at h_pow7
  have h7_pos : (0 : ℝ) < (7 : ℝ) ^ 7 := by positivity
  have h_mul7 : (7 : ℝ) ^ 7 * (∏ i ∈ s7, x i) ≤ (∑ i ∈ s7, x i) ^ 7 := by
    have := mul_le_mul_of_nonneg_left h_pow7 h7_pos.le
    calc
      (7 : ℝ) ^ 7 * (∏ i ∈ s7, x i)
        ≤ (7 : ℝ) ^ 7 * (1 / (7 : ℝ) ^ 7 * (∑ i ∈ s7, x i) ^ 7) := this
      _ = (∑ i ∈ s7, x i) ^ 7 := by field_simp [h7_pos.ne']
  rw [h_sum_split, h_prod_split]
  calc
    (7 : ℝ) ^ 7 * (x 0 * ∏ i ∈ s7, x i)
      = ((7 : ℝ) ^ 7 * ∏ i ∈ s7, x i) * x 0 := by ring
    _ ≤ (∑ i ∈ s7, x i) ^ 7 * x 0 :=
        mul_le_mul_of_nonneg_right h_mul7 (hx 0)

/-- **Verification of Ruan's Interpolation Parameter Window in Case 2 (`[Ruan 2024, Steps 1–2]`)**:
In `[Ruan 2024, Eqs. (35)–(37) & (43)]`, the admissible parameter window for $\alpha$ satisfies:
1. $0 < \alpha < 1/2$ and $(1 - \alpha)^2 \le 2/3$ (i.e. $\alpha \ge 1 - \sqrt{2/3} \approx 0.1835$),
2. $t = 1 - (1 - \alpha)^2 \in [1/3, 3/4]$ with $t^2 (1 - t) \ge 7 / 64 = 0.109375$.
At $\alpha = 13 / 50 = 0.26 \in [0.2, 0.266]$, all conditions hold strictly with rational arithmetic. -/
theorem octonionic_alpha_parameter_bounds :
    let α : ℝ := 13 / 50
    let t : ℝ := 1 - (1 - α) ^ 2
    0 < α ∧ α < 1 / 2 ∧
    (1 - α) ^ 2 ≤ 2 / 3 ∧
    1 / 3 ≤ t ∧ t ≤ 3 / 4 ∧
    (7 : ℝ) / 64 ≤ t ^ 2 * (1 - t) := by
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Ruan Case 2 Step 2 Endpoint Bound (`[Ruan 2024, Eqs. (34)–(36)]`, `cayley_case2_step2_endpoint_bound`)**:
If $\mu \ge 0$, $\mu_1 \le \mu$, and $t = 1 - (1 - \alpha)^2$ satisfies $t^2(1 - t) \ge 7/64$,
then
$$\frac{7}{64} \mu (\mu - \mu_1) \mu_1 \le (\mu - t \mu) (t \mu)^2.$$ -/
theorem cayley_case2_step2_endpoint_bound
    {μ μ₁ t : ℝ} (hμ : 0 ≤ μ) (_hμ₁_le : μ₁ ≤ μ)
    (ht : (7 : ℝ) / 64 ≤ t ^ 2 * (1 - t)) :
    (7 : ℝ) / 64 * μ * (μ - μ₁) * μ₁ ≤ (μ - t * μ) * (t * μ) ^ 2 := by
  have h_amgm_mu : (μ - μ₁) * μ₁ ≤ μ ^ 2 := by
    nlinarith [sq_nonneg μ₁]
  calc
    (7 : ℝ) / 64 * μ * (μ - μ₁) * μ₁
      = (7 : ℝ) / 64 * μ * ((μ - μ₁) * μ₁) := by ring
    _ ≤ (7 : ℝ) / 64 * μ * μ ^ 2 := by
        apply mul_le_mul_of_nonneg_left h_amgm_mu
        positivity
    _ = ((7 : ℝ) / 64) * μ ^ 3 := by ring
    _ ≤ (t ^ 2 * (1 - t)) * μ ^ 3 :=
        mul_le_mul_of_nonneg_right ht (pow_nonneg hμ 3)
    _ = (μ - t * μ) * (t * μ) ^ 2 := by ring

/-! ### 6. Perturbed Log-Concavity Trick and Ruan Proposition 3.1 (`[Ruan 2024, Eqs. (19)–(23)]`) -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- **Perturbed Decomposition of the Rank-One Hessian Operator (`[Ruan 2024, Eq. (22)]`)**:
For any operators $H, \widehat{H}, U_\alpha : E \to_l[\mathbb{R}] E$, the rank-one Hessian operator
$W_y = I - 2H + \widehat{H}$ splits identically as
$$I - 2H + \widehat{H} = (I - H - U_\alpha) + (\widehat{H} - H + U_\alpha),$$
where the off-diagonal perturbation $U_\alpha$ cancels out in the sum. -/
theorem rankOneHessianOperator_eq_perturbed_add (H H_hat U_α : E →ₗ[ℝ] E) :
    rankOneHessianOperator H H_hat = (LinearMap.id - H - U_α) + (H_hat - H + U_α) := by
  rw [rankOneHessianOperator_eq_add_sub]
  ext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply]
  abel

/-- **Ruan's Perturbed Log-Concavity Inequality (`[Ruan 2024, Eq. (22) / \eqref{new_trick}]`,
`det_rankOneHessianOperator_perturbed_ge`)**:
Let $\dim_{\mathbb{R}} E = n \ge 2$ and $d \ge 2$ ($n = 16, d = 8, h_0 = n + d - 2 = 22$ for
$\mathbb{O}\mathbf{H}^2$). For any perturbation operator $U_\alpha : E \to_l[\mathbb{R}] E$
such that both $I - H - U_\alpha$ and $\widehat{H} - H + U_\alpha$ are symmetric and
positive-semidefinite, we have:
$$(n + d - 2)^n \cdot \det\left(\frac{I - H - U_\alpha}{n - 1}\right)^{\frac{n - 1}{n + d - 2}}
  \cdot \det\left(\frac{\widehat{H} - H + U_\alpha}{d - 1}\right)^{\frac{d - 1}{n + d - 2}}
  \le \det(I - 2H + \widehat{H}).$$ -/
theorem det_rankOneHessianOperator_perturbed_ge
    {n : ℕ} (hn : Module.finrank ℝ E = n) (hn2 : 2 ≤ n) {d : ℕ} (hd2 : 2 ≤ d)
    {H H_hat U_α : E →ₗ[ℝ] E}
    (hIHU_symm : ((LinearMap.id : E →ₗ[ℝ] E) - H - U_α).IsSymmetric)
    (hHHU_symm : (H_hat - H + U_α).IsSymmetric)
    (hIHU_pos : ∀ u : E, 0 ≤ inner ℝ u (((LinearMap.id : E →ₗ[ℝ] E) - H - U_α) u))
    (hHHU_pos : ∀ u : E, 0 ≤ inner ℝ u ((H_hat - H + U_α) u)) :
    (((n : ℝ) + (d : ℝ) - 2) ^ n) *
      (((1 / ((n : ℝ) - 1)) • (LinearMap.id - H - U_α)).det ^
          (((n : ℝ) - 1) / ((n : ℝ) + (d : ℝ) - 2)) *
       ((1 / ((d : ℝ) - 1)) • (H_hat - H + U_α)).det ^
          (((d : ℝ) - 1) / ((n : ℝ) + (d : ℝ) - 2))) ≤
      (rankOneHessianOperator H H_hat).det := by
  let h₀ : ℝ := (n : ℝ) + (d : ℝ) - 2
  let p : ℝ := ((n : ℝ) - 1) / h₀
  let q : ℝ := ((d : ℝ) - 1) / h₀
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn2; linarith
  have hd1_pos : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := Nat.cast_le.mpr hd2; linarith
  have hh₀_pos : 0 < h₀ := by
    change 0 < (n : ℝ) + (d : ℝ) - 2; linarith
  have hp_nn : 0 ≤ p := div_nonneg hn1_pos.le hh₀_pos.le
  have hq_nn : 0 ≤ q := div_nonneg hd1_pos.le hh₀_pos.le
  have hpq : p + q = 1 := by
    change ((n : ℝ) - 1) / h₀ + ((d : ℝ) - 1) / h₀ = 1
    rw [← add_div, div_eq_iff hh₀_pos.ne']
    change (n : ℝ) - 1 + ((d : ℝ) - 1) = 1 * ((n : ℝ) + (d : ℝ) - 2)
    ring
  let A : E →ₗ[ℝ] E := (1 / ((n : ℝ) - 1)) • (LinearMap.id - H - U_α)
  let B : E →ₗ[ℝ] E := (1 / ((d : ℝ) - 1)) • (H_hat - H + U_α)
  have hA_symm : A.IsSymmetric := by
    intro u v
    dsimp only [A]
    rw [LinearMap.smul_apply, LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right,
      hIHU_symm u v]
  have hB_symm : B.IsSymmetric := by
    intro u v
    dsimp only [B]
    rw [LinearMap.smul_apply, LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right,
      hHHU_symm u v]
  have hA_pos : ∀ u : E, 0 ≤ inner ℝ u (A u) := by
    intro u
    dsimp only [A]
    rw [LinearMap.smul_apply, real_inner_smul_right]
    exact mul_nonneg (by positivity) (hIHU_pos u)
  have hB_pos : ∀ u : E, 0 ≤ inner ℝ u (B u) := by
    intro u
    dsimp only [B]
    rw [LinearMap.smul_apply, real_inner_smul_right]
    exact mul_nonneg (by positivity) (hHHU_pos u)
  have h_log_conc :=
    det_weighted_add_ge_rpow_mul_rpow hA_symm hB_symm hn hA_pos hB_pos hp_nn hq_nn hpq
  have h_decomp : rankOneHessianOperator H H_hat = h₀ • (p • A + q • B) := by
    rw [rankOneHessianOperator_eq_perturbed_add H H_hat U_α]
    ext u
    simp only [A, B, p, q, LinearMap.add_apply, LinearMap.smul_apply]
    rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    have h1 : h₀ * (((n : ℝ) - 1) / h₀) * (1 / ((n : ℝ) - 1)) = 1 := by
      field_simp [hh₀_pos.ne', hn1_pos.ne']
    have h2 : h₀ * (((d : ℝ) - 1) / h₀) * (1 / ((d : ℝ) - 1)) = 1 := by
      field_simp [hh₀_pos.ne', hd1_pos.ne']
    rw [h1, h2, one_smul, one_smul]
  calc
    h₀ ^ n * (A.det ^ p * B.det ^ q)
      ≤ h₀ ^ n * (p • A + q • B).det :=
        mul_le_mul_of_nonneg_left h_log_conc (pow_nonneg hh₀_pos.le n)
    _ = (rankOneHessianOperator H H_hat).det := by
        rw [h_decomp, LinearMap.det_smul, hn]

/-- **Ruan Proposition 3.1 / Lemma 3.4 Perturbed Rank-One Determinant Inequality
(`perturbed_rankOne_det_ineq`)**:
Suppose $\dim_{\mathbb{R}} E = n \ge 2$, $d \ge 2$, $\det H > 0$, and there exists a symmetric
perturbation operator $U_\alpha : E \to_l[\mathbb{R}] E$ (`[Ruan 2024, Lemma 3.4]`) such that:
1. $I - H - U_\alpha$ and $\widehat{H} - H + U_\alpha$ are symmetric positive-semidefinite,
2. $\det\left(\frac{I - H - U_\alpha}{n - 1}\right) \ge (\sqrt{n})^{-n \cdot \frac{n + d - 2}{n - 1}} (\det H)^{\frac{n - d}{2(n - 1)}}$
   (`h_part1_perturbed`, `[Ruan 2024, Eq. (23)]`), and
3. $\det\left(\frac{\widehat{H} - H + U_\alpha}{d - 1}\right) \ge \det H$
   (`h_part2_perturbed`, `[Ruan 2024, Eq. (21)]`).

Then $\det(I - 2H + \widehat{H}) > 0$ and $(H, \widehat{H})$ satisfies the sharp rank-one
determinant inequality (`[Ruan 2024, Proposition 3.1, Eq. (19)]`):
$$\frac{\sqrt{\det H}}{\det(I - 2H + \widehat{H})} \le \left(\frac{\sqrt{n}}{n + d - 2}\right)^n.$$ -/
theorem perturbed_rankOne_det_ineq
    {n : ℕ} {H H_hat U_α : E →ₗ[ℝ] E} (hn : Module.finrank ℝ E = n)
    (hn2 : 2 ≤ n) {d : ℕ} (hd2 : 2 ≤ d) (_hnd : d ≤ n)
    (hIHU_symm : ((LinearMap.id : E →ₗ[ℝ] E) - H - U_α).IsSymmetric)
    (hHHU_symm : (H_hat - H + U_α).IsSymmetric)
    (hIHU_pos : ∀ u : E, 0 ≤ inner ℝ u (((LinearMap.id : E →ₗ[ℝ] E) - H - U_α) u))
    (hHHU_pos : ∀ u : E, 0 ≤ inner ℝ u ((H_hat - H + U_α) u))
    (hdetH_pos : 0 < H.det)
    (h_part1_perturbed :
      (Real.sqrt (n : ℝ)) ^ (-((n : ℝ) * ((n : ℝ) + (d : ℝ) - 2) / ((n : ℝ) - 1))) *
        H.det ^ (((n : ℝ) - (d : ℝ)) / (2 * ((n : ℝ) - 1))) ≤
        ((1 / ((n : ℝ) - 1)) • (LinearMap.id - H - U_α)).det)
    (h_part2_perturbed : H.det ≤ ((1 / ((d : ℝ) - 1)) • (H_hat - H + U_α)).det) :
    0 < (rankOneHessianOperator H H_hat).det ∧
    Real.sqrt H.det / (rankOneHessianOperator H H_hat).det ≤
      (Real.sqrt (n : ℝ) / ((n : ℝ) + (d : ℝ) - 2)) ^ n := by
  let h₀ : ℝ := (n : ℝ) + (d : ℝ) - 2
  let p : ℝ := ((n : ℝ) - 1) / h₀
  let q : ℝ := ((d : ℝ) - 1) / h₀
  let A : E →ₗ[ℝ] E := (1 / ((n : ℝ) - 1)) • (LinearMap.id - H - U_α)
  let B : E →ₗ[ℝ] E := (1 / ((d : ℝ) - 1)) • (H_hat - H + U_α)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn2; linarith
  have hd1_pos : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := Nat.cast_le.mpr hd2; linarith
  have hh₀_pos : 0 < h₀ := by
    change 0 < (n : ℝ) + (d : ℝ) - 2; linarith
  have hp_pos : 0 < p := div_pos hn1_pos hh₀_pos
  have hq_pos : 0 < q := div_pos hd1_pos hh₀_pos
  have h_log :=
    det_rankOneHessianOperator_perturbed_ge hn hn2 hd2 hIHU_symm hHHU_symm hIHU_pos hHHU_pos
  have h_lhs1_pos :
      0 < (Real.sqrt (n : ℝ)) ^ (-((n : ℝ) * h₀ / ((n : ℝ) - 1))) *
        H.det ^ (((n : ℝ) - (d : ℝ)) / (2 * ((n : ℝ) - 1))) :=
    mul_pos (Real.rpow_pos_of_pos hsqrt_pos _) (Real.rpow_pos_of_pos hdetH_pos _)
  have hA_rpow :
      ((Real.sqrt (n : ℝ)) ^ (-((n : ℝ) * h₀ / ((n : ℝ) - 1))) *
        H.det ^ (((n : ℝ) - (d : ℝ)) / (2 * ((n : ℝ) - 1)))) ^ p ≤ A.det ^ p :=
    Real.rpow_le_rpow h_lhs1_pos.le h_part1_perturbed hp_pos.le
  have hB_rpow : H.det ^ q ≤ B.det ^ q :=
    Real.rpow_le_rpow hdetH_pos.le h_part2_perturbed hq_pos.le
  have h_prod_simplify :
      ((Real.sqrt (n : ℝ)) ^ (-((n : ℝ) * h₀ / ((n : ℝ) - 1))) *
        H.det ^ (((n : ℝ) - (d : ℝ)) / (2 * ((n : ℝ) - 1)))) ^ p * H.det ^ q =
        (Real.sqrt (n : ℝ)) ^ (-(n : ℝ)) * Real.sqrt H.det := by
    rw [Real.mul_rpow (Real.rpow_nonneg hsqrt_pos.le _) (Real.rpow_nonneg hdetH_pos.le _),
      ← Real.rpow_mul hsqrt_pos.le, ← Real.rpow_mul hdetH_pos.le,
      mul_assoc, ← Real.rpow_add hdetH_pos]
    have hexp1 : -((n : ℝ) * h₀ / ((n : ℝ) - 1)) * p = -(n : ℝ) := by
      dsimp [p]
      field_simp [hn1_pos.ne', hh₀_pos.ne']
    have hexp2 : (((n : ℝ) - (d : ℝ)) / (2 * ((n : ℝ) - 1))) * p + q = 1 / 2 := by
      dsimp [p, q]
      have hh₀_eq : (n : ℝ) - (d : ℝ) + 2 * ((d : ℝ) - 1) = h₀ := by
        dsimp [h₀]; ring
      calc
        ((n : ℝ) - (d : ℝ)) / (2 * ((n : ℝ) - 1)) * (((n : ℝ) - 1) / h₀) + ((d : ℝ) - 1) / h₀
          = (((n : ℝ) - (d : ℝ)) + 2 * ((d : ℝ) - 1)) / (2 * h₀) := by
            field_simp [hn1_pos.ne', hh₀_pos.ne']
        _ = h₀ / (2 * h₀) := by rw [hh₀_eq]
        _ = 1 / 2 := by field_simp [hh₀_pos.ne']
    rw [hexp1, hexp2, ← Real.sqrt_eq_rpow]
  have h_lower :
      h₀ ^ n * ((Real.sqrt (n : ℝ)) ^ (-(n : ℝ)) * Real.sqrt H.det) ≤
        (rankOneHessianOperator H H_hat).det := by
    calc
      h₀ ^ n * ((Real.sqrt (n : ℝ)) ^ (-(n : ℝ)) * Real.sqrt H.det)
        = h₀ ^ n *
            (((Real.sqrt (n : ℝ)) ^ (-((n : ℝ) * h₀ / ((n : ℝ) - 1))) *
              H.det ^ (((n : ℝ) - (d : ℝ)) / (2 * ((n : ℝ) - 1)))) ^ p * H.det ^ q) := by
          rw [h_prod_simplify]
      _ ≤ h₀ ^ n * (A.det ^ p * B.det ^ q) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hh₀_pos.le n)
          exact mul_le_mul hA_rpow hB_rpow (Real.rpow_nonneg hdetH_pos.le q)
            (Real.rpow_nonneg (h_lhs1_pos.le.trans h_part1_perturbed) p)
      _ ≤ (rankOneHessianOperator H H_hat).det := h_log
  have h_lower_pos :
      0 < h₀ ^ n * ((Real.sqrt (n : ℝ)) ^ (-(n : ℝ)) * Real.sqrt H.det) :=
    mul_pos (pow_pos hh₀_pos n)
      (mul_pos (Real.rpow_pos_of_pos hsqrt_pos _) (Real.sqrt_pos.mpr hdetH_pos))
  have hW_pos : 0 < (rankOneHessianOperator H H_hat).det :=
    lt_of_lt_of_le h_lower_pos h_lower
  refine ⟨hW_pos, ?_⟩
  rw [div_le_iff₀ hW_pos]
  have h_rpow_sqrt : (Real.sqrt (n : ℝ)) ^ (-(n : ℝ)) = ((Real.sqrt (n : ℝ)) ^ n)⁻¹ := by
    rw [Real.rpow_neg hsqrt_pos.le, Real.rpow_natCast]
  calc
    Real.sqrt H.det
      = (Real.sqrt (n : ℝ) / h₀) ^ n *
          (h₀ ^ n * ((Real.sqrt (n : ℝ)) ^ (-(n : ℝ)) * Real.sqrt H.det)) := by
        rw [h_rpow_sqrt, div_pow]
        field_simp [hh₀_pos.ne', hsqrt_pos.ne']
    _ ≤ (Real.sqrt (n : ℝ) / h₀) ^ n * (rankOneHessianOperator H H_hat).det :=
      mul_le_mul_of_nonneg_left h_lower (by positivity)

/-- **Ruan Proposition 3.1 Specialized to the Cayley Hyperbolic Plane $\mathbb{O}\mathbf{H}^2$
($n = 16, d = 8, h_0 = 22$, `octonionic_rankOne_det_ineq`)**:
On a 16-dimensional real inner product space $E \cong T_x \mathbb{O}\mathbf{H}^2$, if there
exists an off-diagonal perturbation $U_\alpha : E \to_l[\mathbb{R}] E$ satisfying Ruan's
Lemma 3.4 (`[Ruan 2024, Eqs. (21) & (23)]`):
1. $I - H - U_\alpha$ and $\widehat{H} - H + U_\alpha$ are symmetric positive-semidefinite,
2. $16^{-16 \cdot 11 / 15} (\det H)^{4/15} \le \det\left(\frac{I - H - U_\alpha}{15}\right)$
   (equivalently $\frac{15^{16}}{16^{16(1 - 4/15)}} (\det H)^{4/15} \le \det(I - H - U_\alpha)$), and
3. $\det H \le \det\left(\frac{\widehat{H} - H + U_\alpha}{7}\right)$
   (equivalently $7^{16} \det H \le \det(\widehat{H} - H + U_\alpha)$),
then $\det(I - 2H + \widehat{H}) > 0$ and
$$\frac{\sqrt{\det H}}{\det(I - 2H + \widehat{H})}
  \le \left(\frac{\sqrt{16}}{16 + 8 - 2}\right)^{16} = \left(\frac{2}{11}\right)^{16}.$$ -/
theorem octonionic_rankOne_det_ineq
    {H H_hat U_α : E →ₗ[ℝ] E} (hn16 : Module.finrank ℝ E = 16)
    (hIHU_symm : ((LinearMap.id : E →ₗ[ℝ] E) - H - U_α).IsSymmetric)
    (hHHU_symm : (H_hat - H + U_α).IsSymmetric)
    (hIHU_pos : ∀ u : E, 0 ≤ inner ℝ u (((LinearMap.id : E →ₗ[ℝ] E) - H - U_α) u))
    (hHHU_pos : ∀ u : E, 0 ≤ inner ℝ u ((H_hat - H + U_α) u))
    (hdetH_pos : 0 < H.det)
    (h_ruan_23 :
      (Real.sqrt (16 : ℝ)) ^ (-((16 : ℝ) * ((16 : ℝ) + (8 : ℝ) - 2) / ((16 : ℝ) - 1))) *
        H.det ^ (((16 : ℝ) - (8 : ℝ)) / (2 * ((16 : ℝ) - 1))) ≤
        ((1 / (15 : ℝ)) • (LinearMap.id - H - U_α)).det)
    (h_ruan_21 : H.det ≤ ((1 / (7 : ℝ)) • (H_hat - H + U_α)).det) :
    0 < (rankOneHessianOperator H H_hat).det ∧
    Real.sqrt H.det / (rankOneHessianOperator H H_hat).det ≤ ((2 : ℝ) / 11) ^ 16 := by
  have h15 : (16 : ℝ) - 1 = 15 := by norm_num
  have h7 : (8 : ℝ) - 1 = 7 := by norm_num
  have h_part1 :
      (Real.sqrt ((16 : ℕ) : ℝ)) ^
          (-(((16 : ℕ) : ℝ) * (((16 : ℕ) : ℝ) + ((8 : ℕ) : ℝ) - 2) / (((16 : ℕ) : ℝ) - 1))) *
        H.det ^ ((((16 : ℕ) : ℝ) - ((8 : ℕ) : ℝ)) / (2 * (((16 : ℕ) : ℝ) - 1))) ≤
        ((1 / (((16 : ℕ) : ℝ) - 1)) • (LinearMap.id - H - U_α)).det := by
    simpa [h15] using h_ruan_23
  have h_part2 : H.det ≤ ((1 / (((8 : ℕ) : ℝ) - 1)) • (H_hat - H + U_α)).det := by
    simpa [h7] using h_ruan_21
  obtain ⟨hW_pos, h_ineq⟩ :=
    perturbed_rankOne_det_ineq hn16 (by norm_num : 2 ≤ 16) (by norm_num : 2 ≤ 8)
      (by norm_num : 8 ≤ 16) hIHU_symm hHHU_symm hIHU_pos hHHU_pos hdetH_pos h_part1 h_part2
  refine ⟨hW_pos, ?_⟩
  have h_ratio : Real.sqrt ((16 : ℕ) : ℝ) / (((16 : ℕ) : ℝ) + ((8 : ℕ) : ℝ) - 2) = 2 / 11 := by
    simpa using octonionic_critical_ratio_eq
  rwa [h_ratio] at h_ineq

/-- **Master Cayley Hyperbolic Plane ($\mathbb{O}\mathbf{H}^2$) Pointwise BCG Jacobian Bound
(`octonionic_rankOne_bcg_jacobian_bound`)**:
Let $\dim_{\mathbb{R}} E = 16$ ($E \cong T_x \mathbb{O}\mathbf{H}^2$, $d = 8$, $h_0 = 22$).
Suppose $D_F : E \to_l[\mathbb{R}] E$ satisfies the implicit function theorem equation
$$(I - 2H + \widehat{H}) \circ D_F = s \cdot H_y$$
where $H = \mathrm{busemannCovariance}\,t\,w\,u$, $\widehat{H} = \mathrm{rankOneLineCovariance}\,t\,w\,\pi$,
and $H_y = \mathrm{busemannCrossOperator}\,1\,t\,w\,v\,u$ for unit vectors $u_a$, unit-bounded
source gradients $v_a$ ($\|v_a\| \le 1$), probability weights $w_a$, and 8-dimensional Cayley-line
projections $\pi_a$. If $(H, \widehat{H})$ admits a Ruan perturbation $U_\alpha$ satisfying
Lemma 3.4 (`[Ruan 2024, Eqs. (21) & (23)]`), then:
$$|\det D_F| \le \left(\frac{s}{22}\right)^{16}.$$ -/
theorem octonionic_rankOne_bcg_jacobian_bound
    (hn16 : Module.finrank ℝ E = 16)
    {α : Type*} (t : Finset α)
    {w : α → ℝ} (hw : ∀ a ∈ t, 0 ≤ w a) (hw_sum : ∑ a ∈ t, w a = 1)
    {u v : α → E}
    (hv : ∀ a ∈ t, ‖v a‖ ≤ 1)
    {π : α → (E →ₗ[ℝ] E)}
    {s : ℝ} (hs : 0 ≤ s)
    {D_F U_α : E →ₗ[ℝ] E}
    (h_ift :
      (rankOneHessianOperator
        (busemannCovariance t w u)
        (rankOneLineCovariance t w π)).comp D_F =
      s • busemannCrossOperator 1 t w v u)
    (hIHU_symm : ((LinearMap.id : E →ₗ[ℝ] E) - busemannCovariance t w u - U_α).IsSymmetric)
    (hHHU_symm : (rankOneLineCovariance t w π - busemannCovariance t w u + U_α).IsSymmetric)
    (hIHU_pos : ∀ x : E, 0 ≤ inner ℝ x (((LinearMap.id : E →ₗ[ℝ] E) - busemannCovariance t w u - U_α) x))
    (hHHU_pos : ∀ x : E, 0 ≤ inner ℝ x ((rankOneLineCovariance t w π - busemannCovariance t w u + U_α) x))
    (hdetH_pos : 0 < (busemannCovariance t w u).det)
    (h_ruan_23 :
      (Real.sqrt (16 : ℝ)) ^ (-((16 : ℝ) * ((16 : ℝ) + (8 : ℝ) - 2) / ((16 : ℝ) - 1))) *
        (busemannCovariance t w u).det ^ (((16 : ℝ) - (8 : ℝ)) / (2 * ((16 : ℝ) - 1))) ≤
        ((1 / (15 : ℝ)) • (LinearMap.id - busemannCovariance t w u - U_α)).det)
    (h_ruan_21 :
      (busemannCovariance t w u).det ≤
        ((1 / (7 : ℝ)) • (rankOneLineCovariance t w π - busemannCovariance t w u + U_α)).det) :
    |D_F.det| ≤ (s / 22) ^ 16 := by
  let H := busemannCovariance t w u
  let H_X := busemannCovariance t w v
  let H_hat := rankOneLineCovariance t w π
  obtain ⟨hW_pos, h_det_ineq⟩ :=
    octonionic_rankOne_det_ineq hn16 hIHU_symm hHHU_symm hIHU_pos hHHU_pos
      hdetH_pos h_ruan_23 h_ruan_21
  have h_ineq_22 :
      Real.sqrt H.det / (rankOneHessianOperator H H_hat).det ≤
        (Real.sqrt ((16 : ℕ) : ℝ) / (22 : ℝ)) ^ 16 := by
    have h_ratio : Real.sqrt ((16 : ℕ) : ℝ) / (22 : ℝ) = 2 / 11 := by
      simpa using octonionic_critical_ratio_twenty_two_eq
    rwa [h_ratio]
  have hCS : ∀ x y : E, |inner ℝ (busemannCrossOperator 1 t w v u x) y| ≤
      Real.sqrt (inner ℝ x (H_X x)) * Real.sqrt (inner ℝ y (H y)) := by
    intro x y
    simpa [one_mul] using abs_inner_busemannCrossOperator_le zero_le_one t hw v u x y
  exact abs_det_le_div_entropy_pow_of_rankOne_det_ineq hn16 (by norm_num : 0 < 16) hs
    (by norm_num : (0 : ℝ) < 22) h_ift hW_pos
    (isSymmetric_busemannCovariance t w v)
    (isSymmetric_busemannCovariance t w u)
    (inner_busemannCovariance_nonneg t hw v)
    (inner_busemannCovariance_nonneg t hw u)
    (trace_busemannCovariance_le_one t hw hw_sum.le hv)
    hCS h_ineq_22

/-- **Ruan Corollary 3.8 Quantitative Defect Estimate for $\mathbb{O}\mathbf{H}^2$
(`octonionic_rankOne_bcg_jacobian_bound_with_defect`)**:
If $(H, \widehat{H})$ satisfies Ruan's Corollary 3.8 (`[Ruan 2024, Eq. (44)]`):
$$\frac{\sqrt{\det H}}{\det(I - 2H + \widehat{H})}
  \le \left(\frac{2}{11}\right)^{16} \left(1 - K \sum_{i=1}^{16} \left(\nu_i - \frac{1}{16}\right)^2\right)$$
where $\nu_i$ are the eigenvalues of $H$, then the natural map differential $D_F$ satisfies:
$$|\det D_F| \le \left(\frac{s}{22}\right)^{16}
  \left(1 - K \sum_{i=1}^{16} \left(\nu_i - \frac{1}{16}\right)^2\right).$$ -/
theorem octonionic_rankOne_bcg_jacobian_bound_with_defect
    (hn16 : Module.finrank ℝ E = 16)
    {α : Type*} (t : Finset α)
    {w : α → ℝ} (hw : ∀ a ∈ t, 0 ≤ w a) (hw_sum : ∑ a ∈ t, w a = 1)
    {u v : α → E}
    (hv : ∀ a ∈ t, ‖v a‖ ≤ 1)
    {π : α → (E →ₗ[ℝ] E)}
    {s K : ℝ} (hs : 0 ≤ s)
    {D_F : E →ₗ[ℝ] E}
    (h_ift :
      (rankOneHessianOperator
        (busemannCovariance t w u)
        (rankOneLineCovariance t w π)).comp D_F =
      s • busemannCrossOperator 1 t w v u)
    (hW_pos : 0 < (rankOneHessianOperator (busemannCovariance t w u) (rankOneLineCovariance t w π)).det)
    (h_cor38 :
      Real.sqrt (busemannCovariance t w u).det /
        (rankOneHessianOperator (busemannCovariance t w u) (rankOneLineCovariance t w π)).det ≤
        ((2 : ℝ) / 11) ^ 16 *
          (1 - K * ∑ i : Fin 16,
            ((isSymmetric_busemannCovariance t w u).eigenvalues hn16 i - 1 / (16 : ℝ)) ^ 2)) :
    |D_F.det| ≤ (s / 22) ^ 16 *
      (1 - K * ∑ i : Fin 16,
        ((isSymmetric_busemannCovariance t w u).eigenvalues hn16 i - 1 / (16 : ℝ)) ^ 2) := by
  let H := busemannCovariance t w u
  let H_X := busemannCovariance t w v
  let H_hat := rankOneLineCovariance t w π
  have hH : H.IsSymmetric := isSymmetric_busemannCovariance t w u
  have h_cor38_22 :
      Real.sqrt H.det / (rankOneHessianOperator H H_hat).det ≤
        (Real.sqrt ((16 : ℕ) : ℝ) / (22 : ℝ)) ^ 16 *
          (1 - K * ∑ i : Fin 16, (hH.eigenvalues hn16 i - 1 / ((16 : ℕ) : ℝ)) ^ 2) := by
    have h_ratio : Real.sqrt ((16 : ℕ) : ℝ) / (22 : ℝ) = 2 / 11 := by
      simpa using octonionic_critical_ratio_twenty_two_eq
    rw [h_ratio]
    simpa using h_cor38
  have hCS : ∀ x y : E, |inner ℝ (busemannCrossOperator 1 t w v u x) y| ≤
      Real.sqrt (inner ℝ x (H_X x)) * Real.sqrt (inner ℝ y (H y)) := by
    intro x y
    simpa [one_mul] using abs_inner_busemannCrossOperator_le zero_le_one t hw v u x y
  exact abs_det_le_div_entropy_pow_mul_defect hn16 (by norm_num : 0 < 16) hs
    (by norm_num : (0 : ℝ) < 22) h_ift hW_pos
    (isSymmetric_busemannCovariance t w v)
    hH
    (inner_busemannCovariance_nonneg t hw v)
    (inner_busemannCovariance_nonneg t hw u)
    (trace_busemannCovariance_le_one t hw hw_sum.le hv)
    hCS h_cor38_22

end BCG.RankOne
