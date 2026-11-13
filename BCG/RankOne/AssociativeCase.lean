import BCG.RankOne.BusemannHessian

/-!
# Step 4B: BCG Appendix B — Log-Concavity of $\det$ and the Associative Rank-One Case ($\mathbb{R}, \mathbb{C}, \mathbb{H}$)

This file formalizes Appendix B of Besson–Courtois–Gallot (1995) (`[BCG1, Appendice B]`) and
Section 3.2 of Ruan (2024) (`arXiv:2203.14418`, Equations (13)–(17) and Properties `(P1)`–`(P2)`),
establishing the rank-one Busemann Hessian determinant inequality and BCG Jacobian bound for the
associative normed division algebras $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}, \mathbb{H}\}$
($d \in \{1, 2, 4\}$).

## Main Results

1. **Simultaneous Diagonalization & Minkowski / Ky Fan Log-Concavity of $\det$ (`[BCG1, Lemme B.2]`,
   `det_weighted_add_ge_rpow_mul_rpow`, `det_sum_smul_ge_of_forall_det_ge`)**:
   Using the spectral inverse square root $D = A^{-1/2}$ from `BCG.LinearAlgebra.exists_inv_sqrt_of_det_pos`
   to simultaneously diagonalize $A$ and $B$ into $I$ and $M = A^{-1/2} B A^{-1/2}$, and applying the
   weighted AM–GM inequality to the eigenvalues of $p I + q M$, we prove that for any symmetric
   positive-semidefinite operators $A, B : E \to_l[\mathbb{R}] E$ and weights $p, q \ge 0$ with
   $p + q = 1$:
   $$(\det A)^p \cdot (\det B)^q \le \det(p \bullet A + q \bullet B).$$
   By induction on finite convex combinations, the superlevel sets $\{A \ge 0 \mid \det A \ge c\}$
   are convex (`det_sum_smul_ge_of_forall_det_ge`).

2. **Orthogonal $\mathbb{K}$-Structures & Conjugation Formula for $\widehat{H} - H$
   (`IsOrthogonalKStructure`, `isKLineProjection_kLineProj`, `sub_busemannCovariance_eq_sum_conjugate`,
   `det_sub_div_ge_det_of_orthogonal_conjugates`, `[BCG1, Lemme B.3]` / `[Ruan 2024, (P1)–(P2) & Eq. (17)]`)**:
   When $E$ carries orthogonal endomorphisms $J_0 = \mathrm{id}, J_1, \dots, J_{d-1} \in \mathrm{O}(E)$
   such that $\{J_r u\}_{r=0}^{d-1}$ is orthogonal for every $u \in E$ (as in $\mathbb{C}\mathbf{H}^m$
   with $d = 2$ and $\mathbb{H}\mathbf{H}^m$ with $d = 4$), the orthogonal projection onto
   $\mathbb{K} \cdot u$ is
   $$\pi_u = \sum_{r=0}^{d-1} (J_r u) \otimes (J_r u)^* = \sum_{r=0}^{d-1} J_r \circ (u \otimes u^*) \circ J_r^*,$$
   so that
   $$\widehat{H} - H = \sum_{r \in \mathrm{Fin}\,d \setminus \{0\}} J_r \circ H \circ J_r^*, \qquad
     \det\left(\left(\frac{1}{d - 1 : \mathbb{R}}\right) \bullet (\widehat{H} - H)\right) \ge \det H.$$

3. **AM–GM Lower Bound on $\det((I - H)/(n - 1))$ & Log-Concavity Synthesis
   (`det_id_sub_div_ge_det`, `det_rankOneHessianOperator_ge`, `associative_rankOne_det_ineq`,
   `associative_rankOne_bcg_jacobian_bound`, `[BCG1, Lemmes B.3–B.4]` / `[Ruan 2024, Eqs. (14)–(17)]`)**:
   - Proves the unconditional AM–GM inequality $\det((I - H)/(n - 1)) \ge \det H$ for any
     symmetric positive-semidefinite $H$ with $\operatorname{Tr}(H) = 1$ ($n \ge 2$).
   - Proves the log-concavity splitting ([Ruan 2024, Eq. (14)]):
     $$\det(I - 2H + \widehat{H}) \ge (n + d - 2)^n
       \det\left(\frac{I - H}{n - 1}\right)^{\frac{n - 1}{n + d - 2}}
       \det\left(\frac{\widehat{H} - H}{d - 1}\right)^{\frac{d - 1}{n + d - 2}}.$$
   - Combines `[Ruan 2024, Eqs. (14), (16), (17)]` to derive the sharp rank-one determinant
     inequality
     $$\frac{\sqrt{\det H}}{\det(I - 2H + \widehat{H})} \le \left(\frac{\sqrt{n}}{n + d - 2}\right)^n$$
     and the resulting pointwise BCG Jacobian bound $|\det D_F| \le (s / (n + d - 2))^n$.

### Faithfulness Note on `[BCG1, Lemme B.4]` vs. `[Ruan 2024, Eq. (16) & p. 14]`
In `[BCG1, Lemme B.4]`, for a symmetric positive-semidefinite $n \times n$ matrix $H$ with
$\operatorname{Tr}(H) = 1$, the function $H \mapsto (\det H)^s / \det(I - H)$ achieves its global
maximum on $\{H \ge 0, \operatorname{Tr}(H) = 1\}$ at $H = \frac{1}{n} I$ whenever
$\frac{1}{n - 1} \le s \le 1$ (since as $\lambda_1 \to 1^-$ and
$\lambda_2 = \dots = \lambda_n = \varepsilon \to 0^+$, $\det(I - H) \sim (n - 1)\varepsilon$ and
$(\det H)^s \sim \varepsilon^{(n - 1)s}$, which requires $(n - 1)s \ge 1$). In `[Ruan 2024, Eq. (16)]`,
the intermediate exponent was transcribed as $1/n$ rather than $\frac{1}{n - 1}$; however, the
actual exponent used in both `[BCG1]` and `[Ruan 2024]` is $s = \frac{n - d}{2(n - 1)}$
($s = 4/15$ for $\mathbb{O}\mathbf{H}^2$), which satisfies $\frac{1}{n - 1} \le s \le \frac{1}{2}$
for every rank-one symmetric space $\mathbb{K}\mathbf{H}^m$ of dimension $n \ge 3$ ($n - d \ge 2$).
We formalize both the unconditional $s = 1$ AM–GM bound `det_id_sub_div_ge_det` and the exact
`[BCG1, Lemme B.4]` / `[Ruan 2024, Eq. (16)]` bound at $s = \frac{n - d}{2(n - 1)}$.
-/

noncomputable section

open Finset BigOperators

namespace BCG.RankOne

open BCG.LinearAlgebra BCG.Hyperbolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ}

/-!
### 1. Polarization & Simultaneous Diagonalization via $A^{-1/2}$
-/

/-- Product monotonicity for non-negative real functions on a `Finset`. -/
theorem finset_prod_le_prod_of_nonneg {α : Type*} [DecidableEq α] (s : Finset α)
    {f g : α → ℝ} (hf : ∀ a ∈ s, 0 ≤ f a) (hfg : ∀ a ∈ s, f a ≤ g a) :
    ∏ a ∈ s, f a ≤ ∏ a ∈ s, g a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a₀ s' ha₀ ih =>
    rw [Finset.prod_insert ha₀, Finset.prod_insert ha₀]
    exact mul_le_mul
      (hfg a₀ (Finset.mem_insert_self a₀ s'))
      (ih (fun a ha => hf a (Finset.mem_insert_of_mem ha))
          (fun a ha => hfg a (Finset.mem_insert_of_mem ha)))
      (Finset.prod_nonneg (fun a ha => hf a (Finset.mem_insert_of_mem ha)))
      ((hf a₀ (Finset.mem_insert_self a₀ s')).trans (hfg a₀ (Finset.mem_insert_self a₀ s')))

omit [FiniteDimensional ℝ E] in
/-- If a symmetric linear operator $T : E \to_l[\mathbb{R}] E$ satisfies
$\langle u, T u \rangle = \|u\|^2$ for all $u \in E$, then $T = \mathrm{LinearMap.id}$. -/
theorem eq_id_of_isSymmetric_of_inner_eq_norm_sq
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hquad : ∀ u : E, inner ℝ u (T u) = ‖u‖ ^ 2) :
    T = LinearMap.id := by
  ext u
  apply ext_inner_left ℝ
  intro v
  have huv := hquad (u + v)
  have hu := hquad u
  have hv := hquad v
  have h_symm_uv : inner ℝ u (T v) = inner ℝ v (T u) := by
    rw [← hT u v, real_inner_comm]
  rw [map_add, inner_add_left, inner_add_right, inner_add_right,
    h_symm_uv, norm_add_sq_real, hu, hv, real_inner_comm v u] at huv
  rw [LinearMap.id_apply]
  linarith

omit [FiniteDimensional ℝ E] in
/-- If $D$ is symmetric and satisfies $\langle D u, A(D u) \rangle = \|u\|^2$ for a symmetric
operator $A$, then $D \circ_l A \circ_l D = \mathrm{LinearMap.id}$. -/
theorem comp_conj_eq_id_of_quad_eq_norm_sq
    {A D : E →ₗ[ℝ] E} (hA : A.IsSymmetric) (hD : D.IsSymmetric)
    (hquad : ∀ u : E, inner ℝ (D u) (A (D u)) = ‖u‖ ^ 2) :
    D.comp (A.comp D) = LinearMap.id := by
  have hsymm : (D.comp (A.comp D)).IsSymmetric := by
    intro u v
    simp only [LinearMap.comp_apply]
    rw [hD (A (D u)) v, hA (D u) (D v), ← hD u (A (D v))]
  apply eq_id_of_isSymmetric_of_inner_eq_norm_sq hsymm
  intro u
  simp only [LinearMap.comp_apply]
  rw [← hD u (A (D u)), hquad u]

/-!
### 2. BCG Lemma B.2: Minkowski / Ky Fan Log-Concavity of the Determinant
-/

/-- For a symmetric positive-semidefinite operator $M : E \to_l[\mathbb{R}] E$ on an $n$-dimensional
real inner product space and weights $p, q \ge 0$ with $p + q = 1$,
$$(\det M)^q \le \det(p \bullet \mathrm{LinearMap.id} + q \bullet M).$$ -/
theorem det_rpow_le_det_smul_id_add_smul
    {M : E →ₗ[ℝ] E} (hM : M.IsSymmetric) (hn : Module.finrank ℝ E = n)
    (hpos : ∀ u : E, 0 ≤ inner ℝ u (M u))
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    M.det ^ q ≤ (p • (LinearMap.id : E →ₗ[ℝ] E) + q • M).det := by
  let b := (hM.eigenvectorBasis hn).toBasis
  have h_det_M : M.det = ∏ i : Fin n, hM.eigenvalues hn i := by
    have hd := hM.det_eq_prod_eigenvalues hn
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hd
    exact hd
  have h_det_comb :
      (p • (LinearMap.id : E →ₗ[ℝ] E) + q • M).det =
        ∏ i : Fin n, (p + q * hM.eigenvalues hn i) := by
    rw [← LinearMap.det_toMatrix b (p • (LinearMap.id : E →ₗ[ℝ] E) + q • M),
      map_add, map_smul, map_smul, LinearMap.toMatrix_id, hM.toMatrix_eigenvectorBasis hn]
    have hdiag : p • (1 : Matrix (Fin n) (Fin n) ℝ) +
        q • Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues hn) =
        Matrix.diagonal (fun i => p + q * hM.eigenvalues hn i) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
    rw [hdiag, Matrix.det_diagonal]
  have hμ_nn : ∀ i : Fin n, 0 ≤ hM.eigenvalues hn i :=
    eigenvalues_nonneg_of_inner_nonneg hM hn hpos
  rw [h_det_M, h_det_comb, ← Real.finsetProd_rpow _ _ (fun i _ => hμ_nn i)]
  refine finset_prod_le_prod_of_nonneg Finset.univ
    (fun i _ => Real.rpow_nonneg (hμ_nn i) q) (fun i _ => ?_)
  have h_amgm := Real.geom_mean_le_arith_mean2_weighted hp hq zero_le_one (hμ_nn i) hpq
  simpa using h_amgm

/-- **BCG Lemma B.2 (`det_weighted_add_ge_rpow_mul_rpow`)**:
For any symmetric positive-semidefinite operators $A, B : E \to_l[\mathbb{R}] E$ on an
$n$-dimensional real inner product space ($n \ge 1$) and weights $p, q \ge 0$ with $p + q = 1$:
$$(\det A)^p \cdot (\det B)^q \le \det(p \bullet A + q \bullet B).$$ -/
theorem det_weighted_add_ge_rpow_mul_rpow
    {A B : E →ₗ[ℝ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank ℝ E = n)
    (hposA : ∀ u : E, 0 ≤ inner ℝ u (A u))
    (hposB : ∀ u : E, 0 ≤ inner ℝ u (B u))
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    A.det ^ p * B.det ^ q ≤ (p • A + q • B).det := by
  have hdA_nn := det_nonneg_of_inner_nonneg hA hn hposA
  have hdB_nn := det_nonneg_of_inner_nonneg hB hn hposB
  have hcomb_symm : (p • A + q • B).IsSymmetric := by
    intro u v
    simp only [LinearMap.add_apply, LinearMap.smul_apply,
      inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [hA u v, hB u v]
  have hcomb_pos : ∀ u : E, 0 ≤ inner ℝ u ((p • A + q • B) u) := by
    intro u
    simp only [LinearMap.add_apply, LinearMap.smul_apply,
      inner_add_right, real_inner_smul_right]
    exact add_nonneg (mul_nonneg hp (hposA u)) (mul_nonneg hq (hposB u))
  have hcomb_det_nn := det_nonneg_of_inner_nonneg hcomb_symm hn hcomb_pos
  by_cases hp0 : p = 0
  · subst hp0
    have hq1 : q = 1 := by linarith
    subst hq1
    simp
  · have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    by_cases hq0 : q = 0
    · subst hq0
      have hp1 : p = 1 := by linarith
      subst hp1
      simp
    · have hq_pos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
      by_cases hdA0 : A.det = 0
      · rw [hdA0, Real.zero_rpow hp_pos.ne', zero_mul]
        exact hcomb_det_nn
      · have hdA_pos : 0 < A.det := lt_of_le_of_ne hdA_nn (Ne.symm hdA0)
        obtain ⟨D, hD_symm, hD_quad, hD_det⟩ := exists_inv_sqrt_of_det_pos hA hn hposA hdA_pos
        have hDAD : D.comp (A.comp D) = LinearMap.id :=
          comp_conj_eq_id_of_quad_eq_norm_sq hA hD_symm hD_quad
        let M : E →ₗ[ℝ] E := D.comp (B.comp D)
        have hM_symm : M.IsSymmetric := by
          intro u v
          simp only [M, LinearMap.comp_apply]
          rw [hD_symm (B (D u)) v, hB (D u) (D v), ← hD_symm u (B (D v))]
        have hM_pos : ∀ u : E, 0 ≤ inner ℝ u (M u) := by
          intro u
          simp only [M, LinearMap.comp_apply]
          rw [← hD_symm u (B (D u))]
          exact hposB (D u)
        have h_conj : D.comp ((p • A + q • B).comp D) =
            p • (LinearMap.id : E →ₗ[ℝ] E) + q • M := by
          ext u
          simp only [M, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
            map_add, map_smul]
          have h1 := LinearMap.congr_fun hDAD u
          simp only [LinearMap.comp_apply] at h1
          rw [h1]
        have hD_sq : D.det * D.det * A.det = 1 := by
          have h_sqrt : Real.sqrt A.det * Real.sqrt A.det = A.det := Real.mul_self_sqrt hdA_pos.le
          calc
            D.det * D.det * A.det
              = D.det * D.det * (Real.sqrt A.det * Real.sqrt A.det) := by rw [h_sqrt]
            _ = (D.det * Real.sqrt A.det) * (D.det * Real.sqrt A.det) := by ring
            _ = 1 := by rw [hD_det, mul_one]
        have hM_det : M.det = B.det / A.det := by
          dsimp [M]
          rw [LinearMap.det_comp, LinearMap.det_comp, eq_div_iff hdA_pos.ne']
          calc
            D.det * (B.det * D.det) * A.det = B.det * (D.det * D.det * A.det) := by ring
            _ = B.det := by rw [hD_sq, mul_one]
        have h_conj_det : (p • (LinearMap.id : E →ₗ[ℝ] E) + q • M).det =
            (p • A + q • B).det / A.det := by
          rw [← h_conj, LinearMap.det_comp, LinearMap.det_comp, eq_div_iff hdA_pos.ne']
          calc
            D.det * ((p • A + q • B).det * D.det) * A.det
              = (p • A + q • B).det * (D.det * D.det * A.det) := by ring
            _ = (p • A + q • B).det := by rw [hD_sq, mul_one]
        have h_ineq := det_rpow_le_det_smul_id_add_smul hM_symm hn hM_pos hp hq hpq
        rw [hM_det, h_conj_det, Real.div_rpow hdB_nn hdA_pos.le] at h_ineq
        have h_mul := mul_le_mul_of_nonneg_left h_ineq hdA_pos.le
        have h_lhs : A.det * (B.det ^ q / A.det ^ q) = A.det ^ p * B.det ^ q := by
          have hp_eq : p = 1 - q := by linarith
          rw [hp_eq, Real.rpow_sub hdA_pos, Real.rpow_one, div_mul_eq_mul_div, mul_div_assoc']
        have h_rhs : A.det * ((p • A + q • B).det / A.det) = (p • A + q • B).det :=
          mul_div_cancel₀ _ hdA_pos.ne'
        rwa [h_lhs, h_rhs] at h_mul

/-- **Convexity of Determinant Superlevel Sets (`det_add_smul_ge_of_det_ge`)**:
If $A, B : E \to_l[\mathbb{R}] E$ are symmetric positive-semidefinite with $\det A \ge c$ and
$\det B \ge c$ ($c \ge 0$), and $p, q \ge 0$ satisfy $p + q = 1$, then
$\det(p \bullet A + q \bullet B) \ge c$. -/
theorem det_add_smul_ge_of_det_ge
    {A B : E →ₗ[ℝ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank ℝ E = n)
    (hposA : ∀ u : E, 0 ≤ inner ℝ u (A u))
    (hposB : ∀ u : E, 0 ≤ inner ℝ u (B u))
    {c p q : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hdetA : c ≤ A.det) (hdetB : c ≤ B.det) :
    c ≤ (p • A + q • B).det := by
  calc
    c = c ^ (1 : ℝ) := (Real.rpow_one c).symm
    _ = c ^ (p + q) := by rw [hpq]
    _ = c ^ p * c ^ q := Real.rpow_add_of_nonneg hc hp hq
    _ ≤ A.det ^ p * B.det ^ q :=
      mul_le_mul (Real.rpow_le_rpow hc hdetA hp) (Real.rpow_le_rpow hc hdetB hq)
        (Real.rpow_nonneg hc q) (Real.rpow_nonneg (hc.trans hdetA) p)
    _ ≤ (p • A + q • B).det :=
      det_weighted_add_ge_rpow_mul_rpow hA hB hn hposA hposB hp hq hpq

/-- **Finite Convex Combination Determinant Superlevel Bound (`det_sum_smul_ge_of_forall_det_ge`)**:
For any finite family $A_a : E \to_l[\mathbb{R}] E$ ($a \in s$) of symmetric positive-semidefinite
operators with $\det(A_a) \ge c$ ($c \ge 0$) and weights $w_a \ge 0$ with $\sum_{a \in s} w_a = 1$,
$$c \le \det\left(\sum_{a \in s} w_a \bullet A_a\right).$$ -/
theorem det_sum_smul_ge_of_forall_det_ge
    {α : Type*} [DecidableEq α] (s : Finset α)
    {w : α → ℝ} (hw : ∀ a ∈ s, 0 ≤ w a) (hw_sum : ∑ a ∈ s, w a = 1)
    {A : α → (E →ₗ[ℝ] E)}
    (hA_symm : ∀ a ∈ s, (A a).IsSymmetric)
    (hn : Module.finrank ℝ E = n)
    (hA_pos : ∀ a ∈ s, ∀ u : E, 0 ≤ inner ℝ u (A a u))
    {c : ℝ} (hc : 0 ≤ c) (hA_det : ∀ a ∈ s, c ≤ (A a).det) :
    c ≤ (∑ a ∈ s, w a • A a).det := by
  induction s using Finset.induction_on generalizing w with
  | empty =>
    simp at hw_sum
  | @insert a₀ s' ha₀ ih =>
    rw [Finset.sum_insert ha₀] at hw_sum ⊢
    have hw₀ : 0 ≤ w a₀ := hw a₀ (Finset.mem_insert_self a₀ s')
    let S := ∑ a ∈ s', w a
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun a ha => hw a (Finset.mem_insert_of_mem ha))
    by_cases hS0 : S = 0
    · have hw_zero : ∀ a ∈ s', w a = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun a ha => hw a (Finset.mem_insert_of_mem ha))).mp hS0
      have h_sum_zero : ∑ a ∈ s', w a • A a = 0 :=
        Finset.sum_eq_zero (fun a ha => by rw [hw_zero a ha, zero_smul])
      have hw₀_one : w a₀ = 1 := by linarith
      rw [h_sum_zero, add_zero, hw₀_one, one_smul]
      exact hA_det a₀ (Finset.mem_insert_self a₀ s')
    · have hS_pos : 0 < S := lt_of_le_of_ne hS_nn (Ne.symm hS0)
      let w' : α → ℝ := fun a => w a / S
      have hw'_nn : ∀ a ∈ s', 0 ≤ w' a :=
        fun a ha => div_nonneg (hw a (Finset.mem_insert_of_mem ha)) hS_pos.le
      have hw'_sum : ∑ a ∈ s', w' a = 1 := by
        dsimp [w']
        rw [← Finset.sum_div, div_self hS_pos.ne']
      let B : E →ₗ[ℝ] E := ∑ a ∈ s', w' a • A a
      have hB_det : c ≤ B.det := ih hw'_nn hw'_sum
        (fun a ha => hA_symm a (Finset.mem_insert_of_mem ha))
        (fun a ha => hA_pos a (Finset.mem_insert_of_mem ha))
        (fun a ha => hA_det a (Finset.mem_insert_of_mem ha))
      have hB_symm : B.IsSymmetric := by
        intro u v
        dsimp [B]
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_sum,
          real_inner_smul_left, real_inner_smul_right]
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [hA_symm a (Finset.mem_insert_of_mem ha) u v]
      have hB_pos : ∀ u : E, 0 ≤ inner ℝ u (B u) := by
        intro u
        dsimp [B]
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, real_inner_smul_right]
        exact Finset.sum_nonneg fun a ha =>
          mul_nonneg (hw'_nn a ha) (hA_pos a (Finset.mem_insert_of_mem ha) u)
      have hSB : S • B = ∑ a ∈ s', w a • A a := by
        dsimp [B, w']
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [smul_smul, mul_div_cancel₀ _ hS_pos.ne']
      rw [← hSB]
      exact det_add_smul_ge_of_det_ge
        (hA_symm a₀ (Finset.mem_insert_self a₀ s')) hB_symm hn
        (hA_pos a₀ (Finset.mem_insert_self a₀ s')) hB_pos
        hc hw₀ hS_pos.le hw_sum (hA_det a₀ (Finset.mem_insert_self a₀ s')) hB_det

/-!
### 3. Orthogonal $\mathbb{K}$-Structures & BCG Lemma B.3 ($\mathbb{K} \in \{\mathbb{R}, \mathbb{C}, \mathbb{H}\}$)
-/

/-- `IsOrthogonalKStructure d J` packages a family $J : \mathrm{Fin}\,d \to (E \to_l[\mathbb{R}] E)$
of orthogonal endomorphisms representing the division algebra multiplication on $T_x \mathbb{K}\mathbf{H}^m$
for the associative division algebras $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}, \mathbb{H}\}$
($d \in \{1, 2, 4\}$):
1. $J_0 = \mathrm{LinearMap.id}$,
2. Each $J_r$ is an orthogonal transformation ($\langle J_r u, J_r v \rangle = \langle u, v \rangle$), and
3. Distinct basis elements are pointwise orthogonal ($\langle J_r u, J_s u \rangle = 0$ for $r \ne s$).
As noted in [Ruan 2024, Remark after Cor. 2.4 & §3.1], such a structure exists for $d \in \{1, 2, 4\}$
but does **not** exist globally on $T_x \mathbb{O}\mathbf{H}^2$ for $d = 8$. -/
structure IsOrthogonalKStructure (d : ℕ) [NeZero d] (J : Fin d → (E →ₗ[ℝ] E)) : Prop where
  zero_eq_id : J 0 = LinearMap.id
  inner_map_map : ∀ (r : Fin d) (u v : E), inner ℝ (J r u) (J r v) = inner ℝ u v
  inner_orthogonal : ∀ {r s : Fin d}, r ≠ s → ∀ u : E, inner ℝ (J r u) (J s u) = 0

namespace IsOrthogonalKStructure

variable {d : ℕ} [NeZero d] {J : Fin d → (E →ₗ[ℝ] E)}

omit [FiniteDimensional ℝ E] in
theorem norm_map (hJ : IsOrthogonalKStructure d J) (r : Fin d) (u : E) :
    ‖J r u‖ = ‖u‖ := by
  have hsq : ‖J r u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hJ.inner_map_map r u u, real_inner_self_eq_norm_sq]
  have h := congr_arg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

theorem adjoint_comp_self (hJ : IsOrthogonalKStructure d J) (r : Fin d) :
    (J r).adjoint.comp (J r) = LinearMap.id := by
  ext u
  apply ext_inner_right ℝ
  intro v
  simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.adjoint_inner_left]
  exact hJ.inner_map_map r u v

theorem det_sq_eq_one (hJ : IsOrthogonalKStructure d J) (r : Fin d) :
    (J r).det ^ 2 = 1 := by
  have h := congr_arg LinearMap.det (hJ.adjoint_comp_self r)
  rw [LinearMap.det_comp, det_adjoint, LinearMap.det_id] at h
  linarith [sq ((J r).det)]

omit [NeZero d] in
/-- The rank-one outer product $(J_r u) \otimes (J_r u)^*$ equals the orthogonal conjugate
$J_r \circ_l (u \otimes u^*) \circ_l J_r^*$. -/
theorem selfOuter_map_eq_conj (r : Fin d) (u : E) :
    selfOuter (J r u) = (J r).comp ((selfOuter u).comp (J r).adjoint) := by
  ext v
  simp only [selfOuter_apply, LinearMap.comp_apply, map_smul, LinearMap.adjoint_inner_right]

/-- The orthogonal projection $\pi_u = \sum_{r=0}^{d-1} (J_r u) \otimes (J_r u)^*$ onto the
$d$-dimensional $\mathbb{K}$-line $\mathbb{K} \cdot u$. -/
def kLineProj (J : Fin d → (E →ₗ[ℝ] E)) (u : E) : E →ₗ[ℝ] E :=
  ∑ r : Fin d, selfOuter (J r u)

/-- Every $\pi_u = \mathrm{kLineProj}\,J\,u$ constructed from an `IsOrthogonalKStructure`
satisfies `IsKLineProjection d u (kLineProj J u)`. -/
theorem isKLineProjection_kLineProj (hJ : IsOrthogonalKStructure d J)
    {u : E} (hu : ‖u‖ = 1) :
    IsKLineProjection d u (kLineProj J u) where
  norm_u := hu
  isSymmetric := by
    intro v w
    unfold kLineProj
    simp only [LinearMap.sum_apply, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun r _ => isSymmetric_selfOuter (J r u) v w
  idempotent := by
    ext v
    change kLineProj J u (kLineProj J u v) = kLineProj J u v
    unfold kLineProj
    simp only [LinearMap.sum_apply, selfOuter_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 1
    rw [Finset.sum_eq_single r]
    · rw [hJ.inner_map_map r u u, real_inner_self_eq_norm_sq, hu, one_pow, one_smul]
    · intro s _ hs_ne
      rw [hJ.inner_orthogonal hs_ne u, zero_smul]
    · intro hr
      exact False.elim (hr (Finset.mem_univ r))
  apply_u := by
    unfold kLineProj
    simp only [LinearMap.sum_apply, selfOuter_apply]
    rw [Finset.sum_eq_single 0]
    · rw [hJ.zero_eq_id, LinearMap.id_apply, real_inner_self_eq_norm_sq, hu, one_pow, one_smul]
    · intro r _ hr0
      have h0 : inner ℝ (J r u) u = 0 := by
        have h1 := hJ.inner_orthogonal hr0 u
        rwa [hJ.zero_eq_id, LinearMap.id_apply] at h1
      rw [h0, zero_smul]
    · intro h0
      exact False.elim (h0 (Finset.mem_univ 0))
  trace_eq := by
    unfold kLineProj
    rw [map_sum]
    have h_tr : ∀ r : Fin d, LinearMap.trace ℝ E (selfOuter (J r u)) = 1 := by
      intro r
      rw [trace_selfOuter, hJ.norm_map r u, hu, one_pow]
    simp [h_tr]

/-- **Ruan's Property (P2) (`sub_busemannCovariance_eq_sum_conjugate`)**:
For an orthogonal $\mathbb{K}$-structure $J_0 = \mathrm{id}, J_1, \dots, J_{d-1}$, the difference
$\widehat{H} - H$ between the average $\mathbb{K}$-line projection $\widehat{H}$ and the Busemann
covariance $H$ is the sum of the $d - 1$ orthogonal conjugates $J_r \circ H \circ J_r^*$ ($r \ne 0$). -/
theorem sub_busemannCovariance_eq_sum_conjugate
    (hJ : IsOrthogonalKStructure d J)
    {α : Type*} (s : Finset α) (w : α → ℝ) (u : α → E) :
    rankOneLineCovariance s w (fun a => kLineProj J (u a)) - busemannCovariance s w u =
      ∑ r ∈ (Finset.univ : Finset (Fin d)).erase 0,
        (J r).comp ((busemannCovariance s w u).comp (J r).adjoint) := by
  have h_full : rankOneLineCovariance s w (fun a => kLineProj J (u a)) =
      ∑ r : Fin d, (J r).comp ((busemannCovariance s w u).comp (J r).adjoint) := by
    ext v
    simp only [rankOneLineCovariance, kLineProj, busemannCovariance,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      map_sum, map_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [selfOuter_map_eq_conj, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [h_full, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin d)),
    hJ.zero_eq_id]
  have hid_adj : (LinearMap.id : E →ₗ[ℝ] E).adjoint = LinearMap.id := by
    ext x
    apply ext_inner_right ℝ
    intro y
    rw [LinearMap.adjoint_inner_left, LinearMap.id_apply, LinearMap.id_apply]
  rw [hid_adj, LinearMap.comp_id, LinearMap.id_comp, add_sub_cancel_left]

/-- **BCG Lemma B.3 / Ruan Eq. (17) (`det_sub_div_ge_det_of_orthogonal_conjugates`)**:
For an orthogonal $\mathbb{K}$-structure with $d \ge 2$ ($\mathbb{C}\mathbf{H}^m$ or $\mathbb{H}\mathbf{H}^m$)
and non-negative weights $w$,
$$\det H \le \det\left(\left(\frac{1}{d - 1 : \mathbb{R}}\right) \bullet (\widehat{H} - H)\right).$$ -/
theorem det_sub_div_ge_det_of_orthogonal_conjugates
    (hJ : IsOrthogonalKStructure d J) (hd : 2 ≤ d)
    (hn : Module.finrank ℝ E = n)
    {α : Type*} (s : Finset α) {w : α → ℝ} (hw : ∀ a ∈ s, 0 ≤ w a) (u : α → E) :
    let H := busemannCovariance s w u
    let H_hat := rankOneLineCovariance s w (fun a => kLineProj J (u a))
    H.det ≤ ((1 / ((d : ℝ) - 1)) • (H_hat - H)).det := by
  intro H H_hat
  have hd1_pos : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := Nat.cast_le.mpr hd
    linarith
  let S_idx : Finset (Fin d) := (Finset.univ : Finset (Fin d)).erase 0
  have hS_card : (S_idx.card : ℝ) = (d : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega), Nat.cast_one]
  let A : Fin d → (E →ₗ[ℝ] E) := fun r => (J r).comp (H.comp (J r).adjoint)
  have hH_symm : H.IsSymmetric := isSymmetric_busemannCovariance s w u
  have hH_pos : ∀ v : E, 0 ≤ inner ℝ v (H v) := inner_busemannCovariance_nonneg s hw u
  have hH_det_nn : 0 ≤ H.det := det_nonneg_of_inner_nonneg hH_symm hn hH_pos
  have hA_symm : ∀ r ∈ S_idx, (A r).IsSymmetric := by
    intro r _ v z
    simp only [A, LinearMap.comp_apply]
    rw [← LinearMap.adjoint_inner_right (J r) _ z,
      hH_symm ((J r).adjoint v) ((J r).adjoint z)]
    exact LinearMap.adjoint_inner_left (J r) _ v
  have hA_pos : ∀ r ∈ S_idx, ∀ v : E, 0 ≤ inner ℝ v (A r v) := by
    intro r _ v
    simp only [A, LinearMap.comp_apply]
    rw [← LinearMap.adjoint_inner_left]
    exact hH_pos ((J r).adjoint v)
  have hA_det : ∀ r ∈ S_idx, H.det ≤ (A r).det := by
    intro r _
    dsimp [A]
    rw [LinearMap.det_comp, LinearMap.det_comp, det_adjoint]
    have hsq := hJ.det_sq_eq_one r
    have h_eq : (J r).det * (H.det * (J r).det) = H.det := by
      calc
        (J r).det * (H.det * (J r).det) = ((J r).det ^ 2) * H.det := by ring
        _ = H.det := by rw [hsq, one_mul]
    exact h_eq.ge
  let ω : Fin d → ℝ := fun _ => 1 / ((d : ℝ) - 1)
  have hω_nn : ∀ r ∈ S_idx, 0 ≤ ω r := fun _ _ => by positivity
  have hω_sum : ∑ r ∈ S_idx, ω r = 1 := by
    dsimp [ω]
    rw [Finset.sum_const, nsmul_eq_mul, hS_card, mul_one_div_cancel hd1_pos.ne']
  have h_sum_eq : ∑ r ∈ S_idx, ω r • A r = (1 / ((d : ℝ) - 1)) • (H_hat - H) := by
    dsimp [H_hat, H, A, ω, S_idx]
    rw [hJ.sub_busemannCovariance_eq_sum_conjugate s w u, Finset.smul_sum]
  rw [← h_sum_eq]
  exact det_sum_smul_ge_of_forall_det_ge S_idx hω_nn hω_sum hA_symm hn hA_pos hH_det_nn hA_det

end IsOrthogonalKStructure

/-!
### 4. BCG Lemma B.4 & Rank-One Determinant Inequality Synthesis
-/

/-- **Unconditional AM–GM Bound on $\det((I - H)/(n - 1))$ (`det_id_sub_div_ge_det`)**:
For any symmetric positive-semidefinite operator $H : E \to_l[\mathbb{R}] E$ on an $n$-dimensional
real inner product space ($n \ge 2$) with $\operatorname{Tr}(H) = 1$,
$$\det H \le \det\left(\left(\frac{1}{n - 1 : \mathbb{R}}\right) \bullet (\mathrm{LinearMap.id} - H)\right).$$
*Proof*: For each eigenvalue $\lambda_i$ of $H$, $1 - \lambda_i = \sum_{j \ne i} \lambda_j$, so
by the AM–GM inequality on the $n - 1$ eigenvalues $\{\lambda_j\}_{j \ne i}$,
$\left(\frac{1 - \lambda_i}{n - 1}\right)^{n - 1} \ge \prod_{j \ne i} \lambda_j$. Multiplying over
all $i \in \mathrm{Fin}\,n$ yields $\det((I - H)/(n - 1))^{n - 1} \ge (\det H)^{n - 1}$. -/
theorem det_id_sub_div_ge_det
    {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (hn2 : 2 ≤ n)
    (hpos : ∀ u : E, 0 ≤ inner ℝ u (H u))
    (htr : LinearMap.trace ℝ E H = 1) :
    H.det ≤ ((1 / ((n : ℝ) - 1)) • (LinearMap.id - H)).det := by
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn2
    linarith
  have hn1_nat_pos : 0 < n - 1 := by omega
  let μ := hH.eigenvalues hn
  have hμ_nn : ∀ i : Fin n, 0 ≤ μ i := eigenvalues_nonneg_of_inner_nonneg hH hn hpos
  have hμ_sum : ∑ i : Fin n, μ i = 1 := by
    rw [← trace_eq_sum_eigenvalues hH hn, htr]
  have h_det_H : H.det = ∏ i : Fin n, μ i := by
    have hd := hH.det_eq_prod_eigenvalues hn
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hd
    exact hd
  have h_det_sub : ((1 / ((n : ℝ) - 1)) • (LinearMap.id - H)).det =
      ∏ i : Fin n, ((1 - μ i) / ((n : ℝ) - 1)) := by
    rw [LinearMap.det_smul, hn]
    change (1 / ((n : ℝ) - 1)) ^ n * LinearMap.det (1 - H) = _
    rw [det_one_sub_eq_prod_eigenvalues hH hn]
    have h_const : (1 / ((n : ℝ) - 1)) ^ n = ∏ _i : Fin n, (1 / ((n : ℝ) - 1)) := by
      simp
    rw [h_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  have hμ_le_one : ∀ i : Fin n, μ i ≤ 1 := by
    intro i
    rw [← hμ_sum]
    exact Finset.single_le_sum (fun j _ => hμ_nn j) (Finset.mem_univ i)
  have h_each : ∀ i : Fin n,
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, μ j ≤
        ((1 - μ i) / ((n : ℝ) - 1)) ^ (n - 1) := by
    intro i
    let s_i := (Finset.univ : Finset (Fin n)).erase i
    have hs_card : (s_i.card : ℝ) = (n : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
        Nat.cast_sub (by omega), Nat.cast_one]
    let w : Fin n → ℝ := fun _ => 1 / ((n : ℝ) - 1)
    have hw_nn : ∀ j ∈ s_i, 0 ≤ w j := fun _ _ => by positivity
    have hw_sum : ∑ j ∈ s_i, w j = 1 := by
      dsimp [w]
      rw [Finset.sum_const, nsmul_eq_mul, hs_card, mul_one_div_cancel hn1_pos.ne']
    have h_amgm := Real.geom_mean_le_arith_mean_weighted s_i w μ hw_nn hw_sum (fun j _ => hμ_nn j)
    have h_lhs_nn : 0 ≤ ∏ j ∈ s_i, μ j ^ w j :=
      Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hμ_nn j) _
    have h_pow := pow_le_pow_left₀ h_lhs_nn h_amgm (n - 1)
    have h_lhs_eq : (∏ j ∈ s_i, μ j ^ w j) ^ (n - 1) = ∏ j ∈ s_i, μ j := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← Real.rpow_natCast (μ j ^ w j) (n - 1), ← Real.rpow_mul (hμ_nn j)]
      have hexp : w j * ((n - 1 : ℕ) : ℝ) = 1 := by
        dsimp [w]
        rw [Nat.cast_sub (by omega), Nat.cast_one, one_div_mul_cancel hn1_pos.ne']
      rw [hexp, Real.rpow_one]
    have h_sum_erase : ∑ j ∈ s_i, μ j = 1 - μ i := by
      have h1 := Finset.add_sum_erase (Finset.univ : Finset (Fin n)) μ (Finset.mem_univ i)
      linarith
    have h_rhs_eq : ∑ j ∈ s_i, w j * μ j = (1 - μ i) / ((n : ℝ) - 1) := by
      dsimp [w]
      rw [← Finset.mul_sum, h_sum_erase, one_div_mul_eq_div]
    rwa [h_lhs_eq, h_rhs_eq] at h_pow
  have h_prod_erase :
      (∏ i : Fin n, ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, μ j) =
        (∏ j : Fin n, μ j) ^ (n - 1) := by
    have h_mul :
        (∏ i : Fin n, μ i) *
          (∏ i : Fin n, ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, μ j) =
        (∏ i : Fin n, μ i) * (∏ j : Fin n, μ j) ^ (n - 1) := by
      rw [← Finset.prod_mul_distrib]
      have h_inner : ∀ i : Fin n,
          μ i * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, μ j = ∏ j : Fin n, μ j :=
        fun i => Finset.mul_prod_erase Finset.univ μ (Finset.mem_univ i)
      simp only [h_inner, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    by_cases h0 : (∏ i : Fin n, μ i) = 0
    · rw [Finset.prod_eq_zero_iff] at h0
      rcases h0 with ⟨i₀, _, hi₀⟩
      have h_rhs0 : (∏ j : Fin n, μ j) ^ (n - 1) = 0 := by
        rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hi₀, zero_pow hn1_nat_pos.ne']
      have h_lhs0 : (∏ i : Fin n, ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, μ j) = 0 := by
        have h_exists : ∃ i₁ : Fin n, i₁ ≠ i₀ := by
          by_contra h_all
          simp only [not_exists, not_ne_iff] at h_all
          have hcard : Fintype.card (Fin n) ≤ 1 :=
            Fintype.card_le_one_iff.mpr (fun a b => (h_all a).trans (h_all b).symm)
          rw [Fintype.card_fin] at hcard
          omega
        rcases h_exists with ⟨i₁, hi₁⟩
        refine Finset.prod_eq_zero (Finset.mem_univ i₁) ?_
        exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hi₁.symm, Finset.mem_univ i₀⟩) hi₀
      rw [h_lhs0, h_rhs0]
    · exact mul_left_cancel₀ h0 h_mul
  have h_pow_ineq :
      (∏ i : Fin n, μ i) ^ (n - 1) ≤
        (∏ i : Fin n, ((1 - μ i) / ((n : ℝ) - 1))) ^ (n - 1) := by
    rw [← h_prod_erase, ← Finset.prod_pow]
    exact finset_prod_le_prod_of_nonneg Finset.univ
      (fun i _ => Finset.prod_nonneg (fun j _ => hμ_nn j))
      (fun i _ => h_each i)
  rw [h_det_H, h_det_sub]
  exact le_of_pow_le_pow_left₀ hn1_nat_pos.ne'
    (Finset.prod_nonneg fun i _ => div_nonneg (sub_nonneg.mpr (hμ_le_one i)) hn1_pos.le)
    h_pow_ineq

/-- **Log-Concavity Splitting of `rankOneHessianOperator` ([Ruan 2024, Eq. (14)] / `[BCG1, Lemme B.3]`)**:
For $n \ge 2$ and $d \ge 2$, if $I - H$ and $\widehat{H} - H$ are symmetric positive-semidefinite,
then
$$((n + d - 2 : \mathbb{R}))^n \cdot
  \det\left(\left(\frac{1}{n - 1 : \mathbb{R}}\right) \bullet (I - H)\right)^{\frac{n - 1}{n + d - 2}} \cdot
  \det\left(\left(\frac{1}{d - 1 : \mathbb{R}}\right) \bullet (\widehat{H} - H)\right)^{\frac{d - 1}{n + d - 2}}
  \le \det(I - 2H + \widehat{H}).$$ -/
theorem det_rankOneHessianOperator_ge
    {H H_hat : E →ₗ[ℝ] E} (hn : Module.finrank ℝ E = n)
    (hn2 : 2 ≤ n) {d : ℕ} (hd2 : 2 ≤ d)
    (hIH_symm : ((LinearMap.id : E →ₗ[ℝ] E) - H).IsSymmetric)
    (hHH_symm : (H_hat - H).IsSymmetric)
    (hIH_pos : ∀ u : E, 0 ≤ inner ℝ u (((LinearMap.id : E →ₗ[ℝ] E) - H) u))
    (hHH_pos : ∀ u : E, 0 ≤ inner ℝ u ((H_hat - H) u)) :
    let h₀ : ℝ := (n : ℝ) + (d : ℝ) - 2
    let p : ℝ := ((n : ℝ) - 1) / h₀
    let q : ℝ := ((d : ℝ) - 1) / h₀
    let A : E →ₗ[ℝ] E := (1 / ((n : ℝ) - 1)) • (LinearMap.id - H)
    let B : E →ₗ[ℝ] E := (1 / ((d : ℝ) - 1)) • (H_hat - H)
    h₀ ^ n * (A.det ^ p * B.det ^ q) ≤ (rankOneHessianOperator H H_hat).det := by
  intro h₀ p q A B
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn2; linarith
  have hd1_pos : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := Nat.cast_le.mpr hd2; linarith
  have hh₀_pos : 0 < h₀ := by
    change 0 < (n : ℝ) + (d : ℝ) - 2
    linarith
  have hp_nn : 0 ≤ p := div_nonneg hn1_pos.le hh₀_pos.le
  have hq_nn : 0 ≤ q := div_nonneg hd1_pos.le hh₀_pos.le
  have hpq : p + q = 1 := by
    dsimp [p, q, h₀]
    rw [← add_div, show (n : ℝ) - 1 + ((d : ℝ) - 1) = (n : ℝ) + (d : ℝ) - 2 by ring,
      div_self hh₀_pos.ne']
  have hA_symm : A.IsSymmetric := by
    intro u v
    change inner ℝ (A u) v = inner ℝ u (A v)
    dsimp only [A]
    rw [LinearMap.smul_apply, LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right,
      hIH_symm u v]
  have hB_symm : B.IsSymmetric := by
    intro u v
    change inner ℝ (B u) v = inner ℝ u (B v)
    dsimp only [B]
    rw [LinearMap.smul_apply, LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right,
      hHH_symm u v]
  have hA_pos : ∀ u : E, 0 ≤ inner ℝ u (A u) := by
    intro u
    dsimp only [A]
    rw [LinearMap.smul_apply, real_inner_smul_right]
    exact mul_nonneg (by positivity) (hIH_pos u)
  have hB_pos : ∀ u : E, 0 ≤ inner ℝ u (B u) := by
    intro u
    dsimp only [B]
    rw [LinearMap.smul_apply, real_inner_smul_right]
    exact mul_nonneg (by positivity) (hHH_pos u)
  have h_log_conc := det_weighted_add_ge_rpow_mul_rpow hA_symm hB_symm hn hA_pos hB_pos hp_nn hq_nn hpq
  have h_decomp : rankOneHessianOperator H H_hat = h₀ • (p • A + q • B) := by
    rw [rankOneHessianOperator_eq_add_sub]
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

/-- **Algebraic Combination of `[Ruan 2024, Eqs. (14), (16), (17)]` (`associative_rankOne_det_ineq`)**:
Suppose $n \ge 2$, $d \ge 2$, and $H, \widehat{H} : E \to_l[\mathbb{R}] E$ satisfy:
1. $I - H$ and $\widehat{H} - H$ are symmetric positive-semidefinite,
2. $0 < \det H$,
3. $\det\left(\frac{I - H}{n - 1}\right) \ge (\sqrt{n})^{-n \cdot \frac{n + d - 2}{n - 1}} (\det H)^{\frac{n - d}{2(n - 1)}}$
   (`[Ruan 2024, Eq. (16)]` / `[BCG1, Lemme B.4]`), and
4. $\det\left(\frac{\widehat{H} - H}{d - 1}\right) \ge \det H$
   (`[Ruan 2024, Eq. (17)]` / `[BCG1, Lemme B.3]`).
Then $\det(I - 2H + \widehat{H}) > 0$ and $(H, \widehat{H})$ satisfies the sharp rank-one
determinant inequality (`[Ruan 2024, Eq. (13)]`):
$$\frac{\sqrt{\det H}}{\det(I - 2H + \widehat{H})} \le \left(\frac{\sqrt{n}}{n + d - 2}\right)^n.$$ -/
theorem associative_rankOne_det_ineq
    {H H_hat : E →ₗ[ℝ] E} (hn : Module.finrank ℝ E = n)
    (hn2 : 2 ≤ n) {d : ℕ} (hd2 : 2 ≤ d) (_hnd : d ≤ n)
    (hIH_symm : ((LinearMap.id : E →ₗ[ℝ] E) - H).IsSymmetric)
    (hHH_symm : (H_hat - H).IsSymmetric)
    (hIH_pos : ∀ u : E, 0 ≤ inner ℝ u (((LinearMap.id : E →ₗ[ℝ] E) - H) u))
    (hHH_pos : ∀ u : E, 0 ≤ inner ℝ u ((H_hat - H) u))
    (hdetH_pos : 0 < H.det)
    (h_part1 :
      (Real.sqrt (n : ℝ)) ^ (-((n : ℝ) * ((n : ℝ) + (d : ℝ) - 2) / ((n : ℝ) - 1))) *
        H.det ^ (((n : ℝ) - (d : ℝ)) / (2 * ((n : ℝ) - 1))) ≤
        ((1 / ((n : ℝ) - 1)) • (LinearMap.id - H)).det)
    (h_part2 : H.det ≤ ((1 / ((d : ℝ) - 1)) • (H_hat - H)).det) :
    0 < (rankOneHessianOperator H H_hat).det ∧
    Real.sqrt H.det / (rankOneHessianOperator H H_hat).det ≤
      (Real.sqrt (n : ℝ) / ((n : ℝ) + (d : ℝ) - 2)) ^ n := by
  let h₀ : ℝ := (n : ℝ) + (d : ℝ) - 2
  let p : ℝ := ((n : ℝ) - 1) / h₀
  let q : ℝ := ((d : ℝ) - 1) / h₀
  let A : E →ₗ[ℝ] E := (1 / ((n : ℝ) - 1)) • (LinearMap.id - H)
  let B : E →ₗ[ℝ] E := (1 / ((d : ℝ) - 1)) • (H_hat - H)
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
  have h_log := det_rankOneHessianOperator_ge hn hn2 hd2 hIH_symm hHH_symm hIH_pos hHH_pos
  dsimp only at h_log
  have h_lhs1_pos :
      0 < (Real.sqrt (n : ℝ)) ^ (-((n : ℝ) * h₀ / ((n : ℝ) - 1))) *
        H.det ^ (((n : ℝ) - (d : ℝ)) / (2 * ((n : ℝ) - 1))) :=
    mul_pos (Real.rpow_pos_of_pos hsqrt_pos _) (Real.rpow_pos_of_pos hdetH_pos _)
  have hA_rpow :
      ((Real.sqrt (n : ℝ)) ^ (-((n : ℝ) * h₀ / ((n : ℝ) - 1))) *
        H.det ^ (((n : ℝ) - (d : ℝ)) / (2 * ((n : ℝ) - 1)))) ^ p ≤ A.det ^ p :=
    Real.rpow_le_rpow h_lhs1_pos.le h_part1 hp_pos.le
  have hB_rpow : H.det ^ q ≤ B.det ^ q :=
    Real.rpow_le_rpow hdetH_pos.le h_part2 hq_pos.le
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
            (Real.rpow_nonneg (h_lhs1_pos.le.trans h_part1) p)
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

/-- **Real Hyperbolic ($d = 1$) Rank-One Determinant Inequality (`real_rankOne_det_ineq`)**:
For any operator $H : E \to_l[\mathbb{R}] E$ on an $n$-dimensional real inner product space
($n \ge 2$) with $\det H > 0$ satisfying the $d = 1$ ($s = 1/2$) case of `[BCG1, Lemme B.4]` /
`[Ruan 2024, Eq. (16)]`:
$$(\sqrt{n})^{-n} \sqrt{\det H} \le \det\left(\left(\frac{1}{n - 1 : \mathbb{R}}\right) \bullet (\mathrm{LinearMap.id} - H)\right),$$
where $\widehat{H} = H$ ($d = 1$), we have $\det(I - 2H + H) = \det(I - H) > 0$ and
$$\frac{\sqrt{\det H}}{\det(I - 2H + H)} \le \left(\frac{\sqrt{n}}{n - 1}\right)^n.$$ -/
theorem real_rankOne_det_ineq
    {H : E →ₗ[ℝ] E} (hn : Module.finrank ℝ E = n) (hn2 : 2 ≤ n)
    (hdetH_pos : 0 < H.det)
    (h_b4 :
      (Real.sqrt (n : ℝ)) ^ (-(n : ℝ)) * Real.sqrt H.det ≤
        ((1 / ((n : ℝ) - 1)) • (LinearMap.id - H)).det) :
    0 < (rankOneHessianOperator H H).det ∧
    Real.sqrt H.det / (rankOneHessianOperator H H).det ≤
      (Real.sqrt (n : ℝ) / ((n : ℝ) - 1)) ^ n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn2; linarith
  have hW_eq : rankOneHessianOperator H H = LinearMap.id - H := rankOneHessianOperator_self H
  have h_lower :
      ((n : ℝ) - 1) ^ n * ((Real.sqrt (n : ℝ)) ^ (-(n : ℝ)) * Real.sqrt H.det) ≤
        (rankOneHessianOperator H H).det := by
    calc
      ((n : ℝ) - 1) ^ n * ((Real.sqrt (n : ℝ)) ^ (-(n : ℝ)) * Real.sqrt H.det)
        ≤ ((n : ℝ) - 1) ^ n * ((1 / ((n : ℝ) - 1)) • (LinearMap.id - H)).det :=
          mul_le_mul_of_nonneg_left h_b4 (pow_nonneg hn1_pos.le n)
      _ = (rankOneHessianOperator H H).det := by
          rw [hW_eq, LinearMap.det_smul, hn, div_pow, one_pow, ← mul_assoc,
            mul_one_div_cancel (pow_ne_zero n hn1_pos.ne'), one_mul]
  have h_lower_pos :
      0 < ((n : ℝ) - 1) ^ n * ((Real.sqrt (n : ℝ)) ^ (-(n : ℝ)) * Real.sqrt H.det) :=
    mul_pos (pow_pos hn1_pos n)
      (mul_pos (Real.rpow_pos_of_pos hsqrt_pos _) (Real.sqrt_pos.mpr hdetH_pos))
  have hW_pos : 0 < (rankOneHessianOperator H H).det :=
    lt_of_lt_of_le h_lower_pos h_lower
  refine ⟨hW_pos, ?_⟩
  rw [div_le_iff₀ hW_pos]
  have h_rpow_sqrt : (Real.sqrt (n : ℝ)) ^ (-(n : ℝ)) = ((Real.sqrt (n : ℝ)) ^ n)⁻¹ := by
    rw [Real.rpow_neg hsqrt_pos.le, Real.rpow_natCast]
  calc
    Real.sqrt H.det
      = (Real.sqrt (n : ℝ) / ((n : ℝ) - 1)) ^ n *
          (((n : ℝ) - 1) ^ n * ((Real.sqrt (n : ℝ)) ^ (-(n : ℝ)) * Real.sqrt H.det)) := by
        rw [h_rpow_sqrt, div_pow]
        field_simp [hn1_pos.ne', hsqrt_pos.ne']
    _ ≤ (Real.sqrt (n : ℝ) / ((n : ℝ) - 1)) ^ n * (rankOneHessianOperator H H).det :=
        mul_le_mul_of_nonneg_left h_lower (by positivity)

omit [FiniteDimensional ℝ E] in
/-- For sub-probability weights $w_a \ge 0$, $\sum_{a \in t} w_a \le 1$, and unit-bounded vectors
$\|u_a\| \le 1$, the operator $I - \mathrm{busemannCovariance}\,t\,w\,u$ is positive-semidefinite. -/
theorem id_sub_busemannCovariance_nonneg
    {α : Type*} (t : Finset α)
    {w : α → ℝ} (hw : ∀ a ∈ t, 0 ≤ w a) (hw_sum : ∑ a ∈ t, w a ≤ 1)
    {u : α → E} (hu : ∀ a ∈ t, ‖u a‖ ≤ 1) (x : E) :
    0 ≤ inner ℝ x (((LinearMap.id : E →ₗ[ℝ] E) - busemannCovariance t w u) x) := by
  rw [LinearMap.sub_apply, LinearMap.id_apply, inner_sub_right, sub_nonneg,
    inner_busemannCovariance_eq_sum, real_inner_self_eq_norm_sq]
  calc
    ∑ a ∈ t, w a * inner ℝ (u a) x ^ 2
      ≤ ∑ a ∈ t, w a * ‖x‖ ^ 2 := by
        refine Finset.sum_le_sum fun a ha => ?_
        apply mul_le_mul_of_nonneg_left _ (hw a ha)
        have hcs := abs_real_inner_le_norm (u a) x
        have hle : |inner ℝ (u a) x| ≤ ‖x‖ := by
          calc
            |inner ℝ (u a) x| ≤ ‖u a‖ * ‖x‖ := hcs
            _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (hu a ha) (norm_nonneg x)
            _ = ‖x‖ := one_mul _
        have hsq := pow_le_pow_left₀ (abs_nonneg _) hle 2
        rwa [sq_abs] at hsq
    _ = (∑ a ∈ t, w a) * ‖x‖ ^ 2 := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hw_sum (sq_nonneg _)
    _ = ‖x‖ ^ 2 := one_mul _

/-- **Master Associative Rank-One BCG Jacobian Bound (`associative_rankOne_bcg_jacobian_bound`)**:
For an associative division algebra structure `IsOrthogonalKStructure d J` ($d \in \{2, 4\}$, i.e.,
$\mathbb{C}\mathbf{H}^m$ or $\mathbb{H}\mathbf{H}^m$) on an $n$-dimensional real inner product space
($n \ge d \ge 2$), if $D_F : E \to_l[\mathbb{R}] E$ satisfies the implicit function theorem equation
$$(I - 2H + \widehat{H}) \circ D_F = s \cdot H_y$$
where $H = \mathrm{busemannCovariance}\,t\,w\,u$, $\widehat{H} = \mathrm{rankOneLineCovariance}\,t\,w\,(\mathrm{kLineProj}\,J \circ u)$,
and $H_y = \mathrm{busemannCrossOperator}\,1\,t\,w\,v\,u$ for unit vectors $u_a$ ($\|u_a\| = 1$),
unit-bounded source gradients $v_a$ ($\|v_a\| \le 1$), and probability weights $w_a$,
and $H$ satisfies `[BCG1, Lemme B.4]` / `[Ruan 2024, Eq. (16)]`, then:
$$|\det D_F| \le \left(\frac{s}{n + d - 2}\right)^n.$$ -/
theorem associative_rankOne_bcg_jacobian_bound
    {d : ℕ} [NeZero d] {J : Fin d → (E →ₗ[ℝ] E)}
    (hJ : IsOrthogonalKStructure d J) (hd2 : 2 ≤ d) (hnd : d ≤ n)
    (hn : Module.finrank ℝ E = n)
    {α : Type*} (t : Finset α)
    {w : α → ℝ} (hw : ∀ a ∈ t, 0 ≤ w a) (hw_sum : ∑ a ∈ t, w a = 1)
    {u v : α → E}
    (hu : ∀ a ∈ t, ‖u a‖ = 1)
    (hv : ∀ a ∈ t, ‖v a‖ ≤ 1)
    {s : ℝ} (hs : 0 ≤ s)
    {D_F : E →ₗ[ℝ] E}
    (h_ift :
      (rankOneHessianOperator
        (busemannCovariance t w u)
        (rankOneLineCovariance t w (fun a => IsOrthogonalKStructure.kLineProj J (u a)))).comp D_F =
      s • busemannCrossOperator 1 t w v u)
    (hdetH_pos : 0 < (busemannCovariance t w u).det)
    (h_part1 :
      (Real.sqrt (n : ℝ)) ^ (-((n : ℝ) * ((n : ℝ) + (d : ℝ) - 2) / ((n : ℝ) - 1))) *
        (busemannCovariance t w u).det ^ (((n : ℝ) - (d : ℝ)) / (2 * ((n : ℝ) - 1))) ≤
        ((1 / ((n : ℝ) - 1)) • (LinearMap.id - busemannCovariance t w u)).det) :
    |D_F.det| ≤ (s / ((n : ℝ) + (d : ℝ) - 2)) ^ n := by
  have hn2 : 2 ≤ n := le_trans hd2 hnd
  have hh₀_pos : (0 : ℝ) < (n : ℝ) + (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn2
    have : (2 : ℝ) ≤ d := Nat.cast_le.mpr hd2
    linarith
  let H := busemannCovariance t w u
  let H_X := busemannCovariance t w v
  let H_hat := rankOneLineCovariance t w (fun a => IsOrthogonalKStructure.kLineProj J (u a))
  have hπ : ∀ a ∈ t, IsKLineProjection d (u a) (IsOrthogonalKStructure.kLineProj J (u a)) :=
    fun a ha => hJ.isKLineProjection_kLineProj (hu a ha)
  have hH_symm : H.IsSymmetric := isSymmetric_busemannCovariance t w u
  have hHX_symm : H_X.IsSymmetric := isSymmetric_busemannCovariance t w v
  have hIH_symm : ((LinearMap.id : E →ₗ[ℝ] E) - H).IsSymmetric := by
    intro x y
    simp only [LinearMap.sub_apply, inner_sub_left, inner_sub_right, LinearMap.id_apply]
    rw [hH_symm x y]
  have hIH_pos : ∀ x : E, 0 ≤ inner ℝ x (((LinearMap.id : E →ₗ[ℝ] E) - H) x) :=
    id_sub_busemannCovariance_nonneg t hw hw_sum.le (fun a ha => (hu a ha).le)
  have hHH_symm : (H_hat - H).IsSymmetric := by
    intro x y
    simp only [LinearMap.sub_apply, inner_sub_left, inner_sub_right]
    rw [isSymmetric_rankOneLineCovariance t w hπ x y, hH_symm x y]
  have hHH_pos : ∀ x : E, 0 ≤ inner ℝ x ((H_hat - H) x) :=
    sub_busemannCovariance_nonneg t hw hπ
  have h_part2 : H.det ≤ ((1 / ((d : ℝ) - 1)) • (H_hat - H)).det :=
    hJ.det_sub_div_ge_det_of_orthogonal_conjugates hd2 hn t hw u
  obtain ⟨hW_pos, h_rankOne_ineq⟩ :=
    associative_rankOne_det_ineq hn hn2 hd2 hnd hIH_symm hHH_symm hIH_pos hHH_pos
      hdetH_pos h_part1 h_part2
  have hCS : ∀ x y : E, |inner ℝ (busemannCrossOperator 1 t w v u x) y| ≤
      Real.sqrt (inner ℝ x (H_X x)) * Real.sqrt (inner ℝ y (H y)) := by
    intro x y
    simpa [one_mul] using abs_inner_busemannCrossOperator_le zero_le_one t hw v u x y
  exact abs_det_le_div_entropy_pow_of_rankOne_det_ineq hn (by omega) hs hh₀_pos h_ift hW_pos
    hHX_symm hH_symm
    (inner_busemannCovariance_nonneg t hw v)
    (inner_busemannCovariance_nonneg t hw u)
    (trace_busemannCovariance_le_one t hw hw_sum.le hv)
    hCS h_rankOne_ineq

end BCG.RankOne
