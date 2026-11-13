# Formalization Report: The Besson–Courtois–Gallot Barycenter Method and Ruan's Octonionic Repair in Lean 4 (`formalized-barycenter-methods`)

**Repository:** `https://github.com/psuarezserrato/formalized-barycenter-methods`  
**Toolchain:** Lean 4 (`v4.35.0`) + Mathlib (`v4.35.0`) + vendored `DifferentialGeometry` (`v0.1.5`, 509 modules, D. Yang et al.)  
**Verification Status:** `lake build` passing · **5,247 LOC** across **12 `.lean` modules** · **27 `leanblueprint` DAG nodes** (19 proved theorems `#1CAC78` + 8 definitions `#B0ECA3`, **100% green**) · **227 tracked Lean declarations** · **0 `sorryAx`** · **0 custom axioms**  
**Executive Report PDF:** [`report/bcg_executive_report.pdf`](report/bcg_executive_report.pdf) (5 pages: 4 body pages + 1 portrait appendix page)  
**Blueprint Website & Dependency Graph:** [`blueprint/web/index.html`](blueprint/web/index.html) · [`blueprint/web/dep_graph_document.html`](blueprint/web/dep_graph_document.html) · [`report/blueprint_dep_graph.pdf`](report/blueprint_dep_graph.pdf) · [`blueprint/print/print.pdf`](blueprint/print/print.pdf)

---

## 1. Executive Summary & Repository Structure

This core repository contains a machine-checked Lean 4 formalization of the **Besson–Courtois–Gallot (BCG, 1995)** and **Souto (2008)** barycenter method and **Yuping Ruan's (2024)** repair of the octonionic gap across:
1. **Smooth real hyperbolic manifolds** $\mathbb{R}\mathbf{H}^n$ (both the global volume-entropy inequality $|\deg(f)| \cdot n^n \mathrm{Vol}(Y) \le h(X)^n \mathrm{Vol}(X)$ and the infinitesimal Mostow/BCG rigidity characterization of the equality case),
2. **Associative rank-one locally symmetric spaces** $\mathbb{K}\mathbf{H}^m$ ($\mathbb{K} \in \{\mathbb{R}, \mathbb{C}, \mathbb{H}\}$, real dimension $n = d m$, fiber dimension $d = \dim_{\mathbb{R}} \mathbb{K} \in \{1, 2, 4\}$, volume entropy $h_0 = n + d - 2$), including BCG's Appendix B Minkowski–Ky Fan log-concavity proof, and
3. **Yuping Ruan's (2024) resolution of the 22-year octonionic gap** on the 16-dimensional **Cayley hyperbolic plane** $\mathbb{O}\mathbf{H}^2$ ($n = 16, d = 8, h_0 = 22$, `arXiv:2408.13375`), repairing the failure of BCG's global orthogonal conjugation property $\mathrm{(P2)}$ (observed by Chris Connell around 2002) via a perturbed log-concavity decomposition $(I - H - U_\alpha) + (\widehat{H} - H + U_\alpha)$ adapted to two orthogonal 8-dimensional Cayley lines $\mathcal{C}ay(v_1) \oplus \mathcal{C}ay(v_2)$.

Every theorem in the library compiles with **0 `sorryAx`** and depends solely on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

### Companion Journal Subrepositories

Two downstream formalization repositories are mounted as Git submodules and depend on this library via Lake:
- **[`rcd-entropy-degree-rigidity/`](rcd-entropy-degree-rigidity/)** — Non-smooth extension to closed orientable non-collapsed $\mathsf{RCD}(K, N)$ and Alexandrov spaces via Sturm's $\mathsf{CAT}(0)$ barycenter and CMMP orientation currents (*"Entropy-degree rigidity for non-collapsed $\mathsf{RCD}$ spaces"*).
- **[`alexandrov-entropy-degree-applications/`](alexandrov-entropy-degree-applications/)** — Degree-theoretic bridge (§5), Theorem 1.1, Remark 1.15, and all 14 geometric/topological consequences (*"The entropy-degree theorem for Alexandrov spaces"*, `arXiv:2606.30403`).

---

## 2. Formalization Methodology & Architectural Highlights

### 2.1. Lorentzian Duality for the Hyperbolic Barycenter (`NaturalMap.lean`, Step 1)
In the hyperboloid model $\mathbb{H}^n = \mathrm{Hyperboloid}\,E \subset \mathbb{R} \times E$, the exponentiated Busemann function is a linear Lorentzian pairing $e^{B_\xi(p)} = p.\mathrm{time} - \langle \xi, p.\mathrm{space} \rangle_E = -\langle (1, \xi), p \rangle_{1,n}$. Consequently, for non-negative weights $w : \iota \to \mathbb{R}$ on $\xi : \iota \to S(E)$, the weighted Busemann functional is
$$\mathcal{B}_w(p) = \sum_{i \in \iota} w_i e^{B_{\xi_i}(p)} = \tau \cosh d_{\mathbb{H}^n}(p_0, p), \qquad \tau = \sqrt{T^2 - \|V\|_E^2}, \quad p_0 = (\tau^{-1} T, \tau^{-1} V),$$
giving global existence and uniqueness of the minimizer $p_0 = \mathrm{hyperboloidBarycenter}(w, \xi, hw)$ (`busemannFunctional_unique_min`), closed-form $C^\infty$ smoothness (`contMDiff_hyperboloidBarycenterMap`), and $\mathrm{Isometry}(\mathbb{H}^n)$-equivariance (`hyperboloidBarycenter_isometry`) without needing an abstract manifold Implicit Function Theorem.

### 2.2. Canonical Riemannian Metric Gauge & Exact Radial Cancellation (`JacobianBound.lean`, Step 2)
We construct an explicit linear isometry $\Phi_p : (T_p \mathbb{H}^n, g_p) \xrightarrow{\sim} (E, \langle \cdot, \cdot \rangle_E)$ (`metricGauge`, `metricGaugeEquiv`) and prove that the radial derivative $\dot{\tau}$ of $Z(w)/\|Z(w)\|_{\mathcal{L}}$ cancels identically against the $-p.\mathrm{time}^{-2}\langle p.\mathrm{space}, \cdot \rangle^2$ term of $g_p$ (`riemannianMetric_inner_lorentzNormalization_deriv`). In this orthonormal gauge, the Riemannian differential $D^{\mathrm{Riem}} F_s(x)$ equals the weighted Busemann cross-operator `busemannCrossOperator` on the nose (`riemannianBarycenterDifferential_eq_busemannCrossOperator`), yielding $|\det D^{\mathrm{Riem}} F_s(x)| \le (s/n)^n$.

### 2.3. Spectral Inverse Square Root & Infinitesimal Rigidity (`BarycenterOperator.lean`, `EqualityCase.lean`, Step 3)
We prove Souto's bilinear Cauchy–Schwarz determinant bound $|\det L| \le c^n \sqrt{\det H_1}\sqrt{\det H_2}$ (`abs_det_le_of_abs_inner_le`) via spectral inverse square roots $D_i = H_i^{-1/2}$ (`exists_inv_sqrt_of_det_pos`). For the equality case $|\det L| = (c/n)^n$ (`isotropic_and_norm_eq_of_abs_det_eq_div_dim_pow`), strict concavity of $\log z \le z - 1$ forces all eigenvalues of $H_1, H_2$, and the normalized Gram operator $T = (n(c/n)^2)^{-1}(L^* \circ L)$ to equal $1/n$, proving $H_1 = H_2 = \frac{1}{n}\mathrm{id}_E$ and $L^* \circ L = (c/n)^2 \mathrm{id}_E$.

### 2.4. General Rank-One Busemann Hessian & Associative $\mathbb{K}$-Structures (`BusemannHessian.lean`, `AssociativeCase.lean`, Steps 4A–4B)
For $\widetilde{M} = \mathbb{K}\mathbf{H}^m$, the single-direction Busemann Hessian $W(u, \pi_u) = I - 2(u \otimes u^*) + \pi_u$ has eigenvalues $0$ on $\mathbb{R} u$, $2$ on $\mathbb{K} u \ominus \mathbb{R} u$ ($\dim = d - 1$), and $1$ on $(\mathbb{K} u)^\perp$ ($\dim = n - d$), satisfying the Riccati equation $W(u, \pi_u)^2 = 4(\pi_u - u \otimes u^*) + (I - \pi_u)$ (`sq_rankOneSingleHessian_eq_jacobi`) and $\mathrm{Tr}(W(u, \pi_u)) = n + d - 2$ (`trace_rankOneSingleHessian`). Using simultaneous diagonalization via $A^{-1/2}$, we prove BCG Lemma B.2 ($\det(p A + q B) \ge (\det A)^p (\det B)^q$, `det_weighted_add_ge_rpow_mul_rpow`) and BCG Lemmas B.3–B.4 (`associative_rankOne_det_ineq`) for any associative orthogonal $\mathbb{K}$-structure `IsOrthogonalKStructure d J`.

### 2.5. Ruan's 2024 Octonionic Repair on $\mathbb{O}\mathbf{H}^2$ (`OctonionicCase.lean`, Step 4C)
Because octonion multiplication is non-associative, no global `IsOrthogonalKStructure 8 J` exists on $T_x \mathbb{O}\mathbf{H}^2 \cong \mathbb{R}^{16}$. Following Ruan (2024):
- We formalize `IsLocalCayleyLineStructure d J` on each individual 8-dimensional Cayley line $V = \mathcal{C}ay(v_i) \cong \mathbb{R}^8$ (Ruan's $\mathrm{(P2')}$), polarize quadratic forms to prove $\sum_{r=0}^7 J_r A J_r^* = \lambda \mathrm{id}_V$, and use cyclic trace invariance to prove $\mathrm{Tr}(A) = \lambda$ (`trace_cayleyLine_eq_eigenvalue`) and Ruan's Eq. (28): $\det(\lambda I_8 - A) \ge 7^8 \det A$ (`det_lambda_sub_cayleyBlock_eight_ge`).
- We prove Case 1 ($\alpha = 0$, $2\lambda_1 \le \lambda, 2\mu_1 \le \mu$) via Schur complement monotonicity (`cayley_schur_monotone_finset_prod`, `cayley_case1_det_bound`), and Case 2 ($\alpha \in [1-\sqrt{2/3}, 0.266]$) via the 8-dimensional reverse AM–GM inequality $7^7 \prod_{i=0}^7 x_i \le (\sum_{i \ne 0} x_i)^7 x_0$ (`reverse_amgm_eight_dim`, Ruan Lemma 3.6) and cubic endpoint bounds (`octonionic_alpha_parameter_bounds`, `cayley_case2_step2_endpoint_bound`).
- Combining Ruan's perturbed splitting $I - 2H + \widehat{H} = (I - H - U_\alpha) + (\widehat{H} - H + U_\alpha)$ with log-concavity ($p = 15/22, q = 7/22$) yields Ruan's Proposition 3.1 (`octonionic_rankOne_det_ineq`), Corollary 3.8 (`octonionic_rankOne_bcg_jacobian_bound`), and Theorem 1.1 (`octonionic_bcg_main_theorem`):
  $$\frac{\sqrt{\det H}}{\det(I - 2H + \widehat{H})} \le \left(\frac{2}{11}\right)^{16}, \qquad |\det D_F| \le \left(\frac{s}{22}\right)^{16}, \qquad |\deg(f)| \cdot 22^{16} \mathrm{Vol}(Y) \le c_X^{16} \mathrm{Vol}(X).$$

---

## 3. Module-by-Module Catalog of the 12 Core Lean 4 Files (5,247 LOC)

| Module | LOC | Blueprint Nodes & Key Theorems |
| :--- | :---: | :--- |
| [`BCG/LinearAlgebra/TraceDet.lean`](BCG/LinearAlgebra/TraceDet.lean) | 165 | `thm_spectral_trace_det`, `thm_trace_det_amgm` (`det_le_trace_div_dim_pow`, `mul_sqrt_det_le_of_trace_le_one`) |
| [`BCG/LinearAlgebra/BarycenterOperator.lean`](BCG/LinearAlgebra/BarycenterOperator.lean) | 286 | `thm_gram_det`, `thm_bilinear_cs_det` (`exists_inv_sqrt_of_det_pos`, `abs_det_le_div_dim_pow_of_abs_inner_le`) |
| [`BCG/Entropy/VolumeEntropy.lean`](BCG/Entropy/VolumeEntropy.lean) | 104 | `def_critical_exponent`, `thm_critical_exponent_invariance` (`criticalExponent_eq`) |
| [`BCG/Hyperbolic/BarycenterFunctional.lean`](BCG/Hyperbolic/BarycenterFunctional.lean) | 282 | `def_hyperboloid_busemann`, `thm_hyperboloid_busemann_hessian`, `def_busemann_operators`, `thm_busemann_cross_det` |
| [`BCG/Hyperbolic/NaturalMap.lean`](BCG/Hyperbolic/NaturalMap.lean) | 572 | **Step 1:** `def_hyperboloid_barycenter`, `thm_hyperboloid_barycenter_props` (`hyperboloidBarycenter`, `busemannFunctional_unique_min`, `hyperboloidBarycenter_isometry`) |
| [`BCG/Hyperbolic/JacobianBound.lean`](BCG/Hyperbolic/JacobianBound.lean) | 575 | **Step 2:** `def_riemannian_barycenter_diff`, `thm_hyperbolic_jacobian_bound` (`metricGaugeEquiv`, `hasFDerivAt_barycenter_space`, `abs_det_riemannianBarycenterDifferential_le`) |
| [`BCG/Rigidity/EqualityCase.lean`](BCG/Rigidity/EqualityCase.lean) | 433 | **Step 3:** `thm_hyperbolic_rigidity` (`isotropic_and_norm_eq_of_abs_det_eq_div_dim_pow`, `measureReal_image_eq_integral_abs_det_fderiv`, `riemannianBarycenterDifferential_rigidity`) |
| [`BCG/RankOne/BusemannHessian.lean`](BCG/RankOne/BusemannHessian.lean) | 599 | **Step 4A:** `def_rank_one_invariants`, `thm_rank_one_hessian_reduction` (`sq_rankOneSingleHessian_eq_jacobi`, `abs_det_le_div_entropy_pow_of_rankOne_det_ineq`, `isotropic_of_abs_det_eq_div_entropy_pow`) |
| [`BCG/RankOne/AssociativeCase.lean`](BCG/RankOne/AssociativeCase.lean) | 985 | **Step 4B:** `thm_bcg_lemma_b2`, `def_orthogonal_k_structure`, `thm_associative_rank_one` (`det_weighted_add_ge_rpow_mul_rpow`, `associative_rankOne_det_ineq`, `associative_rankOne_bcg_jacobian_bound`) |
| [`BCG/RankOne/OctonionicCase.lean`](BCG/RankOne/OctonionicCase.lean) | 848 | **Step 4C:** `def_local_cayley_structure`, `thm_cayley_block_bounds`, `thm_ruan_cases_1_and_2`, `thm_ruan_prop_3_1` (`trace_cayleyLine_eq_eigenvalue`, `det_lambda_sub_cayleyBlock_eight_ge`, `cayley_case1_det_bound`, `reverse_amgm_eight_dim`, `octonionic_rankOne_det_ineq`, `octonionic_rankOne_bcg_jacobian_bound`) |
| [`BCG/MainTheorem.lean`](BCG/MainTheorem.lean) | 366 | `thm_bcg_global_integration`, `thm_master_hyperbolic_bcg`, `thm_master_rank_one_bcg` (`hyperbolic_bcg_natural_map_main_theorem`, `hyperbolic_bcg_natural_map_rigidity`, `rankOne_bcg_main_theorem`, `octonionic_bcg_main_theorem`) |
| [`BCG.lean`](BCG.lean) | 32 | Top-level library root importing all 11 core submodules |
