import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Busemann
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BusemannHessian
import DifferentialGeometry.Geometry.CenterOfMass.Basic
import BCG.Hyperbolic.BarycenterFunctional

/-!
# Hyperbolic Barycenter Map, Busemann Cocycle Equivariance, and Quotient Descent

This file constructs the smooth hyperbolic natural map $F_s : \tilde{X} \to \mathrm{Hyperboloid}(E)$
via the Souto–Besson–Courtois–Gallot Busemann barycenter functional, proves its $C^\infty$
smoothness, first-order critical-point vanishing, isometry equivariance under the Busemann cocycle,
and canonical descent to quotient manifolds $\Gamma \backslash \tilde{X} \to \Gamma \backslash \mathbb{H}^n$.

## Main Results
1. **Busemann Cocycle under Hyperbolic Isometries** (`expHyperboloidBusemann_isometry`,
   `hyperboloidBusemann_isometry`):
   For any isometry $f : \mathrm{Hyperboloid}(E) \simeq_i \mathrm{Hyperboloid}(F)$ and boundary
   point $\xi \in S(E)$,
   $$c(f, \xi) \cdot \exp(B_{\partial f(\xi)}(f(y))) = \exp(B_\xi(y)), \qquad
     B_{\partial f(\xi)}(f(y)) = B_\xi(y) - \log c(f, \xi),$$
   where $c(f, \xi) = (\mathrm{lorentzExtension}\,f\,(1, \xi)).1 > 0$.
2. **Hyperbolic Distance Formula for the Busemann Barycenter Functional**
   (`busemannFunctional_eq_lorentzNorm_mul_cosh_dist`, `busemannFunctional_min`,
   `busemannFunctional_unique_min`):
   For any weights $w : \iota \to \mathbb{R}$ and boundary directions $\xi : \iota \to S(E)$ whose
   Lorentz resultant $Z(w, \xi) = (\sum_i w_i, \sum_i w_i \xi_i)$ is future-timelike
   ($\|\sum_i w_i \xi_i\| < \sum_i w_i$), the Busemann functional
   $$\mathcal{B}_{w, \xi}(y) = \sum_{i \in \iota} w_i \exp(B_{\xi_i}(y))$$
   satisfies the exact hyperbolic distance identity
   $$\mathcal{B}_{w, \xi}(y) = \tau(w, \xi) \cdot \cosh\big(\mathrm{dist}(\mathrm{hyperboloidBarycenter}(w, \xi), \, y)\big),$$
   and `hyperboloidBarycenter w ξ` is its unique global minimizer on `Hyperboloid E`.
3. **$C^\infty$ Smoothness and Critical-Point Vanishing**
   (`contMDiff_busemannFunctional`, `gradientFun_busemannFunctional_eq_zero`,
   `mvfderiv_busemannFunctional_eq_zero`, `contMDiff_hyperboloidBarycenterMap`):
   At $p = \mathrm{hyperboloidBarycenter}(w, \xi)$, $\nabla \mathcal{B}_{w, \xi}(p) = 0$ and
   $d\mathcal{B}_{w, \xi}(p) = 0$. Moreover, for any $C^\infty$ family of weights $x \mapsto w(x)$
   on a smooth manifold $X$, the induced barycenter map $x \mapsto \mathrm{hyperboloidBarycenter}(w(x), \xi)$
   is $C^\infty$ smooth.
4. **Isometry Equivariance and Quotient Descent**
   (`busemannFunctional_isometry`, `hyperboloidBarycenter_isometry`,
   `equivariantQuotientMap`, `continuous_equivariantQuotientMap`):
   The barycenter map is equivariant under hyperbolic isometries and descends via `Quotient.lift`
   to a continuous map between the orbit quotients $\Gamma \backslash \tilde{X} \to \Gamma \backslash \mathrm{Hyperboloid}(E)$.
-/

noncomputable section

open Finset BigOperators
open scoped Manifold ContDiff Topology

namespace BCG.Hyperbolic

open DifferentialGeometry
open DifferentialGeometry.Hyperboloid
open DifferentialGeometry.Geometry.Operator

section BusemannCocycle

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The exponential Busemann height $\exp(B_\xi(y))$ equals the Lorentz null height
$y.\mathrm{time} - \langle \xi, y.\mathrm{space} \rangle$. -/
theorem expHyperboloidBusemann_eq (ξ : Metric.sphere (0 : E) 1) (y : Hyperboloid E) :
    expHyperboloidBusemann ξ y = y.time - inner ℝ (ξ : E) y.space := by
  unfold expHyperboloidBusemann hyperboloidBusemann
  have hpos : 0 < y.time - inner ℝ (ξ : E) y.space := by
    have hξ : ‖(ξ : E)‖ = 1 := norm_eq_of_mem_sphere ξ
    have hi : inner ℝ (ξ : E) y.space ≤ ‖y.space‖ := by
      simpa only [hξ, one_mul] using real_inner_le_norm (ξ : E) y.space
    have ht : ‖y.space‖ < y.time := by
      nlinarith [y.time_sq, y.time_pos, norm_nonneg y.space]
    linarith
  exact Real.exp_log hpos

/-- The exponential Busemann height is strictly positive everywhere on `Hyperboloid E`. -/
theorem expHyperboloidBusemann_pos (ξ : Metric.sphere (0 : E) 1) (y : Hyperboloid E) :
    0 < expHyperboloidBusemann ξ y :=
  Real.exp_pos _

/-- The exponential Busemann height is the negative Lorentz pairing with the null vector $(1, \xi)$. -/
theorem expHyperboloidBusemann_eq_neg_lorentzForm
    (ξ : Metric.sphere (0 : E) 1) (y : Hyperboloid E) :
    expHyperboloidBusemann ξ y = -lorentzForm E (1, (ξ : E)) (y.time, y.space) := by
  rw [expHyperboloidBusemann_eq, lorentzForm_apply]
  ring

/-- The Busemann cocycle factor $c(f, \xi) = (\mathrm{lorentzExtension}\,f\,(1, \xi)).1 > 0$
associated to a hyperbolic isometry $f : \mathrm{Hyperboloid}(E) \simeq_i \mathrm{Hyperboloid}(F)$
and a boundary direction $\xi \in S(E)$. -/
def busemannCocycleFactor (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (ξ : Metric.sphere (0 : E) 1) : ℝ :=
  (lorentzExtension f (1, (ξ : E))).1

theorem busemannCocycleFactor_pos (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (ξ : Metric.sphere (0 : E) 1) :
    0 < busemannCocycleFactor f ξ :=
  lorentzExtension_sphere_time_pos f ξ

/-- **Multiplicative Busemann Cocycle Identity for Exponential Busemann Heights**:
$$c(f, \xi) \cdot \exp(B_{\partial f(\xi)}(f(y))) = \exp(B_\xi(y)).$$ -/
theorem expHyperboloidBusemann_isometry
    (f : Hyperboloid E ≃ᵢ Hyperboloid F) (ξ : Metric.sphere (0 : E) 1) (y : Hyperboloid E) :
    busemannCocycleFactor f ξ *
      expHyperboloidBusemann (boundaryHomeomorph f ξ) (f y) =
        expHyperboloidBusemann ξ y := by
  rw [expHyperboloidBusemann_eq_neg_lorentzForm, expHyperboloidBusemann_eq_neg_lorentzForm]
  have h_ext := lorentzExtension_apply f y
  have h_sph := lorentzExtension_sphere_eq_smul_boundaryHomeomorph f ξ
  have h_iso := (lorentzExtension f).map_app (y.time, y.space) (1, (ξ : E))
  rw [h_ext, h_sph] at h_iso
  simp only [lorentzForm_apply, Prod.smul_fst, Prod.smul_snd, real_inner_smul_left,
    smul_eq_mul, busemannCocycleFactor] at h_iso ⊢
  linarith

/-- **Additive Busemann Cocycle Identity on `Hyperboloid E`**:
$$B_{\partial f(\xi)}(f(y)) = B_\xi(y) - \log c(f, \xi).$$ -/
theorem hyperboloidBusemann_isometry
    (f : Hyperboloid E ≃ᵢ Hyperboloid F) (ξ : Metric.sphere (0 : E) 1) (y : Hyperboloid E) :
    hyperboloidBusemann (boundaryHomeomorph f ξ) (f y) =
      hyperboloidBusemann ξ y - Real.log (busemannCocycleFactor f ξ) := by
  have h_exp := expHyperboloidBusemann_isometry f ξ y
  have hc_pos : 0 < busemannCocycleFactor f ξ := busemannCocycleFactor_pos f ξ
  have h_log := congrArg Real.log h_exp
  unfold expHyperboloidBusemann at h_log
  rw [Real.log_mul hc_pos.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at h_log
  linarith

end BusemannCocycle

section FutureTimelikeNormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Lorentz norm $\tau(z) = \sqrt{z_0^2 - \|z_{\mathrm{space}}\|^2}$ of a vector
$z \in \mathbb{R} \times E$. -/
def lorentzNorm (z : ℝ × E) : ℝ :=
  Real.sqrt (z.1 ^ 2 - ‖z.2‖ ^ 2)

omit [InnerProductSpace ℝ E] in
theorem lorentzNorm_sq_pos {z : ℝ × E} (hz : ‖z.2‖ < z.1) :
    0 < z.1 ^ 2 - ‖z.2‖ ^ 2 := by
  nlinarith [norm_nonneg z.2]

omit [InnerProductSpace ℝ E] in
theorem lorentzNorm_pos {z : ℝ × E} (hz : ‖z.2‖ < z.1) :
    0 < lorentzNorm z :=
  Real.sqrt_pos.mpr (lorentzNorm_sq_pos hz)

omit [InnerProductSpace ℝ E] in
theorem lorentzNorm_sq {z : ℝ × E} (hz : ‖z.2‖ < z.1) :
    (lorentzNorm z) ^ 2 = z.1 ^ 2 - ‖z.2‖ ^ 2 :=
  Real.sq_sqrt (lorentzNorm_sq_pos hz).le

/-- Radial projection of a future-timelike vector $z = (t, v) \in \mathbb{R} \times E$
($\|v\| < t$) onto the upper sheet `Hyperboloid E`. -/
def normalizeFuture (z : ℝ × E) (hz : ‖z.2‖ < z.1) : Hyperboloid E where
  time := (lorentzNorm z)⁻¹ * z.1
  space := (lorentzNorm z)⁻¹ • z.2
  time_pos := mul_pos (inv_pos.mpr (lorentzNorm_pos hz)) (lt_of_le_of_lt (norm_nonneg _) hz)
  time_sq_sub_inner_self := by
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have h := lorentzNorm_sq hz
    have hn := (lorentzNorm_pos hz).ne'
    field_simp [hn]
    nlinarith

@[simp]
theorem normalizeFuture_time (z : ℝ × E) (hz : ‖z.2‖ < z.1) :
    (normalizeFuture z hz).time = (lorentzNorm z)⁻¹ * z.1 := rfl

@[simp]
theorem normalizeFuture_space (z : ℝ × E) (hz : ‖z.2‖ < z.1) :
    (normalizeFuture z hz).space = (lorentzNorm z)⁻¹ • z.2 := rfl

/-- `normalizeFuture` is the composition of `ofSpace` with spatial scaling by `(lorentzNorm z)⁻¹`. -/
theorem normalizeFuture_eq_ofSpace (z : ℝ × E) (hz : ‖z.2‖ < z.1) :
    normalizeFuture z hz = ofSpace ((lorentzNorm z)⁻¹ • z.2) := by
  ext
  rfl

/-- **Exact Hyperbolic Distance Identity for Future-Timelike Pairings**:
$$z_0 \cdot y.\mathrm{time} - \langle z_{\mathrm{space}}, y.\mathrm{space} \rangle
  = \tau(z) \cdot \cosh\big(\mathrm{dist}(\mathrm{normalizeFuture}(z), \, y)\big).$$ -/
theorem lorentzPairing_eq_lorentzNorm_mul_cosh_dist
    (z : ℝ × E) (hz : ‖z.2‖ < z.1) (y : Hyperboloid E) :
    z.1 * y.time - inner ℝ z.2 y.space =
      lorentzNorm z * Real.cosh (dist (normalizeFuture z hz) y) := by
  rw [cosh_dist]
  dsimp [normalizeFuture]
  rw [real_inner_smul_left]
  have hne : lorentzNorm z ≠ 0 := (lorentzNorm_pos hz).ne'
  field_simp [hne]

@[simp]
theorem lorentzPairing_normalizeFuture_self (z : ℝ × E) (hz : ‖z.2‖ < z.1) :
    z.1 * (normalizeFuture z hz).time - inner ℝ z.2 (normalizeFuture z hz).space =
      lorentzNorm z := by
  rw [lorentzPairing_eq_lorentzNorm_mul_cosh_dist z hz, dist_self, Real.cosh_zero, mul_one]

/-- `normalizeFuture z hz` is a global minimizer of $y \mapsto z_0 y.\mathrm{time} - \langle z_{\mathrm{space}}, y.\mathrm{space} \rangle$. -/
theorem lorentzNorm_le_lorentzPairing
    (z : ℝ × E) (hz : ‖z.2‖ < z.1) (y : Hyperboloid E) :
    lorentzNorm z ≤ z.1 * y.time - inner ℝ z.2 y.space := by
  rw [lorentzPairing_eq_lorentzNorm_mul_cosh_dist z hz y]
  exact le_mul_of_one_le_right (lorentzNorm_pos hz).le (Real.one_le_cosh _)

/-- `normalizeFuture z hz` is the **unique** global minimizer of the Lorentz pairing on `Hyperboloid E`. -/
theorem eq_normalizeFuture_iff_lorentzPairing_eq
    (z : ℝ × E) (hz : ‖z.2‖ < z.1) (y : Hyperboloid E) :
    z.1 * y.time - inner ℝ z.2 y.space = lorentzNorm z ↔ y = normalizeFuture z hz := by
  rw [lorentzPairing_eq_lorentzNorm_mul_cosh_dist z hz y]
  have hpos : (lorentzNorm z) ≠ 0 := (lorentzNorm_pos hz).ne'
  constructor
  · intro h
    have hcosh : Real.cosh (dist (normalizeFuture z hz) y) = 1 := by
      apply mul_left_cancel₀ hpos
      linarith
    by_contra hne
    have hpos_d : 0 < dist (normalizeFuture z hz) y := dist_pos.mpr (Ne.symm hne)
    have hlt : Real.cosh 0 < Real.cosh (dist (normalizeFuture z hz) y) :=
      Real.cosh_lt_cosh.mpr (by simpa [abs_of_pos hpos_d] using hpos_d)
    rw [Real.cosh_zero, hcosh] at hlt
    exact lt_irrefl 1 hlt
  · rintro rfl
    rw [dist_self, Real.cosh_zero, mul_one]

end FutureTimelikeNormalization

section BusemannBarycenter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- The Souto–BCG Busemann barycenter functional on `Hyperboloid E`:
$$\mathcal{B}_{w, \xi}(y) = \sum_{i \in \iota} w_i \exp(B_{\xi_i}(y)).$$ -/
def busemannFunctional (w : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1) (y : Hyperboloid E) : ℝ :=
  ∑ i : ι, w i * expHyperboloidBusemann (ξ i) y

/-- The resultant Lorentz vector $Z(w, \xi) = \left(\sum_i w_i, \sum_i w_i \xi_i\right) \in \mathbb{R} \times E$. -/
def busemannLorentzVector (w : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1) : ℝ × E :=
  (∑ i : ι, w i, ∑ i : ι, w i • (ξ i : E))

@[simp]
theorem busemannLorentzVector_fst (w : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1) :
    (busemannLorentzVector w ξ).1 = ∑ i : ι, w i := rfl

@[simp]
theorem busemannLorentzVector_snd (w : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1) :
    (busemannLorentzVector w ξ).2 = ∑ i : ι, w i • (ξ i : E) := rfl

/-- For any two distinct boundary points $\xi_1 \ne \xi_2$ in $S(E)$ and positive weights
$a, b > 0$, we have $\|a \xi_1 + b \xi_2\| < a + b$. -/
theorem norm_add_smul_sphere_lt
    {ξ₁ ξ₂ : Metric.sphere (0 : E) 1} (hne : ξ₁ ≠ ξ₂)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ‖a • (ξ₁ : E) + b • (ξ₂ : E)‖ < a + b := by
  have h1 : ‖(ξ₁ : E)‖ = 1 := norm_eq_of_mem_sphere ξ₁
  have h2 : ‖(ξ₂ : E)‖ = 1 := norm_eq_of_mem_sphere ξ₂
  have hne_coe : (ξ₁ : E) ≠ (ξ₂ : E) := fun h => hne (Subtype.ext h)
  have hdiff_pos : 0 < ‖(ξ₁ : E) - (ξ₂ : E)‖ ^ 2 :=
    sq_pos_of_pos (norm_sub_pos_iff.mpr hne_coe)
  rw [norm_sub_sq_real, h1, h2] at hdiff_pos
  have h_inner_lt : inner ℝ (ξ₁ : E) (ξ₂ : E) < 1 := by linarith
  have hab : 0 < a * b * (1 - inner ℝ (ξ₁ : E) (ξ₂ : E)) :=
    mul_pos (mul_pos ha hb) (by linarith)
  have h_sq_lt : ‖a • (ξ₁ : E) + b • (ξ₂ : E)‖ ^ 2 < (a + b) ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos ha, abs_of_pos hb, h1, h2, real_inner_smul_left, real_inner_smul_right]
    linarith
  exact (sq_lt_sq₀ (norm_nonneg _) (by linarith)).mp h_sq_lt

/-- **Non-Atomic Support Criterion for Future-Timelike Busemann Resultant**:
If $w_k \ge 0$ for all $k \in \iota$ and there exist $i, j \in \iota$ with $w_i > 0$, $w_j > 0$,
and $\xi_i \ne \xi_j$, then the resultant Lorentz vector is strictly future-timelike:
$$\left\|\sum_{k \in \iota} w_k \xi_k\right\| < \sum_{k \in \iota} w_k.$$ -/
theorem norm_busemannVector_lt_sum_of_ne [DecidableEq ι]
    {w : ι → ℝ} (hw_nn : ∀ k : ι, 0 ≤ w k)
    {ξ : ι → Metric.sphere (0 : E) 1}
    {i j : ι} (hi : 0 < w i) (hj : 0 < w j) (hξ_ne : ξ i ≠ ξ j) :
    ‖∑ k : ι, w k • (ξ k : E)‖ < ∑ k : ι, w k := by
  have hij : i ≠ j := fun h => hξ_ne (congrArg ξ h)
  let s₁ := (Finset.univ : Finset ι).erase i
  have hj_mem : j ∈ s₁ := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  let s₂ := s₁.erase j
  have h_sum_vec : ∑ k : ι, w k • (ξ k : E) =
      (w i • (ξ i : E) + w j • (ξ j : E)) + ∑ k ∈ s₂, w k • (ξ k : E) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ hj_mem, add_assoc]
  have h_sum_wt : ∑ k : ι, w k = (w i + w j) + ∑ k ∈ s₂, w k := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ hj_mem, add_assoc]
  have h_rest : ‖∑ k ∈ s₂, w k • (ξ k : E)‖ ≤ ∑ k ∈ s₂, w k := by
    calc
      ‖∑ k ∈ s₂, w k • (ξ k : E)‖ ≤ ∑ k ∈ s₂, ‖w k • (ξ k : E)‖ := norm_sum_le _ _
      _ = ∑ k ∈ s₂, w k := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw_nn k),
          norm_eq_of_mem_sphere (ξ k), mul_one]
  rw [h_sum_vec, h_sum_wt]
  calc
    ‖(w i • (ξ i : E) + w j • (ξ j : E)) + ∑ k ∈ s₂, w k • (ξ k : E)‖
      ≤ ‖w i • (ξ i : E) + w j • (ξ j : E)‖ + ‖∑ k ∈ s₂, w k • (ξ k : E)‖ :=
        norm_add_le _ _
    _ < (w i + w j) + ∑ k ∈ s₂, w k :=
        add_lt_add_of_lt_of_le (norm_add_smul_sphere_lt hξ_ne hi hj) h_rest

/-- The Busemann barycenter functional equals the Lorentz pairing with `busemannLorentzVector w ξ`. -/
theorem busemannFunctional_eq_lorentzPairing
    (w : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1) (y : Hyperboloid E) :
    busemannFunctional w ξ y =
      (busemannLorentzVector w ξ).1 * y.time -
        inner ℝ (busemannLorentzVector w ξ).2 y.space := by
  unfold busemannFunctional busemannLorentzVector
  dsimp only
  rw [Finset.sum_mul, sum_inner, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [expHyperboloidBusemann_eq, real_inner_smul_left]
  ring

/-- The Busemann barycenter functional is $C^\infty$ smooth on `Hyperboloid E`. -/
theorem contMDiff_busemannFunctional (w : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (busemannFunctional w ξ) := by
  have h_eq : busemannFunctional w ξ =
      fun y : Hyperboloid E =>
        (busemannLorentzVector w ξ).1 * y.time -
          inner ℝ (busemannLorentzVector w ξ).2 y.space := by
    funext y
    exact busemannFunctional_eq_lorentzPairing w ξ y
  rw [h_eq]
  exact (contMDiff_const.mul contMDiff_time).sub
    ((innerSL ℝ (busemannLorentzVector w ξ).2).contDiff.contMDiff.comp contMDiff_space)

/-- The explicit hyperbolic barycenter of a future-timelike boundary distribution $(w, \xi)$
on `Hyperboloid E`. -/
def hyperboloidBarycenter (w : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i) : Hyperboloid E :=
  normalizeFuture (busemannLorentzVector w ξ) hw

/-- **Exact Hyperbolic Distance Representation of the Busemann Barycenter Functional**:
$$\mathcal{B}_{w, \xi}(y) = \tau(w, \xi) \cdot \cosh\big(\mathrm{dist}(\mathrm{hyperboloidBarycenter}(w, \xi), \, y)\big).$$ -/
theorem busemannFunctional_eq_lorentzNorm_mul_cosh_dist
    (w : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i) (y : Hyperboloid E) :
    busemannFunctional w ξ y =
      lorentzNorm (busemannLorentzVector w ξ) *
        Real.cosh (dist (hyperboloidBarycenter w ξ hw) y) := by
  rw [busemannFunctional_eq_lorentzPairing]
  exact lorentzPairing_eq_lorentzNorm_mul_cosh_dist (busemannLorentzVector w ξ) hw y

@[simp]
theorem busemannFunctional_hyperboloidBarycenter
    (w : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i) :
    busemannFunctional w ξ (hyperboloidBarycenter w ξ hw) =
      lorentzNorm (busemannLorentzVector w ξ) := by
  rw [busemannFunctional_eq_lorentzNorm_mul_cosh_dist w ξ hw, dist_self, Real.cosh_zero, mul_one]

/-- The normalized Busemann probability weights at the barycenter $p = \mathrm{hyperboloidBarycenter}(w, \xi)$:
$$\mu_i(w, \xi) = \frac{w_i \exp(B_{\xi_i}(p))}{\mathcal{B}_{w, \xi}(p)}.$$ -/
def barycenterProbWeight (w : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i) (i : ι) : ℝ :=
  w i * expHyperboloidBusemann (ξ i) (hyperboloidBarycenter w ξ hw) /
    busemannFunctional w ξ (hyperboloidBarycenter w ξ hw)

theorem barycenterProbWeight_nonneg {w : ι → ℝ} (hw_nn : ∀ i : ι, 0 ≤ w i)
    (ξ : ι → Metric.sphere (0 : E) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i) (i : ι) :
    0 ≤ barycenterProbWeight w ξ hw i := by
  unfold barycenterProbWeight
  rw [busemannFunctional_hyperboloidBarycenter]
  exact div_nonneg
    (mul_nonneg (hw_nn i) (expHyperboloidBusemann_pos _ _).le)
    (lorentzNorm_pos hw).le

/-- The normalized Busemann probability weights at the barycenter sum to $1$:
$$\sum_{i \in \iota} \mu_i(w, \xi) = 1.$$ -/
theorem sum_barycenterProbWeight_eq_one (w : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i) :
    ∑ i : ι, barycenterProbWeight w ξ hw i = 1 := by
  unfold barycenterProbWeight
  rw [← Finset.sum_div]
  change busemannFunctional w ξ (hyperboloidBarycenter w ξ hw) /
    busemannFunctional w ξ (hyperboloidBarycenter w ξ hw) = 1
  rw [busemannFunctional_hyperboloidBarycenter]
  exact div_self (lorentzNorm_pos hw).ne'

/-- **Global Minimization Property of `hyperboloidBarycenter`**:
For every $y \in \mathrm{Hyperboloid}(E)$,
$\mathcal{B}_{w, \xi}(\mathrm{hyperboloidBarycenter}(w, \xi)) \le \mathcal{B}_{w, \xi}(y)$. -/
theorem busemannFunctional_min
    (w : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i) (y : Hyperboloid E) :
    busemannFunctional w ξ (hyperboloidBarycenter w ξ hw) ≤ busemannFunctional w ξ y := by
  rw [busemannFunctional_hyperboloidBarycenter, busemannFunctional_eq_lorentzPairing]
  exact lorentzNorm_le_lorentzPairing (busemannLorentzVector w ξ) hw y

/-- **Uniqueness of the Global Minimizer of `busemannFunctional`**:
Any point $y \in \mathrm{Hyperboloid}(E)$ satisfying $\forall z, \mathcal{B}_{w, \xi}(y) \le \mathcal{B}_{w, \xi}(z)$
is equal to `hyperboloidBarycenter w ξ hw`. -/
theorem busemannFunctional_unique_min
    (w : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i) {y : Hyperboloid E}
    (hy : ∀ z : Hyperboloid E, busemannFunctional w ξ y ≤ busemannFunctional w ξ z) :
    y = hyperboloidBarycenter w ξ hw := by
  have hle : busemannFunctional w ξ y ≤ busemannFunctional w ξ (hyperboloidBarycenter w ξ hw) :=
    hy (hyperboloidBarycenter w ξ hw)
  have hge : busemannFunctional w ξ (hyperboloidBarycenter w ξ hw) ≤ busemannFunctional w ξ y :=
    busemannFunctional_min w ξ hw y
  have heq : busemannFunctional w ξ y = lorentzNorm (busemannLorentzVector w ξ) := by
    linarith [busemannFunctional_hyperboloidBarycenter w ξ hw]
  rw [busemannFunctional_eq_lorentzPairing] at heq
  exact (eq_normalizeFuture_iff_lorentzPairing_eq (busemannLorentzVector w ξ) hw y).mp heq

/-- **First-Order Critical-Point Vanishing (Barycenter Gradient Equation)**:
At $p = \mathrm{hyperboloidBarycenter}(w, \xi)$, the Riemannian gradient of $\mathcal{B}_{w, \xi}$
vanishes identically:
$$\nabla \mathcal{B}_{w, \xi}(p) = 0 \in T_p(\mathrm{Hyperboloid}\,E).$$ -/
theorem gradientFun_busemannFunctional_eq_zero [FiniteDimensional ℝ E]
    (w : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i) :
    gradientFun riemannianMetric (busemannFunctional w ξ) (hyperboloidBarycenter w ξ hw) = 0 := by
  have hlocal : IsLocalMin (busemannFunctional w ξ) (hyperboloidBarycenter w ξ hw) :=
    Filter.Eventually.of_forall (busemannFunctional_min w ξ hw)
  have hdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (busemannFunctional w ξ)
      (hyperboloidBarycenter w ξ hw) :=
    (contMDiff_busemannFunctional w ξ).mdifferentiableAt (by simp)
  exact gradientFun_eq_zero_of_isLocalMin riemannianMetric hlocal hdiff

/-- **First-Order Critical-Point Vanishing (Barycenter Differential Equation)**:
At $p = \mathrm{hyperboloidBarycenter}(w, \xi)$, the Riemannian differential $d\mathcal{B}_{w, \xi}(p)$
vanishes on every tangent vector $v \in T_p(\mathrm{Hyperboloid}\,E)$. -/
theorem mvfderiv_busemannFunctional_eq_zero [FiniteDimensional ℝ E]
    (w : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i)
    (v : TangentSpace 𝓘(ℝ, E) (hyperboloidBarycenter w ξ hw)) :
    mvfderiv 𝓘(ℝ, E) (busemannFunctional w ξ) (hyperboloidBarycenter w ξ hw) v = 0 := by
  rw [← inner_gradientFun riemannianMetric (busemannFunctional w ξ)
    (hyperboloidBarycenter w ξ hw) v]
  rw [gradientFun_busemannFunctional_eq_zero w ξ hw]
  simp

/-- **$C^\infty$ Smoothness of the Hyperbolic Barycenter Natural Map**:
For any smooth manifold $X$ and any $C^\infty$ family of weights $w : X \to \iota \to \mathbb{R}$
satisfying the future-timelike condition $\|\sum_i w(x, i) \xi_i\| < \sum_i w(x, i)$ at every
$x \in X$, the natural map
$$x \mapsto \mathrm{hyperboloidBarycenter}(w(x), \xi, hw(x)) : X \to \mathrm{Hyperboloid}(E)$$
is $C^\infty$ smooth (`ContMDiff I 𝓘(ℝ, E) ∞`). -/
theorem contMDiff_hyperboloidBarycenterMap
    {E_X : Type*} [NormedAddCommGroup E_X] [NormedSpace ℝ E_X]
    {H_X : Type*} [TopologicalSpace H_X] {I : ModelWithCorners ℝ E_X H_X}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H_X X] [IsManifold I ∞ X]
    (w : X → ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1)
    (hw_smooth : ∀ i : ι, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => w x i))
    (hw : ∀ x : X, ‖∑ i : ι, w x i • (ξ i : E)‖ < ∑ i : ι, w x i) :
    ContMDiff I 𝓘(ℝ, E) ∞ (fun x : X => hyperboloidBarycenter (w x) ξ (hw x)) := by
  have h_eq : (fun x : X => hyperboloidBarycenter (w x) ξ (hw x)) =
      ofSpace ∘ (fun x : X =>
        (lorentzNorm (busemannLorentzVector (w x) ξ))⁻¹ •
          (busemannLorentzVector (w x) ξ).2) := by
    funext x
    exact normalizeFuture_eq_ofSpace (busemannLorentzVector (w x) ξ) (hw x)
  rw [h_eq]
  refine contMDiff_ofSpace.comp ?_
  have h_fst : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : X => ∑ i : ι, w x i) :=
    ContMDiff.sum fun i _ => hw_smooth i
  have h_snd : ContMDiff I 𝓘(ℝ, E) ∞ (fun x : X => ∑ i : ι, w x i • (ξ i : E)) :=
    ContMDiff.sum fun i _ => (hw_smooth i).smul contMDiff_const
  have h_diff_sq : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : X => (∑ i : ι, w x i) ^ 2 - ‖∑ i : ι, w x i • (ξ i : E)‖ ^ 2) :=
    (h_fst.pow 2).sub ((contDiff_norm_sq ℝ).contMDiff.comp h_snd)
  have h_norm : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : X => lorentzNorm (busemannLorentzVector (w x) ξ)) := by
    intro x
    exact (Real.contDiffAt_sqrt (lorentzNorm_sq_pos (hw x)).ne').contMDiffAt.comp x
      (h_diff_sq x)
  have h_inv : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : X => (lorentzNorm (busemannLorentzVector (w x) ξ))⁻¹) := by
    intro x
    exact (contDiffAt_inv ℝ (lorentzNorm_pos (hw x)).ne').contMDiffAt.comp x (h_norm x)
  exact h_inv.smul h_snd

end BusemannBarycenter

section EquivarianceAndQuotientDescent

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {ι : Type*} [Fintype ι]

/-- **Isometry Invariance of the Busemann Barycenter Functional under the Busemann Cocycle**:
If $f : \mathrm{Hyperboloid}(E) \simeq_i \mathrm{Hyperboloid}(F)$ is a hyperbolic isometry,
$e : \iota \simeq \iota$ is a permutation of the index set, $\xi'_{e(i)} = \partial f(\xi_i)$,
and the weights transform by the Busemann cocycle $w'(e(i)) = c(f, \xi_i) \cdot w_i$, then
$$\mathcal{B}_{w', \xi'}(f(y)) = \mathcal{B}_{w, \xi}(y).$$ -/
theorem busemannFunctional_isometry
    (f : Hyperboloid E ≃ᵢ Hyperboloid F) (e : ι ≃ ι)
    (w w' : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1) (ξ' : ι → Metric.sphere (0 : F) 1)
    (hw' : ∀ i : ι, w' (e i) = w i * busemannCocycleFactor f (ξ i))
    (hξ' : ∀ i : ι, ξ' (e i) = boundaryHomeomorph f (ξ i))
    (y : Hyperboloid E) :
    busemannFunctional w' ξ' (f y) = busemannFunctional w ξ y := by
  unfold busemannFunctional
  rw [← Equiv.sum_comp e (fun j => w' j * expHyperboloidBusemann (ξ' j) (f y))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hw' i, hξ' i, mul_assoc, expHyperboloidBusemann_isometry f (ξ i) y]

/-- **Isometry Equivariance of `hyperboloidBarycenter`**:
Under any hyperbolic isometry $f : \mathrm{Hyperboloid}(E) \simeq_i \mathrm{Hyperboloid}(F)$
and Busemann cocycle transformation of $(w, \xi)$,
$$f(\mathrm{hyperboloidBarycenter}(w, \xi)) = \mathrm{hyperboloidBarycenter}(w', \xi').$$ -/
theorem hyperboloidBarycenter_isometry
    (f : Hyperboloid E ≃ᵢ Hyperboloid F) (e : ι ≃ ι)
    (w w' : ι → ℝ) (ξ : ι → Metric.sphere (0 : E) 1) (ξ' : ι → Metric.sphere (0 : F) 1)
    (hw : ‖∑ i : ι, w i • (ξ i : E)‖ < ∑ i : ι, w i)
    (hw' : ‖∑ i : ι, w' i • (ξ' i : F)‖ < ∑ i : ι, w' i)
    (hw_rel : ∀ i : ι, w' (e i) = w i * busemannCocycleFactor f (ξ i))
    (hξ_rel : ∀ i : ι, ξ' (e i) = boundaryHomeomorph f (ξ i)) :
    f (hyperboloidBarycenter w ξ hw) = hyperboloidBarycenter w' ξ' hw' := by
  apply busemannFunctional_unique_min w' ξ' hw'
  intro z
  obtain ⟨y, rfl⟩ := f.surjective z
  rw [busemannFunctional_isometry f e w w' ξ ξ' hw_rel hξ_rel,
    busemannFunctional_isometry f e w w' ξ ξ' hw_rel hξ_rel]
  exact busemannFunctional_min w ξ hw y

/-- **Canonical Quotient Descent (`Quotient.lift`) for Equivariant Maps**:
Given a group $\Gamma$ acting on $\tilde{X}$ and $\tilde{Y}$, any $\Gamma$-equivariant map
$\tilde{F} : \tilde{X} \to \tilde{Y}$ ($\forall \gamma \, x, \tilde{F}(\gamma \cdot x) = \gamma \cdot \tilde{F}(x)$)
descends canonically to the orbit quotients
$\Gamma \backslash \tilde{X} \to \Gamma \backslash \tilde{Y}$. -/
def equivariantQuotientMap
    {Γ : Type*} [Group Γ]
    {X_tilde Y_tilde : Type*} [MulAction Γ X_tilde] [MulAction Γ Y_tilde]
    (F_tilde : X_tilde → Y_tilde)
    (h_equiv : ∀ (γ : Γ) (x : X_tilde), F_tilde (γ • x) = γ • F_tilde x) :
    MulAction.orbitRel.Quotient Γ X_tilde → MulAction.orbitRel.Quotient Γ Y_tilde :=
  Quotient.lift
    (fun x => Quotient.mk (MulAction.orbitRel Γ Y_tilde) (F_tilde x))
    (by
      intro a b hab
      obtain ⟨γ, rfl⟩ := hab
      apply Quotient.sound
      exact ⟨γ, (h_equiv γ b).symm⟩)

@[simp]
theorem equivariantQuotientMap_mk
    {Γ : Type*} [Group Γ]
    {X_tilde Y_tilde : Type*} [MulAction Γ X_tilde] [MulAction Γ Y_tilde]
    (F_tilde : X_tilde → Y_tilde)
    (h_equiv : ∀ (γ : Γ) (x : X_tilde), F_tilde (γ • x) = γ • F_tilde x)
    (x : X_tilde) :
    equivariantQuotientMap F_tilde h_equiv
      (Quotient.mk (MulAction.orbitRel Γ X_tilde) x) =
        Quotient.mk (MulAction.orbitRel Γ Y_tilde) (F_tilde x) :=
  rfl

/-- If the equivariant lift $\tilde{F} : \tilde{X} \to \tilde{Y}$ is continuous, then the
descended quotient map $F : \Gamma \backslash \tilde{X} \to \Gamma \backslash \tilde{Y}$ is continuous. -/
theorem continuous_equivariantQuotientMap
    {Γ : Type*} [Group Γ]
    {X_tilde Y_tilde : Type*} [TopologicalSpace X_tilde] [TopologicalSpace Y_tilde]
    [MulAction Γ X_tilde] [MulAction Γ Y_tilde]
    (F_tilde : X_tilde → Y_tilde)
    (h_equiv : ∀ (γ : Γ) (x : X_tilde), F_tilde (γ • x) = γ • F_tilde x)
    (h_cont : Continuous F_tilde) :
    Continuous (equivariantQuotientMap F_tilde h_equiv) :=
  (continuous_quotient_mk'.comp h_cont).quotient_lift _

end EquivarianceAndQuotientDescent

end BCG.Hyperbolic
