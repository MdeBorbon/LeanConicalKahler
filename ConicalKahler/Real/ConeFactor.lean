module

public import ConicalKahler.Cone.FlatCone
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# One cone factor in the real coordinates of de Borbon–Edwards

The paper (*Schauder estimates on products of cones*, p. 2) writes the cone `C(S¹_{2πβ})` in polar
coordinates `(r, θ)`, `θ ∈ ℝ/2πℤ`, with metric

  `g = dr² + β² r² dθ²`,

and identifies it with `ℝ²` by reading `(r, θ)` as Euclidean polar coordinates (p. 5, eq. (2.1)).
We use `ℂ` as a model of `ℝ²` (only its real structure): the point with coordinates `(r, θ)` is
`w = r e^{iθ}` (`polarMap (r, θ)`).

**The paper's real coordinates keep the angle `θ`.** They are globally defined on the cone. The
flat developing coordinates `ρ e^{iβθ}` of `ConicalKahler.Cone.FlatCone` use the angle `βθ` and
are not single-valued on the cone when `β ∉ ℤ` (`developing_add_two_pi_ne`).

## Main declarations

* `paperConeMetric β w v`: the quadratic form of `g` at `w` on the tangent vector `v`;
  `paperConeMetric_polar`: in polar coordinates it is `dr² + β² r² dθ²`.
* Uniform equivalence with the Euclidean metric: `β² |v|² ≤ g(v) ≤ |v|²` for `0 < β ≤ 1`
  (`paperConeMetric_le_of_le_one`, `le_paperConeMetric_of_le_one`, the factor case of eq. (2.1)).
  General `β > 0`: `paperConeMetric_bounds`.
* `paperConeGram`, `det_paperConeGram`: the Gram matrix in the coordinates `(x, y)` has determinant
  `β²` at every `w ≠ 0`. So the Riemannian volume density is `√det g = β`, a constant.
* **The bridge to the Kähler model** `ω_β = i β² |z|^{2β-2} dz ∧ dz̄`:
  `realConeChart β z = |z|^{β-1} z` (`r = |z|^β`, the same angle) is a homeomorphism of `ℂ`
  (`realConeChartHomeomorph`) with `realConeChart β (ρ^{1/β} e^{iθ}) = ρ e^{iθ}`. It is an isometry
  from the Hermitian form of the model to the paper's metric
  (`transverseConeMetric_eq_paperConeMetric`): `β² |z|^{2β-2} |v|² = g(Φ z; DΦ(z) v)`. The
  Riemannian metric of the Kähler form is `ω_β(v, Jv) = 2 β² |z|^{2β-2} |v|²`, so it is **twice**
  the paper's metric.
-/

@[expose] public section

open scoped Topology Real ComplexConjugate
open Filter Set

namespace ConicalKahler

/-! ### The paper's metric on one cone factor -/

/-- The paper's cone metric `dr² + β² r² dθ²` at the point `w ≠ 0` of `ℝ² ≅ ℂ`, on the tangent
vector `v`. Since `dr(v) = Re(w̄ v)/|w|` and `r dθ(v) = Im(w̄ v)/|w|`, it equals
`(Re(w̄ v)² + β² Im(w̄ v)²) / |w|²`. -/
noncomputable def paperConeMetric (β : ℝ) (w v : ℂ) : ℝ :=
  ((conj w * v).re ^ 2 + β ^ 2 * (conj w * v).im ^ 2) / Complex.normSq w

/-- The associated symmetric bilinear form. -/
noncomputable def paperConeBilin (β : ℝ) (w u v : ℂ) : ℝ :=
  ((conj w * u).re * (conj w * v).re + β ^ 2 * ((conj w * u).im * (conj w * v).im)) /
    Complex.normSq w

theorem paperConeBilin_self (β : ℝ) (w v : ℂ) :
    paperConeBilin β w v v = paperConeMetric β w v := by
  unfold paperConeBilin paperConeMetric
  ring

/-- Lagrange's identity: `Re(w̄ v)² + Im(w̄ v)² = |w|² |v|²`. -/
theorem re_sq_add_im_sq_conj_mul (w v : ℂ) :
    (conj w * v).re ^ 2 + (conj w * v).im ^ 2 = Complex.normSq w * Complex.normSq v := by
  have h := Complex.normSq_apply (conj w * v)
  rw [Complex.normSq_mul, Complex.normSq_conj] at h
  rw [h]
  ring

/-- `β = 1`: the paper's metric is Euclidean. -/
theorem paperConeMetric_one {w : ℂ} (hw : w ≠ 0) (v : ℂ) :
    paperConeMetric 1 w v = Complex.normSq v := by
  rw [paperConeMetric, one_pow, one_mul, re_sq_add_im_sq_conj_mul]
  field_simp [Complex.normSq_eq_zero.not.mpr hw]

/-- **The paper's metric in polar coordinates:** `dr² + β² r² dθ²`. -/
theorem paperConeMetric_polar (β : ℝ) {x : ℝ × ℝ} (hx : x.1 ≠ 0) (u : ℝ × ℝ) :
    paperConeMetric β (polarMap x) (fderiv ℝ polarMap x u) = u.1 ^ 2 + β ^ 2 * x.1 ^ 2 * u.2 ^ 2 := by
  rw [fderiv_polarMap, paperConeMetric, polarMap]
  have hexp : conj (Complex.exp (x.2 * Complex.I)) * Complex.exp (x.2 * Complex.I) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp [Complex.conj_ofReal]
  have key : conj ((x.1 : ℂ) * Complex.exp (x.2 * Complex.I)) *
      ((u.1 + x.1 * u.2 * Complex.I) * Complex.exp (x.2 * Complex.I)) =
      (x.1 : ℂ) * (u.1 + x.1 * u.2 * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal]
    linear_combination ((x.1 : ℂ) * (u.1 + x.1 * u.2 * Complex.I)) * hexp
  have hn : Complex.normSq ((x.1 : ℂ) * Complex.exp (x.2 * Complex.I)) = x.1 ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq (Complex.exp _),
      Complex.norm_exp_ofReal_mul_I]
    ring
  rw [key, hn]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
  have hx2 : x.1 ^ 2 ≠ 0 := pow_ne_zero 2 hx
  field_simp
  ring

/-! ### Uniform equivalence with the Euclidean metric -/

theorem paperConeMetric_nonneg (β : ℝ) (w v : ℂ) : 0 ≤ paperConeMetric β w v :=
  div_nonneg (by positivity) (Complex.normSq_nonneg w)

/-- Upper bound for `β ≤ 1`: `g(v) ≤ |v|²`. -/
theorem paperConeMetric_le_of_le_one {β : ℝ} (hβ1 : β ^ 2 ≤ 1) {w : ℂ} (hw : w ≠ 0) (v : ℂ) :
    paperConeMetric β w v ≤ Complex.normSq v := by
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  rw [paperConeMetric, div_le_iff₀ hn]
  have hL := re_sq_add_im_sq_conj_mul w v
  have hi := sq_nonneg (conj w * v).im
  nlinarith

/-- Lower bound for `β ≤ 1`: `β² |v|² ≤ g(v)`. -/
theorem le_paperConeMetric_of_le_one {β : ℝ} (hβ1 : β ^ 2 ≤ 1) {w : ℂ} (hw : w ≠ 0) (v : ℂ) :
    β ^ 2 * Complex.normSq v ≤ paperConeMetric β w v := by
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  rw [paperConeMetric, le_div_iff₀ hn]
  have hL := re_sq_add_im_sq_conj_mul w v
  have hr := sq_nonneg (conj w * v).re
  nlinarith

/-- For general `β`: `min(1, β²)|v|² ≤ g(v) ≤ max(1, β²)|v|²`. -/
theorem paperConeMetric_bounds (β : ℝ) {w : ℂ} (hw : w ≠ 0) (v : ℂ) :
    min 1 (β ^ 2) * Complex.normSq v ≤ paperConeMetric β w v ∧
      paperConeMetric β w v ≤ max 1 (β ^ 2) * Complex.normSq v := by
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  have hL := re_sq_add_im_sq_conj_mul w v
  have hr := sq_nonneg (conj w * v).re
  have hi := sq_nonneg (conj w * v).im
  have hv := Complex.normSq_nonneg v
  have hmin1 := min_le_left 1 (β ^ 2)
  have hmin2 := min_le_right 1 (β ^ 2)
  have hmax1 := le_max_left 1 (β ^ 2)
  have hmax2 := le_max_right 1 (β ^ 2)
  constructor
  · rw [paperConeMetric, le_div_iff₀ hn]
    nlinarith [mul_le_mul_of_nonneg_right hmin1 hr, mul_le_mul_of_nonneg_right hmin2 hi]
  · rw [paperConeMetric, div_le_iff₀ hn]
    nlinarith [mul_le_mul_of_nonneg_right hmax1 hr, mul_le_mul_of_nonneg_right hmax2 hi]

/-! ### Gram matrix and volume density -/

/-- The Gram matrix of the paper's metric in the real coordinates `(x, y)` (basis `1, i` of `ℂ`). -/
noncomputable def paperConeGram (β : ℝ) (w : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![paperConeBilin β w 1 1, paperConeBilin β w 1 Complex.I;
    paperConeBilin β w Complex.I 1, paperConeBilin β w Complex.I Complex.I]

/-- **The Gram determinant is `β²`** at every `w ≠ 0`. Hence the Riemannian volume density of the
paper's cone metric in the real coordinates is `√det g = β`. -/
theorem det_paperConeGram (β : ℝ) {w : ℂ} (hw : w ≠ 0) : (paperConeGram β w).det = β ^ 2 := by
  have hn : Complex.normSq w ≠ 0 := Complex.normSq_eq_zero.not.mpr hw
  rw [paperConeGram, Matrix.det_fin_two_of]
  simp only [paperConeBilin]
  rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, div_eq_iff (mul_ne_zero hn hn)]
  simp only [mul_one, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  rw [Complex.normSq_apply]
  ring

theorem sqrt_det_paperConeGram {β : ℝ} (hβ : 0 ≤ β) {w : ℂ} (hw : w ≠ 0) :
    Real.sqrt (paperConeGram β w).det = β := by
  rw [det_paperConeGram β hw, Real.sqrt_sq hβ]

/-! ### Real coordinates versus developing coordinates -/

/-- The paper's coordinates are single-valued on the cone: `θ ↦ θ + 2π` gives the same point. -/
theorem polarMap_paperCoords_add_two_pi (r θ : ℝ) :
    polarMap (r, θ + 2 * π) = polarMap (r, θ) :=
  polarMap_add_two_pi r θ

/-- The flat developing coordinates `ρ e^{iβθ}` are **not** single-valued on the cone when
`β ∉ ℤ`: going once around the vertex rotates them by `e^{2πiβ} ≠ 1`. -/
theorem developing_add_two_pi_ne {β ρ : ℝ} (hβ : ¬ ∃ m : ℤ, β = m) (hρ : 0 < ρ) (θ : ℝ) :
    polarMap (ρ, β * (θ + 2 * π)) ≠ polarMap (ρ, β * θ) := by
  rw [show β * (θ + 2 * π) = β * θ + (2 * π * β) by ring, polarMap_add_snd]
  intro h
  have hne : polarMap (ρ, β * θ) ≠ 0 := polarMap_ne_zero hρ
  have h1 : Complex.exp ((2 * π * β : ℝ) * Complex.I) = 1 := by
    have := mul_right_cancel₀ hne (h.trans (one_mul _).symm)
    exact this
  exact hβ ((exp_two_pi_mul_I_eq_one_iff β).mp h1)

/-! ### The bridge to the Kähler model -/

/-- **The paper's real coordinate of a Kähler-model point:** `Φ_β(z) = |z|^{β-1} z`, so
`r = |Φ_β z| = |z|^β` and `Φ_β` keeps the angle. -/
noncomputable def realConeChart (β : ℝ) (z : ℂ) : ℂ :=
  ((‖z‖ ^ (β - 1) : ℝ) : ℂ) * z

theorem norm_realConeChart {β : ℝ} (z : ℂ) (hz : z ≠ 0) : ‖realConeChart β z‖ = ‖z‖ ^ β := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [realConeChart, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hn.le _), ← Real.rpow_add_one hn.ne']
  ring_nf

theorem realConeChart_zero (β : ℝ) : realConeChart β 0 = 0 := by
  simp [realConeChart]

/-- `β = 1`: the paper's coordinate is the Kähler coordinate. -/
@[simp] theorem realConeChart_one (z : ℂ) : realConeChart 1 z = z := by
  simp [realConeChart]

/-- **`Φ_β` in polar coordinates:** `Φ_β(ρ^{1/β} e^{iθ}) = ρ e^{iθ}`. The angle is unchanged and the
radius becomes `ρ`, the paper's `r`. -/
theorem realConeChart_polarMap {β : ℝ} (hβ : β ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    realConeChart β (polarMap (ρ ^ β⁻¹, θ)) = polarMap (ρ, θ) := by
  have hr : 0 < ρ ^ β⁻¹ := Real.rpow_pos_of_pos hρ _
  have hpow : (ρ ^ β⁻¹) ^ (β - 1) * ρ ^ β⁻¹ = ρ := by
    rw [← Real.rpow_add_one hr.ne', ← Real.rpow_mul hρ.le, sub_add_cancel, inv_mul_cancel₀ hβ,
      Real.rpow_one]
  rw [realConeChart, norm_polarMap_of_nonneg hr.le]
  simp only [polarMap]
  rw [← mul_assoc, ← Complex.ofReal_mul, hpow]

/-- `Φ_{1/β}` inverts `Φ_β`. -/
theorem realConeChart_inv_realConeChart {β : ℝ} (hβ : 0 < β) (z : ℂ) :
    realConeChart β⁻¹ (realConeChart β z) = z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [realConeChart]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [realConeChart, norm_realConeChart z hz, realConeChart, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.rpow_mul hn.le, ← Real.rpow_add hn]
  have : β * (β⁻¹ - 1) + (β - 1) = 0 := by field_simp; ring
  rw [this, Real.rpow_zero, Complex.ofReal_one, one_mul]

theorem realConeChart_realConeChart_inv {β : ℝ} (hβ : 0 < β) (w : ℂ) :
    realConeChart β (realConeChart β⁻¹ w) = w := by
  have h := realConeChart_inv_realConeChart (inv_pos.mpr hβ) w
  rwa [inv_inv] at h

theorem continuous_realConeChart {β : ℝ} (hβ : 0 < β) : Continuous (realConeChart β) := by
  rw [continuous_iff_continuousAt]
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · -- at the vertex: `‖Φ z‖ = ‖z‖^β → 0`
    rw [ContinuousAt, realConeChart_zero, tendsto_zero_iff_norm_tendsto_zero]
    have h : Tendsto (fun w : ℂ => ‖w‖ ^ β) (𝓝 0) (𝓝 0) := by
      have := ((continuous_norm.rpow_const fun _ => Or.inr hβ.le).tendsto (0 : ℂ))
      simpa [Real.zero_rpow hβ.ne'] using this
    refine h.congr' ?_
    filter_upwards with w
    rcases eq_or_ne w 0 with rfl | hw
    · simp [realConeChart, Real.zero_rpow hβ.ne']
    · exact (norm_realConeChart w hw).symm
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    exact ((Complex.continuous_ofReal.continuousAt.comp
      (continuous_norm.continuousAt.rpow_const (Or.inl hn))).mul continuousAt_id)

/-- **The paper's real coordinates as a homeomorphism `ℂ ≃ₜ ℂ`** (`z ↦ |z|^{β-1} z`). It is globally
defined, including at the vertex. -/
noncomputable def realConeChartHomeomorph {β : ℝ} (hβ : 0 < β) : ℂ ≃ₜ ℂ where
  toFun := realConeChart β
  invFun := realConeChart β⁻¹
  left_inv := realConeChart_inv_realConeChart hβ
  right_inv := realConeChart_realConeChart_inv hβ
  continuous_toFun := continuous_realConeChart hβ
  continuous_invFun := continuous_realConeChart (inv_pos.mpr hβ)

/-- The derivative of `Φ_β` at `z ≠ 0`:
`DΦ_β(z) v = |z|^{β-1} v + (β-1) |z|^{β-3} Re(z̄ v) z`. -/
noncomputable def realConeChartDeriv (β : ℝ) (z v : ℂ) : ℂ :=
  ((‖z‖ ^ (β - 1) : ℝ) : ℂ) * v + (((β - 1) * ‖z‖ ^ (β - 3) * (conj z * v).re : ℝ) : ℂ) * z

theorem hasFDerivAt_realConeChart (β : ℝ) {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (realConeChart β)
      ((‖z‖ ^ (β - 1)) • ContinuousLinearMap.id ℝ ℂ +
        (((β - 1) * ‖z‖ ^ (β - 3)) • innerSL ℝ z).smulRight z) z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hsq : HasFDerivAt (fun w : ℂ => ‖w‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hpow := hsq.rpow_const (p := (β - 1) / 2) (Or.inl (pow_pos hn 2).ne')
  have hfun : (fun w : ℂ => (‖w‖ ^ 2) ^ ((β - 1) / 2)) = fun w => ‖w‖ ^ (β - 1) := by
    funext w
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg w)]
    congr 1
    push_cast
    ring
  have hcoef : (β - 1) / 2 * (‖z‖ ^ 2) ^ ((β - 1) / 2 - 1) * 2 = (β - 1) * ‖z‖ ^ (β - 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    push_cast
    rw [show (2 : ℝ) * ((β - 1) / 2 - 1) = β - 3 by ring]
    ring
  rw [hfun] at hpow
  have hprod := hpow.smul (hasFDerivAt_id z)
  have hfeq : realConeChart β = fun w => ‖w‖ ^ (β - 1) • id w := by
    funext w
    simp [realConeChart, Complex.real_smul]
  rw [hfeq]
  convert hprod using 2
  ext v
  simp only [ContinuousLinearMap.smulRight_apply, _root_.smul_apply, innerSL_apply_apply, id_eq,
    nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  rw [← hcoef]
  congr 1
  ring

theorem fderiv_realConeChart_apply (β : ℝ) {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    fderiv ℝ (realConeChart β) z v = realConeChartDeriv β z v := by
  rw [(hasFDerivAt_realConeChart β hz).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, realConeChartDeriv,
    Complex.inner, Complex.real_smul, smul_eq_mul]
  push_cast
  ring_nf

/-- **The bridge is an isometry of metric tensors.** The Hermitian form of the Kähler model,
`β² |z|^{2β-2} |v|²`, equals the paper's metric at `Φ_β z` on `DΦ_β(z) v`. -/
theorem transverseConeMetric_eq_paperConeMetric (β : ConeAngle) {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    transverseConeMetric β z v =
      paperConeMetric β.beta (realConeChart β.beta z) (fderiv ℝ (realConeChart β.beta) z v) := by
  rw [fderiv_realConeChart_apply β.beta hz]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hN : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
  have hN0 : Complex.normSq z ≠ 0 := Complex.normSq_eq_zero.not.mpr hz
  have hcpos : 0 < ‖z‖ ^ (β.beta - 1) := Real.rpow_pos_of_pos hn _
  have hc2 : (‖z‖ ^ (β.beta - 1)) ^ 2 = ‖z‖ ^ (2 * β.beta - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    ring_nf
  have hdt : (β.beta - 1) * ‖z‖ ^ (β.beta - 3) * (conj z * v).re * Complex.normSq z =
      (β.beta - 1) * ‖z‖ ^ (β.beta - 1) * (conj z * v).re := by
    have h3 : ‖z‖ ^ (β.beta - 3) * ‖z‖ ^ 2 = ‖z‖ ^ (β.beta - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hn]
      congr 1
      push_cast
      ring
    rw [hN]
    linear_combination (β.beta - 1) * (conj z * v).re * h3
  have hL := re_sq_add_im_sq_conj_mul z v
  unfold transverseConeMetric paperConeMetric realConeChart realConeChartDeriv
  generalize ‖z‖ ^ (β.beta - 1) = c at hcpos hc2 hdt ⊢
  generalize (β.beta - 1) * ‖z‖ ^ (β.beta - 3) * (conj z * v).re = d at hdt ⊢
  generalize ‖z‖ ^ (2 * β.beta - 2) = e at hc2 ⊢
  have hre : (conj ((c : ℂ) * z) * ((c : ℂ) * v + (d : ℂ) * z)).re =
      β.beta * c ^ 2 * (conj z * v).re := by
    rw [Complex.normSq_apply] at hdt
    simp only [map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
      at hdt ⊢
    linear_combination c * hdt
  have him : (conj ((c : ℂ) * z) * ((c : ℂ) * v + (d : ℂ) * z)).im = c ^ 2 * (conj z * v).im := by
    simp only [map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [hre, him, Complex.normSq_mul, Complex.normSq_ofReal,
    eq_div_iff (mul_ne_zero (mul_ne_zero hcpos.ne' hcpos.ne') hN0)]
  linear_combination (-(β.beta ^ 2 * c ^ 2 * Complex.normSq z * Complex.normSq v)) * hc2 +
    (-(β.beta ^ 2 * c ^ 4)) * hL

end ConicalKahler
