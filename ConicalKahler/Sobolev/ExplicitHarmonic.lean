module

public import ConicalKahler.Sobolev.Classical
public import ConicalKahler.Real.D2Linear

/-!
# The explicit harmonic functions of the models are weakly harmonic

The paper's harmonic functions (App. A.2, Prop. 3.4) are classical solutions of `Δu = 0` on the
regular part. Here they are shown to be **weak solutions** in `W^{1,2}(Ω)` of `-div(g⁻¹ ∇u) = 0` on
every bounded open set `Ω ⊆ ℝ^d` of the real coordinates, including sets that meet the singular
set.

## Results

* `IsClassicalHarmonic β P`: `P` is `C²` on the regular part of the real model, harmonic there for
  the paper's Laplacian in polar coordinates, measurable, bounded on bounded sets, and with
  gradient bounded on the bounded parts of the regular set. These functions form a subspace
  (`classicalHarmonic β`).
* `IsClassicalHarmonic.isWeakSolution`: **such a `P`, in the real coordinates numbered by `e`, is a
  weak solution of `-div(g⁻¹ ∇u) = 0` on every bounded open `Ω`.** This uses the classical-to-weak
  theorem `cone_isWeakSolution_of_classical`.
* Members: the constants, the Euclidean coordinates `s_i`, the functions `r_a^{k/β_a} cos kθ_a`
  and `r_a^{k/β_a} sin kθ_a` for `β_a ≤ k` (`isClassicalHarmonic_harmCos`, `_harmSin`), and the
  quadratics `∑_a c_a r_a² + ∑_{ij} Q_{ij} s_i s_j` with `2 ∑ c_a + tr Q = 0`
  (`isClassicalHarmonic_quadFn`).
* The gradient bound for `r^{k/β} cos kθ` comes from **homogeneity**: a function homogeneous of
  degree `γ` and `C¹` off the origin has `|Df(w)| ≤ M |w|^{γ-1}`
  (`exists_norm_fderiv_le_of_homogeneous`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set
open scoped ContDiff ENNReal

namespace ConicalKahler.Sobolev

open RealConeModel

/-! ### Homogeneous functions -/

section Homogeneous

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The derivative of a homogeneous function is homogeneous.** If `f(t w) = t^γ f(w)` for all
`t > 0`, then `Df(t w) = t^{γ-1} Df(w)` wherever both sides are derivatives. -/
theorem fderiv_smul_of_homogeneous {f : E → ℝ} {γ : ℝ}
    (hf : ∀ t > 0, ∀ w, f (t • w) = t ^ γ * f w) {w : E} (hw : DifferentiableAt ℝ f w) {t : ℝ}
    (ht : 0 < t) (hwt : DifferentiableAt ℝ f (t • w)) :
    fderiv ℝ f (t • w) = t ^ (γ - 1) • fderiv ℝ f w := by
  have h1 : HasFDerivAt (fun x => f (t • x))
      ((fderiv ℝ f (t • w)).comp (t • ContinuousLinearMap.id ℝ E)) w :=
    hwt.hasFDerivAt.comp w ((hasFDerivAt_id w).const_smul t)
  have h2 : HasFDerivAt (fun x => f (t • x)) (t ^ γ • fderiv ℝ f w) w := by
    have : (fun x => f (t • x)) = fun x => t ^ γ * f x := funext (hf t ht)
    rw [this]
    exact hw.hasFDerivAt.const_mul (t ^ γ)
  have h := h1.unique h2
  ext v
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) h
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, map_smul] at hv
  rw [_root_.smul_apply, smul_eq_mul, Real.rpow_sub_one ht.ne']
  field_simp
  linear_combination hv

/-- **Gradient bound for homogeneous functions.** A function homogeneous of degree `γ` and `C¹`
off the origin satisfies `|Df(w)| ≤ M |w|^{γ-1}`. -/
theorem exists_norm_fderiv_le_of_homogeneous [FiniteDimensional ℝ E] {f : E → ℝ} {γ : ℝ}
    (hf : ∀ t > 0, ∀ w, f (t • w) = t ^ γ * f w) (hd : ContDiffOn ℝ 1 f {0}ᶜ) :
    ∃ M, ∀ w ≠ 0, ‖fderiv ℝ f w‖ ≤ M * ‖w‖ ^ (γ - 1) := by
  have hopen : IsOpen ({0}ᶜ : Set E) := isOpen_compl_singleton
  have hcont : ContinuousOn (fderiv ℝ f) {0}ᶜ := hd.continuousOn_fderiv_of_isOpen hopen le_rfl
  have hsub : Metric.sphere (0 : E) 1 ⊆ {0}ᶜ := fun u hu h => by
    rw [mem_singleton_iff] at h
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hu
    exact zero_ne_one hu
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨M, fun w hw => ?_⟩
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set u : E := ‖w‖⁻¹ • w
  have hu : u ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hwu : w = ‖w‖ • u := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hdiff : ∀ x ∈ ({0}ᶜ : Set E), DifferentiableAt ℝ f x := fun x hx =>
    (hd.differentiableOn one_ne_zero x hx).differentiableAt (hopen.mem_nhds hx)
  have h := fderiv_smul_of_homogeneous hf (hdiff u (hsub hu)) hn (by rw [← hwu]; exact hdiff w hw)
  rw [← hwu] at h
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn.le _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hM u hu) (Real.rpow_nonneg hn.le _)

end Homogeneous

/-! ### `r^{k/β} cos kθ` and `r^{k/β} sin kθ` in the real coordinates -/

section OneFactor

/-- `r^{k/b} cos kθ = |w|^{k/b - k} Re(w^k)` in the real coordinate `w = r e^{iθ}` of a factor. -/
def harmCosC (b : ℝ) (k : ℕ) (w : ℂ) : ℝ := ‖w‖ ^ ((k : ℝ) / b - k) * (w ^ k).re

/-- `r^{k/b} sin kθ = |w|^{k/b - k} Im(w^k)`. -/
def harmSinC (b : ℝ) (k : ℕ) (w : ℂ) : ℝ := ‖w‖ ^ ((k : ℝ) / b - k) * (w ^ k).im

theorem polarMap_pow (k : ℕ) (r θ : ℝ) :
    polarMap (r, θ) ^ k = ((r ^ k : ℝ) : ℂ) * Complex.exp ((k * θ : ℝ) * Complex.I) := by
  rw [polarMap, mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

theorem norm_polarMap (r θ : ℝ) : ‖polarMap (r, θ)‖ = |r| := by
  rw [polarMap, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

theorem harmCosC_polarMap (b : ℝ) (k : ℕ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    harmCosC b k (polarMap (r, θ)) = coneHarmonicCos b k r θ := by
  rw [harmCosC, coneHarmonicCos, polarMap_pow, norm_polarMap, abs_of_pos hr, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hr]
  ring_nf

theorem harmSinC_polarMap (b : ℝ) (k : ℕ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    harmSinC b k (polarMap (r, θ)) = coneHarmonicSin b k r θ := by
  rw [harmSinC, coneHarmonicSin, polarMap_pow, norm_polarMap, abs_of_pos hr, Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_im, ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hr]
  ring_nf

theorem homogeneous_aux {b : ℝ} {k : ℕ} {t : ℝ} (ht : 0 < t) (w : ℂ) :
    ‖(t : ℂ) * w‖ ^ ((k : ℝ) / b - k) * t ^ k = t ^ ((k : ℝ) / b) * ‖w‖ ^ ((k : ℝ) / b - k) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, Real.mul_rpow ht.le (norm_nonneg _),
    mul_comm (t ^ _) (‖w‖ ^ _), mul_assoc, ← Real.rpow_natCast t, ← Real.rpow_add ht, mul_comm]
  ring_nf

/-- `r^{k/b} cos kθ` is homogeneous of degree `k/b`. -/
theorem harmCosC_smul (b : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) (w : ℂ) :
    harmCosC b k (t • w) = t ^ ((k : ℝ) / b) * harmCosC b k w := by
  rw [harmCosC, harmCosC, Complex.real_smul, mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    ← mul_assoc, homogeneous_aux ht, mul_assoc]

theorem harmSinC_smul (b : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) (w : ℂ) :
    harmSinC b k (t • w) = t ^ ((k : ℝ) / b) * harmSinC b k w := by
  rw [harmSinC, harmSinC, Complex.real_smul, mul_pow, ← Complex.ofReal_pow, Complex.im_ofReal_mul,
    ← mul_assoc, homogeneous_aux ht, mul_assoc]

theorem contDiffAt_harmCosC (b : ℝ) (k : ℕ) {n : WithTop ℕ∞} {w : ℂ} (hw : w ≠ 0) :
    ContDiffAt ℝ n (harmCosC b k) w :=
  ((contDiffAt_norm ℝ hw).rpow_const_of_ne (norm_ne_zero_iff.mpr hw)).mul
    (Complex.reCLM.contDiff.comp (contDiff_id.pow k)).contDiffAt

theorem contDiffAt_harmSinC (b : ℝ) (k : ℕ) {n : WithTop ℕ∞} {w : ℂ} (hw : w ≠ 0) :
    ContDiffAt ℝ n (harmSinC b k) w :=
  ((contDiffAt_norm ℝ hw).rpow_const_of_ne (norm_ne_zero_iff.mpr hw)).mul
    (Complex.imCLM.contDiff.comp (contDiff_id.pow k)).contDiffAt

theorem contDiffOn_harmCosC (b : ℝ) (k : ℕ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (harmCosC b k) {0}ᶜ :=
  fun _ hw => (contDiffAt_harmCosC b k hw).contDiffWithinAt

theorem contDiffOn_harmSinC (b : ℝ) (k : ℕ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (harmSinC b k) {0}ᶜ :=
  fun _ hw => (contDiffAt_harmSinC b k hw).contDiffWithinAt

theorem measurable_harmCosC (b : ℝ) (k : ℕ) : Measurable (harmCosC b k) :=
  (continuous_norm.measurable.pow_const _).mul
    (Complex.continuous_re.comp (continuous_pow k)).measurable

theorem measurable_harmSinC (b : ℝ) (k : ℕ) : Measurable (harmSinC b k) :=
  (continuous_norm.measurable.pow_const _).mul
    (Complex.continuous_im.comp (continuous_pow k)).measurable

theorem abs_harmC_le_aux {b : ℝ} (k : ℕ) {w : ℂ} {x : ℝ} (hx : |x| ≤ ‖w ^ k‖)
    (h0 : w = 0 → 0 < k → x = 0) :
    |‖w‖ ^ ((k : ℝ) / b - k) * x| ≤ ‖w‖ ^ ((k : ℝ) / b) := by
  rcases eq_or_ne w 0 with rfl | hw
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [CharP.cast_eq_zero, zero_div, sub_zero, Real.rpow_zero, one_mul, norm_zero] at hx ⊢
      simpa using hx
    · rw [h0 rfl hk, mul_zero, abs_zero]
      exact Real.rpow_nonneg (norm_nonneg _) _
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hn.le _)]
    calc ‖w‖ ^ ((k : ℝ) / b - k) * |x| ≤ ‖w‖ ^ ((k : ℝ) / b - k) * ‖w‖ ^ k :=
          mul_le_mul_of_nonneg_left (hx.trans (norm_pow w k).le) (Real.rpow_nonneg hn.le _)
      _ = ‖w‖ ^ ((k : ℝ) / b) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hn]
          ring_nf

theorem abs_harmCosC_le (b : ℝ) (k : ℕ) (w : ℂ) :
    |harmCosC b k w| ≤ ‖w‖ ^ ((k : ℝ) / b) :=
  abs_harmC_le_aux k (Complex.abs_re_le_norm _) fun hw hk => by
    rw [hw, zero_pow hk.ne', Complex.zero_re]

theorem abs_harmSinC_le (b : ℝ) (k : ℕ) (w : ℂ) :
    |harmSinC b k w| ≤ ‖w‖ ^ ((k : ℝ) / b) :=
  abs_harmC_le_aux k (Complex.abs_im_le_norm _) fun hw hk => by
    rw [hw, zero_pow hk.ne', Complex.zero_im]

end OneFactor

/-! ### Classically harmonic functions of the real model -/

section Model

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-- The regular part `{y | y_a ≠ 0 for all a}` of the real model. -/
def regularModel (κ ι : Type) [Fintype κ] : Set (RealConeModel κ ι) := {y | ∀ a, y.cone a ≠ 0}

theorem isOpen_regularModel : IsOpen (regularModel κ ι) := isOpen_regular

theorem toModel_mem_regularModel {c : PolarPoint κ ι} (hc : c ∈ regularPolar κ ι) :
    c.toModel ∈ regularModel κ ι :=
  toModel_cone_ne_zero hc

theorem norm_cone_le (y : RealConeModel κ ι) (a : κ) : ‖y.cone a‖ ≤ ‖y‖ := by
  have h := norm_sq_eq y
  have h1 : ‖y.cone a‖ ^ 2 ≤ ∑ b, ‖y.cone b‖ ^ 2 :=
    Finset.single_le_sum (f := fun b => ‖y.cone b‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
  have h2 : 0 ≤ ∑ i, y.eucl i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by linarith)

theorem norm_coneProj_le (a : κ) : ‖coneProj (ι := ι) a‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [coneProj_apply, one_mul]
    exact norm_cone_le y a

/-- **Classically harmonic functions of the real model.** `P` is `C²` on the regular part,
harmonic there for the paper's Laplacian in polar coordinates, measurable, bounded on bounded sets,
and its gradient is bounded on the bounded parts of the regular set. -/
structure IsClassicalHarmonic (β : κ → ConeAngle) (P : RealConeModel κ ι → ℝ) : Prop where
  contDiffOn : ContDiffOn ℝ 2 P (regularModel κ ι)
  measurable : Measurable P
  bounded : ∀ R, ∃ C, ∀ y, ‖y‖ ≤ R → |P y| ≤ C
  fderiv_bounded : ∀ R, ∃ C, ∀ y ∈ regularModel κ ι, ‖y‖ ≤ R → ‖fderiv ℝ P y‖ ≤ C
  harmonic : ∀ c ∈ regularPolar κ ι, paperLaplacian β (fun c' => P c'.toModel) c = 0

/-- The polar expression of a function that is `C²` on the regular part is `C²` at regular polar
coordinates. -/
theorem contDiffAt_comp_toModel {P : RealConeModel κ ι → ℝ}
    (hP : ContDiffOn ℝ 2 P (regularModel κ ι)) {c : PolarPoint κ ι} (hc : c ∈ regularPolar κ ι) :
    ContDiffAt ℝ 2 (fun c' : PolarPoint κ ι => P c'.toModel) c :=
  (hP.contDiffAt (isOpen_regularModel.mem_nhds (toModel_mem_regularModel hc))).comp c
    PolarPoint.contDiff_toModel.contDiffAt

namespace IsClassicalHarmonic

variable {β : κ → ConeAngle} {P Q : RealConeModel κ ι → ℝ}

theorem differentiableAt (hP : IsClassicalHarmonic β P) {y : RealConeModel κ ι}
    (hy : y ∈ regularModel κ ι) : DifferentiableAt ℝ P y :=
  (hP.contDiffOn.contDiffAt (isOpen_regularModel.mem_nhds hy)).differentiableAt (by norm_num)

theorem zero : IsClassicalHarmonic β (0 : RealConeModel κ ι → ℝ) where
  contDiffOn := contDiffOn_const
  measurable := measurable_const
  bounded R := ⟨0, fun y _ => by simp⟩
  fderiv_bounded R := ⟨0, fun y _ _ => by simp⟩
  harmonic c _ := by
    simp [paperLaplacian, coneLaplacian]

theorem add (hP : IsClassicalHarmonic β P) (hQ : IsClassicalHarmonic β Q) :
    IsClassicalHarmonic β (P + Q) where
  contDiffOn := hP.contDiffOn.add hQ.contDiffOn
  measurable := hP.measurable.add hQ.measurable
  bounded R := by
    obtain ⟨C₁, h₁⟩ := hP.bounded R
    obtain ⟨C₂, h₂⟩ := hQ.bounded R
    exact ⟨C₁ + C₂, fun y hy => (abs_add_le _ _).trans (add_le_add (h₁ y hy) (h₂ y hy))⟩
  fderiv_bounded R := by
    obtain ⟨C₁, h₁⟩ := hP.fderiv_bounded R
    obtain ⟨C₂, h₂⟩ := hQ.fderiv_bounded R
    refine ⟨C₁ + C₂, fun y hy hR => ?_⟩
    rw [fderiv_add (hP.differentiableAt hy) (hQ.differentiableAt hy)]
    exact (norm_add_le _ _).trans (add_le_add (h₁ y hy hR) (h₂ y hy hR))
  harmonic c hc := by
    have h := paperLaplacian_add β (contDiffAt_comp_toModel hP.contDiffOn hc)
      (contDiffAt_comp_toModel hQ.contDiffOn hc)
    rw [hP.harmonic c hc, hQ.harmonic c hc, add_zero] at h
    exact h

theorem const_smul (hP : IsClassicalHarmonic β P) (r : ℝ) : IsClassicalHarmonic β (r • P) where
  contDiffOn := hP.contDiffOn.const_smul r
  measurable := hP.measurable.const_smul r
  bounded R := by
    obtain ⟨C, h⟩ := hP.bounded R
    refine ⟨|r| * C, fun y hy => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (h y hy) (abs_nonneg r)
  fderiv_bounded R := by
    obtain ⟨C, h⟩ := hP.fderiv_bounded R
    refine ⟨|r| * C, fun y hy hR => ?_⟩
    rw [fderiv_const_smul (hP.differentiableAt hy),
      norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (h y hy hR) (abs_nonneg r)
  harmonic c hc := by
    have h := paperLaplacian_const_smul β (contDiffAt_comp_toModel hP.contDiffOn hc) r
    rw [hP.harmonic c hc, mul_zero] at h
    exact h

/-- A smooth function on the whole model that is harmonic on the regular part. -/
theorem of_contDiff (hP : ContDiff ℝ 2 P)
    (hΔ : ∀ c ∈ regularPolar κ ι, paperLaplacian β (fun c' => P c'.toModel) c = 0) :
    IsClassicalHarmonic β P where
  contDiffOn := hP.contDiffOn
  measurable := hP.continuous.measurable
  bounded R := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : RealConeModel κ ι) R).exists_bound_of_continuousOn
      hP.continuous.continuousOn
    exact ⟨C, fun y hy => by
      simpa [Real.norm_eq_abs] using hC y (mem_closedBall_zero_iff.mpr hy)⟩
  fderiv_bounded R := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : RealConeModel κ ι) R).exists_bound_of_continuousOn
      (hP.continuous_fderiv (by norm_num)).continuousOn
    exact ⟨C, fun y _ hy => hC y (mem_closedBall_zero_iff.mpr hy)⟩
  harmonic := hΔ

end IsClassicalHarmonic

/-- The classically harmonic functions form a subspace. -/
def classicalHarmonic (β : κ → ConeAngle) : Submodule ℝ (RealConeModel κ ι → ℝ) where
  carrier := {P | IsClassicalHarmonic β P}
  zero_mem' := IsClassicalHarmonic.zero
  add_mem' := IsClassicalHarmonic.add
  smul_mem' r _ hP := IsClassicalHarmonic.const_smul hP r

/-! ### Classically harmonic functions are weakly harmonic -/

variable {d : ℕ} [NeZero d]

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

namespace IsClassicalHarmonic

variable {β : κ → ConeAngle} {P : RealConeModel κ ι → ℝ}

theorem coordIso_symm_mem_regularModel (e : RealConeIndex κ ι ≃ Fin d) {x : 𝔼}
    (hx : x ∉ coneSingular e) : (coordIso e).symm x ∈ regularModel κ ι := by
  intro a ha
  rw [coneSingular_eq] at hx
  exact hx ⟨a, ha⟩

theorem memLp (hP : IsClassicalHarmonic β P) (e : RealConeIndex κ ι ≃ Fin d) {Ω : Set 𝔼}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    MemLp (fun x => P ((coordIso e).symm x)) 2 (volume.restrict Ω) := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  obtain ⟨C, hC⟩ := hP.bounded R
  refine MemLp.of_bound (hP.measurable.comp (coordIso e).symm.continuous.measurable).aestronglyMeasurable
    C ?_
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  rw [Real.norm_eq_abs]
  refine hC _ ?_
  rw [LinearIsometryEquiv.norm_map]
  exact mem_closedBall_zero_iff.mp (hR hx)

theorem memLp_gradient (hP : IsClassicalHarmonic β P) (e : RealConeIndex κ ι ≃ Fin d)
    {Ω : Set 𝔼} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    MemLp (gradient fun x => P ((coordIso e).symm x)) 2 (volume.restrict Ω) := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  obtain ⟨C, hC⟩ := hP.fderiv_bounded R
  have hmeas : Measurable (gradient fun x => P ((coordIso e).symm x)) :=
    (toDual ℝ 𝔼).symm.continuous.measurable.comp (measurable_fderiv ℝ _)
  refine MemLp.of_bound hmeas.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem hΩ.measurableSet,
    ae_restrict_of_ae (ae_notMem_coneSingular e)] with x hx hxS
  rw [norm_gradient_eq_norm_fderiv]
  have hfd : fderiv ℝ (fun x => P ((coordIso e).symm x)) x =
      (fderiv ℝ P ((coordIso e).symm x)).comp
        ((coordIso e).symm.toContinuousLinearEquiv : 𝔼 →L[ℝ] RealConeModel κ ι) :=
    (coordIso e).symm.toContinuousLinearEquiv.comp_right_fderiv (𝕜 := ℝ) (f := P) (x := x)
  rw [hfd]
  have hreg := coordIso_symm_mem_regularModel e hxS
  have hnorm : ‖(coordIso e).symm x‖ ≤ R := by
    rw [LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.mp (hR hx)
  refine ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans (hC _ hreg hnorm)) fun v => ?_
  calc ‖(fderiv ℝ P ((coordIso e).symm x)) ((coordIso e).symm v)‖
      ≤ ‖fderiv ℝ P ((coordIso e).symm x)‖ * ‖(coordIso e).symm v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * ‖v‖ := by
        rw [LinearIsometryEquiv.norm_map]
        exact mul_le_mul_of_nonneg_right (hC _ hreg hnorm) (norm_nonneg _)

/-- **Classically harmonic functions are weakly harmonic.** On every bounded open `Ω ⊆ ℝ^d`
(which may meet the singular set), `u = P` in the real coordinates numbered by `e` is a weak
solution of `-div(g⁻¹ ∇u) = 0` in `W^{1,2}(Ω)`. -/
theorem isWeakSolution (hP : IsClassicalHarmonic β P) (e : RealConeIndex κ ι ≃ Fin d)
    {Ω : Set 𝔼} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    (coneCoeff β e).IsWeakSolution 0
      (classicalPair (hP.memLp e hΩ hb) (hP.memLp_gradient e hΩ hb)) := by
  have hf : MemLp (fun _ : 𝔼 => (0 : ℝ)) 2 (volume.restrict Ω) := MemLp.zero
  have h := cone_isWeakSolution_of_classical β e hΩ (u := fun x => P ((coordIso e).symm x))
    (hP.contDiffOn.comp (coordIso e).symm.contDiff.contDiffOn fun x hx =>
      coordIso_symm_mem_regularModel e hx.2)
    (hP.memLp e hΩ hb) (hP.memLp_gradient e hΩ hb) hf fun c hc _ => by
      simp only [LinearIsometryEquiv.symm_apply_apply]
      rw [hP.harmonic c hc, neg_zero]
  rwa [show hf.toLp (fun _ : 𝔼 => (0 : ℝ)) = 0 from MemLp.toLp_zero hf] at h

end IsClassicalHarmonic

end Model

/-! ### The explicit harmonic functions -/

section Explicit

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-- `r_a^{k/b} cos kθ_a` on the real model. -/
def harmCosFn (b : ℝ) (k : ℕ) (a : κ) (y : RealConeModel κ ι) : ℝ := harmCosC b k (y.cone a)

/-- `r_a^{k/b} sin kθ_a` on the real model. -/
def harmSinFn (b : ℝ) (k : ℕ) (a : κ) (y : RealConeModel κ ι) : ℝ := harmSinC b k (y.cone a)

/-- The quadratic `∑_a c_a r_a² + ∑_{i,j} Q_{ij} s_i s_j`. -/
def quadFn (cc : κ → ℝ) (Q : ι → ι → ℝ) (y : RealConeModel κ ι) : ℝ :=
  ∑ a, cc a * ‖y.cone a‖ ^ 2 + ∑ i, ∑ j, Q i j * (y.eucl i * y.eucl j)

theorem harmCosFn_eq_comp (b : ℝ) (k : ℕ) (a : κ) :
    harmCosFn (ι := ι) b k a = harmCosC b k ∘ coneProj a := rfl

theorem harmSinFn_eq_comp (b : ℝ) (k : ℕ) (a : κ) :
    harmSinFn (ι := ι) b k a = harmSinC b k ∘ coneProj a := rfl

theorem isOpen_r_pos (a : κ) : IsOpen {c : PolarPoint κ ι | 0 < c (.r a)} :=
  isOpen_lt continuous_const (continuous_apply _)

/-- In polar coordinates, near a point with `r_a > 0`, `harmCosFn` is `harmonicCos`. -/
theorem harmCosFn_toModel_eventuallyEq (b : ℝ) (k : ℕ) (a : κ) {c : PolarPoint κ ι}
    (hc : 0 < c (.r a)) :
    (fun c' : PolarPoint κ ι => harmCosFn b k a c'.toModel) =ᶠ[𝓝 c] harmonicCos b k a := by
  filter_upwards [(isOpen_r_pos a).mem_nhds hc] with c' hc'
  simp only [harmCosFn, PolarPoint.cone_toModel, harmonicCos]
  exact harmCosC_polarMap b k hc' _

theorem harmSinFn_toModel_eventuallyEq (b : ℝ) (k : ℕ) (a : κ) {c : PolarPoint κ ι}
    (hc : 0 < c (.r a)) :
    (fun c' : PolarPoint κ ι => harmSinFn b k a c'.toModel) =ᶠ[𝓝 c] harmonicSin b k a := by
  filter_upwards [(isOpen_r_pos a).mem_nhds hc] with c' hc'
  simp only [harmSinFn, PolarPoint.cone_toModel, harmonicSin]
  exact harmSinC_polarMap b k hc' _

/-- `quadFn` in polar coordinates. -/
theorem quadFn_toModel (cc : κ → ℝ) (Q : ι → ι → ℝ) :
    (fun c' : PolarPoint κ ι => quadFn cc Q c'.toModel) =
      fun c' => ∑ a, cc a * c' (.r a) ^ 2 + ∑ i, ∑ j, Q i j * (c' (.s i) * c' (.s j)) := by
  funext c'
  simp [quadFn, norm_polarMap, sq_abs]

theorem isClassicalHarmonic_const (β : κ → ConeAngle) (r : ℝ) :
    IsClassicalHarmonic β (fun _ : RealConeModel κ ι => r) :=
  IsClassicalHarmonic.of_contDiff contDiff_const fun c _ => by simp [paperLaplacian, coneLaplacian]

theorem contDiff_eucl {n : WithTop ℕ∞} (i : ι) :
    ContDiff ℝ n fun y : RealConeModel κ ι => y.eucl i :=
  (EuclideanSpace.proj (𝕜 := ℝ) (Sum.inr i : RealConeIndex κ ι)).contDiff

/-- **The Euclidean coordinates `s_i` are harmonic.** -/
theorem isClassicalHarmonic_eucl (β : κ → ConeAngle) (i : ι) :
    IsClassicalHarmonic β (fun y : RealConeModel κ ι => y.eucl i) := by
  refine IsClassicalHarmonic.of_contDiff (contDiff_eucl i) fun c _ => ?_
  simp only [PolarPoint.eucl_toModel]
  simp [paperLaplacian, coneLaplacian, pd_coord]

theorem bounded_harmC {b : ℝ} (hb : 0 < b) (k : ℕ) (a : κ) {f : ℂ → ℝ}
    (hf : ∀ w, |f w| ≤ ‖w‖ ^ ((k : ℝ) / b)) (R : ℝ) :
    ∃ C, ∀ y : RealConeModel κ ι, ‖y‖ ≤ R → |f (y.cone a)| ≤ C :=
  ⟨R ^ ((k : ℝ) / b), fun y hy => (hf _).trans (Real.rpow_le_rpow (norm_nonneg _)
    ((norm_cone_le y a).trans hy) (div_nonneg (Nat.cast_nonneg k) hb.le))⟩

theorem fderiv_bounded_harmC {b : ℝ} (hb : 0 < b) {k : ℕ} (hk : b ≤ k) (a : κ) {f : ℂ → ℝ}
    (hf : ∀ t > 0, ∀ w, f (t • w) = t ^ ((k : ℝ) / b) * f w) (hd : ContDiffOn ℝ 2 f {0}ᶜ)
    (R : ℝ) :
    ∃ C, ∀ y ∈ regularModel κ ι, ‖y‖ ≤ R → ‖fderiv ℝ (f ∘ coneProj (ι := ι) a) y‖ ≤ C := by
  obtain ⟨M, hM⟩ := exists_norm_fderiv_le_of_homogeneous hf (hd.of_le (by norm_num))
  have hγ : 0 ≤ (k : ℝ) / b - 1 := by
    rw [sub_nonneg, le_div_iff₀ hb, one_mul]
    exact hk
  refine ⟨|M| * R ^ ((k : ℝ) / b - 1), fun y hy hR => ?_⟩
  have hdiff : DifferentiableAt ℝ f (y.cone a) :=
    ((hd.contDiffAt (isOpen_compl_singleton.mem_nhds (hy a))).differentiableAt (by norm_num))
  rw [fderiv_comp y hdiff (coneProj (ι := ι) a).differentiableAt, (coneProj a).fderiv]
  have h1 : ‖fderiv ℝ f (y.cone a)‖ ≤ |M| * ‖y.cone a‖ ^ ((k : ℝ) / b - 1) :=
    (hM _ (hy a)).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.rpow_nonneg (norm_nonneg _) _))
  have h2 : ‖y.cone a‖ ^ ((k : ℝ) / b - 1) ≤ R ^ ((k : ℝ) / b - 1) :=
    Real.rpow_le_rpow (norm_nonneg _) ((norm_cone_le y a).trans hR) hγ
  calc ‖(fderiv ℝ f (y.cone a)).comp (coneProj (ι := ι) a)‖
      ≤ ‖fderiv ℝ f (y.cone a)‖ * ‖coneProj (ι := ι) a‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ f (y.cone a)‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_coneProj_le a) (norm_nonneg _)
    _ ≤ |M| * R ^ ((k : ℝ) / b - 1) := by
        rw [mul_one]
        exact h1.trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg M))

/-- **`r_a^{k/β_a} cos kθ_a` is weakly harmonic** (as a member of `IsClassicalHarmonic`), for
`β_a ≤ k`. This covers every `k ≥ 1` in the paper's range `β_a < 1`. -/
theorem isClassicalHarmonic_harmCos (β : κ → ConeAngle) {k : ℕ} {a : κ} (hk : (β a).beta ≤ k) :
    IsClassicalHarmonic β (harmCosFn (ι := ι) (β a).beta k a) where
  contDiffOn := fun y hy =>
    ((contDiffAt_harmCosC _ k (hy a)).comp y (coneProj (ι := ι) a).contDiff.contDiffAt).contDiffWithinAt
  measurable := (measurable_harmCosC _ k).comp (continuous_cone a).measurable
  bounded := bounded_harmC (β a).pos k a (abs_harmCosC_le _ k)
  fderiv_bounded R := by
    rw [harmCosFn_eq_comp]
    exact fderiv_bounded_harmC (β a).pos hk a (fun t ht w => harmCosC_smul _ k ht w) (contDiffOn_harmCosC _ k) R
  harmonic c hc := by
    rw [paperLaplacian_congr β (harmCosFn_toModel_eventuallyEq _ k a (hc a))]
    exact paperLaplacian_harmonicCos β k a (hc a)

/-- **`r_a^{k/β_a} sin kθ_a` is weakly harmonic**, for `β_a ≤ k`. -/
theorem isClassicalHarmonic_harmSin (β : κ → ConeAngle) {k : ℕ} {a : κ} (hk : (β a).beta ≤ k) :
    IsClassicalHarmonic β (harmSinFn (ι := ι) (β a).beta k a) where
  contDiffOn := fun y hy =>
    ((contDiffAt_harmSinC _ k (hy a)).comp y (coneProj (ι := ι) a).contDiff.contDiffAt).contDiffWithinAt
  measurable := (measurable_harmSinC _ k).comp (continuous_cone a).measurable
  bounded := bounded_harmC (β a).pos k a (abs_harmSinC_le _ k)
  fderiv_bounded R := by
    rw [harmSinFn_eq_comp]
    exact fderiv_bounded_harmC (β a).pos hk a (fun t ht w => harmSinC_smul _ k ht w) (contDiffOn_harmSinC _ k) R
  harmonic c hc := by
    rw [paperLaplacian_congr β (harmSinFn_toModel_eventuallyEq _ k a (hc a))]
    exact paperLaplacian_harmonicSin β k a (hc a)

theorem contDiff_quadFn {n : WithTop ℕ∞} (cc : κ → ℝ) (Q : ι → ι → ℝ) :
    ContDiff ℝ n (quadFn (κ := κ) cc Q) := by
  have h1 : ∀ a, ContDiff ℝ n fun y : RealConeModel κ ι => ‖y.cone a‖ ^ 2 := fun a =>
    (contDiff_norm_sq ℝ).comp (coneProj (ι := ι) a).contDiff
  exact (ContDiff.sum fun a _ => contDiff_const.mul (h1 a)).add
    (ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      contDiff_const.mul ((contDiff_eucl i).mul (contDiff_eucl j)))

/-- The Laplacian of `∑_a c_a r_a² + ∑ Q_{ij} s_i s_j` is `4 ∑_a c_a + 2 tr Q`. -/
theorem paperLaplacian_quadFn (β : κ → ConeAngle) (cc : κ → ℝ) (Q : ι → ι → ℝ)
    {c : PolarPoint κ ι} (hc : c ∈ regularPolar κ ι) :
    paperLaplacian β (fun c' => quadFn cc Q c'.toModel) c = 2 * (2 * ∑ a, cc a + ∑ i, Q i i) := by
  have hr : ∀ a, ContDiffAt ℝ 2 (fun c' : PolarPoint κ ι => cc a * c' (.r a) ^ 2) c := fun a =>
    contDiffAt_const.mul ((contDiff_apply ℝ ℝ _).contDiffAt.pow 2)
  have hs : ∀ i j, ContDiffAt ℝ 2
      (fun c' : PolarPoint κ ι => Q i j * (c' (.s i) * c' (.s j))) c := fun i j =>
    contDiffAt_const.mul ((contDiff_apply ℝ ℝ _).contDiffAt.mul (contDiff_apply ℝ ℝ _).contDiffAt)
  have hs' : ∀ i, ContDiffAt ℝ 2
      (fun c' : PolarPoint κ ι => ∑ j, Q i j * (c' (.s i) * c' (.s j))) c := fun i =>
    ContDiffAt.sum fun j _ => hs i j
  rw [quadFn_toModel, show (fun c' : PolarPoint κ ι => ∑ a, cc a * c' (.r a) ^ 2 +
      ∑ i, ∑ j, Q i j * (c' (.s i) * c' (.s j))) =
      (fun c' => ∑ a, cc a * c' (.r a) ^ 2) + fun c' => ∑ i, ∑ j, Q i j * (c' (.s i) * c' (.s j))
      from rfl,
    paperLaplacian_add β (ContDiffAt.sum fun a _ => hr a) (ContDiffAt.sum fun i _ => hs' i),
    paperLaplacian_sum β Finset.univ fun a _ => hr a,
    paperLaplacian_sum β Finset.univ fun i _ => hs' i]
  simp_rw [paperLaplacian_sum β Finset.univ fun j _ => hs _ j]
  simp_rw [paperLaplacian_const_mul β ((contDiff_apply ℝ ℝ _).contDiffAt.pow 2),
    paperLaplacian_const_mul β ((contDiff_apply ℝ ℝ _).contDiffAt.mul
      (contDiff_apply ℝ ℝ _).contDiffAt), paperLaplacian_s_mul,
    paperLaplacian_r_sq β _ (hc _)]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- **The quadratics `∑ c_a r_a² + ∑ Q_{ij} s_i s_j` with `2 ∑ c_a + tr Q = 0` are harmonic.** They
include the paper's `r_a² − r_b²`, `r_a² − 2 s_i²` and `𝓗_2(ℝ^{m−2n})` (Prop. 3.4(3)). -/
theorem isClassicalHarmonic_quadFn (β : κ → ConeAngle) {cc : κ → ℝ} {Q : ι → ι → ℝ}
    (h : 2 * ∑ a, cc a + ∑ i, Q i i = 0) : IsClassicalHarmonic β (quadFn cc Q) :=
  IsClassicalHarmonic.of_contDiff (contDiff_quadFn cc Q) fun c hc => by
    rw [paperLaplacian_quadFn β cc Q hc, h, mul_zero]

end Explicit

end ConicalKahler.Sobolev
