module

public import ConicalKahler.Sobolev.H1
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Polar coordinates on `ℝ^d` and homogeneous extensions

The link of the model cone is the unit sphere `S^{d-1}` of `ℝ^d` (the paper's `S^{m-1}`, with the
metric `ḡ` induced by the cone metric). Mathlib's `homeomorphUnitSphereProd` identifies `ℝ^d \ {0}`
with `S^{d-1} × (0, ∞)`, carrying Lebesgue measure to `σ ⊗ r^{d-1} dr`, where `σ = volume.toSphere`
is the surface measure (`measurePreserving_homeomorphUnitSphereProd`). This file packages that
identification for the link.

* `sphProj x = x / |x|` (junk value at `0`).
* `integral_polar`, `lintegral_polar`: `∫_{ℝ^d} g = ∫_{S × (0,∞)} g(r ω) r^{d-1} dr dσ(ω)`.
* `ae_sphere_of_ae`, `ae_of_ae_sphere`: a `0`-homogeneous property holds almost everywhere on `ℝ^d`
  iff it holds `σ`-almost everywhere on the sphere.
* `homFun k Ψ x = |x|^k Ψ(x/|x|)`, the **homogeneous extension of degree `k`** of a function on the
  sphere, and its `L²` norm on shells `{a < |x| < b}` (`lintegral_shell_homFun`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set Metric
open scoped ContDiff ENNReal

namespace ConicalKahler.Sobolev

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The unit sphere of `ℝ^d`, the link of the model cone. -/
abbrev Sph (d : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1

/-- The surface measure `σ` on the unit sphere. -/
abbrev sphMeasure (d : ℕ) : Measure (Sph d) :=
  (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere

/-- The radial measure `r^{d-1} dr` on `(0, ∞)`. -/
abbrev radMeasure (d : ℕ) : Measure (Ioi (0 : ℝ)) := Measure.volumeIoiPow (d - 1)

/-- The polar measure `σ ⊗ r^{d-1} dr` on `S^{d-1} × (0, ∞)`. -/
abbrev polarMeasure (d : ℕ) : Measure (Sph d × Ioi (0 : ℝ)) :=
  (sphMeasure d).prod (radMeasure d)

theorem finrank_euclidean : Module.finrank ℝ 𝔼 = d := finrank_euclideanSpace_fin

/-- The polar map `(ω, r) ↦ r ω`. -/
def polarMap (p : Sph d × Ioi (0 : ℝ)) : 𝔼 := (p.2 : ℝ) • (p.1 : 𝔼)

theorem polarMap_eq (p : Sph d × Ioi (0 : ℝ)) :
    polarMap p = ((homeomorphUnitSphereProd 𝔼).symm p : 𝔼) := by
  simp [polarMap]

theorem continuous_polarMap : Continuous (polarMap (d := d)) := by
  unfold polarMap
  fun_prop

theorem measurable_polarMap : Measurable (polarMap (d := d)) :=
  continuous_polarMap.measurable

theorem norm_polarMap (p : Sph d × Ioi (0 : ℝ)) : ‖polarMap p‖ = p.2 := by
  rw [polarMap, norm_smul, norm_eq_of_mem_sphere p.1, mul_one, Real.norm_eq_abs,
    abs_of_pos p.2.2]

variable [NeZero d]

/-- **Polar coordinates**, Bochner integral version:
`∫_{ℝ^d} g = ∫_{S × (0,∞)} g(r ω) d(σ ⊗ r^{d-1} dr)`. -/
theorem integral_polar {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (g : 𝔼 → G) :
    ∫ x, g x = ∫ p, g (polarMap p) ∂polarMeasure d := by
  have hmp := (volume : Measure 𝔼).measurePreserving_homeomorphUnitSphereProd
  rw [finrank_euclidean] at hmp
  calc ∫ x, g x = ∫ x : ({(0 : 𝔼)}ᶜ : Set 𝔼), g x.1 ∂((volume : Measure 𝔼).comap Subtype.val) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫ x : ({(0 : 𝔼)}ᶜ : Set 𝔼), g (polarMap (homeomorphUnitSphereProd 𝔼 x))
          ∂((volume : Measure 𝔼).comap Subtype.val) := by
        congr 1
        funext x
        rw [polarMap_eq, Homeomorph.symm_apply_apply]
    _ = ∫ p, g (polarMap p) ∂polarMeasure d :=
        hmp.integral_comp (Homeomorph.measurableEmbedding _) (fun p => g (polarMap p))

/-- **Polar coordinates**, Lebesgue integral version. -/
theorem lintegral_polar (g : 𝔼 → ℝ≥0∞) :
    ∫⁻ x, g x = ∫⁻ p, g (polarMap p) ∂polarMeasure d := by
  have hmp := (volume : Measure 𝔼).measurePreserving_homeomorphUnitSphereProd
  rw [finrank_euclidean] at hmp
  calc ∫⁻ x, g x = ∫⁻ x : ({(0 : 𝔼)}ᶜ : Set 𝔼), g x.1 ∂((volume : Measure 𝔼).comap Subtype.val) := by
        rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫⁻ x : ({(0 : 𝔼)}ᶜ : Set 𝔼), g (polarMap (homeomorphUnitSphereProd 𝔼 x))
          ∂((volume : Measure 𝔼).comap Subtype.val) := by
        congr 1
        funext x
        rw [polarMap_eq, Homeomorph.symm_apply_apply]
    _ = ∫⁻ p, g (polarMap p) ∂polarMeasure d :=
        hmp.lintegral_comp_emb (Homeomorph.measurableEmbedding _) (fun p => g (polarMap p))

theorem polarMap_homeomorph (x : ({(0 : 𝔼)}ᶜ : Set 𝔼)) :
    polarMap (homeomorphUnitSphereProd 𝔼 x) = x := by
  rw [polarMap_eq, Homeomorph.symm_apply_apply]

/-- Integrability in polar coordinates. -/
theorem integrable_polar_iff {G : Type*} [NormedAddCommGroup G] (g : 𝔼 → G) :
    Integrable g ↔ Integrable (fun p => g (polarMap p)) (polarMeasure d) := by
  have hmp := (volume : Measure 𝔼).measurePreserving_homeomorphUnitSphereProd
  rw [finrank_euclidean] at hmp
  rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)]
  have h1 : ((fun p => g (polarMap p)) ∘ homeomorphUnitSphereProd 𝔼) =
      fun x : ({(0 : 𝔼)}ᶜ : Set 𝔼) => g x := by
    funext x
    simp only [Function.comp_apply, polarMap_homeomorph]
  rw [h1, show (fun x : ({(0 : 𝔼)}ᶜ : Set 𝔼) => g x) = g ∘ Subtype.val from rfl,
    ← integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl,
    IntegrableOn, restrict_compl_singleton]

/-! ### The radial projection -/

/-- A base point of the unit sphere. -/
def sphBase : Sph d := ⟨EuclideanSpace.single 0 1, by simp⟩

/-- **The radial projection** `x ↦ x / |x|` onto the unit sphere (`sphBase` at `0`). -/
def sphProj (x : 𝔼) : Sph d :=
  if hx : x ∈ ({0}ᶜ : Set 𝔼) then (homeomorphUnitSphereProd 𝔼 ⟨x, hx⟩).1 else sphBase

theorem sphProj_of_ne {x : 𝔼} (hx : x ≠ 0) :
    sphProj x = (homeomorphUnitSphereProd 𝔼 ⟨x, hx⟩).1 := by
  simp only [sphProj, Set.mem_compl_iff, Set.mem_singleton_iff, hx, not_false_eq_true,
    ↓reduceDIte]

theorem sphProj_coe {x : 𝔼} (hx : x ≠ 0) : (sphProj x : 𝔼) = ‖x‖⁻¹ • x := by
  rw [sphProj_of_ne hx]
  simp

theorem measurable_sphProj : Measurable (sphProj (d := d)) := by
  unfold sphProj
  exact Measurable.dite ((homeomorphUnitSphereProd 𝔼).continuous.fst.measurable)
    measurable_const (measurableSet_singleton _).compl

theorem continuousOn_sphProj : ContinuousOn (sphProj (d := d)) {0}ᶜ := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : ({(0 : 𝔼)}ᶜ : Set 𝔼).domRestrict sphProj =
      fun x => (homeomorphUnitSphereProd 𝔼 x).1 := by
    funext x
    rw [Set.domRestrict_apply, sphProj_of_ne x.2]
  rw [this]
  exact (homeomorphUnitSphereProd 𝔼).continuous.fst

theorem sphProj_polarMap (p : Sph d × Ioi (0 : ℝ)) : sphProj (polarMap p) = p.1 := by
  have h0 : polarMap p ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_polarMap]
    exact p.2.2.ne'
  apply Subtype.ext
  rw [sphProj_coe h0, norm_polarMap, polarMap, smul_smul, inv_mul_cancel₀ p.2.2.ne', one_smul]

theorem sphProj_smul {t : ℝ} (ht : 0 < t) (x : 𝔼) : sphProj (t • x) = sphProj x := by
  by_cases hx : x = 0
  · simp [hx]
  have htx : t • x ≠ 0 := smul_ne_zero ht.ne' hx
  apply Subtype.ext
  rw [sphProj_coe htx, sphProj_coe hx, norm_smul, Real.norm_eq_abs, abs_of_pos ht, smul_smul]
  congr 1
  field_simp

theorem norm_smul_sphProj {x : 𝔼} : ‖x‖ • (sphProj x : 𝔼) = x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [sphProj_coe hx, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

theorem polarMap_sphProj {x : 𝔼} (hx : x ≠ 0) :
    polarMap (sphProj x, ⟨‖x‖, norm_pos_iff.mpr hx⟩) = x := by
  simp [polarMap, norm_smul_sphProj]

/-! ### The radial measure -/

theorem lintegral_radMeasure (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ r, f r ∂radMeasure d = ∫⁻ r in Ioi 0, ENNReal.ofReal (r ^ (d - 1)) * f r := by
  have h := lintegral_withDensity_eq_lintegral_mul (Measure.comap Subtype.val volume)
    (f := fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ (d - 1))) (by fun_prop)
    (hf.comp measurable_subtype_coe)
  simp only [Function.comp_def] at h
  rw [radMeasure, Measure.volumeIoiPow, h]
  exact lintegral_subtype_comap measurableSet_Ioi (fun r => ENNReal.ofReal (r ^ (d - 1)) * f r)

theorem integral_radMeasure {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (f : ℝ → G) :
    ∫ r, f r ∂radMeasure d = ∫ r in Ioi 0, r ^ (d - 1) • f r := by
  simp only [radMeasure, Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul (by fun_prop),
    integral_subtype_comap measurableSet_Ioi fun a ↦ Real.toNNReal (a ^ (d - 1)) • f a,
    setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_]
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hx) _)]

theorem radMeasure_Iio_pos : radMeasure d (Iio ⟨1, mem_Ioi.mpr one_pos⟩) ≠ 0 := by
  rw [radMeasure, Measure.volumeIoiPow_apply_Iio]
  simp only [one_pow, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  positivity

theorem radMeasure_univ_ne_zero : radMeasure d univ ≠ 0 := fun h =>
  radMeasure_Iio_pos (measure_mono_null (subset_univ _) h)

/-! ### Transfer of null sets between `ℝ^d` and the sphere -/

/-- The cone over a set `N` of the sphere has measure `σ(N) · ∞` (or `0`). Valid for every `N`. -/
theorem volume_preimage_sphProj (N : Set (Sph d)) :
    volume (sphProj ⁻¹' N) = sphMeasure d N * radMeasure d univ := by
  have hmp := (volume : Measure 𝔼).measurePreserving_homeomorphUnitSphereProd
  rw [finrank_euclidean] at hmp
  have hmp' : MeasurePreserving (homeomorphUnitSphereProd 𝔼).toMeasurableEquiv
      ((volume : Measure 𝔼).comap Subtype.val) (polarMeasure d) := hmp
  rw [← Measure.prod_prod, ← hmp'.measure_preimage_equiv,
    comap_subtype_coe_apply (measurableSet_singleton _).compl,
    ← measure_sdiff_null (s := sphProj ⁻¹' N) (measure_singleton (0 : 𝔼))]
  congr 1
  ext x
  simp only [Set.mem_sdiff, mem_preimage, mem_image, Homeomorph.toMeasurableEquiv_coe,
    mem_prod, mem_univ, and_true]
  constructor
  · rintro ⟨hx, hx0⟩
    exact ⟨⟨x, hx0⟩, by rwa [← sphProj_of_ne hx0], rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, y.2⟩
    rw [sphProj_of_ne y.2]
    exact hy

/-- **`x ↦ x/|x|` is quasi-measure-preserving** from Lebesgue measure to the surface measure. -/
theorem quasiMeasurePreserving_sphProj :
    Measure.QuasiMeasurePreserving (sphProj (d := d)) volume (sphMeasure d) := by
  refine ⟨measurable_sphProj, Measure.AbsolutelyContinuous.mk fun N hN hσ => ?_⟩
  rw [Measure.map_apply measurable_sphProj hN, volume_preimage_sphProj, hσ, zero_mul]

/-- A property of points of the sphere holding `σ`-almost everywhere holds for `x/|x|` for almost
every `x ∈ ℝ^d`. -/
theorem ae_of_ae_sphere {P : Sph d → Prop} (h : ∀ᵐ w ∂(sphMeasure d), P w) :
    ∀ᵐ x : 𝔼, P (sphProj x) :=
  quasiMeasurePreserving_sphProj.ae h

/-- Conversely, if `P(x/|x|)` holds for almost every `x`, then `P` holds `σ`-almost everywhere. -/
theorem ae_sphere_of_ae {P : Sph d → Prop} (h : ∀ᵐ x : 𝔼, P (sphProj x)) :
    ∀ᵐ w ∂(sphMeasure d), P w := by
  rw [ae_iff] at h ⊢
  have h' : volume (sphProj ⁻¹' {w : Sph d | ¬P w}) = 0 := h
  rw [volume_preimage_sphProj] at h'
  exact (mul_eq_zero.mp h').resolve_right radMeasure_univ_ne_zero

/-! ### Homogeneous extensions -/

section Hom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The homogeneous extension of degree `k`** of a function on the sphere:
`x ↦ |x|^k Ψ(x/|x|)`. For `k = 0` this is the `0`-homogeneous extension. -/
def homFun (k : ℝ) (Ψ : Sph d → E) (x : 𝔼) : E := ‖x‖ ^ k • Ψ (sphProj x)

theorem homFun_polarMap (k : ℝ) (Ψ : Sph d → E) (p : Sph d × Ioi (0 : ℝ)) :
    homFun k Ψ (polarMap p) = (p.2 : ℝ) ^ k • Ψ p.1 := by
  rw [homFun, norm_polarMap, sphProj_polarMap]

theorem homFun_smul (k : ℝ) (Ψ : Sph d → E) {t : ℝ} (ht : 0 < t) (x : 𝔼) :
    homFun k Ψ (t • x) = t ^ k • homFun k Ψ x := by
  rw [homFun, homFun, sphProj_smul ht, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
    Real.mul_rpow ht.le (norm_nonneg _), smul_smul]

theorem homFun_congr_ae {Ψ Ψ' : Sph d → E} (h : Ψ =ᵐ[sphMeasure d] Ψ') (k : ℝ) :
    homFun k Ψ =ᵐ[volume] homFun k Ψ' := by
  filter_upwards [ae_of_ae_sphere h] with x hx
  rw [homFun, homFun, hx]

theorem aestronglyMeasurable_homFun {Ψ : Sph d → E} (hΨ : AEStronglyMeasurable Ψ (sphMeasure d))
    (k : ℝ) (ν : Measure 𝔼) (hν : ν ≪ volume) : AEStronglyMeasurable (homFun k Ψ) ν := by
  have h1 : AEStronglyMeasurable (fun x : 𝔼 => Ψ (sphProj x)) volume :=
    hΨ.comp_quasiMeasurePreserving quasiMeasurePreserving_sphProj
  have h2 : AEStronglyMeasurable (fun x : 𝔼 => ‖x‖ ^ k) volume :=
    (measurable_norm.pow_const k).aestronglyMeasurable
  exact (h2.smul h1).mono_ac hν

/-- The radial weight `∫_a^b r^{2k} r^{d-1} dr` of a shell. -/
def shellWeight (d : ℕ) (k a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioo a b, ENNReal.ofReal ((r ^ k) ^ 2 * r ^ (d - 1))

theorem enorm_rpow_smul_sq {r : ℝ} (hr : 0 < r) (k : ℝ) (v : E) :
    ‖r ^ k • v‖ₑ ^ 2 = ENNReal.ofReal ((r ^ k) ^ 2) * ‖v‖ₑ ^ 2 := by
  rw [enorm_smul, mul_pow, Real.enorm_of_nonneg (Real.rpow_nonneg hr.le k),
    ← ENNReal.ofReal_pow (Real.rpow_nonneg hr.le k)]

theorem measurableSet_shell (a b : ℝ) : MeasurableSet {x : 𝔼 | ‖x‖ ∈ Ioo a b} :=
  measurableSet_Ioo.preimage measurable_norm

/-- **The `L²` norm of a homogeneous extension on a shell** `{a < |x| < b}`:
`∫_{a<|x|<b} |x|^{2k} |Ψ(x/|x|)|² dx = (∫_a^b r^{2k+d-1} dr) ∫_S |Ψ|² dσ`. -/
theorem lintegral_shell_homFun (k : ℝ) {Ψ : Sph d → E}
    (hΨ : AEStronglyMeasurable Ψ (sphMeasure d)) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    ∫⁻ x in {x : 𝔼 | ‖x‖ ∈ Ioo a b}, ‖homFun k Ψ x‖ₑ ^ 2 =
      (∫⁻ w, ‖Ψ w‖ₑ ^ 2 ∂(sphMeasure d)) * shellWeight d k a b := by
  rw [← lintegral_indicator (measurableSet_shell a b), lintegral_polar]
  have hfun : ∀ p : Sph d × Ioi (0 : ℝ),
      {x : 𝔼 | ‖x‖ ∈ Ioo a b}.indicator (fun x => ‖homFun k Ψ x‖ₑ ^ 2) (polarMap p) =
        ‖Ψ p.1‖ₑ ^ 2 * (Ioo a b).indicator (fun r => ENNReal.ofReal ((r ^ k) ^ 2)) (p.2 : ℝ) := by
    intro p
    by_cases hp : (p.2 : ℝ) ∈ Ioo a b
    · rw [indicator_of_mem (show polarMap p ∈ {x : 𝔼 | ‖x‖ ∈ Ioo a b} by
          simpa [norm_polarMap] using hp), indicator_of_mem hp, homFun_polarMap,
        enorm_rpow_smul_sq p.2.2, mul_comm]
    · rw [indicator_of_notMem (show polarMap p ∉ {x : 𝔼 | ‖x‖ ∈ Ioo a b} by
          simpa [norm_polarMap] using hp), indicator_of_notMem hp, mul_zero]
  simp_rw [hfun]
  have hg : Measurable fun r : ℝ => (Ioo a b).indicator (fun r => ENNReal.ofReal ((r ^ k) ^ 2)) r :=
    (by fun_prop : Measurable fun r : ℝ => ENNReal.ofReal ((r ^ k) ^ 2)).indicator measurableSet_Ioo
  have hprod := lintegral_prod_mul (μ := sphMeasure d) (ν := radMeasure d)
    (f := fun w => ‖Ψ w‖ₑ ^ 2)
    (g := fun r : Ioi (0 : ℝ) => (Ioo a b).indicator (fun r => ENNReal.ofReal ((r ^ k) ^ 2)) (r : ℝ))
    (hΨ.enorm.pow_const 2) (hg.comp measurable_subtype_coe).aemeasurable
  refine hprod.trans ?_
  congr 1
  rw [lintegral_radMeasure _ hg, shellWeight, ← lintegral_indicator measurableSet_Ioo,
    ← lintegral_indicator measurableSet_Ioi]
  congr 1
  funext r
  by_cases hr : r ∈ Ioo a b
  · have hr0 : r ∈ Ioi (0 : ℝ) := lt_of_le_of_lt ha hr.1
    rw [indicator_of_mem hr0, indicator_of_mem hr, indicator_of_mem hr,
      ← ENNReal.ofReal_mul (pow_nonneg hr0.out.le _), mul_comm]
  · rw [indicator_of_notMem hr]
    by_cases hr0 : r ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hr0, indicator_of_notMem hr, mul_zero]
    · rw [indicator_of_notMem hr0]

end Hom

/-- **Polar coordinates, iterated**: `∫_{ℝ^d} g = ∫_S ∫_0^∞ r^{d-1} g(r w) dr dσ(w)`. -/
theorem integral_polar_iter {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {g : 𝔼 → G} (hg : Integrable g) :
    ∫ x, g x = ∫ w, (∫ r in Ioi (0 : ℝ), r ^ (d - 1) • g (r • (w : 𝔼))) ∂(sphMeasure d) := by
  rw [integral_polar, integral_prod _ ((integrable_polar_iff g).mp hg)]
  congr 1
  funext w
  exact integral_radMeasure (fun r => g (r • (w : 𝔼)))

/-- **Polar coordinates, iterated the other way**:
`∫_{ℝ^d} g = ∫_0^∞ r^{d-1} (∫_S g(r w) dσ(w)) dr`. -/
theorem integral_polar_iter_symm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {g : 𝔼 → G} (hg : Integrable g) :
    ∫ x, g x = ∫ r in Ioi (0 : ℝ), r ^ (d - 1) • ∫ w, g (r • (w : 𝔼)) ∂(sphMeasure d) := by
  rw [integral_polar, integral_prod_symm _ ((integrable_polar_iff g).mp hg)]
  exact integral_radMeasure (fun r => ∫ w, g (r • (w : 𝔼)) ∂(sphMeasure d))

section HomL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lintegral_homFun_le (k : ℝ) {Ψ : Sph d → E} (hΨ : AEStronglyMeasurable Ψ (sphMeasure d))
    {Ω : Set 𝔼} {a b : ℝ} (ha : 0 ≤ a) (hΩ : Ω ⊆ {x | ‖x‖ ∈ Ioo a b}) :
    ∫⁻ x in Ω, ‖homFun k Ψ x‖ₑ ^ 2 ≤
      (∫⁻ w, ‖Ψ w‖ₑ ^ 2 ∂(sphMeasure d)) * shellWeight d k a b :=
  (lintegral_mono_set hΩ).trans_eq (lintegral_shell_homFun k hΨ ha b)

theorem eLpNorm_two_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf]
  simp

theorem eLpNorm_homFun_le (k : ℝ) {Ψ : Sph d → E} (hΨ : AEStronglyMeasurable Ψ (sphMeasure d))
    {Ω : Set 𝔼} {a b : ℝ} (ha : 0 ≤ a) (hΩ : Ω ⊆ {x | ‖x‖ ∈ Ioo a b}) :
    eLpNorm (homFun k Ψ) 2 (volume.restrict Ω) ≤
      shellWeight d k a b ^ (1 / 2 : ℝ) * eLpNorm Ψ 2 (sphMeasure d) := by
  rw [eLpNorm_two_eq (aestronglyMeasurable_homFun hΨ k _ Measure.restrict_le_self.absolutelyContinuous),
    eLpNorm_two_eq hΨ, mul_comm, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  exact ENNReal.rpow_le_rpow (lintegral_homFun_le k hΨ ha hΩ) (by norm_num)

theorem memLp_homFun (k : ℝ) {Ψ : Sph d → E} (hΨ : MemLp Ψ 2 (sphMeasure d))
    {Ω : Set 𝔼} {a b : ℝ} (ha : 0 ≤ a) (hΩ : Ω ⊆ {x | ‖x‖ ∈ Ioo a b})
    (hW : shellWeight d k a b ≠ ⊤) : MemLp (homFun k Ψ) 2 (volume.restrict Ω) := by
  exact (eLpNorm_homFun_le k hΨ.aestronglyMeasurable ha hΩ).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hW) hΨ.eLpNorm_lt_top)

/-- **The homogeneous extension as a bounded operator** `L²(S) → L²(Ω)`, for `Ω` inside a shell
`{a < |x| < b}` of finite radial weight. -/
def homL (k : ℝ) {Ω : Set 𝔼} {a b : ℝ} (ha : 0 ≤ a) (hΩ : Ω ⊆ {x | ‖x‖ ∈ Ioo a b})
    (hW : shellWeight d k a b ≠ ⊤) :
    Lp E 2 (sphMeasure d) →L[ℝ] Lp E 2 (volume.restrict Ω) :=
  LinearMap.mkContinuous
    { toFun := fun Ψ => (memLp_homFun k (Lp.memLp Ψ) ha hΩ hW).toLp _
      map_add' := fun Ψ Ψ' => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [ae_restrict_of_ae (homFun_congr_ae (Lp.coeFn_add Ψ Ψ') k)] with x hx
        rw [hx]
        simp [homFun, smul_add]
      map_smul' := fun c Ψ => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [ae_restrict_of_ae (homFun_congr_ae (Lp.coeFn_smul c Ψ) k)] with x hx
        rw [hx]
        simp [homFun, smul_comm c] }
    (shellWeight d k a b ^ (1 / 2 : ℝ)).toReal fun Ψ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
      refine ENNReal.toReal_mono (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hW) (Lp.eLpNorm_ne_top Ψ)) ?_
      exact eLpNorm_homFun_le k (Lp.aestronglyMeasurable Ψ) ha hΩ

theorem homL_ae (k : ℝ) {Ω : Set 𝔼} {a b : ℝ} (ha : 0 ≤ a) (hΩ : Ω ⊆ {x | ‖x‖ ∈ Ioo a b})
    (hW : shellWeight d k a b ≠ ⊤) (Ψ : Lp E 2 (sphMeasure d)) :
    homL k ha hΩ hW Ψ =ᵐ[volume.restrict Ω] homFun k Ψ :=
  (memLp_homFun k (Lp.memLp Ψ) ha hΩ hW).coeFn_toLp

end HomL

end ConicalKahler.Sobolev
