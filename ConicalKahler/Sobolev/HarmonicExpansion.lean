module

public import ConicalKahler.Sobolev.Expansion
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Lemma 3.3: the expansion of harmonic functions

Let `c` be conical, `d ≥ 2`, and `u ∈ W^{1,2}(B_1)` weakly harmonic. For a link eigenfunction
`φ` (eigenvalue `λ = δ(δ + d - 2)`, `δ ≥ 0`) the **ray coefficient**

  `u_φ(r) = ∫_S u(r w) φ(w) dσ(w)`

satisfies `u_φ(r) = C r^δ` for almost every `r ∈ (0, 1)` (`rayCoeff_eq`). This is the paper's
separation of variables, proved without the maximum principle: the key identity
(`key_identity`) in polar coordinates says `∫_0^1 r^{-δ} u_φ(r) K'(r) dr = 0` for all
`K ∈ C_c^∞(0, 1)`, and the du Bois-Reymond lemma (`ae_eq_const_of_integral_mul_deriv_eq_zero`)
gives `r^{-δ} u_φ = C`.

**Lemma 3.3** (`expansion`): with the Hilbert basis `{φ_i}` of link eigenfunctions (Lemma 3.1),
`u = ∑_i c_i P_i` in `L²(B_1)`, where `P_i = |x|^{δ_i} φ_i(x/|x|)`; the sum converges
unconditionally (Parseval on each sphere `|x| = r`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set Metric
open scoped ContDiff ENNReal Interval

namespace ConicalKahler.Sobolev

variable {d : ℕ} [NeZero d]

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### Ray coefficients -/

/-- **The ray coefficient** `u_φ(r) = ∫_S u(r w) φ(w) dσ(w)`. -/
def rayCoeff (u : 𝔼 → ℝ) (φ : Sph d → ℝ) (r : ℝ) : ℝ :=
  ∫ w, u (r • (w : 𝔼)) * φ w ∂(sphMeasure d)

theorem stronglyMeasurable_rayCoeff {u : 𝔼 → ℝ} (hu : StronglyMeasurable u) {φ : Sph d → ℝ}
    (hφ : StronglyMeasurable φ) : StronglyMeasurable (rayCoeff u φ) := by
  refine StronglyMeasurable.integral_prod_right (f := fun r (w : Sph d) => u (r • (w : 𝔼)) * φ w) ?_
  exact (hu.comp_measurable (measurable_fst.smul (measurable_subtype_coe.comp
    measurable_snd))).mul (hφ.comp_measurable measurable_snd)

/-- **Polar coordinates for the key identity.** If `g` is bounded, measurable and vanishes outside
`(ε, ρ)`, `0 < ε`, `ρ ≤ 1`, then
`∫_{B_1} u P g(|x|) = ∫_0^∞ r^{d-1} r^δ g(r) u_φ(r) dr`. -/
theorem integral_ball_homP_eq (u : Lp ℝ 2 (volume.restrict (ball (0 : 𝔼) 1))) (δ : ℝ)
    (v : LinkPair d) {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ t, |g t| ≤ C)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : ρ ≤ 1) (hsupp : ∀ t, t ∉ Ioo ε ρ → g t = 0) :
    ∫ x in ball (0 : 𝔼) 1, u x * (homP δ v x * g ‖x‖) =
      ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * (r ^ δ * g r * rayCoeff u (fun w => v.fst w) r) := by
  have hshell : shell d ε ρ ⊆ ball (0 : 𝔼) 1 := fun x hx =>
    mem_ball_zero_iff.mpr (hx.2.trans_le hρ)
  have hzero : ∀ x, x ∉ shell d ε ρ → u x * (homP δ v x * g ‖x‖) = 0 := fun x hx => by
    rw [hsupp _ hx, mul_zero, mul_zero]
  -- integrability
  have := isFiniteMeasure_shell (d := d) ε ρ
  have hu2 : MemLp (fun x => u x) 2 (volume.restrict (shell d ε ρ)) :=
    (Lp.memLp u).mono_measure (Measure.restrict_mono hshell le_rfl)
  have hP2 : MemLp (homP δ v) 2 (volume.restrict (shell d ε ρ)) :=
    memLp_homFun δ (Lp.memLp v.fst) hε.le (subset_refl _) (shellWeight_ne_top hε ρ δ)
  have hon : IntegrableOn (fun x => u x * (homP δ v x * g ‖x‖)) (shell d ε ρ) := by
    have h := (integrable_mul_of_memLp_two hu2 hP2).mul_bdd
      (hg.comp measurable_norm).aestronglyMeasurable (c := C)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC _)
    exact h.congr (Eventually.of_forall fun x => by simp only [Function.comp_apply]; ring)
  have hint : Integrable fun x => u x * (homP δ v x * g ‖x‖) :=
    hon.integrable_of_forall_notMem_eq_zero hzero
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      hzero x fun h => hx (hshell h), integral_polar_iter_symm hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : (0 : ℝ) < r := hr
  simp only [smul_eq_mul]
  congr 1
  rw [rayCoeff, ← integral_const_mul]
  congr 1
  funext w
  have hn : ‖r • (w : 𝔼)‖ = r := by
    rw [norm_smul, norm_eq_of_mem_sphere w, mul_one, Real.norm_eq_abs, abs_of_pos hr0]
  rw [homP, homFun_smul_sph δ _ hr0, hn, smul_eq_mul]
  ring

/-- **Polar coordinates on a shell**, Lebesgue integral version:
`∫_{a<|x|<b} F = ∫_a^b r^{d-1} ∫_S F(r w) dσ dr`. -/
theorem lintegral_shell_polar {F : 𝔼 → ℝ≥0∞} (hF : Measurable F) {a b : ℝ} (ha : 0 ≤ a) :
    ∫⁻ x in shell d a b, F x =
      ∫⁻ r in Ioo a b, ENNReal.ofReal (r ^ (d - 1)) * ∫⁻ w, F (r • (w : 𝔼)) ∂(sphMeasure d) := by
  have hmeas : Measurable fun r : ℝ => ∫⁻ w, F (r • (w : 𝔼)) ∂(sphMeasure d) :=
    Measurable.lintegral_prod_right (f := fun r (w : Sph d) => F (r • (w : 𝔼)))
      (hF.comp (measurable_fst.smul (measurable_subtype_coe.comp measurable_snd)))
  rw [← lintegral_indicator (isOpen_shell (d := d) a b).measurableSet, lintegral_polar]
  have hpt : ∀ p : Sph d × Ioi (0 : ℝ), (shell d a b).indicator F (sphPolarMap p) =
      (Ioo a b).indicator (fun r => F (r • (p.1 : 𝔼))) (p.2 : ℝ) := by
    intro p
    by_cases hp : (p.2 : ℝ) ∈ Ioo a b
    · rw [indicator_of_mem (show sphPolarMap p ∈ shell d a b by
          simpa [shell, norm_sphPolarMap] using hp), indicator_of_mem hp]
      rfl
    · rw [indicator_of_notMem (show sphPolarMap p ∉ shell d a b by
          simpa [shell, norm_sphPolarMap] using hp), indicator_of_notMem hp]
  simp_rw [hpt]
  have hmeasP : Measurable fun p : Sph d × Ioi (0 : ℝ) =>
      (Ioo a b).indicator (fun r => F (r • (p.1 : 𝔼))) (p.2 : ℝ) := by
    have h1 : Measurable fun p : Sph d × Ioi (0 : ℝ) => F ((p.2 : ℝ) • (p.1 : 𝔼)) :=
      hF.comp ((measurable_subtype_coe.comp measurable_snd).smul
        (measurable_subtype_coe.comp measurable_fst))
    have h2 : MeasurableSet {p : Sph d × Ioi (0 : ℝ) | (p.2 : ℝ) ∈ Ioo a b} :=
      measurableSet_Ioo.preimage (measurable_subtype_coe.comp measurable_snd)
    have : (fun p : Sph d × Ioi (0 : ℝ) => (Ioo a b).indicator (fun r => F (r • (p.1 : 𝔼)))
        (p.2 : ℝ)) = {p : Sph d × Ioi (0 : ℝ) | (p.2 : ℝ) ∈ Ioo a b}.indicator
          fun p => F ((p.2 : ℝ) • (p.1 : 𝔼)) := by
      funext p
      by_cases hp : (p.2 : ℝ) ∈ Ioo a b
      · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ {p : Sph d × Ioi (0 : ℝ) |
          (p.2 : ℝ) ∈ Ioo a b} from hp)]
      · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ {p : Sph d × Ioi (0 : ℝ) |
          (p.2 : ℝ) ∈ Ioo a b} from hp)]
    rw [this]
    exact h1.indicator h2
  rw [lintegral_prod_symm _ hmeasP.aemeasurable]
  have hin : ∀ r : Ioi (0 : ℝ), ∫⁻ w, (Ioo a b).indicator (fun r => F (r • (w : 𝔼))) (r : ℝ)
      ∂(sphMeasure d) = (Ioo a b).indicator (fun r => ∫⁻ w, F (r • (w : 𝔼)) ∂(sphMeasure d))
        (r : ℝ) := by
    intro r
    by_cases hr : (r : ℝ) ∈ Ioo a b
    · simp only [indicator_of_mem hr]
    · simp only [indicator_of_notMem hr, lintegral_zero]
  simp_rw [hin]
  rw [lintegral_radMeasure _ (hmeas.indicator measurableSet_Ioo),
    ← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioo]
  congr 1
  funext r
  by_cases hr : r ∈ Ioo a b
  · have hr0 : r ∈ Ioi (0 : ℝ) := ha.trans_lt hr.1
    simp only [indicator_of_mem hr0, indicator_of_mem hr]
  · simp only [indicator_of_notMem hr]
    by_cases hr0 : r ∈ Ioi (0 : ℝ)
    · simp [indicator_of_mem hr0, indicator_of_notMem hr]
    · simp [indicator_of_notMem hr0]

theorem measurable_homFun_real {Ψ : Sph d → ℝ} (hΨ : Measurable Ψ) (k : ℝ) :
    Measurable (homFun k Ψ) :=
  (measurable_norm.pow_const k).smul (hΨ.comp measurable_sphProj)

/-- **Ray coefficients are integrable on subintervals `(a, b)`, `0 < a`, `b ≤ 1`.** -/
theorem integrableOn_rayCoeff (u : Lp ℝ 2 (volume.restrict (ball (0 : 𝔼) 1)))
    (φ : Lp ℝ 2 (sphMeasure d)) {a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) :
    IntegrableOn (rayCoeff u φ) (Ioo a b) := by
  have hshell : shell d a b ⊆ ball (0 : 𝔼) 1 := fun x hx =>
    mem_ball_zero_iff.mpr (hx.2.trans_le hb)
  have := isFiniteMeasure_shell (d := d) a b
  have hu2 : MemLp (fun x => u x) 2 (volume.restrict (shell d a b)) :=
    (Lp.memLp u).mono_measure (Measure.restrict_mono hshell le_rfl)
  have hφ2 : MemLp (homFun 0 fun w => φ w) 2 (volume.restrict (shell d a b)) :=
    memLp_homFun 0 (Lp.memLp φ) ha.le (subset_refl _) (shellWeight_ne_top ha b 0)
  have hfin : ∫⁻ x in shell d a b, ‖u x‖ₑ * ‖homFun 0 (fun w => φ w) x‖ₑ < ⊤ := by
    have := (integrable_mul_of_memLp_two hu2 hφ2).2
    rw [HasFiniteIntegral] at this
    simpa only [enorm_mul] using this
  rw [lintegral_shell_polar (F := fun x => ‖u x‖ₑ * ‖homFun 0 (fun w => φ w) x‖ₑ)
    ((Lp.stronglyMeasurable u).measurable.enorm.mul
    (measurable_homFun_real (Lp.stronglyMeasurable φ).measurable 0).enorm) ha.le] at hfin
  set L : ℝ → ℝ≥0∞ := fun r => ∫⁻ w, ‖u (r • (w : 𝔼)) * φ w‖ₑ ∂(sphMeasure d)
  have hL : ∀ r ∈ Ioo a b, ∫⁻ w, ‖u (r • (w : 𝔼))‖ₑ * ‖homFun 0 (fun w => φ w) (r • (w : 𝔼))‖ₑ
      ∂(sphMeasure d) = L r := fun r hr => by
    refine lintegral_congr fun w => ?_
    rw [homFun_smul_sph 0 _ (ha.trans hr.1), Real.rpow_zero, one_smul, enorm_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioo fun r hr => by rw [hL r hr] ] at hfin
  have ha0 : ENNReal.ofReal (a ^ (d - 1)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hLfin : ∫⁻ r in Ioo a b, L r < ⊤ := by
    have hle : ENNReal.ofReal (a ^ (d - 1)) * ∫⁻ r in Ioo a b, L r ≤
        ∫⁻ r in Ioo a b, ENNReal.ofReal (r ^ (d - 1)) * L r := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
      gcongr
      exact hr.1.le
    have h2 := hle.trans_lt hfin
    rcases ENNReal.mul_lt_top_iff.mp h2 with h | h | h
    · exact h.2
    · exact (ha0 h).elim
    · rw [h]
      exact ENNReal.zero_lt_top
  refine ⟨(stronglyMeasurable_rayCoeff (Lp.stronglyMeasurable u)
    (Lp.stronglyMeasurable φ)).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun r => ?_) hLfin
  exact enorm_integral_le_lintegral_enorm _

/-- Ray coefficients are locally integrable on `(0, 1)`. -/
theorem locallyIntegrableOn_rayCoeff (u : Lp ℝ 2 (volume.restrict (ball (0 : 𝔼) 1)))
    (φ : Lp ℝ 2 (sphMeasure d)) : LocallyIntegrableOn (rayCoeff u φ) (Ioo 0 1) := by
  intro t ht
  refine ⟨Ioo (t / 2) ((t + 1) / 2), mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds
    ⟨by linarith [ht.1], by linarith [ht.2]⟩), integrableOn_rayCoeff u φ (by linarith [ht.1])
      (by linarith [ht.2])⟩

/-! ### The du Bois-Reymond lemma -/

theorem exists_Ioo_of_tsupport {g : ℝ → ℝ} (hg : HasCompactSupport g)
    (h : tsupport g ⊆ Ioo 0 1) :
    ∃ ε ρ : ℝ, 0 < ε ∧ ρ < 1 ∧ ε ≤ ρ ∧ ∀ t, t ∉ Ioo ε ρ → g t = 0 := by
  by_cases hK : (tsupport g).Nonempty
  · have hKc : IsCompact (tsupport g) := hg.isCompact
    have hm := hKc.sInf_mem hK
    have hM := hKc.sSup_mem hK
    refine ⟨sInf (tsupport g) / 2, (sSup (tsupport g) + 1) / 2, by linarith [(h hm).1],
      by linarith [(h hM).2], ?_, fun t ht => image_eq_zero_of_notMem_tsupport fun htK => ?_⟩
    · have := csInf_le hKc.bddBelow hm
      have h2 := le_csSup hKc.bddAbove hm
      linarith [(h hm).1, (h hM).2]
    · apply ht
      have h1 := csInf_le hKc.bddBelow htK
      have h2 := le_csSup hKc.bddAbove htK
      exact ⟨by linarith [(h hm).1], by linarith [(h hM).2]⟩
  · refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, le_rfl, fun t _ =>
      image_eq_zero_of_notMem_tsupport fun ht => hK ⟨t, ht⟩⟩

/-- **The du Bois-Reymond lemma on `(0, 1)`.** If `W` is locally integrable on `(0, 1)` and
`∫ W K' = 0` for every smooth `K` supported in `(0, 1)`, then `W` is almost everywhere constant
on `(0, 1)`. -/
theorem ae_eq_const_of_integral_mul_deriv_eq_zero {W : ℝ → ℝ}
    (hW : LocallyIntegrableOn W (Ioo 0 1))
    (h : ∀ K : ℝ → ℝ, ContDiff ℝ ∞ K → ∀ ε ρ : ℝ, 0 < ε → ρ < 1 →
      (∀ t, t ∉ Ioo ε ρ → K t = 0) → ∫ r, W r * deriv K r = 0) :
    ∃ C, ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), W r = C := by
  -- a normalised bump in `(1/4, 3/4)`
  let b : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  set χ := b.normed volume
  have hχs : ContDiff ℝ ∞ χ := b.contDiff_normed (n := ⊤)
  have hχ1 : ∫ r, χ r = 1 := b.integral_normed
  have hχ0 : ∀ t, t ∉ Ioo (1 / 4 : ℝ) (3 / 4) → χ t = 0 := fun t ht => by
    rw [← Function.notMem_support, ContDiffBump.support_normed_eq]
    intro hb
    apply ht
    rw [Real.ball_eq_Ioo] at hb
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  -- integrability of `W g` for `g` continuous, vanishing outside `[ε, ρ] ⊂ (0, 1)`
  have hWint : ∀ {g : ℝ → ℝ} {ε ρ : ℝ}, Continuous g → 0 < ε → ρ < 1 →
      (∀ t, t ∉ Ioo ε ρ → g t = 0) → Integrable fun r => W r * g r := by
    intro g ε ρ hg hε hρ hgz
    have hIcc : IntegrableOn W (Icc ε ρ) :=
      hW.integrableOn_compact_subset (fun t ht => ⟨hε.trans_le ht.1, ht.2.trans_lt hρ⟩)
        isCompact_Icc
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn (s := Icc ε ρ))
    have hon : IntegrableOn (fun r => W r * g r) (Icc ε ρ) :=
      hIcc.mul_bdd hg.aestronglyMeasurable.restrict (c := M) (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact hM t ht)
    exact hon.integrable_of_forall_notMem_eq_zero fun t ht => by
      rw [hgz t fun h' => ht (Ioo_subset_Icc_self h'), mul_zero]
  set C := ∫ r, W r * χ r
  refine ⟨C, ?_⟩
  have hloc : LocallyIntegrableOn (fun r => W r - C) (Ioo 0 1) :=
    hW.sub (locallyIntegrableOn_const C)
  have hae := (isOpen_Ioo (a := (0 : ℝ)) (b := 1)).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hloc fun g hg hgc hgs => ?_
  · rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hae] with r hr hr01
    exact sub_eq_zero.mp (hr hr01)
  -- the main computation
  obtain ⟨ε, ρ, hε, hρ, hερ, hgz⟩ := exists_Ioo_of_tsupport hgc hgs
  set ε₀ := min ε (1 / 4)
  set ρ₀ := max ρ (3 / 4)
  have hε₀ : 0 < ε₀ := lt_min hε (by norm_num)
  have hρ₀ : ρ₀ < 1 := max_lt hρ (by norm_num)
  set F : ℝ → ℝ := fun t => g t - (∫ s, g s) * χ t
  have hFc : ContDiff ℝ ∞ F := hg.sub (contDiff_const.mul hχs)
  have hFz : ∀ t, t ∉ Ioo ε₀ ρ₀ → F t = 0 := fun t ht => by
    have h1 : t ∉ Ioo ε ρ := fun h' => ht ⟨(min_le_left _ _).trans_lt h'.1,
      h'.2.trans_le (le_max_left _ _)⟩
    have h2 : t ∉ Ioo (1 / 4 : ℝ) (3 / 4) := fun h' => ht ⟨(min_le_right _ _).trans_lt h'.1,
      h'.2.trans_le (le_max_right _ _)⟩
    simp only [F, hgz t h1, hχ0 t h2, mul_zero, sub_zero]
  set K : ℝ → ℝ := fun r => ∫ t in (0 : ℝ)..r, F t
  have hKd : ∀ r, HasDerivAt K (F r) r := fun r =>
    (hFc.continuous.integral_hasStrictDerivAt 0 r).hasDerivAt
  have hKs : ContDiff ℝ ∞ K := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun r => (hKd r).differentiableAt, ?_⟩
    have : deriv K = F := funext fun r => (hKd r).deriv
    rw [this]
    exact hFc
  have hKz : ∀ t, t ∉ Ioo ε₀ ρ₀ → K t = 0 := by
    intro t ht
    rcases not_and_or.mp ht with h1 | h1
    · -- `t ≤ ε₀`: the integrand vanishes on the interval
      refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun s hs => hFz s ?_)
      intro hs'
      rcases le_total 0 t with h0 | h0
      · rw [uIoc_of_le h0] at hs
        linarith [hs.2, hs'.1, not_lt.mp h1]
      · rw [uIoc_of_ge h0] at hs
        linarith [hs.2, hs'.1, hε₀]
    · -- `t ≥ ρ₀`: the integral of `F` over `ℝ` vanishes
      have ht' : ρ₀ ≤ t := not_lt.mp h1
      have hall : ∀ s, s ∉ Ioc 0 t → F s = 0 := fun s hs => hFz s fun h' => hs
        ⟨hε₀.trans h'.1, h'.2.le.trans ht'⟩
      rw [show K t = ∫ s in Ioc 0 t, F s from intervalIntegral.integral_of_le
        (hε₀.le.trans ((min_le_right _ _).trans (by
          linarith [le_max_right ρ (3 / 4 : ℝ)]))),
        setIntegral_eq_integral_of_forall_compl_eq_zero hall]
      have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
      have hχi : Integrable χ := hχs.continuous.integrable_of_hasCompactSupport
        b.hasCompactSupport_normed
      simp only [F]
      rw [integral_sub hgi (hχi.const_mul _), integral_const_mul, hχ1, mul_one, sub_self]
  have hK := h K hKs ε₀ ρ₀ hε₀ hρ₀ hKz
  have hdK : deriv K = F := funext fun r => (hKd r).deriv
  rw [hdK] at hK
  have hWg : Integrable fun r => W r * g r := hWint hg.continuous hε hρ hgz
  have hWχ : Integrable fun r => W r * χ r := hWint hχs.continuous (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1) hχ0
  have e1 : ∫ r, W r * F r = (∫ r, W r * g r) - (∫ s, g s) * C := by
    rw [← integral_const_mul, ← integral_sub hWg (hWχ.const_mul _)]
    congr 1
    funext r
    simp only [F]
    ring
  rw [e1] at hK
  have e2 : ∫ x, g x • (W x - C) = (∫ r, W r * g r) - (∫ s, g s) * C := by
    have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
    rw [← integral_mul_const, ← integral_sub hWg (hgi.mul_const _)]
    congr 1
    funext r
    simp only [smul_eq_mul]
    ring
  rw [e2, hK]

/-! ### The radial ODE: `u_φ(r) = C r^δ` -/

theorem exists_bound_of_vanish {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ}
    (hz : ∀ t, t ∉ Ioo a b → g t = 0) : ∃ C, ∀ t, |g t| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn (s := Icc a b))
  refine ⟨max C 0, fun t => ?_⟩
  by_cases ht : t ∈ Ioo a b
  · exact ((Real.norm_eq_abs _).symm.trans_le (hC t (Ioo_subset_Icc_self ht))).trans
      (le_max_left _ _)
  · rw [hz t ht, abs_zero]
    exact le_max_right _ _

/-- `K(r) r^p` is smooth when `K` is smooth and vanishes on `(-∞, ε]`, `ε > 0`. -/
theorem contDiff_mul_rpow {K : ℝ → ℝ} (hK : ContDiff ℝ ∞ K) {ε : ℝ} (hε : 0 < ε)
    (hK0 : ∀ t, t ≤ ε → K t = 0) (p : ℝ) : ContDiff ℝ ∞ fun r => K r * r ^ p := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  by_cases hx : 0 < x
  · exact hK.contDiffAt.mul (Real.contDiffAt_rpow_const_of_ne hx.ne')
  · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds (show x < ε by linarith [not_lt.mp hx])] with y hy
    rw [hK0 y hy.le, zero_mul]

theorem locallyIntegrableOn_rpow_mul_rayCoeff (u : Lp ℝ 2 (volume.restrict (ball (0 : 𝔼) 1)))
    (φ : Lp ℝ 2 (sphMeasure d)) (p : ℝ) :
    LocallyIntegrableOn (fun r => r ^ p * rayCoeff u φ r) (Ioo 0 1) := by
  intro t ht
  set a := t / 2
  set b := (t + 1) / 2
  have ha : 0 < a := by simp only [a]; linarith [ht.1]
  have hb : b ≤ 1 := by simp only [b]; linarith [ht.2]
  refine ⟨Ioo a b, mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds
    ⟨by simp only [a]; linarith [ht.1], by simp only [b]; linarith [ht.2]⟩), ?_⟩
  have hcont : ContinuousOn (fun r : ℝ => r ^ p) (Icc a b) := fun r hr =>
    (Real.continuousAt_rpow_const r p (Or.inl (ha.trans_le hr.1).ne')).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact (integrableOn_rayCoeff u φ ha hb).bdd_mul
    ((measurable_id.pow_const p).aestronglyMeasurable) (c := C) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hC r (Ioo_subset_Icc_self hr))

variable {c : CoeffField (EuclideanSpace ℝ (Fin d)) volume}

/-- **The radial ODE** (separation of variables in Lemma 3.3). Let `u ∈ W^{1,2}(B_1)` be weakly
harmonic, and `(φ, Γ)` a link eigenfunction with eigenvalue `λ = δ(δ + d - 2)`. Then the ray
coefficient is `u_φ(r) = C r^δ` for almost every `r ∈ (0, 1)`. -/
theorem rayCoeff_eq (hd : 2 ≤ d) (hc : c.IsConical) {lam δ : ℝ} {v : LinkPair d}
    (hE : IsLinkEigen hc lam v) (hlam : lam = δ * (δ + d - 2))
    (hP : MemLp (homP δ v) 2 (volume.restrict (ball (0 : 𝔼) 1)))
    (hG : MemLp (homG δ v) 2 (volume.restrict (ball (0 : 𝔼) 1)))
    {u : L2Pair volume (ball (0 : 𝔼) 1)} (hu : c.IsWeakSolution 0 u) :
    ∃ C, ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      rayCoeff u.fst (fun w => v.fst w) r = C * r ^ δ := by
  set U := rayCoeff u.fst (fun w => v.fst w)
  set q := 2 * δ + d - 1
  -- the identity `∫ r^{-δ} U K' = 0`
  have hid : ∀ K : ℝ → ℝ, ContDiff ℝ ∞ K → ∀ ε ρ : ℝ, 0 < ε → ρ < 1 →
      (∀ t, t ∉ Ioo ε ρ → K t = 0) → ∫ r, r ^ (-δ) * U r * deriv K r = 0 := by
    intro K hK ε ρ hε hρ hKz
    have hK0 : ∀ t, t ≤ ε → K t = 0 := fun t ht => hKz t fun h => by linarith [h.1]
    set f : ℝ → ℝ := fun r => K r * r ^ (-q)
    have hf : ContDiff ℝ ∞ f := contDiff_mul_rpow hK hε hK0 (-q)
    have hfz : ∀ t, t ∉ Ioo ε ρ → f t = 0 := fun t ht => by simp only [f, hKz t ht, zero_mul]
    have key := key_identity hd hc hE hlam hP hG hu hf hε hρ hfz
    set g : ℝ → ℝ := fun r => deriv f r + (2 * δ + d - 1) * (f r / r)
    -- `g` vanishes outside `(ε/2, (ρ+1)/2)`
    have hfz' : ∀ t, t ∉ Ioo (ε / 2) ((ρ + 1) / 2) → deriv f t = 0 := by
      intro t ht
      have hloc : f =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        rcases not_and_or.mp ht with h1 | h1
        · filter_upwards [Iio_mem_nhds (show t < ε by linarith [not_lt.mp h1])] with s hs
          exact hfz s fun h => by linarith [h.1, mem_Iio.mp hs]
        · filter_upwards [Ioi_mem_nhds (show ρ < t by linarith [not_lt.mp h1])] with s hs
          exact hfz s fun h => by linarith [h.2, mem_Ioi.mp hs]
      rw [hloc.deriv_eq, deriv_const]
    have hgz : ∀ t, t ∉ Ioo (ε / 2) ((ρ + 1) / 2) → g t = 0 := fun t ht => by
      have : t ∉ Ioo ε ρ := fun h => ht ⟨by linarith [h.1], by linarith [h.2]⟩
      simp only [g, hfz' t ht, hfz t this, zero_div, mul_zero, add_zero]
    have hdcont : Continuous (deriv f) := hf.continuous_deriv (by simp)
    obtain ⟨M1, hM1⟩ := exists_bound_of_vanish hdcont hfz'
    obtain ⟨M2, hM2⟩ := exists_bound_of_vanish hf.continuous hfz
    have hgb : ∀ t, |g t| ≤ M1 + |2 * δ + d - 1| * (M2 / ε) := by
      intro t
      have hM2' : 0 ≤ M2 := (abs_nonneg _).trans (hM2 0)
      have hdiv : |f t / t| ≤ M2 / ε := by
        by_cases ht : t ∈ Ioo ε ρ
        · rw [abs_div, abs_of_pos (hε.trans ht.1)]
          exact div_le_div₀ hM2' (hM2 t) hε ht.1.le
        · rw [hfz t ht, zero_div, abs_zero]
          positivity
      calc |g t| ≤ |deriv f t| + |2 * δ + d - 1| * |f t / t| := by
            simp only [g]
            rw [← abs_mul]
            exact abs_add_le _ _
        _ ≤ _ := by gcongr; exact hM1 t
    have hgm : Measurable g :=
      hdcont.measurable.add (measurable_const.mul (hf.continuous.measurable.div measurable_id))
    have hpolar := integral_ball_homP_eq u.fst δ v hgm hgb (by linarith : (0 : ℝ) < ε / 2)
      (by linarith : (ρ + 1) / 2 ≤ 1) hgz
    rw [key] at hpolar
    -- compare with `∫ r^{-δ} U K'`
    have hKd0 : ∀ r, r ∉ Ioi (0 : ℝ) → r ^ (-δ) * U r * deriv K r = 0 := by
      intro r hr
      have hloc : K =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds (show r < ε by linarith [not_lt.mp hr])] with s hs
        exact hK0 s (mem_Iio.mp hs).le
      rw [hloc.deriv_eq, deriv_const, mul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hKd0]
    refine Eq.trans ?_ hpolar.symm
    refine setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ))) fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    have hfd : deriv f r = deriv K r * r ^ (-q) + K r * (-q * r ^ (-q - 1)) := by
      have h1 := (hK.differentiable (by simp) r).hasDerivAt.mul
        (Real.hasDerivAt_rpow_const (x := r) (p := -q) (Or.inl hr0.ne'))
      exact h1.deriv
    simp only [g]
    rw [hfd, ← rpow_sub_one_eq_pow]
    have e1 : r ^ (-q) / r = r ^ (-q - 1) := by rw [Real.rpow_sub_one hr0.ne']
    have e2 : r ^ ((d : ℝ) - 1) * r ^ δ * r ^ (-q) = r ^ (-δ) := by
      rw [← Real.rpow_add hr0, ← Real.rpow_add hr0]
      congr 1
      simp only [q]
      ring
    simp only [f]
    rw [show K r * r ^ (-q) / r = K r * (r ^ (-q) / r) by ring, e1]
    rw [show r ^ ((d : ℝ) - 1) * (r ^ δ * (deriv K r * r ^ (-q) + K r * (-q * r ^ (-q - 1)) +
        (2 * δ + d - 1) * (K r * r ^ (-q - 1))) * U r) =
        (r ^ ((d : ℝ) - 1) * r ^ δ * r ^ (-q)) * U r * deriv K r by simp only [q]; ring, e2]
  obtain ⟨C, hC⟩ := ae_eq_const_of_integral_mul_deriv_eq_zero
    (locallyIntegrableOn_rpow_mul_rayCoeff u.fst v.fst (-δ)) hid
  refine ⟨C, ?_⟩
  filter_upwards [hC, ae_restrict_mem measurableSet_Ioo] with r hr hr01
  have hr0 : 0 < r := hr01.1
  rw [← hr, mul_comm, ← mul_assoc, ← Real.rpow_add hr0, add_neg_cancel, Real.rpow_zero]
  simp [U]

/-! ### Parseval on spheres -/

/-- **Parseval on a sphere.** If `w ↦ f(r w)` is square integrable on the sphere, its squared
`L²` norm is the sum of the squares of the ray coefficients in a Hilbert basis. -/
theorem lintegral_slice_eq_tsum {ι : Type*} (B : HilbertBasis ι ℝ (Lp ℝ 2 (sphMeasure d)))
    {f : 𝔼 → ℝ} (hf : StronglyMeasurable f) {r : ℝ}
    (hr : ∫⁻ w, ‖f (r • (w : 𝔼))‖ₑ ^ 2 ∂(sphMeasure d) < ⊤) :
    ∫⁻ w, ‖f (r • (w : 𝔼))‖ₑ ^ 2 ∂(sphMeasure d) =
      ∑' i, ENNReal.ofReal (rayCoeff f (fun w => B i w) r ^ 2) := by
  have hmeas : AEStronglyMeasurable (fun w : Sph d => f (r • (w : 𝔼))) (sphMeasure d) :=
    (hf.comp_measurable (g := fun w : Sph d => r • (w : 𝔼))
      (measurable_subtype_coe.const_smul r)).aestronglyMeasurable
  have hm : MemLp (fun w : Sph d => f (r • (w : 𝔼))) 2 (sphMeasure d) := by
    change eLpNorm _ 2 _ < ⊤
    rw [eLpNorm_two_eq hmeas]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hr.ne
  set S := hm.toLp _
  have hG : ∫⁻ w, ‖f (r • (w : 𝔼))‖ₑ ^ 2 ∂(sphMeasure d) = ENNReal.ofReal (‖S‖ ^ 2) := by
    rw [norm_sq_eq_lintegral, ENNReal.ofReal_toReal]
    · refine lintegral_congr_ae ?_
      filter_upwards [hm.coeFn_toLp] with w hw
      rw [hw]
    · exact (lintegral_sq_lt_top S).ne
  have hc : ∀ i, ⟪S, B i⟫_ℝ = rayCoeff f (fun w => B i w) r := fun i => by
    rw [L2.inner_def, rayCoeff]
    refine integral_congr_ae ?_
    filter_upwards [hm.coeFn_toLp] with w hw
    rw [hw, RCLike.inner_apply, conj_trivial, mul_comm]
  have hsum := B.hasSum_inner_mul_inner S S
  simp_rw [real_inner_comm S, hc, real_inner_self_eq_norm_sq] at hsum
  rw [hG, ← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun i => mul_self_nonneg _)
    hsum.summable]
  congr 1
  funext i
  rw [sq]

theorem ball_ae_eq_shell : (ball (0 : 𝔼) 1 : Set 𝔼) =ᵐ[volume] shell d 0 1 := by
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null (fun x hx => ?_) (measure_singleton (0 : 𝔼))
    by_contra h0
    exact hx.2 ⟨norm_pos_iff.mpr h0, mem_ball_zero_iff.mp hx.1⟩
  · refine measure_mono_null (fun x hx => ?_) (measure_empty (μ := (volume : Measure 𝔼)))
    exact hx.2 (mem_ball_zero_iff.mpr hx.1.2)

theorem restrict_ball_eq_shell :
    (volume.restrict (ball (0 : 𝔼) 1)) = volume.restrict (shell d 0 1) :=
  Measure.restrict_congr_set ball_ae_eq_shell

/-- **`L²(B_1)` norms in terms of ray coefficients** (Parseval on each sphere). For a
square-integrable `f` on `B_1` and a Hilbert basis `{φ_i}` of `L²(S)`,
`∫_{B_1} |f|² = ∑_i ∫_0^1 r^{d-1} f_{φ_i}(r)² dr`. -/
theorem lintegral_ball_eq_tsum {ι : Type*} [Countable ι]
    (B : HilbertBasis ι ℝ (Lp ℝ 2 (sphMeasure d))) {f : 𝔼 → ℝ} (hf : StronglyMeasurable f)
    (hf2 : ∫⁻ x in ball (0 : 𝔼) 1, ‖f x‖ₑ ^ 2 < ⊤) :
    ∫⁻ x in ball (0 : 𝔼) 1, ‖f x‖ₑ ^ 2 =
      ∑' i, ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ (d - 1)) *
        ENNReal.ofReal (rayCoeff f (fun w => B i w) r ^ 2) := by
  have hmeasG : Measurable fun r : ℝ => ∫⁻ w, ‖f (r • (w : 𝔼))‖ₑ ^ 2 ∂(sphMeasure d) :=
    Measurable.lintegral_prod_right (f := fun r (w : Sph d) => ‖f (r • (w : 𝔼))‖ₑ ^ 2)
      ((hf.measurable.comp (measurable_fst.smul (measurable_subtype_coe.comp
        measurable_snd))).enorm.pow_const 2)
  rw [restrict_ball_eq_shell, lintegral_shell_polar (hf.measurable.enorm.pow_const 2) le_rfl]
    at hf2 ⊢
  -- the slices are square integrable for almost every radius
  have hfin : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∫⁻ w, ‖f (r • (w : 𝔼))‖ₑ ^ 2 ∂(sphMeasure d) < ⊤ := by
    filter_upwards [ae_lt_top ((by fun_prop : Measurable fun r : ℝ =>
      ENNReal.ofReal (r ^ (d - 1))).mul hmeasG) hf2.ne,
      ae_restrict_mem measurableSet_Ioo] with r hr hr01
    have hpos : ENNReal.ofReal (r ^ (d - 1)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact pow_pos hr01.1 _
    rcases ENNReal.mul_lt_top_iff.mp hr with h | h | h
    · exact h.2
    · exact (hpos h).elim
    · simp only at h
      rw [h]
      exact ENNReal.zero_lt_top
  have hT := lintegral_tsum (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (f := fun i r => ENNReal.ofReal (r ^ (d - 1)) *
      ENNReal.ofReal (rayCoeff f (fun w => B i w) r ^ 2)) fun i =>
      ((by fun_prop : Measurable fun r : ℝ => ENNReal.ofReal (r ^ (d - 1))).mul
        (ENNReal.measurable_ofReal.comp
          ((stronglyMeasurable_rayCoeff hf (Lp.stronglyMeasurable (B i))).measurable.pow_const
            2))).aemeasurable
  rw [← hT]
  refine lintegral_congr_ae ?_
  filter_upwards [hfin] with r hr
  rw [ENNReal.tsum_mul_left, lintegral_slice_eq_tsum B hf hr]

/-- **Polar coordinates for `∫_{B_1} f P`**, `δ ≥ 0`:
`∫_{B_1} f(x) |x|^δ φ(x/|x|) dx = ∫_0^1 r^{d-1} r^δ f_φ(r) dr`. -/
theorem integral_ball_mul_homP {f : 𝔼 → ℝ} (hf2 : MemLp f 2 (volume.restrict (ball (0 : 𝔼) 1)))
    {δ : ℝ} (hδ : 0 ≤ δ) (v : LinkPair d) :
    ∫ x in ball (0 : 𝔼) 1, f x * homP δ v x =
      ∫ r in Ioo (0 : ℝ) 1, r ^ (d - 1) * (r ^ δ * rayCoeff f (fun w => v.fst w) r) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hP2 := memLp_homFun_ball δ (Lp.memLp v.fst) 1 (by linarith)
  have hint : IntegrableOn (fun x => f x * homP δ v x) (ball (0 : 𝔼) 1) :=
    integrable_mul_of_memLp_two hf2 hP2
  rw [← integral_indicator measurableSet_ball,
    integral_polar_iter_symm (hint.integrable_indicator measurableSet_ball)]
  have hin : ∀ r ∈ Ioi (0 : ℝ), r ^ (d - 1) • ∫ w, (ball (0 : 𝔼) 1).indicator
      (fun x => f x * homP δ v x) (r • (w : 𝔼)) ∂(sphMeasure d) =
      (Iio (1 : ℝ)).indicator (fun r => r ^ (d - 1) * (r ^ δ *
        rayCoeff f (fun w => v.fst w) r)) r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    have hn : ∀ w : Sph d, ‖r • (w : 𝔼)‖ = r := fun w => by
      rw [norm_smul, norm_eq_of_mem_sphere w, mul_one, Real.norm_eq_abs, abs_of_pos hr0]
    by_cases hr1 : r < 1
    · have e : ∫ w, (ball (0 : 𝔼) 1).indicator (fun x => f x * homP δ v x) (r • (w : 𝔼))
          ∂(sphMeasure d) = r ^ δ * rayCoeff f (fun w => v.fst w) r := by
        rw [rayCoeff, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        simp only
        rw [indicator_of_mem (mem_ball_zero_iff.mpr (by rw [hn w]; exact hr1)), homP,
          homFun_smul_sph δ _ hr0, smul_eq_mul]
        ring
      rw [indicator_of_mem (show r ∈ Iio (1 : ℝ) from hr1), smul_eq_mul, e]
    · rw [indicator_of_notMem (show r ∉ Iio (1 : ℝ) from hr1)]
      have : ∀ w : Sph d, (ball (0 : 𝔼) 1).indicator (fun x => f x * homP δ v x)
          (r • (w : 𝔼)) = 0 := fun w =>
        indicator_of_notMem (fun h => hr1 (by rw [← hn w]; exact mem_ball_zero_iff.mp h)) _
      simp [this]
  rw [setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ))) hin,
    setIntegral_indicator (measurableSet_Iio (a := (1 : ℝ))), Ioi_inter_Iio]

theorem integral_Ioo_rpow {p : ℝ} (hp : -1 < p) : ∫ r in Ioo (0 : ℝ) 1, r ^ p = 1 / (p + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl hp), Real.one_rpow, Real.zero_rpow (by linarith), sub_zero]

/-! ### Lemma 3.3 -/

/-- `L²(S)` is separable (the instance search exceeds its default size limit, so it is built by
hand). -/
theorem separableSpace_sph : TopologicalSpace.SeparableSpace (Lp ℝ 2 (sphMeasure d)) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have h1 : IsSeparable (sphMeasure d) := instIsSeparableOfCountablyGeneratedOfSFinite _
  have h2 : SecondCountableTopology (Lp ℝ 2 (sphMeasure d)) :=
    MeasureTheory.Lp.SecondCountableTopology
  exact TopologicalSpace.SecondCountableTopology.to_separableSpace

section Lemma33

variable {c : CoeffField (EuclideanSpace ℝ (Fin d)) volume}

/-- `∫_0^1 r^{d-1} f(r)² dr = a² / (2δ + d)` when `f(r) = a r^δ` almost everywhere. -/
theorem lintegral_sq_of_ae_eq_rpow {f : ℝ → ℝ} {a δ : ℝ} (hδ : 0 ≤ δ)
    (hf : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), f r = a * r ^ δ) :
    ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ (d - 1)) * ENNReal.ofReal (f r ^ 2) =
      ENNReal.ofReal (a ^ 2 / (2 * δ + d)) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hp : -1 < 2 * δ + d - 1 := by linarith
  have hint : IntegrableOn (fun r : ℝ => a ^ 2 * r ^ (2 * δ + d - 1)) (Ioo 0 1) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (r := 2 * δ + d - 1) hp).1
    exact (this.mono_set Ioo_subset_Ioc_self).const_mul _
  calc ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ (d - 1)) * ENNReal.ofReal (f r ^ 2)
      = ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (a ^ 2 * r ^ (2 * δ + d - 1)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hf, ae_restrict_mem measurableSet_Ioo] with r hr hr01
        have hr0 : 0 < r := hr01.1
        have h1 : r ^ (d - 1) = r ^ ((d : ℝ) - 1) := (rpow_sub_one_eq_pow).symm
        have h2 : (r ^ δ) ^ 2 = r ^ (2 * δ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
          ring_nf
        have h3 : r ^ ((d : ℝ) - 1) * r ^ (2 * δ) = r ^ (2 * δ + d - 1) := by
          rw [← Real.rpow_add hr0]
          ring_nf
        have hreal : r ^ (d - 1) * (a * r ^ δ) ^ 2 = a ^ 2 * r ^ (2 * δ + d - 1) := by
          rw [mul_pow, h1, h2, ← h3]
          ring
        rw [hr, ← ENNReal.ofReal_mul (pow_nonneg hr0.le _), hreal]
    _ = ENNReal.ofReal (a ^ 2 / (2 * δ + d)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint (by
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hr.1.le _)),
          integral_const_mul, integral_Ioo_rpow hp]
        congr 1
        rw [show 2 * δ + d - 1 + 1 = 2 * δ + d by ring]
        ring

/-- The nonnegative indicial root `δ ≥ 0` of `δ (δ + d - 2) = λ`. -/
def indicialRoot (d : ℕ) (lam : ℝ) : ℝ := (-((d : ℝ) - 2) + √(((d : ℝ) - 2) ^ 2 + 4 * lam)) / 2

theorem indicialRoot_nonneg (hd : 2 ≤ d) {lam : ℝ} (hlam : 0 ≤ lam) : 0 ≤ indicialRoot d lam := by
  have hd' : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h : (d : ℝ) - 2 ≤ √(((d : ℝ) - 2) ^ 2 + 4 * lam) :=
    Real.le_sqrt_of_sq_le (by linarith)
  unfold indicialRoot
  linarith

theorem indicialRoot_spec (lam : ℝ) (hlam : 0 ≤ lam) :
    lam = indicialRoot d lam * (indicialRoot d lam + d - 2) := by
  have hpos : 0 ≤ ((d : ℝ) - 2) ^ 2 + 4 * lam := by positivity
  have hs := Real.sq_sqrt hpos
  unfold indicialRoot
  nlinarith [hs]

/-- The `L²(B_1)` pairing of `f` with `P = |x|^δ φ(x/|x|)` when the ray coefficient of `f` along
`φ` is `a r^γ`: `∫_{B_1} f P = a / (δ + γ + d)`. -/
theorem integral_ball_mul_homP_of_rayCoeff' {f : 𝔼 → ℝ}
    (hf2 : MemLp f 2 (volume.restrict (ball (0 : 𝔼) 1))) {δ γ a : ℝ} (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (v : LinkPair d)
    (ha : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), rayCoeff f (fun w => v.fst w) r = a * r ^ γ) :
    ∫ x in ball (0 : 𝔼) 1, f x * homP δ v x = a / (δ + γ + d) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  rw [integral_ball_mul_homP hf2 hδ v]
  have e2 : ∫ r in Ioo (0 : ℝ) 1, r ^ (d - 1) * (r ^ δ * rayCoeff f (fun w => v.fst w) r) =
      ∫ r in Ioo (0 : ℝ) 1, a * r ^ (δ + γ + d - 1) := by
    refine integral_congr_ae ?_
    filter_upwards [ha, ae_restrict_mem measurableSet_Ioo] with r hr hr01
    have hr0 : 0 < r := hr01.1
    rw [hr, ← rpow_sub_one_eq_pow]
    rw [show r ^ ((d : ℝ) - 1) * (r ^ δ * (a * r ^ γ)) =
      a * (r ^ ((d : ℝ) - 1) * r ^ δ * r ^ γ) by ring, ← Real.rpow_add hr0,
      ← Real.rpow_add hr0]
    congr 2
    ring
  rw [e2, integral_const_mul, integral_Ioo_rpow (by linarith),
    show δ + γ + d - 1 + 1 = δ + γ + d by ring, mul_one_div]

/-- The `L²(B_1)` pairing of `f` with `P = |x|^δ φ(x/|x|)` when the ray coefficient of `f` along
`φ` is `a r^δ`: `∫_{B_1} f P = a / (2δ + d)`. -/
theorem integral_ball_mul_homP_of_rayCoeff {f : 𝔼 → ℝ}
    (hf2 : MemLp f 2 (volume.restrict (ball (0 : 𝔼) 1))) {δ a : ℝ} (hδ : 0 ≤ δ) (v : LinkPair d)
    (ha : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) 1)), rayCoeff f (fun w => v.fst w) r = a * r ^ δ) :
    ∫ x in ball (0 : 𝔼) 1, f x * homP δ v x = a / (2 * δ + d) := by
  rw [integral_ball_mul_homP_of_rayCoeff' hf2 hδ hδ v ha, two_mul]

/-- **The homogeneous harmonic functions are orthogonal in `L²(B_1)` when their link functions
are**: `∫_{B_1} |x|^δ φ(x̂) |x|^{δ'} ψ(x̂) = ⟪φ, ψ⟫_{L²(S)} / (δ + δ' + d)`. -/
theorem integral_ball_homP_mul_homP {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (v w : LinkPair d) :
    ∫ x in ball (0 : 𝔼) 1, homP δ v x * homP δ' w x = ⟪v.fst, w.fst⟫_ℝ / (δ + δ' + d) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hP := memLp_homFun_ball δ (Lp.memLp v.fst) 1 (by linarith)
  rw [integral_ball_mul_homP hP hδ' w]
  have hray : ∀ r : ℝ, 0 < r →
      rayCoeff (homP δ v) (fun y => w.fst y) r = r ^ δ * ⟪v.fst, w.fst⟫_ℝ := by
    intro r hr0
    rw [rayCoeff, L2.inner_def, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [homP, homFun_smul_sph _ _ hr0, smul_eq_mul, RCLike.inner_apply, conj_trivial]
    ring
  have e2 : ∫ r in Ioo (0 : ℝ) 1, r ^ (d - 1) * (r ^ δ' *
      rayCoeff (homP δ v) (fun y => w.fst y) r) =
      ∫ r in Ioo (0 : ℝ) 1, ⟪v.fst, w.fst⟫_ℝ * r ^ (δ + δ' + d - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun r hr01 => ?_
    have hr0 : 0 < r := hr01.1
    rw [hray r hr0, ← rpow_sub_one_eq_pow]
    rw [show r ^ ((d : ℝ) - 1) * (r ^ δ' * (r ^ δ * ⟪v.fst, w.fst⟫_ℝ)) =
      ⟪v.fst, w.fst⟫_ℝ * (r ^ ((d : ℝ) - 1) * r ^ δ' * r ^ δ) by ring, ← Real.rpow_add hr0,
      ← Real.rpow_add hr0]
    congr 2
    ring
  rw [e2, integral_const_mul, integral_Ioo_rpow (by linarith),
    show δ + δ' + d - 1 + 1 = δ + δ' + d by ring, mul_one_div]

/-- The gradient `|x|^{δ-1}(δφ x̂ + Γ(x̂))` of `ρ^δ φ` is in `L²(B_1)` for a link eigenfunction
with `λ = δ(δ + d - 2)`, `δ ≥ 0`, `d ≥ 2` (for `δ = 0` the pair has `Γ = 0`). -/
theorem memLp_homG_of_isLinkEigen (hd : 2 ≤ d) {c : CoeffField 𝔼 volume} {hc : c.IsConical}
    {lam δ : ℝ} {v : LinkPair d} (hE : IsLinkEigen hc lam v) (hlam : lam = δ * (δ + d - 2))
    (hδ : 0 ≤ δ) : MemLp (homG δ v) 2 (volume.restrict (ball (0 : 𝔼) 1)) := by
  have hdpos : (2 : ℝ) ≤ d := by exact_mod_cast hd
  by_cases h : 0 < 2 * (δ - 1) + d
  · exact memLp_homFun_ball (δ - 1) (memLp_homGradProfile _ _) 1 h
  · have hδ0 : δ = 0 := by linarith [not_lt.mp h]
    have hlam0 : lam = 0 := by rw [hlam, hδ0, zero_mul]
    rw [hlam0] at hE
    have hsnd : v.snd = 0 := hE.snd_eq_zero
    have hprof : homGradProfile δ v =ᵐ[sphMeasure d] 0 := by
      filter_upwards [Lp.coeFn_zero 𝔼 2 (sphMeasure d)] with w hw
      rw [homGradProfile, hδ0, zero_mul, zero_smul, zero_add, hsnd, hw, Pi.zero_apply]
    have hz : homG δ v =ᵐ[volume] 0 := by
      filter_upwards [homFun_congr_ae hprof (δ - 1)] with x hx
      rw [homG, hx]
      simp [homFun]
    exact (MemLp.zero : MemLp (0 : 𝔼 → 𝔼) 2 (volume.restrict (ball (0 : 𝔼) 1))).ae_eq
      (Filter.EventuallyEq.symm (ae_restrict_of_ae hz))

/-- **A Parseval criterion for orthogonal expansions** in a real inner product space. If the `P_i`
are orthogonal with `‖P_i‖² = 1/n_i`, `⟪u, P_i⟫ = a_i/n_i`, and `∑ a_i²/n_i = ‖u‖²`, then
`u = ∑ a_i P_i` (unconditional convergence). -/
theorem hasSum_of_parseval {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u : E}
    {P : ι → E} {a n : ι → ℝ} (hA : ∀ i, ⟪u, P i⟫_ℝ = a i / n i)
    (hself : ∀ i, ⟪P i, P i⟫_ℝ = 1 / n i) (horth : ∀ i j, i ≠ j → ⟪P i, P j⟫_ℝ = 0)
    (hC : HasSum (fun i => a i ^ 2 / n i) (‖u‖ ^ 2)) :
    HasSum (fun i => a i • P i) u := by
  classical
  set cf : ι → ℝ := fun i => a i ^ 2 / n i
  have hS : ∀ F : Finset ι, ‖u - ∑ i ∈ F, a i • P i‖ ^ 2 = ‖u‖ ^ 2 - ∑ i ∈ F, cf i := by
    intro F
    have hinner : ⟪u, ∑ i ∈ F, a i • P i⟫_ℝ = ∑ i ∈ F, cf i := by
      rw [inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_right, hA]
      simp only [cf]
      ring
    have hsq : ⟪∑ i ∈ F, a i • P i, ∑ j ∈ F, a j • P j⟫_ℝ = ∑ i ∈ F, cf i := by
      rw [sum_inner]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [inner_sum, Finset.sum_eq_single i (fun j _ hji => by
          rw [real_inner_smul_left, real_inner_smul_right, horth i j (Ne.symm hji), mul_zero,
            mul_zero]) (fun h => (h hi).elim),
        real_inner_smul_left, real_inner_smul_right, hself]
      simp only [cf]
      ring
    rw [norm_sub_sq_real, hinner, ← real_inner_self_eq_norm_sq (∑ i ∈ F, a i • P i), hsq]
    ring
  have hT : Tendsto (fun F : Finset ι => ∑ i ∈ F, cf i) atTop (𝓝 (‖u‖ ^ 2)) := hC
  change Tendsto (fun F : Finset ι => ∑ i ∈ F, a i • P i) atTop (𝓝 u)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have heq : (fun F : Finset ι => ‖∑ i ∈ F, a i • P i - u‖) =
      fun F => √(‖u‖ ^ 2 - ∑ i ∈ F, cf i) := by
    funext F
    rw [norm_sub_rev, ← hS F, Real.sqrt_sq (norm_nonneg _)]
  rw [heq]
  have hlim := ((Real.continuous_sqrt.tendsto _).comp (tendsto_const_nhds.sub hT) :
    Tendsto (fun F : Finset ι => √(‖u‖ ^ 2 - ∑ i ∈ F, cf i)) atTop
      (𝓝 (√(‖u‖ ^ 2 - ‖u‖ ^ 2))))
  rwa [sub_self, Real.sqrt_zero] at hlim

/-- **Lemma 3.3 (expansion of harmonic functions).** Let `c` be conical, `d ≥ 2`, and let
`u ∈ W^{1,2}(B_1)` be weakly harmonic. Then there are a Hilbert basis `{φ_i}` of `L²(S)` of link
eigenfunctions (eigenvalues `λ_i = δ_i (δ_i + d - 2)`, `δ_i ≥ 0`), and coefficients `a_i`, such that
with `P_i = |x|^{δ_i} φ_i(x/|x|)` (weakly harmonic on `B_1`, mutually orthogonal in `L²(B_1)`)

  `u = ∑_i a_i P_i` in `L²(B_1)` (unconditional convergence). -/
theorem expansion (hd : 2 ≤ d) (hc : c.IsConical) {u : L2Pair volume (ball (0 : 𝔼) 1)}
    (hu : c.IsWeakSolution 0 u) :
    ∃ (s : Set (Lp ℝ 2 (sphMeasure d))) (B : HilbertBasis s ℝ (Lp ℝ 2 (sphMeasure d)))
      (Γ : s → Lp 𝔼 2 (sphMeasure d)) (lam δ a : s → ℝ)
      (P : s → Lp ℝ 2 (volume.restrict (ball (0 : 𝔼) 1))),
      ⇑B = ((↑) : s → Lp ℝ 2 (sphMeasure d)) ∧
      (∀ i, 0 ≤ δ i ∧ lam i = δ i * (δ i + d - 2) ∧
        IsLinkEigen hc (lam i) (WithLp.toLp 2 ((i : Lp ℝ 2 (sphMeasure d)), Γ i)) ∧
        (P i : 𝔼 → ℝ) =ᵐ[volume.restrict (ball (0 : 𝔼) 1)]
          homP (δ i) (WithLp.toLp 2 ((i : Lp ℝ 2 (sphMeasure d)), Γ i)) ∧
        ∃ Q : L2Pair volume (ball (0 : 𝔼) 1), c.IsWeakSolution 0 Q ∧ Q.fst = P i) ∧
      (∀ i j, i ≠ j → ⟪P i, P j⟫_ℝ = 0) ∧
      HasSum (fun i => a i • P i) u.fst := by
  classical
  obtain ⟨s, B, Γ, lam, hB, heig, -⟩ := link_spectral hc
  have := separableSpace_sph (d := d)
  have hcount : Countable s :=
    Orthonormal.countable_of_separable
      (hB ▸ B.orthonormal : Orthonormal ℝ (Subtype.val : s → Lp ℝ 2 (sphMeasure d)))
  set v : s → LinkPair d := fun i => WithLp.toLp 2 ((i : Lp ℝ 2 (sphMeasure d)), Γ i)
  set δ : s → ℝ := fun i => indicialRoot d (lam i)
  have hδ0 : ∀ i, 0 ≤ δ i := fun i => indicialRoot_nonneg hd (heig i).1
  have hroot : ∀ i, lam i = δ i * (δ i + d - 2) := fun i => indicialRoot_spec _ (heig i).1
  have hdpos : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hP : ∀ i, MemLp (homP (δ i) (v i)) 2 (volume.restrict (ball (0 : 𝔼) 1)) := fun i =>
    memLp_homFun_ball (δ i) (Lp.memLp (v i).fst) 1 (by linarith [hδ0 i])
  have hG : ∀ i, MemLp (homG (δ i) (v i)) 2 (volume.restrict (ball (0 : 𝔼) 1)) := fun i =>
    memLp_homG_of_isLinkEigen hd (heig i).2 (hroot i) (hδ0 i)
  choose a ha using fun i => rayCoeff_eq hd hc (heig i).2 (hroot i) (hP i) (hG i) hu
  set P : s → Lp ℝ 2 (volume.restrict (ball (0 : 𝔼) 1)) := fun i => (hP i).toLp _
  have hden : ∀ i, (0 : ℝ) < 2 * δ i + d := fun i => by linarith [hδ0 i]
  have hvfst : ∀ i, (v i).fst = (i : Lp ℝ 2 (sphMeasure d)) := fun i => rfl
  -- (A) the coefficients
  have hA : ∀ i, ⟪u.fst, P i⟫_ℝ = a i / (2 * δ i + d) := by
    intro i
    rw [L2.inner_def,
      ← integral_ball_mul_homP_of_rayCoeff (Lp.memLp u.fst) (hδ0 i) (v i) (ha i)]
    refine integral_congr_ae ?_
    filter_upwards [(hP i).coeFn_toLp] with x hx
    rw [hx, RCLike.inner_apply, conj_trivial, mul_comm]
  -- (B) orthogonality
  have hon : Orthonormal ℝ (Subtype.val : s → Lp ℝ 2 (sphMeasure d)) := hB ▸ B.orthonormal
  have hB' : ∀ i j, ⟪P i, P j⟫_ℝ =
      if i = j then 1 / (2 * δ i + d) else 0 := by
    intro i j
    rw [L2.inner_def]
    have e1 : ∫ x in ball (0 : 𝔼) 1, ⟪P i x, P j x⟫_ℝ =
        ∫ x in ball (0 : 𝔼) 1, homP (δ i) (v i) x * homP (δ j) (v j) x := by
      refine integral_congr_ae ?_
      filter_upwards [(hP i).coeFn_toLp, (hP j).coeFn_toLp] with x hx hx'
      rw [hx, hx', RCLike.inner_apply, conj_trivial, mul_comm]
    rw [e1, integral_ball_homP_mul_homP (hδ0 i) (hδ0 j), hvfst, hvfst]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, real_inner_self_eq_norm_sq, hon.1 i]
      ring_nf
    · rw [ite_eq_right hij, hon.2 hij, zero_div]
  -- (C) Parseval for `u`
  set cf : s → ℝ := fun i => a i ^ 2 / (2 * δ i + d)
  have hcf0 : ∀ i, 0 ≤ cf i := fun i => div_nonneg (sq_nonneg _) (hden i).le
  have hterm : ∀ i : s, ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ (d - 1)) *
      ENNReal.ofReal (rayCoeff u.fst (fun w => (i : Lp ℝ 2 (sphMeasure d)) w) r ^ 2) =
        ENNReal.ofReal (cf i) := fun i =>
    lintegral_sq_of_ae_eq_rpow (d := d) (hδ0 i) (ha i)
  have hl := lintegral_ball_eq_tsum B (Lp.stronglyMeasurable u.fst) (lintegral_sq_lt_top u.fst)
  rw [hB, tsum_congr hterm] at hl
  have hfin : ∑' i, ENNReal.ofReal (cf i) ≠ ⊤ := hl ▸ (lintegral_sq_lt_top u.fst).ne
  have hcf : (fun i => (ENNReal.ofReal (cf i)).toReal) = cf :=
    funext fun i => ENNReal.toReal_ofReal (hcf0 i)
  have hsumm : Summable cf := hcf ▸ ENNReal.summable_toReal hfin
  have hnorm : ‖u.fst‖ ^ 2 = ∑' i, cf i := by
    rw [norm_sq_eq_lintegral, hl, ENNReal.tsum_toReal_eq fun i => ENNReal.ofReal_ne_top, hcf]
  have hC : HasSum cf (‖u.fst‖ ^ 2) := hnorm ▸ hsumm.hasSum
  have horth : ∀ i j, i ≠ j → ⟪P i, P j⟫_ℝ = 0 := fun i j hij => by rw [hB', ite_eq_right hij]
  refine ⟨s, B, Γ, lam, δ, a, P, hB, fun i => ⟨hδ0 i, hroot i, (heig i).2, (hP i).coeFn_toLp,
    homPair (δ i) (v i) 1 (hP i) (hG i),
    homPair_isWeakSolution (hP i) (hG i) hd hc (heig i).2 (hroot i), rfl⟩, horth, ?_⟩
  -- (D) the partial sums converge
  exact hasSum_of_parseval (n := fun i => 2 * δ i + d) hA
    (fun i => by rw [hB', ite_eq_left rfl]) horth hC

end Lemma33

end ConicalKahler.Sobolev
