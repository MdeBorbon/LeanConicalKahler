module

public import ConicalKahler.Sobolev.Expansion
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

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
  have hpt : ∀ p : Sph d × Ioi (0 : ℝ), (shell d a b).indicator F (polarMap p) =
      (Ioo a b).indicator (fun r => F (r • (p.1 : 𝔼))) (p.2 : ℝ) := by
    intro p
    by_cases hp : (p.2 : ℝ) ∈ Ioo a b
    · rw [indicator_of_mem (show polarMap p ∈ shell d a b by
          simpa [shell, norm_polarMap] using hp), indicator_of_mem hp]
      rfl
    · rw [indicator_of_notMem (show polarMap p ∉ shell d a b by
          simpa [shell, norm_polarMap] using hp), indicator_of_notMem hp]
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
  · simp only [indicator_of_notMem hr, mul_zero, indicator_zero', Pi.zero_apply]
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
    rw [hfd, ← rpow_sub_one_eq_pow hr0]
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

end ConicalKahler.Sobolev
