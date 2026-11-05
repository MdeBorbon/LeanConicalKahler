module

public import ConicalKahler.Sobolev.ConeLaplacian
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Codimension-two sets have zero capacity: density of test functions on the regular part

The singular set of the real cone model is `S = ⋃_a {r_a = 0}`, a finite union of codimension-two
linear subspaces of `ℝ^d`. Following the paper (§2.1, Lemma 2.2), test functions supported on the
regular part `Ω \ S` are dense in `W^{1,2}_0(Ω)`:

  `dense_testSubmodule_regular : (testSubmodule volume Ω (Ω \ coneSingular e)).topologicalClosure
    = H01 volume Ω`.

The cut-offs are logarithmic, `χ_n(x) = h_n(t(x))` with `t = x_{i₀}² + x_{i₁}²` (so `t = r_a²`) and
`h_n(t) = S(log t / n + 2)` for the smooth step `S` (`Real.smoothTransition`). They are smooth,
vanish near `{t = 0}`, equal `1` for `t ≥ e^{-n}`, and have energy
`∫_{B_R} |∇χ_n|² ≤ C(R)/n → 0`. The energy is computed by splitting `ℝ^d` into the plane of
`(x_{i₀}, x_{i₁})` and its complement (Fubini) and using the radial integral in the plane.

As a consequence (`isWeakSolution_iff_regular`), the weak equation needs to be tested only against
test functions supported on the regular part, where the metric is smooth.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set
open scoped ContDiff ENNReal Real

namespace ConicalKahler.Sobolev

/-! ### The one-dimensional logarithmic cut-off -/

/-- `h_n(t) = S(log t / n + 2)` for `t > 0` and `0` for `t ≤ 0`. -/
def logCut (n : ℕ) (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else Real.smoothTransition (Real.log t / n + 2)

theorem logCut_nonneg (n : ℕ) (t : ℝ) : 0 ≤ logCut n t := by
  unfold logCut
  split_ifs
  · exact le_rfl
  · exact Real.smoothTransition.nonneg _

theorem logCut_le_one (n : ℕ) (t : ℝ) : logCut n t ≤ 1 := by
  unfold logCut
  split_ifs
  · exact zero_le_one
  · exact Real.smoothTransition.le_one _

theorem logCut_eq_zero {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : t < Real.exp (-2 * n)) :
    logCut n t = 0 := by
  unfold logCut
  split_ifs with h
  · rfl
  · push Not at h
    refine Real.smoothTransition.zero_of_nonpos ?_
    have hlog : Real.log t < -2 * n := by
      rw [← Real.log_exp (-2 * n)]
      exact Real.log_lt_log h ht
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [div_add' _ _ _ hn'.ne', div_nonpos_iff]
    right
    exact ⟨by linarith, hn'.le⟩

theorem logCut_eq_one {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : Real.exp (-n) ≤ t) :
    logCut n t = 1 := by
  have htpos : 0 < t := (Real.exp_pos _).trans_le ht
  unfold logCut
  rw [ite_eq_right (not_le.mpr htpos)]
  refine Real.smoothTransition.one_of_one_le ?_
  have hlog : -(n : ℝ) ≤ Real.log t := by
    rw [← Real.log_exp (-(n : ℝ))]
    exact Real.log_le_log (Real.exp_pos _) ht
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have : -1 ≤ Real.log t / n := by
    rw [le_div_iff₀ hn']
    linarith
  linarith

theorem contDiff_logCut {n : ℕ} (hn : 0 < n) : ContDiff ℝ ∞ (logCut n) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge t (Real.exp (-2 * n)) with ht | ht
  · have h : logCut n =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact logCut_eq_zero hn hs
    exact contDiffAt_const.congr_of_eventuallyEq h
  · have htpos : 0 < t := (Real.exp_pos _).trans_le ht
    have h : logCut n =ᶠ[𝓝 t] fun s => Real.smoothTransition (Real.log s / n + 2) := by
      filter_upwards [Ioi_mem_nhds htpos] with s hs
      simp [logCut, not_le.mpr hs]
    refine ContDiffAt.congr_of_eventuallyEq ?_ h
    exact (Real.smoothTransition.contDiffAt (n := ⊤)).comp t
      (((Real.contDiffAt_log.mpr htpos.ne').div_const _).add contDiffAt_const)

theorem hasDerivAt_logCut {n : ℕ} {t : ℝ} (ht : 0 < t) :
    HasDerivAt (logCut n) (deriv Real.smoothTransition (Real.log t / n + 2) * (t⁻¹ / n)) t := by
  have h : logCut n =ᶠ[𝓝 t] fun s => Real.smoothTransition (Real.log s / n + 2) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simp [logCut, not_le.mpr hs]
  refine HasDerivAt.congr_of_eventuallyEq ?_ h
  have hS : DifferentiableAt ℝ Real.smoothTransition (Real.log t / n + 2) :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) _
  exact hS.hasDerivAt.comp t (((Real.hasDerivAt_log ht.ne').div_const _).add_const 2)

theorem deriv_logCut_eq_zero_of_lt {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : t < Real.exp (-2 * n)) :
    deriv (logCut n) t = 0 := by
  have h : logCut n =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact logCut_eq_zero hn hs
  rw [h.deriv_eq, deriv_const]

theorem deriv_logCut_eq_zero_of_gt {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : Real.exp (-n) < t) :
    deriv (logCut n) t = 0 := by
  have h : logCut n =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact logCut_eq_one hn hs.le
  rw [h.deriv_eq, deriv_const]

/-- The derivative of the smooth step is bounded. -/
theorem exists_bound_deriv_smoothTransition :
    ∃ C, 0 ≤ C ∧ ∀ x, |deriv Real.smoothTransition x| ≤ C := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hsupp : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun x hx => ?_
    rcases not_and_or.mp hx with h | h
    · have h' : x < 0 := lt_of_not_ge h
      have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds h'] with s hs
        exact Real.smoothTransition.zero_of_nonpos hs.le
      rw [hev.deriv_eq, deriv_const]
    · have h' : 1 < x := lt_of_not_ge h
      have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds h'] with s hs
        exact Real.smoothTransition.one_of_one_le hs.le
      rw [hev.deriv_eq, deriv_const]
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
  exact ⟨C, (norm_nonneg _).trans (hC 0), fun x => by simpa [Real.norm_eq_abs] using hC x⟩

/-- `|h_n'(t)| ≤ C/(n t)` for `t > 0`. -/
theorem abs_deriv_logCut_le {n : ℕ} (hn : 0 < n) {C : ℝ}
    (hC : ∀ x, |deriv Real.smoothTransition x| ≤ C) {t : ℝ} (ht : 0 < t) :
    |deriv (logCut n) t| ≤ C / (n * t) := by
  rw [(hasDerivAt_logCut ht).deriv, abs_mul]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h1 : |t⁻¹ / n| = 1 / (n * t) := by
    rw [abs_of_pos (by positivity)]
    field_simp
  rw [h1]
  calc |deriv Real.smoothTransition (Real.log t / n + 2)| * (1 / (n * t)) ≤ C * (1 / (n * t)) :=
        mul_le_mul_of_nonneg_right (hC _) (by positivity)
    _ = C / (n * t) := by ring

theorem continuous_deriv_logCut {n : ℕ} (hn : 0 < n) : Continuous (deriv (logCut n)) :=
  (contDiff_logCut hn).continuous_deriv (by simp)

/-! ### The energy of the cut-off in a plane -/

/-- `G_n(s) = 4 s h_n'(s)²`: the squared gradient of `y ↦ h_n(|y|²)` in a plane, at `|y|² = s`. -/
def cutEnergy (n : ℕ) (s : ℝ) : ℝ := 4 * s * deriv (logCut n) s ^ 2

theorem cutEnergy_nonneg (n : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ cutEnergy n s := by
  unfold cutEnergy
  positivity

theorem continuous_cutEnergy {n : ℕ} (hn : 0 < n) : Continuous (cutEnergy n) :=
  (continuous_const.mul continuous_id).mul ((continuous_deriv_logCut hn).pow 2)

theorem cutEnergy_eq_zero_of_gt {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : Real.exp (-n) < s) :
    cutEnergy n s = 0 := by
  simp [cutEnergy, deriv_logCut_eq_zero_of_gt hn hs]

/-- **One-dimensional bound:** `∫_0^∞ y G_n(y²) dy ≤ 2C²/n`. -/
theorem integral_Ioi_cutEnergy_le {n : ℕ} (hn : 0 < n) {C : ℝ}
    (hC : ∀ x, |deriv Real.smoothTransition x| ≤ C) :
    ∫ y in Ioi (0 : ℝ), y * cutEnergy n (y ^ 2) ≤ 2 * C ^ 2 / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set a := Real.exp (-(n : ℝ))
  set b := Real.exp (-(n : ℝ) / 2)
  have ha : 0 < a := Real.exp_pos _
  have hab : a ≤ b := Real.exp_le_exp.mpr (by linarith)
  set g : ℝ → ℝ := (Icc a b).indicator fun y => 4 * C ^ 2 / (n : ℝ) ^ 2 * y⁻¹
  have hpt : ∀ y ∈ Ioi (0 : ℝ), y * cutEnergy n (y ^ 2) ≤ g y := by
    intro y hy
    have hy : 0 < y := hy
    have hg0 : 0 ≤ g y := by
      simp only [g, indicator]
      split_ifs
      · positivity
      · exact le_rfl
    by_cases h1 : y ^ 2 < Real.exp (-2 * n)
    · simp [cutEnergy, deriv_logCut_eq_zero_of_lt hn h1, hg0]
    by_cases h2 : Real.exp (-n) < y ^ 2
    · simp [cutEnergy, deriv_logCut_eq_zero_of_gt hn h2, hg0]
    push Not at h1 h2
    have hsq : ∀ x : ℝ, Real.exp x ^ 2 = Real.exp (2 * x) := fun x => by
      rw [sq, ← Real.exp_add]
      ring_nf
    have hya : a ≤ y := by
      have : a ^ 2 ≤ y ^ 2 := by rw [hsq]; convert h1 using 2; ring
      exact (pow_le_pow_iff_left₀ ha.le hy.le two_ne_zero).mp this
    have hyb : y ≤ b := by
      have : y ^ 2 ≤ b ^ 2 := by rw [hsq]; convert h2 using 2; ring
      exact (pow_le_pow_iff_left₀ hy.le (Real.exp_pos _).le two_ne_zero).mp this
    have hgy : g y = 4 * C ^ 2 / (n : ℝ) ^ 2 * y⁻¹ := by
      simp only [g, indicator, mem_Icc, hya, hyb, and_self, ite_true]
    rw [hgy]
    have hy2 : 0 < y ^ 2 := by positivity
    have hD := abs_deriv_logCut_le hn hC hy2
    have hD2 : deriv (logCut n) (y ^ 2) ^ 2 ≤ (C / (n * y ^ 2)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hD 2
    calc y * cutEnergy n (y ^ 2) = 4 * y ^ 3 * deriv (logCut n) (y ^ 2) ^ 2 := by
          unfold cutEnergy
          ring
      _ ≤ 4 * y ^ 3 * (C / (n * y ^ 2)) ^ 2 := by gcongr
      _ = 4 * C ^ 2 / (n : ℝ) ^ 2 * y⁻¹ := by
          field_simp
  have hLc : Continuous fun y : ℝ => y * cutEnergy n (y ^ 2) :=
    continuous_id.mul ((continuous_cutEnergy hn).comp (continuous_pow 2))
  have hLs : HasCompactSupport fun y : ℝ => y * cutEnergy n (y ^ 2) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -b) (b := b)) fun y hy => ?_
    have hy' : b < |y| := by
      rcases not_and_or.mp hy with h | h
      · rw [abs_of_neg (by have := Real.exp_pos (-(n : ℝ) / 2); linarith)]
        linarith
      · rw [abs_of_pos (by have := Real.exp_pos (-(n : ℝ) / 2); linarith)]
        linarith
    have : Real.exp (-n) < y ^ 2 := by
      have hb2 : b ^ 2 = Real.exp (-n) := by
        rw [sq, ← Real.exp_add]
        ring_nf
      rw [← hb2, ← sq_abs y]
      exact pow_lt_pow_left₀ hy' (Real.exp_pos _).le two_ne_zero
    simp [cutEnergy_eq_zero_of_gt hn this]
  have hgi : Integrable g := by
    refine (integrable_indicator_iff measurableSet_Icc).mpr ?_
    exact ContinuousOn.integrableOn_Icc (continuousOn_const.mul
      (continuousOn_inv₀.mono fun y hy => (ha.trans_le hy.1).ne'))
  calc ∫ y in Ioi (0 : ℝ), y * cutEnergy n (y ^ 2)
      ≤ ∫ y in Ioi (0 : ℝ), g y :=
        setIntegral_mono_on (hLc.integrable_of_hasCompactSupport hLs).integrableOn
          hgi.integrableOn measurableSet_Ioi hpt
    _ = ∫ y in Icc a b, 4 * C ^ 2 / (n : ℝ) ^ 2 * y⁻¹ := by
        rw [setIntegral_indicator measurableSet_Icc,
          show Ioi (0 : ℝ) ∩ Icc a b = Icc a b from inter_eq_right.mpr fun y hy => ha.trans_le hy.1]
    _ = 4 * C ^ 2 / (n : ℝ) ^ 2 * Real.log (b / a) := by
        rw [integral_const_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
          integral_inv_of_pos ha (Real.exp_pos _)]
    _ = 2 * C ^ 2 / n := by
        rw [Real.log_div (Real.exp_pos _).ne' ha.ne', Real.log_exp, Real.log_exp]
        field_simp
        ring

/-- **The energy of the cut-off in a plane:** `∫_{ℝ²} G_n(|y|²) dy ≤ 4π C²/n`. -/
theorem integral_cutEnergy_plane_le {P : Type} [Fintype P] (hP : Fintype.card P = 2) {n : ℕ}
    (hn : 0 < n) {C : ℝ} (hC : ∀ x, |deriv Real.smoothTransition x| ≤ C) :
    ∫ y : EuclideanSpace ℝ P, cutEnergy n (‖y‖ ^ 2) ≤ 4 * π * C ^ 2 / n := by
  have : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  have hrad := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ P))
    (fun r : ℝ => cutEnergy n (r ^ 2))
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ P) = 2 := by simp [hP]
  have hball : (volume : Measure (EuclideanSpace ℝ P)).real (Metric.ball 0 1) = π := by
    rw [measureReal_def, InnerProductSpace.volume_ball_of_dim_even (k := 1) (by rw [hdim]) 0 1]
    simp [Real.pi_pos.le]
  rw [hrad, hdim, hball]
  have h1 := integral_Ioi_cutEnergy_le hn hC
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  calc 2 * (π * ∫ y in Ioi (0 : ℝ), y * cutEnergy n (y ^ 2))
      = (2 * π) * ∫ y in Ioi (0 : ℝ), y * cutEnergy n (y ^ 2) := by ring
    _ ≤ (2 * π) * (2 * C ^ 2 / n) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 4 * π * C ^ 2 / n := by ring

/-! ### Splitting `ℝ^d` into a plane and its complement -/

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- `x_{i₀}² + x_{i₁}²`. -/
def planeSq (i₀ i₁ : Fin d) (x : 𝔼) : ℝ := x i₀ ^ 2 + x i₁ ^ 2

theorem planeSq_nonneg (i₀ i₁ : Fin d) (x : 𝔼) : 0 ≤ planeSq i₀ i₁ x := by
  unfold planeSq
  positivity

theorem continuous_planeSq (i₀ i₁ : Fin d) : Continuous (planeSq i₀ i₁) :=
  ((PiLp.continuous_apply 2 _ i₀).pow 2).add ((PiLp.continuous_apply 2 _ i₁).pow 2)

/-- **Fubini over the plane of `(x_{i₀}, x_{i₁})`.** For `G ≥ 0` continuous with bounded support,
`∫_{B̄_R} G(x_{i₀}² + x_{i₁}²) dx ≤ (∫_{ℝ²} G(|y|²) dy) · |[-R, R]^{d-2}|`. -/
theorem integral_closedBall_le_plane {i₀ i₁ : Fin d} (hi : i₀ ≠ i₁) {G : ℝ → ℝ}
    (hG0 : ∀ s, 0 ≤ s → 0 ≤ G s) (hGc : Continuous G) {M : ℝ} (hGM : ∀ s, M < s → G s = 0)
    (R : ℝ) :
    ∫ x in Metric.closedBall (0 : 𝔼) R, G (planeSq i₀ i₁ x) ≤
      (∫ y : EuclideanSpace ℝ {i : Fin d // i = i₀ ∨ i = i₁}, G (‖y‖ ^ 2)) *
        (volume (Set.univ.pi fun _ : {i : Fin d // ¬(i = i₀ ∨ i = i₁)} => Icc (-R) R)).toReal := by
  classical
  let p : Fin d → Prop := fun i => i = i₀ ∨ i = i₁
  let Φ : 𝔼 ≃ᵐ ({i // p i} → ℝ) × ({i // ¬p i} → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.trans
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ => ℝ) p)
  have hΦ : MeasurePreserving Φ volume (volume.prod volume) :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).trans
      (measurePreserving_piEquivPiSubtypeProd (fun _ : Fin d => (volume : Measure ℝ)) p)
  let box : Set ({i // ¬p i} → ℝ) := Set.univ.pi fun _ => Icc (-R) R
  let f1 : ({i // p i} → ℝ) → ℝ := fun z => G (∑ j, z j ^ 2)
  let f2 : ({i // ¬p i} → ℝ) → ℝ := box.indicator 1
  let F : ({i // p i} → ℝ) × ({i // ¬p i} → ℝ) → ℝ := fun z => f1 z.1 * f2 z.2
  have hsum : ∀ x : 𝔼, ∑ j : {i // p i}, x j.1 ^ 2 = planeSq i₀ i₁ x := fun x => by
    rw [← Finset.sum_subtype ({i₀, i₁} : Finset (Fin d)) (p := p) (fun i => by simp [p])
      (fun i => x i ^ 2), Finset.sum_pair hi]
    rfl
  have hf1e : ∀ y : EuclideanSpace ℝ {i // p i}, f1 (WithLp.ofLp y) = G (‖y‖ ^ 2) := fun y => by
    simp only [f1]
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hGe : Integrable (fun y : EuclideanSpace ℝ {i // p i} => G (‖y‖ ^ 2)) := by
    refine (hGc.comp (continuous_norm.pow 2)).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ {i // p i})
      (Real.sqrt (max M 0))) fun y hy => ?_
    have hy' : Real.sqrt (max M 0) < ‖y‖ := by simpa using hy
    have : max M 0 < ‖y‖ ^ 2 := Real.lt_sq_of_sqrt_lt hy'
    exact hGM _ (lt_of_le_of_lt (le_max_left _ _) this)
  have hT := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp {i // p i}
  have hf1 : Integrable f1 := by
    rw [← hT.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    exact hGe.congr (Eventually.of_forall fun y => (hf1e y).symm)
  have hbox : MeasurableSet box := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hf2 : Integrable f2 :=
    (integrable_indicator_iff hbox).mpr (integrableOn_const
      (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top.ne)
  have hF : Integrable F (volume.prod volume) := hf1.mul_prod hf2
  have hFΦ : Integrable (fun x => F (Φ x)) :=
    (hΦ.integrable_comp_emb Φ.measurableEmbedding).mpr hF
  have hpt : ∀ x : 𝔼, (Metric.closedBall 0 R).indicator (fun x => G (planeSq i₀ i₁ x)) x ≤
      F (Φ x) := by
    intro x
    have hF0 : 0 ≤ F (Φ x) := by
      refine mul_nonneg (hG0 _ (Finset.sum_nonneg fun j _ => sq_nonneg _)) ?_
      simp only [f2, indicator]
      split_ifs <;> norm_num
    by_cases hx : x ∈ Metric.closedBall (0 : 𝔼) R
    · rw [indicator_of_mem hx]
      have hmem : (Φ x).2 ∈ box := by
        intro j _
        have h1 : |x j.1| ≤ R := (PiLp.norm_apply_le x j.1).trans (by simpa using hx)
        exact abs_le.mp h1
      refine le_of_eq ?_
      show G (planeSq i₀ i₁ x) = G (∑ j : {i // p i}, x j.1 ^ 2) * box.indicator 1 (Φ x).2
      rw [indicator_of_mem hmem, Pi.one_apply, mul_one, hsum]
    · rw [indicator_of_notMem hx]
      exact hF0
  have hind : Integrable ((Metric.closedBall (0 : 𝔼) R).indicator fun x => G (planeSq i₀ i₁ x)) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      ((hGc.comp (continuous_planeSq i₀ i₁)).continuousOn.integrableOn_compact
        (isCompact_closedBall _ _))
  calc ∫ x in Metric.closedBall (0 : 𝔼) R, G (planeSq i₀ i₁ x)
      = ∫ x, (Metric.closedBall (0 : 𝔼) R).indicator (fun x => G (planeSq i₀ i₁ x)) x :=
        (integral_indicator measurableSet_closedBall).symm
    _ ≤ ∫ x, F (Φ x) := integral_mono hind hFΦ hpt
    _ = ∫ z, F z ∂(volume.prod volume) := hΦ.integral_comp' F
    _ = (∫ z, f1 z) * ∫ z, f2 z := integral_prod_mul f1 f2
    _ = _ := by
        congr 1
        · rw [← hT.integral_comp' f1]
          exact integral_congr_ae (Eventually.of_forall fun y => hf1e y)
        · rw [integral_indicator_one hbox, measureReal_def]

/-! ### The cut-off on `ℝ^d` -/

/-- **The logarithmic cut-off** `χ_n(x) = h_n(x_{i₀}² + x_{i₁}²)`, which vanishes near the plane
`{x_{i₀} = x_{i₁} = 0}`. -/
def planeCut (n : ℕ) (i₀ i₁ : Fin d) (x : 𝔼) : ℝ := logCut n (planeSq i₀ i₁ x)

theorem contDiff_planeSq (i₀ i₁ : Fin d) : ContDiff ℝ ∞ (planeSq i₀ i₁) := by
  have h0 : ContDiff ℝ ∞ fun x : 𝔼 => x i₀ := (EuclideanSpace.proj (𝕜 := ℝ) i₀).contDiff
  have h1 : ContDiff ℝ ∞ fun x : 𝔼 => x i₁ := (EuclideanSpace.proj (𝕜 := ℝ) i₁).contDiff
  exact (h0.pow 2).add (h1.pow 2)

theorem contDiff_planeCut {n : ℕ} (hn : 0 < n) (i₀ i₁ : Fin d) :
    ContDiff ℝ ∞ (planeCut n i₀ i₁) :=
  (contDiff_logCut hn).comp (contDiff_planeSq i₀ i₁)

theorem planeCut_nonneg (n : ℕ) (i₀ i₁ : Fin d) (x : 𝔼) : 0 ≤ planeCut n i₀ i₁ x :=
  logCut_nonneg n _

theorem planeCut_le_one (n : ℕ) (i₀ i₁ : Fin d) (x : 𝔼) : planeCut n i₀ i₁ x ≤ 1 :=
  logCut_le_one n _

theorem tsupport_planeCut_subset {n : ℕ} (hn : 0 < n) (i₀ i₁ : Fin d) :
    tsupport (planeCut n i₀ i₁) ⊆ {x | Real.exp (-2 * n) ≤ planeSq i₀ i₁ x} := by
  refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_const (continuous_planeSq i₀ i₁))
  by_contra h
  exact hx (logCut_eq_zero hn (lt_of_not_ge h))

theorem norm_gradient_eq_norm_fderiv (f : 𝔼 → ℝ) (x : 𝔼) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (toDual ℝ 𝔼).symm.norm_map _

/-- **Gradient bound:** `|∇χ_n|² ≤ G_n(x_{i₀}² + x_{i₁}²)`. -/
theorem norm_gradient_planeCut_sq_le {n : ℕ} (hn : 0 < n) {i₀ i₁ : Fin d} (hi : i₀ ≠ i₁)
    (x : 𝔼) : ‖gradient (planeCut n i₀ i₁) x‖ ^ 2 ≤ cutEnergy n (planeSq i₀ i₁ x) := by
  set t := planeSq i₀ i₁ x
  set L : 𝔼 →L[ℝ] ℝ := (2 * x i₀) • EuclideanSpace.proj i₀ + (2 * x i₁) • EuclideanSpace.proj i₁
  have hP : HasFDerivAt (planeSq i₀ i₁) L x := by
    have h0 := ((EuclideanSpace.proj (𝕜 := ℝ) i₀).hasFDerivAt (x := x)).pow 2
    have h1 := ((EuclideanSpace.proj (𝕜 := ℝ) i₁).hasFDerivAt (x := x)).pow 2
    show HasFDerivAt (fun y : 𝔼 => EuclideanSpace.proj (𝕜 := ℝ) i₀ y ^ 2 +
      EuclideanSpace.proj (𝕜 := ℝ) i₁ y ^ 2) L x
    refine (h0.add h1).congr_fderiv ?_
    ext v
    simp [L]
  have hD : HasDerivAt (logCut n) (deriv (logCut n) t) t :=
    ((contDiff_logCut hn).differentiable (by simp) t).hasDerivAt
  have hχ : HasFDerivAt (planeCut n i₀ i₁) (deriv (logCut n) t • L) x := hD.comp_hasFDerivAt x hP
  have hL : ‖L‖ ≤ 2 * Real.sqrt t := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have hv : v i₀ ^ 2 + v i₁ ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {i₀, i₁})
        (f := fun i => ‖v i‖ ^ 2) (fun i _ _ => sq_nonneg _)
      rw [Finset.sum_pair hi] at this
      simpa [Real.norm_eq_abs, sq_abs] using this
    have hsq : (L v) ^ 2 ≤ (2 * Real.sqrt t * ‖v‖) ^ 2 := by
      have ht : Real.sqrt t ^ 2 = t := Real.sq_sqrt (planeSq_nonneg i₀ i₁ x)
      have hLv : L v = 2 * x i₀ * v i₀ + 2 * x i₁ * v i₁ := by
        simp [L]
      rw [hLv]
      have htx : x i₀ ^ 2 + x i₁ ^ 2 = t := rfl
      calc (2 * x i₀ * v i₀ + 2 * x i₁ * v i₁) ^ 2
          ≤ 4 * (x i₀ ^ 2 + x i₁ ^ 2) * (v i₀ ^ 2 + v i₁ ^ 2) := by
            nlinarith [sq_nonneg (x i₀ * v i₁ - x i₁ * v i₀)]
        _ ≤ 4 * t * ‖v‖ ^ 2 := by
            rw [htx]
            exact mul_le_mul_of_nonneg_left hv (mul_nonneg (by norm_num) (planeSq_nonneg i₀ i₁ x))
        _ = (2 * Real.sqrt t * ‖v‖) ^ 2 := by rw [mul_pow, mul_pow, ht]; ring
    calc ‖L v‖ = Real.sqrt ((L v) ^ 2) := by rw [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt ((2 * Real.sqrt t * ‖v‖) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 2 * Real.sqrt t * ‖v‖ := Real.sqrt_sq (by positivity)
  rw [norm_gradient_eq_norm_fderiv, hχ.fderiv, norm_smul, Real.norm_eq_abs]
  calc (|deriv (logCut n) t| * ‖L‖) ^ 2 ≤ (|deriv (logCut n) t| * (2 * Real.sqrt t)) ^ 2 := by
        gcongr
    _ = cutEnergy n t := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (planeSq_nonneg i₀ i₁ x), sq_abs]
        unfold cutEnergy
        ring

theorem card_plane {i₀ i₁ : Fin d} (hi : i₀ ≠ i₁) :
    Fintype.card {i : Fin d // i = i₀ ∨ i = i₁} = 2 := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun i : Fin d => i = i₀ ∨ i = i₁) = {i₀, i₁} := by
    ext i
    simp
  rw [this, Finset.card_pair hi]

/-- **The energy of `χ_n` on a ball tends to zero:** `∫_{B̄_R} |∇χ_n|² ≤ (4πC²/n) V_R`. -/
theorem integral_closedBall_norm_gradient_planeCut_le {n : ℕ} (hn : 0 < n) {i₀ i₁ : Fin d}
    (hi : i₀ ≠ i₁) {C : ℝ} (hC : ∀ x, |deriv Real.smoothTransition x| ≤ C) (R : ℝ) :
    ∫ x in Metric.closedBall (0 : 𝔼) R, ‖gradient (planeCut n i₀ i₁) x‖ ^ 2 ≤
      4 * π * C ^ 2 / n *
        (volume (Set.univ.pi fun _ : {i : Fin d // ¬(i = i₀ ∨ i = i₁)} => Icc (-R) R)).toReal := by
  have hgc : Continuous (gradient (planeCut n i₀ i₁)) :=
    (toDual ℝ 𝔼).symm.continuous.comp
      ((contDiff_planeCut hn i₀ i₁).continuous_fderiv (by simp))
  have hV : 0 ≤ (volume (Set.univ.pi fun _ : {i : Fin d // ¬(i = i₀ ∨ i = i₁)} =>
      Icc (-R) R)).toReal := ENNReal.toReal_nonneg
  calc ∫ x in Metric.closedBall (0 : 𝔼) R, ‖gradient (planeCut n i₀ i₁) x‖ ^ 2
      ≤ ∫ x in Metric.closedBall (0 : 𝔼) R, cutEnergy n (planeSq i₀ i₁ x) := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_closedBall fun x _ =>
          norm_gradient_planeCut_sq_le hn hi x
        · exact (hgc.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
        · exact ((continuous_cutEnergy hn).comp (continuous_planeSq i₀ i₁)).continuousOn.integrableOn_compact
            (isCompact_closedBall _ _)
    _ ≤ (∫ y : EuclideanSpace ℝ {i : Fin d // i = i₀ ∨ i = i₁}, cutEnergy n (‖y‖ ^ 2)) *
          (volume (Set.univ.pi fun _ : {i : Fin d // ¬(i = i₀ ∨ i = i₁)} => Icc (-R) R)).toReal :=
        integral_closedBall_le_plane hi (fun s hs => cutEnergy_nonneg n hs) (continuous_cutEnergy hn)
          (M := Real.exp (-n)) (fun s hs => cutEnergy_eq_zero_of_gt hn hs) R
    _ ≤ 4 * π * C ^ 2 / n *
          (volume (Set.univ.pi fun _ : {i : Fin d // ¬(i = i₀ ∨ i = i₁)} => Icc (-R) R)).toReal :=
        mul_le_mul_of_nonneg_right (integral_cutEnergy_plane_le (card_plane hi) hn hC) hV

/-! ### Approximation by test functions vanishing near a plane -/

/-- The plane `{x_{i₀} = x_{i₁} = 0}`. -/
def planeZero (i₀ i₁ : Fin d) : Set 𝔼 := {x | planeSq i₀ i₁ x = 0}

theorem isClosed_planeZero (i₀ i₁ : Fin d) : IsClosed (planeZero i₀ i₁) :=
  isClosed_eq (continuous_planeSq i₀ i₁) continuous_const

/-- The plane is Lebesgue-null. -/
theorem ae_notMem_planeZero (i₀ i₁ : Fin d) : ∀ᵐ x : 𝔼, x ∉ planeZero i₀ i₁ := by
  let L : 𝔼 →ₗ[ℝ] ℝ := (EuclideanSpace.proj (𝕜 := ℝ) i₀).toLinearMap
  have hs : LinearMap.ker L ≠ ⊤ := by
    intro h
    have hmem : EuclideanSpace.single i₀ (1 : ℝ) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    simp [L] at hmem
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) (Measure.addHaar_submodule volume _ hs)
  simp only [Set.mem_ofPred_eq, not_not, planeZero, planeSq] at hx
  have h0 : x i₀ ^ 2 = 0 := by nlinarith [sq_nonneg (x i₀), sq_nonneg (x i₁)]
  show L x = 0
  simpa [L] using h0

theorem eventually_planeCut_eq_one {i₀ i₁ : Fin d} {x : 𝔼} (hx : x ∉ planeZero i₀ i₁) :
    ∀ᶠ n : ℕ in atTop, planeCut (n + 1) i₀ i₁ x = 1 := by
  have hpos : 0 < planeSq i₀ i₁ x :=
    lt_of_le_of_ne (planeSq_nonneg i₀ i₁ x) (Ne.symm hx)
  have hlim : Tendsto (fun n : ℕ => Real.exp (-((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  filter_upwards [(tendsto_order.1 hlim).2 _ hpos] with n hn
  exact logCut_eq_one n.succ_pos hn.le

theorem gradient_mul {f g : 𝔼 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : 𝔼) :
    gradient (fun y => f y * g y) x = f x • gradient g x + g x • gradient f x := by
  simp only [gradient]
  rw [show (fun y => f y * g y) = f * g from rfl, fderiv_mul (hf x) (hg x), map_add, map_smul,
    map_smul]

/-- Dominated convergence: `∫ f (1 - χ_n)² → 0` for integrable `f ≥ 0`. -/
theorem tendsto_integral_mul_one_sub_planeCut {i₀ i₁ : Fin d} {f : 𝔼 → ℝ} (hf : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfm : Continuous f) :
    Tendsto (fun n : ℕ => ∫ x, f x * (1 - planeCut (n + 1) i₀ i₁ x) ^ 2) atTop (𝓝 0) := by
  have hχ01 : ∀ n x, 0 ≤ (1 - planeCut (n + 1) i₀ i₁ x) ^ 2 ∧
      (1 - planeCut (n + 1) i₀ i₁ x) ^ 2 ≤ 1 := fun n x => by
    have h0 := planeCut_nonneg (n + 1) i₀ i₁ x
    have h1 := planeCut_le_one (n + 1) i₀ i₁ x
    exact ⟨sq_nonneg _, by nlinarith⟩
  have h := tendsto_integral_of_dominated_convergence f
    (F := fun n x => f x * (1 - planeCut (n + 1) i₀ i₁ x) ^ 2) (f := fun _ => (0 : ℝ))
    (fun n => (hfm.mul ((continuous_const.sub
      (contDiff_planeCut n.succ_pos i₀ i₁).continuous).pow 2)).aestronglyMeasurable)
    hf (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 x) (hχ01 n x).1)]
      exact mul_le_of_le_one_right (hf0 x) (hχ01 n x).2)
    (by
      filter_upwards [ae_notMem_planeZero i₀ i₁] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_planeCut_eq_one hx] with n hn
      rw [hn, sub_self]
      ring)
  rwa [integral_zero] at h

/-- The pointwise estimate for the gradient of `χ φ - φ`. -/
theorem norm_gradient_mul_sub_sq_le {χ φ : 𝔼 → ℝ} (hχ : Differentiable ℝ χ)
    (hφ : Differentiable ℝ φ) (x : 𝔼) :
    ‖gradient (χ * φ) x - gradient φ x‖ ^ 2 ≤
      2 * (‖gradient φ x‖ ^ 2 * (1 - χ x) ^ 2) + 2 * (φ x ^ 2 * ‖gradient χ x‖ ^ 2) := by
  have hg : gradient (χ * φ) x - gradient φ x = (χ x - 1) • gradient φ x + φ x • gradient χ x := by
    rw [show χ * φ = fun y => χ y * φ y from rfl, gradient_mul hχ hφ]
    module
  rw [hg]
  set a := |χ x - 1| * ‖gradient φ x‖
  set b := |φ x| * ‖gradient χ x‖
  have h1 : ‖(χ x - 1) • gradient φ x + φ x • gradient χ x‖ ≤ a + b := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have ha : a ^ 2 = ‖gradient φ x‖ ^ 2 * (1 - χ x) ^ 2 := by
    simp only [a]
    rw [mul_pow, sq_abs]
    ring
  have hb : b ^ 2 = φ x ^ 2 * ‖gradient χ x‖ ^ 2 := by
    simp only [b]
    rw [mul_pow, sq_abs]
  rw [← ha, ← hb]
  have h0 := norm_nonneg ((χ x - 1) • gradient φ x + φ x • gradient χ x)
  have hab : 0 ≤ a + b := by positivity
  calc ‖(χ x - 1) • gradient φ x + φ x • gradient χ x‖ ^ 2 ≤ (a + b) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
    _ ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]

variable [NeZero d]

theorem norm_fst_cut_sub_le (Ω : Set 𝔼) {U V : Set 𝔼} {φ : 𝔼 → ℝ} (hφ : IsTestFn U φ)
    {χ : 𝔼 → ℝ} (hχ : ContDiff ℝ ∞ χ) (hψ : IsTestFn V (χ * φ)) :
    ‖(graph volume Ω hψ).fst - (graph volume Ω hφ).fst‖ ≤
      Real.sqrt (∫ x, φ x ^ 2 * (1 - χ x) ^ 2) := by
  rw [graph_fst, graph_fst, ← MemLp.toLp_sub]
  refine Real.le_sqrt_of_sq_le ?_
  rw [norm_toLp_sq]
  have hc : Continuous (fun x => ‖(χ * φ - φ) x‖ ^ 2) :=
    ((hχ.continuous.mul hφ.continuous).sub hφ.continuous).norm.pow 2
  have hs : HasCompactSupport (fun x => ‖(χ * φ - φ) x‖ ^ 2) :=
    ((hφ.hasCompactSupport.mul_left.sub hφ.hasCompactSupport).norm).comp_left
      (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hint : Integrable fun x => ‖(χ * φ - φ) x‖ ^ 2 := hc.integrable_of_hasCompactSupport hs
  calc ∫ x in Ω, ‖(χ * φ - φ) x‖ ^ 2 ≤ ∫ x, ‖(χ * φ - φ) x‖ ^ 2 :=
        setIntegral_le_integral hint (Eventually.of_forall fun x => sq_nonneg _)
    _ = ∫ x, φ x ^ 2 * (1 - χ x) ^ 2 := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [Pi.sub_apply, Pi.mul_apply, Real.norm_eq_abs, sq_abs]
        ring

theorem norm_snd_cut_sub_le (Ω : Set 𝔼) {U V : Set 𝔼} {φ : 𝔼 → ℝ} (hφ : IsTestFn U φ)
    {χ : 𝔼 → ℝ} (hχ : ContDiff ℝ ∞ χ) (hψ : IsTestFn V (χ * φ)) :
    ‖(graph volume Ω hψ).snd - (graph volume Ω hφ).snd‖ ≤
      Real.sqrt (2 * (∫ x, ‖gradient φ x‖ ^ 2 * (1 - χ x) ^ 2) +
        2 * ∫ x, φ x ^ 2 * ‖gradient χ x‖ ^ 2) := by
  rw [graph_snd, graph_snd, ← MemLp.toLp_sub]
  refine Real.le_sqrt_of_sq_le ?_
  rw [norm_toLp_sq]
  have hgφ := hφ.continuous_gradient
  have hgχ : Continuous (gradient χ) :=
    (toDual ℝ 𝔼).symm.continuous.comp (hχ.continuous_fderiv (by simp))
  have hcs := hφ.hasCompactSupport
  have c1 : Continuous fun x => ‖(gradient (χ * φ) - gradient φ) x‖ ^ 2 :=
    ((hψ.continuous_gradient).sub hgφ).norm.pow 2
  have s1 : HasCompactSupport fun x => ‖(gradient (χ * φ) - gradient φ) x‖ ^ 2 :=
    ((hψ.hasCompactSupport_gradient.sub hφ.hasCompactSupport_gradient).norm).comp_left
      (g := fun t : ℝ => t ^ 2) (by norm_num)
  have I1 : Integrable fun x => ‖(gradient (χ * φ) - gradient φ) x‖ ^ 2 :=
    c1.integrable_of_hasCompactSupport s1
  have c2 : Continuous fun x => ‖gradient φ x‖ ^ 2 * (1 - χ x) ^ 2 :=
    (hgφ.norm.pow 2).mul ((continuous_const.sub hχ.continuous).pow 2)
  have s2' : HasCompactSupport fun x => ‖gradient φ x‖ ^ 2 :=
    (hφ.hasCompactSupport_gradient.norm).comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have s2 : HasCompactSupport fun x => ‖gradient φ x‖ ^ 2 * (1 - χ x) ^ 2 := s2'.mul_right
  have I2 : Integrable fun x => ‖gradient φ x‖ ^ 2 * (1 - χ x) ^ 2 :=
    c2.integrable_of_hasCompactSupport s2
  have c3 : Continuous fun x => φ x ^ 2 * ‖gradient χ x‖ ^ 2 :=
    (hφ.continuous.pow 2).mul (hgχ.norm.pow 2)
  have s3' : HasCompactSupport fun x => φ x ^ 2 :=
    hcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have s3 : HasCompactSupport fun x => φ x ^ 2 * ‖gradient χ x‖ ^ 2 := s3'.mul_right
  have I3 : Integrable fun x => φ x ^ 2 * ‖gradient χ x‖ ^ 2 :=
    c3.integrable_of_hasCompactSupport s3
  calc ∫ x in Ω, ‖(gradient (χ * φ) - gradient φ) x‖ ^ 2
      ≤ ∫ x, ‖(gradient (χ * φ) - gradient φ) x‖ ^ 2 :=
        setIntegral_le_integral I1 (Eventually.of_forall fun x => sq_nonneg _)
    _ ≤ ∫ x, (2 * (‖gradient φ x‖ ^ 2 * (1 - χ x) ^ 2) + 2 * (φ x ^ 2 * ‖gradient χ x‖ ^ 2)) :=
        integral_mono I1 ((I2.const_mul 2).add (I3.const_mul 2)) fun x =>
          norm_gradient_mul_sub_sq_le (hχ.differentiable (by simp)) hφ.differentiable x
    _ = 2 * (∫ x, ‖gradient φ x‖ ^ 2 * (1 - χ x) ^ 2) +
          2 * ∫ x, φ x ^ 2 * ‖gradient χ x‖ ^ 2 := by
        rw [integral_add (I2.const_mul 2) (I3.const_mul 2), integral_const_mul, integral_const_mul]

/-- `∫ φ² |∇χ|² ≤ M² ∫_{B̄_R} |∇χ|²` when `|φ| ≤ M` and `φ = 0` off `B̄_R`. -/
theorem integral_sq_mul_norm_gradient_le {φ χ : 𝔼 → ℝ} {M R : ℝ}
    (hMφ : ∀ x, |φ x| ≤ M) (hout : ∀ x, x ∉ Metric.closedBall (0 : 𝔼) R → φ x = 0)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hgχ : Continuous (gradient χ)) :
    ∫ x, φ x ^ 2 * ‖gradient χ x‖ ^ 2 ≤
      M ^ 2 * ∫ x in Metric.closedBall (0 : 𝔼) R, ‖gradient χ x‖ ^ 2 := by
  have c3 : Continuous fun x => φ x ^ 2 * ‖gradient χ x‖ ^ 2 := (hφc.pow 2).mul (hgχ.norm.pow 2)
  have s3' : HasCompactSupport fun x => φ x ^ 2 :=
    hφs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have s3 : HasCompactSupport fun x => φ x ^ 2 * ‖gradient χ x‖ ^ 2 := s3'.mul_right
  have I3 : Integrable fun x => φ x ^ 2 * ‖gradient χ x‖ ^ 2 := c3.integrable_of_hasCompactSupport s3
  have c4 : Continuous fun x => M ^ 2 * ‖gradient χ x‖ ^ 2 := continuous_const.mul (hgχ.norm.pow 2)
  have I4 : Integrable ((Metric.closedBall (0 : 𝔼) R).indicator
      fun x => M ^ 2 * ‖gradient χ x‖ ^ 2) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (c4.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
  rw [← integral_const_mul, ← integral_indicator measurableSet_closedBall]
  refine integral_mono I3 I4 fun x => ?_
  · by_cases hx : x ∈ Metric.closedBall (0 : 𝔼) R
    · rw [indicator_of_mem hx]
      exact mul_le_mul_of_nonneg_right
        (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hMφ x) 2) (sq_nonneg _)
    · rw [indicator_of_notMem hx, hout x hx]
      simp

/-- **Approximation.** A test function on `U` is a limit, in `W^{1,2}`, of test functions supported in
`U \ {x_{i₀} = x_{i₁} = 0}`: multiply by the logarithmic cut-offs. -/
theorem graph_mem_closure_testSubmodule_diff (Ω : Set 𝔼) {U : Set 𝔼} {φ : 𝔼 → ℝ}
    (hφ : IsTestFn U φ) {i₀ i₁ : Fin d} (hi : i₀ ≠ i₁) :
    graph volume Ω hφ ∈ closure (testSubmodule volume Ω (U \ planeZero i₀ i₁) :
      Set (L2Pair volume Ω)) := by
  obtain ⟨C, -, hC⟩ := exists_bound_deriv_smoothTransition
  obtain ⟨M, -, hMφ, -⟩ := exists_bound_testFn hφ
  obtain ⟨R, hR⟩ : ∃ R, tsupport φ ⊆ Metric.closedBall (0 : 𝔼) R :=
    hφ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  have hout : ∀ x, x ∉ Metric.closedBall (0 : 𝔼) R → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hR h)
  have hχs : ∀ n : ℕ, ContDiff ℝ ∞ (planeCut (n + 1) i₀ i₁) := fun n =>
    contDiff_planeCut n.succ_pos i₀ i₁
  have hψ : ∀ n : ℕ, IsTestFn (U \ planeZero i₀ i₁) (planeCut (n + 1) i₀ i₁ * φ) := fun n =>
    ⟨(hχs n).mul hφ.contDiff, hφ.hasCompactSupport.mul_left, by
      intro x hx
      refine ⟨hφ.tsupport_subset (tsupport_mul_subset_right hx), fun hz => ?_⟩
      have h1 := tsupport_planeCut_subset n.succ_pos i₀ i₁ (tsupport_mul_subset_left hx)
      have hz' : planeSq i₀ i₁ x = 0 := hz
      rw [Set.mem_ofPred_eq, hz'] at h1
      linarith [Real.exp_pos (-2 * ((n + 1 : ℕ) : ℝ))]⟩
  have hgχ : ∀ n : ℕ, Continuous (gradient (planeCut (n + 1) i₀ i₁)) := fun n =>
    (toDual ℝ 𝔼).symm.continuous.comp ((hχs n).continuous_fderiv (by simp))
  set V := (volume (Set.univ.pi fun _ : {i : Fin d // ¬(i = i₀ ∨ i = i₁)} =>
    Icc (-R) R)).toReal
  -- the three error terms
  have cA : Continuous fun x => φ x ^ 2 := hφ.continuous.pow 2
  have sA : HasCompactSupport fun x => φ x ^ 2 :=
    hφ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hA := tendsto_integral_mul_one_sub_planeCut (i₀ := i₀) (i₁ := i₁)
    (cA.integrable_of_hasCompactSupport sA) (fun x => sq_nonneg _) cA
  have cB : Continuous fun x => ‖gradient φ x‖ ^ 2 := hφ.continuous_gradient.norm.pow 2
  have sB : HasCompactSupport fun x => ‖gradient φ x‖ ^ 2 :=
    (hφ.hasCompactSupport_gradient.norm).comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hB := tendsto_integral_mul_one_sub_planeCut (i₀ := i₀) (i₁ := i₁)
    (cB.integrable_of_hasCompactSupport sB) (fun x => sq_nonneg _) cB
  have hE : Tendsto (fun n : ℕ => ∫ x, φ x ^ 2 * ‖gradient (planeCut (n + 1) i₀ i₁) x‖ ^ 2)
      atTop (𝓝 0) := by
    have hbound : ∀ n : ℕ, ∫ x, φ x ^ 2 * ‖gradient (planeCut (n + 1) i₀ i₁) x‖ ^ 2 ≤
        M ^ 2 * (4 * π * C ^ 2 / ((n + 1 : ℕ) : ℝ) * V) := fun n =>
      (integral_sq_mul_norm_gradient_le hMφ hout hφ.continuous hφ.hasCompactSupport (hgχ n)).trans
        (mul_le_mul_of_nonneg_left
          (integral_closedBall_norm_gradient_planeCut_le n.succ_pos hi hC R) (sq_nonneg _))
    have h0 : Tendsto (fun n : ℕ => M ^ 2 * (4 * π * C ^ 2 / ((n + 1 : ℕ) : ℝ) * V)) atTop
        (𝓝 0) := by
      have h : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      have := ((h.const_mul (4 * π * C ^ 2)).mul_const V).const_mul (M ^ 2)
      simp only [mul_zero, zero_mul] at this
      refine this.congr fun n => ?_
      simp only [div_eq_mul_inv]
    exact squeeze_zero (fun n => integral_nonneg fun x => by positivity) hbound h0
  have hlim : Tendsto (fun n => graph volume Ω (hψ n)) atTop (𝓝 (graph volume Ω hφ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 : Tendsto (fun n : ℕ => Real.sqrt (∫ x, φ x ^ 2 *
        (1 - planeCut (n + 1) i₀ i₁ x) ^ 2)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hA
      rwa [Real.sqrt_zero] at this
    have h2 : Tendsto (fun n : ℕ => Real.sqrt (2 * (∫ x, ‖gradient φ x‖ ^ 2 *
        (1 - planeCut (n + 1) i₀ i₁ x) ^ 2) + 2 * ∫ x, φ x ^ 2 *
          ‖gradient (planeCut (n + 1) i₀ i₁) x‖ ^ 2)) atTop (𝓝 0) := by
      have h := (hB.const_mul 2).add (hE.const_mul 2)
      rw [mul_zero, add_zero] at h
      have := (Real.continuous_sqrt.tendsto 0).comp h
      rwa [Real.sqrt_zero] at this
    have h12 := h1.add h2
    rw [add_zero] at h12
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h12
    refine (norm_le_norm_fst_add_norm_snd _).trans ?_
    rw [WithLp.sub_fst, WithLp.sub_snd]
    exact add_le_add (norm_fst_cut_sub_le Ω hφ (hχs n) (hψ n))
      (norm_snd_cut_sub_le Ω hφ (hχs n) (hψ n))
  exact mem_closure_of_tendsto hlim (Eventually.of_forall fun n => graph_mem_testSubmodule Ω _)

/-! ### Density on the cone models -/

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-- The two real coordinates `x_a, y_a` of the cone factor `a`, numbered by `e`. -/
def coneCoords (e : RealConeIndex κ ι ≃ Fin d) (a : κ) : Fin d × Fin d :=
  (e (Sum.inl (0, a)), e (Sum.inl (1, a)))

theorem coneCoords_ne (e : RealConeIndex κ ι ≃ Fin d) (a : κ) :
    (coneCoords e a).1 ≠ (coneCoords e a).2 := by
  intro h
  have := e.injective h
  simp at this

/-- **The singular set** `S = ⋃_a {r_a = 0}` in the real coordinates numbered by `e`. -/
def coneSingular (e : RealConeIndex κ ι ≃ Fin d) : Set 𝔼 :=
  ⋃ a, planeZero (coneCoords e a).1 (coneCoords e a).2

theorem coneSingular_eq (e : RealConeIndex κ ι ≃ Fin d) :
    coneSingular e = {x : 𝔼 | ∃ a, ((coordIso e).symm x).cone a = 0} := by
  ext x
  simp only [coneSingular, mem_iUnion, planeZero, Set.mem_ofPred_eq]
  refine exists_congr fun a => ?_
  have h0 : ((coordIso e).symm x).cone a = ⟨x (e (Sum.inl (0, a))), x (e (Sum.inl (1, a)))⟩ := by
    simp [coordIso, RealConeModel.cone]
  rw [h0, planeSq, coneCoords]
  constructor
  · intro h
    have h1 : x (e (Sum.inl (0, a))) ^ 2 = 0 := by nlinarith [sq_nonneg (x (e (Sum.inl (1, a))))]
    have h2 : x (e (Sum.inl (1, a))) ^ 2 = 0 := by nlinarith [sq_nonneg (x (e (Sum.inl (0, a))))]
    apply Complex.ext <;> simp [pow_eq_zero_iff (two_ne_zero) |>.mp h1,
      pow_eq_zero_iff (two_ne_zero) |>.mp h2]
  · intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp only [Complex.zero_re, Complex.zero_im] at h1 h2
    rw [h1, h2]
    ring

/-- **Density of test functions on the regular part** (paper, §2.1). Test functions supported in
`Ω \ S` are dense in `W^{1,2}_0(Ω)`: the codimension-two singular set has zero capacity. -/
theorem dense_testSubmodule_regular (e : RealConeIndex κ ι ≃ Fin d) (Ω : Set 𝔼) :
    (testSubmodule volume Ω (Ω \ coneSingular e)).topologicalClosure = H01 volume Ω := by
  refine le_antisymm (Submodule.topologicalClosure_mono (testSubmodule_mono Ω sdiff_subset))
    (Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _))
  -- induction over the cone factors removed so far
  have key : ∀ s : Finset κ, (testSubmodule volume Ω Ω : Set (L2Pair volume Ω)) ⊆
      closure (testSubmodule volume Ω
        (Ω \ ⋃ a ∈ s, planeZero (coneCoords e a).1 (coneCoords e a).2)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using subset_closure
    | insert a s ha ih =>
      refine ih.trans (closure_minimal ?_ isClosed_closure)
      rintro _ ⟨φ, hφ, rfl⟩
      have h := graph_mem_closure_testSubmodule_diff Ω hφ (coneCoords_ne e a)
      have hset : (Ω \ ⋃ b ∈ s, planeZero (coneCoords e b).1 (coneCoords e b).2) \
          planeZero (coneCoords e a).1 (coneCoords e a).2 =
          Ω \ ⋃ b ∈ insert a s, planeZero (coneCoords e b).1 (coneCoords e b).2 := by
        ext x
        simp only [Set.mem_sdiff, mem_iUnion, Finset.mem_insert, exists_prop]
        constructor
        · rintro ⟨⟨hx, hs⟩, ha'⟩
          refine ⟨hx, ?_⟩
          rintro ⟨b, hb | hb, hxb⟩
          · exact ha' (hb ▸ hxb)
          · exact hs ⟨b, hb, hxb⟩
        · rintro ⟨hx, hs⟩
          exact ⟨⟨hx, fun ⟨b, hb, hxb⟩ => hs ⟨b, Or.inr hb, hxb⟩⟩,
            fun hxa => hs ⟨a, Or.inl rfl, hxa⟩⟩
      rwa [hset] at h
  have hfin := key Finset.univ
  have hS : (⋃ a ∈ (Finset.univ : Finset κ), planeZero (coneCoords e a).1 (coneCoords e a).2) =
      coneSingular e := by
    simp [coneSingular]
  rw [hS] at hfin
  intro v hv
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact hfin hv

/-- **The weak equation needs only regular test functions.** For `v ∈ W^{1,2}(Ω)`, `v` is a weak
solution of `-div(A ∇u) = f` on `Ω` iff the weak equation holds for all test functions supported in
`Ω \ S`, away from the singular set. -/
theorem isWeakSolution_iff_regular (c : CoeffField 𝔼 volume) (e : RealConeIndex κ ι ≃ Fin d)
    {Ω : Set 𝔼} {f : Lp ℝ 2 (volume.restrict Ω)} {v : L2Pair volume Ω} (hv : v ∈ W12 volume Ω) :
    c.IsWeakSolution f v ↔ ∀ (φ : 𝔼 → ℝ) (hφ : IsTestFn (Ω \ coneSingular e) φ),
      c.dirichletForm Ω v (graph volume Ω hφ) = ⟪f, (graph volume Ω hφ).fst⟫_ℝ := by
  constructor
  · intro h φ hφ
    exact h.2 φ (hφ.mono sdiff_subset)
  · intro h
    refine ⟨hv, fun φ hφ => ?_⟩
    have hfst : Continuous fun v : L2Pair volume Ω => v.fst :=
      continuous_fst.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous
    have hclosed : IsClosed {ψ : L2Pair volume Ω | c.dirichletForm Ω v ψ = ⟪f, ψ.fst⟫_ℝ} :=
      isClosed_eq (c.dirichletForm Ω v).continuous (continuous_const.inner hfst)
    have hsub : (testSubmodule volume Ω (Ω \ coneSingular e) : Set (L2Pair volume Ω)) ⊆
        {ψ : L2Pair volume Ω | c.dirichletForm Ω v ψ = ⟪f, ψ.fst⟫_ℝ} := by
      rintro _ ⟨ψ, hψ, rfl⟩
      exact h ψ hψ
    have hmem : graph volume Ω hφ ∈ closure (testSubmodule volume Ω (Ω \ coneSingular e) :
        Set (L2Pair volume Ω)) := by
      rw [← Submodule.topologicalClosure_coe, dense_testSubmodule_regular e Ω]
      exact graph_mem_H01 Ω hφ
    exact closure_minimal hsub hclosed hmem

end ConicalKahler.Sobolev
