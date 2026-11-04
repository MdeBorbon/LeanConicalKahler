module

public import ConicalKahler.Cone.SNCChartInvariance
public import ConicalKahler.Cone.Standard

/-!
# Chart invariance of the cone condition for `0 < β ≤ 1` (smooth divisors)

For a smooth divisor and `0 < β ≤ 1`: **if `ω₀` is comparable to the model in one adapted chart at
`p`, it is comparable to the model in any other adapted chart at `p`, after shrinking**
(`ConeComparableIn.exists_restrOpen_of_le_one`, `IsQuasiIsometricCone.forall_chart_of_le_one`).

These theorems are the one-label case of the SNC chart invariance
(`SNCConeComparableIn.exists_restrOpen_of_le_one`), transported through
`coneComparableIn_iff_sncConeComparableIn`. Likewise the two-sided model comparison under a
hyperplane-preserving biholomorphism (`exists_model_comparison`,
`K⁻¹ q_model(ζ; v) ≤ q_model(Φ(ζ); DΦ(ζ) v) ≤ K q_model(ζ; v)`) is the single-hyperplane case of
`exists_weighted_model_comparison`. The analytic argument appears only once, in
`ConicalKahler.Cone.WeightedComparison`.

This file also keeps the explicit single-hyperplane formula `modelConeQuadratic_single_eq`. It
also keeps the inequality with explicit constant `modelConeQuadratic_le_of_le_one`, which is
proved from the shared one-term inequality `cone_term_le`.

Where `β ≤ 1` is used: on `{|ζ_0| ≤ 1}` the weight `β² |ζ_0|^(2β-2)` is `≥ β²`, so the
unweighted norm `|v|²` is controlled by `q_model(ζ; v)`. Tangential derivatives of `Φ` may mix
`v_0` into the smooth directions (as the shear does), which is harmless exactly in this regime.
For `β > 1` the statement is false (`not_coneComparableIn_shear`).
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Set Filter

namespace ConicalKahler

variable {n : ℕ} [NeZero n]

/-! ### The model quadratic form of the single-cone weights -/

/-- `q_model(z; ξ) = β² |z_0|^(2β-2) |ξ_0|² + (|ξ|² - |ξ_0|²)`. -/
theorem modelConeQuadratic_single_eq (β : ConeAngle) (z ξ : E n) :
    modelConeQuadratic (singleConeWeights β) z ξ =
      β.beta ^ 2 * ‖z 0‖ ^ (2 * β.beta - 2) * ‖ξ 0‖ ^ 2 + (‖ξ‖ ^ 2 - ‖ξ 0‖ ^ 2) := by
  have hn : ‖ξ‖ ^ 2 = ∑ j, ‖ξ j‖ ^ 2 := EuclideanSpace.norm_sq_eq ξ
  have hrest : ∑ j ∈ Finset.univ.erase 0,
      modelWeight (singleConeWeights β) z j * Complex.normSq (ξ j) =
        ∑ j ∈ Finset.univ.erase 0, ‖ξ j‖ ^ 2 :=
    Finset.sum_congr rfl fun j hj => by
      rw [modelWeight_single_of_ne β z (Finset.ne_of_mem_erase hj), one_mul,
        Complex.normSq_eq_norm_sq]
  rw [hn, modelConeQuadratic, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0),
    ← Finset.add_sum_erase _ (fun j => ‖ξ j‖ ^ 2) (Finset.mem_univ 0), hrest,
    modelWeight_single_zero, Complex.normSq_eq_norm_sq]
  ring

/-! ### The weighted inequality -/

/-- **The weighted inequality (uses `β ≤ 1`).** Suppose `|ζ_0| ≤ 1`, `ζ_0 ≠ 0`,
`|z_0| ≥ c |ζ_0|`, `|ξ| ≤ L |v|` and `|ξ_0| ≤ L |v_0| + L₂ |ζ_0| |v|`. Then
`q_model(z; ξ) ≤ K q_model(ζ; v)` with an explicit `K`. -/
theorem modelConeQuadratic_le_of_le_one {β : ConeAngle} (hβ : β.beta ≤ 1) {z ζ ξ v : E n}
    {c L L₂ : ℝ} (hc : 0 < c) (hζ0 : ζ 0 ≠ 0) (hζ1 : ‖ζ 0‖ ≤ 1)
    (hz : c * ‖ζ 0‖ ≤ ‖z 0‖) (hξ : ‖ξ‖ ≤ L * ‖v‖)
    (hξ0 : ‖ξ 0‖ ≤ L * ‖v 0‖ + L₂ * ‖ζ 0‖ * ‖v‖) :
    modelConeQuadratic (singleConeWeights β) z ξ ≤
      (2 * L ^ 2 * c ^ (2 * β.beta - 2) +
          (2 * L₂ ^ 2 * c ^ (2 * β.beta - 2) * β.beta ^ 2 + L ^ 2) * (1 + 1 / β.beta ^ 2)) *
        modelConeQuadratic (singleConeWeights β) ζ v := by
  rw [modelConeQuadratic_single_eq, modelConeQuadratic_single_eq]
  have hβ0 := β.pos
  have hx : 0 < ‖ζ 0‖ := norm_pos_iff.mpr hζ0
  set a := 2 * β.beta - 2 with ha_def
  set b2 := β.beta ^ 2 with hb2_def
  have hb2 : 0 < b2 := by positivity
  set w := b2 * ‖ζ 0‖ ^ a * ‖v 0‖ ^ 2 with hw_def
  set q := w + (‖v‖ ^ 2 - ‖v 0‖ ^ 2) with hq_def
  have hv0 : ‖v 0‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_apply_zero_le v) 2
  have hxa1 : 1 ≤ ‖ζ 0‖ ^ a :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx hζ1 (by rw [ha_def]; linarith)
  have hw : 0 ≤ w := by positivity
  have hwq : w ≤ q := by rw [hq_def]; linarith
  -- `|v|² ≤ (1 + 1/β²) q_model(ζ; v)` (this is where `β ≤ 1` enters, through `|ζ_0|^a ≥ 1`)
  have hVq : ‖v‖ ^ 2 ≤ (1 + 1 / b2) * q := by
    have h1 : ‖v 0‖ ^ 2 ≤ 1 / b2 * w := by
      rw [show 1 / b2 * w = ‖ζ 0‖ ^ a * ‖v 0‖ ^ 2 by rw [hw_def]; field_simp]
      exact le_mul_of_one_le_left (sq_nonneg _) hxa1
    have h2 : 1 / b2 * w ≤ 1 / b2 * q := mul_le_mul_of_nonneg_left hwq (by positivity)
    have h3 : (1 + 1 / b2) * q = q + 1 / b2 * q := by ring
    rw [hq_def] at h3 ⊢
    linarith
  -- the singular term, by the one-term inequality
  have hterm := cone_term_le hβ0.le hβ hc hx hζ1 hz (norm_nonneg _) hξ0
  -- the other terms
  have hXle : ‖ξ‖ ^ 2 ≤ L ^ 2 * ‖v‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hξ 2
  have hX0 : 0 ≤ ‖ξ 0‖ ^ 2 := sq_nonneg _
  have hca : 0 ≤ c ^ a := (Real.rpow_pos_of_pos hc a).le
  have hcoef : 0 ≤ 2 * L₂ ^ 2 * c ^ a * b2 + L ^ 2 := by positivity
  calc b2 * ‖z 0‖ ^ a * ‖ξ 0‖ ^ 2 + (‖ξ‖ ^ 2 - ‖ξ 0‖ ^ 2)
      ≤ 2 * L ^ 2 * c ^ a * w + (2 * L₂ ^ 2 * c ^ a * b2 + L ^ 2) * ‖v‖ ^ 2 := by
        rw [hw_def]
        nlinarith [hterm, hXle, hX0]
    _ ≤ 2 * L ^ 2 * c ^ a * q + (2 * L₂ ^ 2 * c ^ a * b2 + L ^ 2) * ((1 + 1 / b2) * q) := by
        gcongr
    _ = (2 * L ^ 2 * c ^ a + (2 * L₂ ^ 2 * c ^ a * b2 + L ^ 2) * (1 + 1 / b2)) * q := by ring

/-! ### Two-sided comparison under hyperplane-preserving biholomorphisms -/

/-- For the single-cone weights, a map preserving `{ζ_0 = 0}` (with an inverse preserving it)
matches the singular hyperplane with itself. -/
theorem weightsMatch_single {β : ConeAngle} {Ψ Ψ' : E n → E n} {ζ₀ : E n} (hζ₀ : ζ₀ 0 = 0)
    (hpres : ∀ᶠ ζ in 𝓝 ζ₀, ζ 0 = 0 → Ψ ζ 0 = 0)
    (hpres' : ∀ᶠ z in 𝓝 (Ψ ζ₀), z 0 = 0 → Ψ' z 0 = 0) :
    WeightsMatch (singleConeWeights β) (singleConeWeights β) Ψ Ψ' ζ₀ := by
  intro k β' hk _
  by_cases hk0 : k = 0
  · subst hk0
    rw [singleConeWeights_angle_zero] at hk
    obtain rfl := Option.some.inj hk
    exact ⟨0, singleConeWeights_angle_zero β, hζ₀, hpres, hpres'⟩
  · rw [singleConeWeights_angle_of_ne β hk0] at hk
    cases hk

theorem singleConeWeights_le_one {β : ConeAngle} (hβ : β.beta ≤ 1) :
    ∀ k β', (singleConeWeights (n := n) β).angle k = some β' → β'.beta ≤ 1 := by
  intro k β' hk
  by_cases hk0 : k = 0
  · subst hk0
    rw [singleConeWeights_angle_zero] at hk
    obtain rfl := Option.some.inj hk
    exact hβ
  · rw [singleConeWeights_angle_of_ne β hk0] at hk
    cases hk

/-- One-sided bound: `q_model(Ψ ζ; DΨ(ζ) v) ≤ K q_model(ζ; v)` near `ζ₀`, for `β ≤ 1`. This is
the single-hyperplane case of `exists_weighted_upper_bound`. -/
theorem exists_model_upper_bound {β : ConeAngle} (hβ : β.beta ≤ 1) {Ψ Ψ' : E n → E n}
    {ζ₀ : E n} (hζ₀ : ζ₀ 0 = 0) (hΨ : ContDiffAt ℂ 2 Ψ ζ₀) (hΨ' : ContDiffAt ℂ 2 Ψ' (Ψ ζ₀))
    (hinv : ∀ᶠ ζ in 𝓝 ζ₀, Ψ' (Ψ ζ) = ζ) (hpres : ∀ᶠ ζ in 𝓝 ζ₀, ζ 0 = 0 → Ψ ζ 0 = 0)
    (hpres' : ∀ᶠ z in 𝓝 (Ψ ζ₀), z 0 = 0 → Ψ' z 0 = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ ζ in 𝓝 ζ₀, ζ 0 ≠ 0 → Ψ ζ 0 ≠ 0 ∧ ∀ v,
      modelConeQuadratic (singleConeWeights β) (Ψ ζ) (fderiv ℂ Ψ ζ v) ≤
        K * modelConeQuadratic (singleConeWeights β) ζ v := by
  obtain ⟨K, hK, hev⟩ := exists_weighted_upper_bound (singleConeWeights_le_one hβ) hΨ hΨ' hinv
    (weightsMatch_single hζ₀ hpres hpres')
  refine ⟨K, hK, hev.mono fun ζ h hζ0 => ?_⟩
  obtain ⟨hdom, hbd⟩ := h (mem_modelDomain_single.mpr hζ0)
  exact ⟨mem_modelDomain_single.mp hdom, hbd⟩

/-- **Two-sided comparison of the model under a hyperplane-preserving biholomorphism**
(`0 < β ≤ 1`). This is the single-hyperplane case of `exists_weighted_model_comparison`. -/
theorem exists_model_comparison {β : ConeAngle} (hβ : β.beta ≤ 1) {Ψ Ψ' : E n → E n}
    {ζ₀ : E n} (hζ₀ : ζ₀ 0 = 0) (hΨ : ContDiffAt ℂ 2 Ψ ζ₀) (hΨ' : ContDiffAt ℂ 2 Ψ' (Ψ ζ₀))
    (hinv : ∀ᶠ ζ in 𝓝 ζ₀, Ψ' (Ψ ζ) = ζ) (hinv' : ∀ᶠ z in 𝓝 (Ψ ζ₀), Ψ (Ψ' z) = z)
    (hpres : ∀ᶠ ζ in 𝓝 ζ₀, ζ 0 = 0 → Ψ ζ 0 = 0)
    (hpres' : ∀ᶠ z in 𝓝 (Ψ ζ₀), z 0 = 0 → Ψ' z 0 = 0) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ ζ in 𝓝 ζ₀, ζ 0 ≠ 0 → Ψ ζ 0 ≠ 0 ∧ ∀ v,
      K⁻¹ * modelConeQuadratic (singleConeWeights β) ζ v ≤
          modelConeQuadratic (singleConeWeights β) (Ψ ζ) (fderiv ℂ Ψ ζ v) ∧
        modelConeQuadratic (singleConeWeights β) (Ψ ζ) (fderiv ℂ Ψ ζ v) ≤
          K * modelConeQuadratic (singleConeWeights β) ζ v := by
  have hz₀ : Ψ ζ₀ 0 = 0 := hpres.self_of_nhds hζ₀
  have hΨ'Ψ : Ψ' (Ψ ζ₀) = ζ₀ := hinv.self_of_nhds
  have hpres'' : ∀ᶠ ζ in 𝓝 (Ψ' (Ψ ζ₀)), ζ 0 = 0 → Ψ ζ 0 = 0 := by rwa [hΨ'Ψ]
  obtain ⟨K, hK, hev⟩ := exists_weighted_model_comparison (singleConeWeights_le_one hβ)
    (singleConeWeights_le_one hβ) hΨ hΨ' hinv hinv' (weightsMatch_single hζ₀ hpres hpres')
    (weightsMatch_single hz₀ hpres' hpres'')
  refine ⟨K, hK, hev.mono fun ζ h hζ0 => ?_⟩
  obtain ⟨hdom, hbd⟩ := h (mem_modelDomain_single.mpr hζ0)
  exact ⟨mem_modelDomain_single.mp hdom, hbd⟩

/-! ### Chart invariance: the one-label case of the SNC theorem -/

section Charts

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X] [IsManifold 𝓘(ℂ, E n) ω X]
  {D : SmoothDivisor n X} {β : ConeAngle} {ω₀ : KahlerForm n D.complement} {p : X}

/-- **Chart invariance of the cone condition for `0 < β ≤ 1`.** If `ω₀` is comparable to the model
in one adapted chart `χ₁` at `p ∈ D`, then it is comparable to the model in any other adapted
chart `χ₂` at `p`, after restricting `χ₂` to a smaller neighbourhood of `p`. This is the one-label
case of `SNCConeComparableIn.exists_restrOpen_of_le_one`. The hypothesis `p ∈ D` is no longer
needed by the proof and is kept so that existing calls are unchanged. -/
theorem ConeComparableIn.exists_restrOpen_of_le_one (hβ : β.beta ≤ 1) (_hp : p ∈ D.carrier)
    {χ₁ : DivisorChart n X D.carrier p} {C : ℝ} (hC : 1 ≤ C)
    (h : ConeComparableIn D β ω₀ χ₁ C) (χ₂ : DivisorChart n X D.carrier p) :
    ∃ (s : Set X) (hs : IsOpen s) (hps : p ∈ s) (C' : ℝ), 1 ≤ C' ∧
      ConeComparableIn D β ω₀ (χ₂.restrOpen s hs hps) C' := by
  have h' := (coneComparableIn_iff_sncConeComparableIn D β ω₀ χ₁ χ₁.toSNCChart rfl rfl C).mp h
  obtain ⟨s, hs, hps, C', hC', hcomp⟩ :=
    h'.exists_restrOpen_of_le_one (fun _ => hβ) hC χ₂.toSNCChart
  exact ⟨s, hs, hps, C', hC', (coneComparableIn_iff_sncConeComparableIn D β ω₀
    (χ₂.restrOpen s hs hps) (χ₂.toSNCChart.restrOpen s hs hps) rfl rfl C').mpr hcomp⟩

/-- **For `0 < β ≤ 1`, the quasi-isometric cone condition holds in every adapted chart** (after
shrinking): it does not depend on the choice of adapted chart in its definition. -/
theorem IsQuasiIsometricCone.forall_chart_of_le_one (hβ : β.beta ≤ 1)
    (h : IsQuasiIsometricCone D β ω₀) (hp : p ∈ D.carrier) (χ : DivisorChart n X D.carrier p) :
    ∃ (s : Set X) (hs : IsOpen s) (hps : p ∈ s) (C : ℝ), 1 ≤ C ∧
      ConeComparableIn D β ω₀ (χ.restrOpen s hs hps) C := by
  obtain ⟨χ₁, C, hC, hcomp⟩ := h p hp
  exact hcomp.exists_restrOpen_of_le_one hβ hp hC χ

end Charts

end ConicalKahler
