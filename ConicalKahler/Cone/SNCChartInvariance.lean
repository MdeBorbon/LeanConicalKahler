module

public import ConicalKahler.Cone.SNCComparison
public import ConicalKahler.Cone.WeightedComparison

/-!
# Chart invariance of the SNC cone condition for angles `0 < β_i ≤ 1`

Let `Δ` be an SNC divisor with labelled components and cone angles `angle : ι → ConeAngle`, all
satisfying `0 < β_i ≤ 1`. If a Kähler form on `X \ ⋃ᵢ Dᵢ` is comparable to the local SNC model in
one SNC chart at `p`, then it is comparable to the local model in **any** other SNC chart at `p`,
after shrinking that chart around `p` (`SNCConeComparableIn.exists_restrOpen_of_le_one`).
Consequently `IsQuasiIsometricSNCCone` does not depend on the chosen charts
(`IsQuasiIsometricSNCCone.forall_chart_of_le_one`).

## Labels and permutations

Two SNC charts at `p` may list the components through `p` in different orders. The relevant
component of slot `k` in the second chart is the one with label `active₂ k`. It is active in the
first chart in some slot `j` with `active₁ j = active₂ k`, and the two local weights there carry
the same angle `angle (active₂ k)`. `SNCChart.weightsMatch` packages exactly this as
`WeightsMatch`, and the analytic core `exists_weighted_model_comparison` uses it. Active
components of a chart that do not pass through `p` need no matching: their weights are bounded
near `p`.

The smooth-divisor theorem `ConeComparableIn.exists_restrOpen_of_le_one` is the one-label case
(`ConicalKahler.Cone.ChartInvariance`). For an angle `β > 1` the statement is false
(`not_coneComparableIn_shear`, which embeds via `isConeAlong_iff_isSNCConeAlong`).
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Set Filter

namespace ConicalKahler

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X] {ι : Type*}

/-! ### Matching of the active components of two SNC charts -/

namespace SNCChart

variable {components : ι → Set X} {p : X}

/-- The local weights of an SNC chart have all angles `≤ 1` if all labelled angles are. -/
theorem localWeights_le_one (χ : SNCChart n X ι components p) {angle : ι → ConeAngle}
    (hangle : ∀ i, (angle i).beta ≤ 1) :
    ∀ k β, (χ.localWeights angle).angle k = some β → β.beta ≤ 1 := by
  intro k β hk
  simp only [localWeights] at hk
  split_ifs at hk with hkk
  · obtain rfl := Option.some.inj hk
    exact hangle _

/-- **Matching of the active components of two SNC charts at `p`.** Every active slot `k` of
`χb` whose component passes through `p` corresponds to the slot `j` of `χa` with the same label;
the two local weights have the same angle, and the transition maps the hyperplane `{ζ_j = 0}`
into `{z_k = 0}`, with the inverse transition mapping `{z_k = 0}` into `{ζ_j = 0}`. The slots `j`
and `k` may differ. -/
theorem weightsMatch (χa χb : SNCChart n X ι components p) (angle : ι → ConeAngle) :
    WeightsMatch (χb.localWeights angle) (χa.localWeights angle)
      (χb.coord ∘ χa.coord.symm) (χa.coord ∘ χb.coord.symm) (χa.coord p) := by
  intro k β hk hzero
  simp only [localWeights] at hk
  split_ifs at hk with hkk
  set jb : Fin χb.k := ⟨k, hkk⟩
  have hslot_b : χb.slot jb = k := Fin.ext rfl
  have hβ : angle (χb.active jb) = β := Option.some.inj hk
  have hcenter : (χb.coord ∘ χa.coord.symm) (χa.coord p) = χb.coord p :=
    χa.toHolChart.transition_apply_center χb.toHolChart χa.center_mem
  rw [hcenter] at hzero
  -- the component of slot `k` of `χb` passes through `p` ...
  have hpi : p ∈ components (χb.active jb) :=
    (χb.coordinate_zero_iff p χb.center_mem jb).mpr (by rw [← hslot_b] at hzero; exact hzero)
  -- ... so it is active in `χa`, in some slot `ja`
  obtain ⟨ja, hja⟩ : χb.active jb ∈ range χa.active := by
    by_contra h
    exact χa.other_components_absent p χa.center_mem _ h hpi
  refine ⟨χa.slot ja, ?_, ?_, ?_, ?_⟩
  · rw [χa.localWeights_angle_slot, hja, hβ]
  · exact (χa.coordinate_zero_iff p χa.center_mem ja).mp (hja ▸ hpi)
  · filter_upwards [χa.toHolChart.eventually_transition χb.toHolChart χa.center_mem
      χb.center_mem] with ζ hζ hζ0
    have hmem : χa.coord.symm ζ ∈ components (χb.active jb) := by
      rw [← hja]
      refine (χa.coordinate_zero_iff _ (χa.coord.map_target hζ.1) ja).mpr ?_
      rw [χa.coord.right_inv hζ.1]
      exact hζ0
    have h := (χb.coordinate_zero_iff _ hζ.2 jb).mp hmem
    rw [← hslot_b]
    exact h
  · rw [hcenter]
    filter_upwards [χb.toHolChart.eventually_transition χa.toHolChart χb.center_mem
      χa.center_mem] with z hz hz0
    have hmem : χb.coord.symm z ∈ components (χb.active jb) := by
      refine (χb.coordinate_zero_iff _ (χb.coord.map_target hz.1) jb).mpr ?_
      rw [χb.coord.right_inv hz.1]
      exact hz0
    rw [← hja] at hmem
    exact (χa.coordinate_zero_iff _ hz.2 ja).mp hmem

end SNCChart

/-! ### Chart invariance -/

section Charts

variable [IsManifold 𝓘(ℂ, E n) ω X] {Δ : SNCDivisor n X ι} {angle : ι → ConeAngle}
  {ω₀ : KahlerForm n Δ.complement} {p : X}

/-- **Chart invariance of the SNC cone condition for `0 < β_i ≤ 1`.** If `ω₀` is comparable to the
local SNC model in one SNC chart `χ₁` at `p`, then it is comparable to the local SNC model in any
other SNC chart `χ₂` at `p`, after restricting `χ₂` to a smaller neighbourhood of `p`. The two
charts may order the components through `p` differently. -/
theorem SNCConeComparableIn.exists_restrOpen_of_le_one (hangle : ∀ i, (angle i).beta ≤ 1)
    {χ₁ : SNCChart n X ι Δ.components p} {C : ℝ} (hC : 1 ≤ C)
    (h : SNCConeComparableIn Δ angle ω₀ χ₁ C) (χ₂ : SNCChart n X ι Δ.components p) :
    ∃ (s : Set X) (hs : IsOpen s) (hps : p ∈ s) (C' : ℝ), 1 ≤ C' ∧
      SNCConeComparableIn Δ angle ω₀ (χ₂.restrOpen s hs hps) C' := by
  -- the transition from `χ₂`-coordinates to `χ₁`-coordinates and its inverse
  set Φ : E n → E n := χ₁.coord ∘ χ₂.coord.symm with hΦ_def
  set Φ' : E n → E n := χ₂.coord ∘ χ₁.coord.symm with hΦ'_def
  set ζ₀ := χ₂.coord p with hζ₀_def
  have hΦζ₀ : Φ ζ₀ = χ₁.coord p :=
    χ₂.toHolChart.transition_apply_center χ₁.toHolChart χ₂.center_mem
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
  have hΦ : ContDiffAt ℂ 2 Φ ζ₀ :=
    (χ₂.toHolChart.contDiffAt_transition_center χ₁.toHolChart χ₂.center_mem
      χ₁.center_mem).of_le h2
  have hΦ' : ContDiffAt ℂ 2 Φ' (Φ ζ₀) := by
    rw [hΦζ₀]
    exact (χ₁.toHolChart.contDiffAt_transition_center χ₂.toHolChart χ₁.center_mem
      χ₂.center_mem).of_le h2
  have hinv : ∀ᶠ ζ in 𝓝 ζ₀, Φ' (Φ ζ) = ζ :=
    χ₂.toHolChart.eventually_transition_left_inv χ₁.toHolChart χ₂.center_mem χ₁.center_mem
  have hinv' : ∀ᶠ z in 𝓝 (Φ ζ₀), Φ (Φ' z) = z := by
    rw [hΦζ₀]
    exact χ₁.toHolChart.eventually_transition_left_inv χ₂.toHolChart χ₁.center_mem
      χ₂.center_mem
  have hmatch : WeightsMatch (χ₁.localWeights angle) (χ₂.localWeights angle) Φ Φ' ζ₀ :=
    SNCChart.weightsMatch χ₂ χ₁ angle
  have hmatch' : WeightsMatch (χ₂.localWeights angle) (χ₁.localWeights angle) Φ' Φ (Φ ζ₀) := by
    rw [hΦζ₀]
    exact SNCChart.weightsMatch χ₁ χ₂ angle
  obtain ⟨K, hK1, hcmp⟩ := exists_weighted_model_comparison (χ₁.localWeights_le_one hangle)
    (χ₂.localWeights_le_one hangle) hΦ hΦ' hinv hinv' hmatch hmatch'
  -- an open neighbourhood `V` of `ζ₀` on which everything holds
  have N := χ₂.toHolChart.eventually_transition χ₁.toHolChart χ₂.center_mem χ₁.center_mem
  obtain ⟨V, hVsub, hVopen, hζ₀V⟩ := mem_nhds_iff.mp (N.and hcmp)
  refine ⟨χ₂.coord.source ∩ χ₂.coord ⁻¹' V,
    χ₂.coord.continuousOn.isOpen_inter_preimage χ₂.coord.open_source hVopen,
    ⟨χ₂.center_mem, hζ₀V⟩, C * K, one_le_mul_of_one_le_of_one_le hC hK1, ?_⟩
  intro ζ hζ haway v
  have hζV : ζ ∈ V := by
    have h := hζ.2.2
    rwa [Set.mem_preimage, χ₂.coord.right_inv hζ.1] at h
  obtain ⟨⟨hζt, hsrc⟩, hgood⟩ := hVsub hζV
  have hdom : ζ ∈ modelDomain (χ₂.localWeights angle) :=
    (χ₂.mem_modelDomain_localWeights angle).mpr haway
  obtain ⟨hΦdom, hK⟩ := hgood hdom
  have haway₁ : χ₁.Away (Φ ζ) := (χ₁.mem_modelDomain_localWeights angle).mp hΦdom
  obtain ⟨hKlo, hKhi⟩ := hK v
  have hzt : Φ ζ ∈ χ₁.coord.target := χ₁.coord.map_source hsrc
  have hsame : χ₂.coord.symm ζ = χ₁.coord.symm (Φ ζ) := (χ₁.coord.left_inv hsrc).symm
  have e : metricQuadraticInSNCChart Δ ω₀ _ ζ hζ haway v =
      metricQuadraticInSNCChart Δ ω₀ χ₂ ζ hζt haway v := rfl
  rw [e, metricQuadraticInSNCChart_change hζt haway hzt haway₁ hsame]
  obtain ⟨hlo, hhi⟩ := h (Φ ζ) hzt haway₁ (fderiv ℂ Φ ζ v)
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  constructor
  · calc (C * K)⁻¹ * modelConeQuadratic (χ₂.localWeights angle) ζ v
        = C⁻¹ * (K⁻¹ * modelConeQuadratic (χ₂.localWeights angle) ζ v) := by
          rw [mul_inv]; ring
      _ ≤ C⁻¹ * modelConeQuadratic (χ₁.localWeights angle) (Φ ζ) (fderiv ℂ Φ ζ v) :=
          mul_le_mul_of_nonneg_left hKlo (inv_nonneg.mpr hC0.le)
      _ ≤ _ := hlo
  · calc _ ≤ C * modelConeQuadratic (χ₁.localWeights angle) (Φ ζ) (fderiv ℂ Φ ζ v) := hhi
      _ ≤ C * (K * modelConeQuadratic (χ₂.localWeights angle) ζ v) :=
          mul_le_mul_of_nonneg_left hKhi hC0.le
      _ = C * K * modelConeQuadratic (χ₂.localWeights angle) ζ v := by ring

/-- **For angles `0 < β_i ≤ 1`, the SNC cone condition holds in every SNC chart** (after
shrinking): it does not depend on the chart used in its definition. -/
theorem IsQuasiIsometricSNCCone.forall_chart_of_le_one (hangle : ∀ i, (angle i).beta ≤ 1)
    (h : IsQuasiIsometricSNCCone Δ angle ω₀) (hp : p ∈ Δ.support)
    (χ : SNCChart n X ι Δ.components p) :
    ∃ (s : Set X) (hs : IsOpen s) (hps : p ∈ s) (C : ℝ), 1 ≤ C ∧
      SNCConeComparableIn Δ angle ω₀ (χ.restrOpen s hs hps) C := by
  obtain ⟨χ₁, C, hC, hcomp⟩ := h p hp
  exact hcomp.exists_restrOpen_of_le_one hangle hC χ

end Charts

end ConicalKahler
