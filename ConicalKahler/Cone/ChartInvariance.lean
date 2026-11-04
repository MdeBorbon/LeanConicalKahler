module

public import ConicalKahler.Analysis.HyperplaneMaps
public import ConicalKahler.Cone.Comparison
public import ConicalKahler.Cone.Standard

/-!
# Chart invariance of the cone condition for `0 < β ≤ 1`

Let `Φ` be a holomorphic map between adapted coordinates, defined near a point `ζ₀` of the
hyperplane `{ζ_0 = 0}`, with a holomorphic local inverse, both preserving the hyperplane. For
`0 < β ≤ 1` the model quadratic forms are uniformly comparable under `Φ` near `ζ₀`
(`exists_model_comparison`):

  `K⁻¹ q_model(ζ; v) ≤ q_model(Φ(ζ); DΦ(ζ) v) ≤ K q_model(ζ; v)`.

Combined with the change-of-chart law for `metricQuadraticInAdaptedChart`, this gives the main
theorem: **for `0 < β ≤ 1`, if `ω₀` is comparable to the model in one adapted chart at `p`, it is
comparable to the model in any other adapted chart at `p`, after shrinking**
(`ConeComparableIn.exists_restrOpen_of_le_one`, `IsQuasiIsometricCone.forall_chart_of_le_one`).

Where `β ≤ 1` is used: on `{|ζ_0| ≤ 1}` the weight `β² |ζ_0|^(2β-2)` is `≥ β²`, so the
unweighted norm `|v|²` is controlled by `q_model(ζ; v)`; tangential derivatives of `Φ` may mix
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
  set a := 2 * β.beta - 2 with ha_def
  have ha : a ≤ 0 := by rw [ha_def]; linarith
  set x := ‖ζ 0‖ with hx_def
  have hx : 0 < x := norm_pos_iff.mpr hζ0
  set y := ‖z 0‖ with hy_def
  have hy : 0 < y := lt_of_lt_of_le (mul_pos hc hx) hz
  set ca := c ^ a with hca_def
  have hca : 0 < ca := Real.rpow_pos_of_pos hc a
  set xa := x ^ a with hxa_def
  have hxa1 : 1 ≤ xa := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx hζ1 ha
  have hya : y ^ a ≤ ca * xa := by
    calc y ^ a ≤ (c * x) ^ a := Real.rpow_le_rpow_of_nonpos (mul_pos hc hx) hz ha
      _ = ca * xa := Real.mul_rpow hc.le hx.le
  have hx2 : xa * x ^ 2 ≤ 1 := by
    have h : xa * x ^ 2 = x ^ (a + 2) := by
      rw [Real.rpow_add hx, Real.rpow_two]
    rw [h]
    exact Real.rpow_le_one hx.le hζ1 (by rw [ha_def]; linarith)
  set b2 := β.beta ^ 2 with hb2_def
  have hb2 : 0 < b2 := by positivity
  set V0 := ‖v 0‖ ^ 2 with hV0_def
  set V := ‖v‖ ^ 2 with hV_def
  have hV0 : 0 ≤ V0 := by positivity
  have hV0V : V0 ≤ V := pow_le_pow_left₀ (norm_nonneg _) (norm_apply_zero_le v) 2
  set X0 := ‖ξ 0‖ ^ 2 with hX0_def
  set X := ‖ξ‖ ^ 2 with hX_def
  have hX0 : 0 ≤ X0 := by positivity
  have hX0X : X0 ≤ X := pow_le_pow_left₀ (norm_nonneg _) (norm_apply_zero_le ξ) 2
  set q := b2 * xa * V0 + (V - V0) with hq_def
  have hw0 : 0 ≤ b2 * xa * V0 := by positivity
  have hwq : b2 * xa * V0 ≤ q := by rw [hq_def]; linarith
  -- `|v|² ≤ (1 + 1/β²) q_model(ζ; v)` (this is where `β ≤ 1` enters, through `xa ≥ 1`)
  have hVq : V ≤ (1 + 1 / b2) * q := by
    have h1 : V0 ≤ 1 / b2 * (b2 * xa * V0) := by
      rw [show 1 / b2 * (b2 * xa * V0) = xa * V0 by field_simp]
      exact le_mul_of_one_le_left hV0 hxa1
    have h2 : 1 / b2 * (b2 * xa * V0) ≤ 1 / b2 * q :=
      mul_le_mul_of_nonneg_left hwq (by positivity)
    have h3 : V - V0 ≤ q := by rw [hq_def]; linarith
    have h4 : (1 + 1 / b2) * q = q + 1 / b2 * q := by ring
    linarith
  -- `|ξ_0|² ≤ 2 L² |v_0|² + 2 L₂² |ζ_0|² |v|²`
  have hX0le : X0 ≤ 2 * L ^ 2 * V0 + 2 * L₂ ^ 2 * x ^ 2 * V := by
    have hsq : ‖ξ 0‖ ^ 2 ≤ (L * ‖v 0‖ + L₂ * x * ‖v‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hξ0 2
    have hid : 2 * (L * ‖v 0‖) ^ 2 + 2 * (L₂ * x * ‖v‖) ^ 2 - (L * ‖v 0‖ + L₂ * x * ‖v‖) ^ 2 =
        (L * ‖v 0‖ - L₂ * x * ‖v‖) ^ 2 := by ring
    have hnn := sq_nonneg (L * ‖v 0‖ - L₂ * x * ‖v‖)
    have hexp : 2 * (L * ‖v 0‖) ^ 2 + 2 * (L₂ * x * ‖v‖) ^ 2 =
        2 * L ^ 2 * V0 + 2 * L₂ ^ 2 * x ^ 2 * V := by
      rw [hV0_def, hV_def]
      ring
    rw [hX0_def]
    linarith
  -- `|ξ|² ≤ L² |v|²`
  have hXle : X ≤ L ^ 2 * V := by
    rw [hX_def, hV_def, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hξ 2
  -- assemble
  have hyaX : b2 * y ^ a * X0 ≤ b2 * (ca * xa) * X0 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hya hb2.le) hX0
  have hmain : b2 * (ca * xa) * X0 ≤
      2 * L ^ 2 * ca * (b2 * xa * V0) + 2 * L₂ ^ 2 * ca * b2 * (xa * x ^ 2) * V := by
    have hpos : 0 ≤ b2 * ca * xa := by positivity
    calc b2 * (ca * xa) * X0 = (b2 * ca * xa) * X0 := by ring
      _ ≤ (b2 * ca * xa) * (2 * L ^ 2 * V0 + 2 * L₂ ^ 2 * x ^ 2 * V) :=
        mul_le_mul_of_nonneg_left hX0le hpos
      _ = 2 * L ^ 2 * ca * (b2 * xa * V0) + 2 * L₂ ^ 2 * ca * b2 * (xa * x ^ 2) * V := by ring
  have hmain2 : 2 * L₂ ^ 2 * ca * b2 * (xa * x ^ 2) * V ≤ 2 * L₂ ^ 2 * ca * b2 * V := by
    have hpos : 0 ≤ 2 * L₂ ^ 2 * ca * b2 * V := by positivity
    calc 2 * L₂ ^ 2 * ca * b2 * (xa * x ^ 2) * V = (2 * L₂ ^ 2 * ca * b2 * V) * (xa * x ^ 2) := by
          ring
      _ ≤ (2 * L₂ ^ 2 * ca * b2 * V) * 1 := mul_le_mul_of_nonneg_left hx2 hpos
      _ = 2 * L₂ ^ 2 * ca * b2 * V := mul_one _
  have h1 : 2 * L ^ 2 * ca * (b2 * xa * V0) ≤ 2 * L ^ 2 * ca * q :=
    mul_le_mul_of_nonneg_left hwq (by positivity)
  have hfinal : b2 * y ^ a * X0 + (X - X0) ≤
      2 * L ^ 2 * ca * q + (2 * L₂ ^ 2 * ca * b2 + L ^ 2) * V := by
    have hexp : (2 * L₂ ^ 2 * ca * b2 + L ^ 2) * V = 2 * L₂ ^ 2 * ca * b2 * V + L ^ 2 * V := by
      ring
    linarith
  have hVq' : (2 * L₂ ^ 2 * ca * b2 + L ^ 2) * V ≤
      (2 * L₂ ^ 2 * ca * b2 + L ^ 2) * ((1 + 1 / b2) * q) :=
    mul_le_mul_of_nonneg_left hVq (by positivity)
  calc b2 * y ^ a * X0 + (X - X0)
      ≤ 2 * L ^ 2 * ca * q + (2 * L₂ ^ 2 * ca * b2 + L ^ 2) * ((1 + 1 / b2) * q) := by
        linarith
    _ = (2 * L ^ 2 * ca + (2 * L₂ ^ 2 * ca * b2 + L ^ 2) * (1 + 1 / b2)) * q := by ring

/-! ### Two-sided comparison under hyperplane-preserving biholomorphisms -/

/-- One-sided bound: `q_model(Ψ ζ; DΨ(ζ) v) ≤ K q_model(ζ; v)` near `ζ₀`, for `β ≤ 1`. -/
theorem exists_model_upper_bound {β : ConeAngle} (hβ : β.beta ≤ 1) {Ψ Ψ' : E n → E n}
    {ζ₀ : E n} (hζ₀ : ζ₀ 0 = 0) (hΨ : ContDiffAt ℂ 2 Ψ ζ₀) (hΨ' : ContDiffAt ℂ 2 Ψ' (Ψ ζ₀))
    (hinv : ∀ᶠ ζ in 𝓝 ζ₀, Ψ' (Ψ ζ) = ζ) (hpres : ∀ᶠ ζ in 𝓝 ζ₀, ζ 0 = 0 → Ψ ζ 0 = 0)
    (hpres' : ∀ᶠ z in 𝓝 (Ψ ζ₀), z 0 = 0 → Ψ' z 0 = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ ζ in 𝓝 ζ₀, ζ 0 ≠ 0 → Ψ ζ 0 ≠ 0 ∧ ∀ v,
      modelConeQuadratic (singleConeWeights β) (Ψ ζ) (fderiv ℂ Ψ ζ v) ≤
        K * modelConeQuadratic (singleConeWeights β) ζ v := by
  have hz₀ : Ψ ζ₀ 0 = 0 := hpres.self_of_nhds hζ₀
  obtain ⟨L, L₂, hL, hL₂, hest⟩ := exists_hyperplane_estimates hζ₀ hΨ hpres
  obtain ⟨L', _, hL', _, hest'⟩ := exists_hyperplane_estimates hz₀ hΨ' hpres'
  have hest'' : ∀ᶠ ζ in 𝓝 ζ₀, ‖Ψ' (Ψ ζ) 0‖ ≤ L' * ‖Ψ ζ 0‖ :=
    hΨ.continuousAt.tendsto.eventually (Filter.Eventually.mono hest' fun _ h => h.1)
  have hsmall : ∀ᶠ ζ in 𝓝 ζ₀, ‖ζ 0‖ ≤ 1 := by
    have hcont : ContinuousAt (fun ζ : E n => ‖ζ 0‖) ζ₀ :=
      (continuous_norm.comp (EuclideanSpace.proj (0 : Fin n) : E n →L[ℂ] ℂ).continuous).continuousAt
    exact (hcont.eventually_lt continuousAt_const (by simp [hζ₀])).mono fun _ h => h.le
  set c := 1 / L' with hc_def
  have hc : 0 < c := by positivity
  have hcpow : 0 < c ^ (2 * β.beta - 2) := Real.rpow_pos_of_pos hc _
  refine ⟨2 * L ^ 2 * c ^ (2 * β.beta - 2) +
    (2 * L₂ ^ 2 * c ^ (2 * β.beta - 2) * β.beta ^ 2 + L ^ 2) * (1 + 1 / β.beta ^ 2),
    by positivity, ?_⟩
  filter_upwards [hest, hest'', hinv, hsmall] with ζ h1 h2 h3 h4
  intro hζ0
  rw [h3] at h2
  have hlow : c * ‖ζ 0‖ ≤ ‖Ψ ζ 0‖ := by
    rw [hc_def, div_mul_eq_mul_div, one_mul, div_le_iff₀ hL']
    linarith
  have hΨ0 : Ψ ζ 0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    exact hζ0 (norm_le_zero_iff.mp (le_of_mul_le_mul_left (by simpa using hlow) hc))
  refine ⟨hΨ0, fun v => ?_⟩
  exact modelConeQuadratic_le_of_le_one hβ hc hζ0 h4 hlow
    (((fderiv ℂ Ψ ζ).le_opNorm v).trans (mul_le_mul_of_nonneg_right h1.2.1 (norm_nonneg _)))
    (h1.2.2 v)

/-- **Two-sided comparison of the model under a hyperplane-preserving biholomorphism**
(`0 < β ≤ 1`). -/
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
  obtain ⟨K₁, hK₁, hup⟩ := exists_model_upper_bound hβ hζ₀ hΨ hΨ' hinv hpres hpres'
  have hΨ'' : ContDiffAt ℂ 2 Ψ (Ψ' (Ψ ζ₀)) := by rwa [hΨ'Ψ]
  have hpres'' : ∀ᶠ ζ in 𝓝 (Ψ' (Ψ ζ₀)), ζ 0 = 0 → Ψ ζ 0 = 0 := by rwa [hΨ'Ψ]
  obtain ⟨K₂, hK₂, hdown⟩ := exists_model_upper_bound hβ hz₀ hΨ' hΨ'' hinv' hpres' hpres''
  have hdown' := hΨ.continuousAt.tendsto.eventually hdown
  have hdΨ : ∀ᶠ ζ in 𝓝 ζ₀, DifferentiableAt ℂ Ψ ζ :=
    (hΨ.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have hdΨ' : ∀ᶠ ζ in 𝓝 ζ₀, DifferentiableAt ℂ Ψ' (Ψ ζ) :=
    hΨ.continuousAt.tendsto.eventually
      ((hΨ'.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num))
  have hloc : ∀ᶠ ζ in 𝓝 ζ₀, ∀ᶠ x in 𝓝 ζ, Ψ' (Ψ x) = x := hinv.eventually_nhds
  set K := max (max K₁ K₂) 1 with hK_def
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hK₁K : K₁ ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hK₂K : K₂ ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨K, hK1, ?_⟩
  filter_upwards [hup, hdown', hdΨ, hdΨ', hloc, hinv] with ζ h1 h2 h3 h4 h5 h6
  intro hζ0
  obtain ⟨hΨ0, hupper⟩ := h1 hζ0
  obtain ⟨-, hlower⟩ := h2 hΨ0
  have hq := modelConeQuadratic_nonneg (singleConeWeights β) ζ
  have hq' := modelConeQuadratic_nonneg (singleConeWeights β) (Ψ ζ)
  refine ⟨hΨ0, fun v => ⟨?_, ?_⟩⟩
  · have hcomp : fderiv ℂ (Ψ' ∘ Ψ) ζ = (fderiv ℂ Ψ' (Ψ ζ)).comp (fderiv ℂ Ψ ζ) :=
      fderiv_comp ζ h4 h3
    have hidf : fderiv ℂ (Ψ' ∘ Ψ) ζ = ContinuousLinearMap.id ℂ (E n) := by
      have h5' : (Ψ' ∘ Ψ) =ᶠ[𝓝 ζ] id := h5
      rw [h5'.fderiv_eq, fderiv_id]
    have hid : fderiv ℂ Ψ' (Ψ ζ) (fderiv ℂ Ψ ζ v) = v := by
      have := congrArg (fun A : E n →L[ℂ] E n => A v) (hcomp.symm.trans hidf)
      simpa using this
    have hlow := hlower (fderiv ℂ Ψ ζ v)
    rw [hid, h6] at hlow
    rw [inv_mul_le_iff₀ hK0]
    exact hlow.trans (mul_le_mul_of_nonneg_right hK₂K (hq' _))
  · exact (hupper v).trans (mul_le_mul_of_nonneg_right hK₁K (hq _))

/-! ### Chart invariance -/

section Charts

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X] [IsManifold 𝓘(ℂ, E n) ω X]
  {D : SmoothDivisor n X} {β : ConeAngle} {ω₀ : KahlerForm n D.complement} {p : X}

/-- **Chart invariance of the cone condition for `0 < β ≤ 1`.** If `ω₀` is comparable to the model
in one adapted chart `χ₁` at `p ∈ D`, then it is comparable to the model in any other adapted
chart `χ₂` at `p`, after restricting `χ₂` to a smaller neighbourhood of `p`. -/
theorem ConeComparableIn.exists_restrOpen_of_le_one (hβ : β.beta ≤ 1) (hp : p ∈ D.carrier)
    {χ₁ : DivisorChart n X D.carrier p} {C : ℝ} (hC : 1 ≤ C)
    (h : ConeComparableIn D β ω₀ χ₁ C) (χ₂ : DivisorChart n X D.carrier p) :
    ∃ (s : Set X) (hs : IsOpen s) (hps : p ∈ s) (C' : ℝ), 1 ≤ C' ∧
      ConeComparableIn D β ω₀ (χ₂.restrOpen s hs hps) C' := by
  set Φ : E n → E n := χ₁.coord ∘ χ₂.coord.symm with hΦ_def
  set Φ' : E n → E n := χ₂.coord ∘ χ₁.coord.symm with hΦ'_def
  set ζ₀ := χ₂.coord p
  have hζ₀t : ζ₀ ∈ χ₂.coord.target := χ₂.coord.map_source χ₂.center_mem
  have hζ₀ : ζ₀ 0 = 0 := χ₂.coord_center_zero hp
  have hpsym : χ₂.coord.symm ζ₀ = p := χ₂.coord.left_inv χ₂.center_mem
  have hz₀t : χ₁.coord p ∈ χ₁.coord.target := χ₁.coord.map_source χ₁.center_mem
  have hΦζ₀ : Φ ζ₀ = χ₁.coord p := by simp only [hΦ_def, Function.comp_apply, hpsym]
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
  have hΦ : ContDiffAt ℂ 2 Φ ζ₀ :=
    (contDiffAt_adaptedTransition χ₂ χ₁ hζ₀t (by rw [hpsym]; exact χ₁.center_mem)).of_le h2
  have hΦ' : ContDiffAt ℂ 2 Φ' (Φ ζ₀) := by
    rw [hΦζ₀]
    exact (contDiffAt_adaptedTransition χ₁ χ₂ hz₀t
      (by rw [χ₁.coord.left_inv χ₁.center_mem]; exact χ₂.center_mem)).of_le h2
  -- neighbourhood facts at `ζ₀` (in `χ₂`-coordinates)
  have N1 : ∀ᶠ ζ in 𝓝 ζ₀, ζ ∈ χ₂.coord.target := χ₂.coord.open_target.mem_nhds hζ₀t
  have N2 : ∀ᶠ ζ in 𝓝 ζ₀, χ₂.coord.symm ζ ∈ χ₁.coord.source :=
    (χ₂.coord.continuousAt_symm hζ₀t).preimage_mem_nhds
      (χ₁.coord.open_source.mem_nhds (by rw [hpsym]; exact χ₁.center_mem))
  have hinv : ∀ᶠ ζ in 𝓝 ζ₀, Φ' (Φ ζ) = ζ := by
    filter_upwards [N1, N2] with ζ h1 h2
    simp only [hΦ_def, hΦ'_def, Function.comp_apply, χ₁.coord.left_inv h2, χ₂.coord.right_inv h1]
  have hpres : ∀ᶠ ζ in 𝓝 ζ₀, ζ 0 = 0 → Φ ζ 0 = 0 := by
    filter_upwards [N1, N2] with ζ h1 h2 hζ
    have hx := χ₂.coord.map_target h1
    have hD : χ₂.coord.symm ζ ∈ D.carrier := by
      rw [χ₂.cutsOut _ hx, χ₂.coord.right_inv h1]
      exact hζ
    exact (χ₁.cutsOut _ h2).mp hD
  -- neighbourhood facts at `z₀ = Φ ζ₀` (in `χ₁`-coordinates)
  have hz₀sym : χ₁.coord.symm (χ₁.coord p) = p := χ₁.coord.left_inv χ₁.center_mem
  have M1 : ∀ᶠ z in 𝓝 (Φ ζ₀), z ∈ χ₁.coord.target := by
    rw [hΦζ₀]
    exact χ₁.coord.open_target.mem_nhds hz₀t
  have M2 : ∀ᶠ z in 𝓝 (Φ ζ₀), χ₁.coord.symm z ∈ χ₂.coord.source := by
    rw [hΦζ₀]
    exact (χ₁.coord.continuousAt_symm hz₀t).preimage_mem_nhds
      (χ₂.coord.open_source.mem_nhds (by rw [hz₀sym]; exact χ₂.center_mem))
  have hinv' : ∀ᶠ z in 𝓝 (Φ ζ₀), Φ (Φ' z) = z := by
    filter_upwards [M1, M2] with z h1 h2
    simp only [hΦ_def, hΦ'_def, Function.comp_apply, χ₂.coord.left_inv h2, χ₁.coord.right_inv h1]
  have hpres' : ∀ᶠ z in 𝓝 (Φ ζ₀), z 0 = 0 → Φ' z 0 = 0 := by
    filter_upwards [M1, M2] with z h1 h2 hz
    have hx := χ₁.coord.map_target h1
    have hD : χ₁.coord.symm z ∈ D.carrier := by
      rw [χ₁.cutsOut _ hx, χ₁.coord.right_inv h1]
      exact hz
    exact (χ₂.cutsOut _ h2).mp hD
  obtain ⟨K, hK1, hcmp⟩ := exists_model_comparison hβ hζ₀ hΦ hΦ' hinv hinv' hpres hpres'
  -- an open neighbourhood `V` of `ζ₀` on which everything holds
  obtain ⟨V, hVsub, hVopen, hζ₀V⟩ := mem_nhds_iff.mp ((N1.and N2).and hcmp)
  refine ⟨χ₂.coord.source ∩ χ₂.coord ⁻¹' V,
    χ₂.coord.continuousOn.isOpen_inter_preimage χ₂.coord.open_source hVopen,
    ⟨χ₂.center_mem, hζ₀V⟩, C * K, one_le_mul_of_one_le_of_one_le hC hK1, ?_⟩
  intro ζ hζ haway v
  have hζV : ζ ∈ V := by
    have h := hζ.2.2
    rwa [Set.mem_preimage, χ₂.coord.right_inv hζ.1] at h
  obtain ⟨⟨hζt, hsrc⟩, hgood⟩ := hVsub hζV
  obtain ⟨hΦ0, hK⟩ := hgood haway
  obtain ⟨hKlo, hKhi⟩ := hK v
  have hzt : Φ ζ ∈ χ₁.coord.target := χ₁.coord.map_source hsrc
  have hsame : χ₂.coord.symm ζ = χ₁.coord.symm (Φ ζ) := (χ₁.coord.left_inv hsrc).symm
  have e : metricQuadraticInAdaptedChart D ω₀
      (χ₂.restrOpen (χ₂.coord.source ∩ χ₂.coord ⁻¹' V)
        (χ₂.coord.continuousOn.isOpen_inter_preimage χ₂.coord.open_source hVopen)
        ⟨χ₂.center_mem, hζ₀V⟩) ζ hζ haway v =
      metricQuadraticInAdaptedChart D ω₀ χ₂ ζ hζt haway v := rfl
  rw [e, metricQuadraticInAdaptedChart_change hζt haway hzt hΦ0 hsame]
  obtain ⟨hlo, hhi⟩ := h (Φ ζ) hzt hΦ0 (fderiv ℂ Φ ζ v)
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  constructor
  · calc (C * K)⁻¹ * modelConeQuadratic (singleConeWeights β) ζ v
        = C⁻¹ * (K⁻¹ * modelConeQuadratic (singleConeWeights β) ζ v) := by
          rw [mul_inv]; ring
      _ ≤ C⁻¹ * modelConeQuadratic (singleConeWeights β) (Φ ζ) (fderiv ℂ Φ ζ v) :=
          mul_le_mul_of_nonneg_left hKlo (inv_nonneg.mpr hC0.le)
      _ ≤ _ := hlo
  · calc _ ≤ C * modelConeQuadratic (singleConeWeights β) (Φ ζ) (fderiv ℂ Φ ζ v) := hhi
      _ ≤ C * (K * modelConeQuadratic (singleConeWeights β) ζ v) :=
          mul_le_mul_of_nonneg_left hKhi hC0.le
      _ = C * K * modelConeQuadratic (singleConeWeights β) ζ v := by ring

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
