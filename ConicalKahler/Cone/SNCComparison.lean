module

public import ConicalKahler.Divisors.SNC
public import ConicalKahler.Cone.Kahler

/-!
# Quasi-isometric cone conditions along SNC divisors

Let `Δ` be an SNC divisor with components labelled by `ι` and let `angle : ι → ConeAngle` assign
an arbitrary cone angle `2πβ_i > 0` to each label. A Kähler form `ω₀` on `X \ ⋃ᵢ Dᵢ` has
**quasi-isometric cone angles `angle` along `Δ`** if near each point of the support there is an
SNC chart `χ` and `C ≥ 1` with

  `C⁻¹ q_model(z; v) ≤ q^χ_{ω₀}(z; v) ≤ C q_model(z; v)`

for all chart points `z` off the active hyperplanes and all `v`. The model is the *same*
`modelConeQuadratic` as before, for the local weights `χ.localWeights angle`
(`some (angle (active j))` in the active slots, `none` elsewhere). Nothing in the model
construction changed.

As for smooth divisors, this is a **quasi-isometry** condition only, with no asymptotic or
regularity content. For angles `β_i > 1` it is an existence-of-compatible-chart condition: the
smooth case embeds (`isConeAlong_iff_isSNCConeAlong`), so the shear counterexample
`not_coneComparableIn_shear` applies.

## Main declarations

* `metricInSNCChart`, `metricQuadraticInSNCChart` (via `formInHolChart`), positivity and the
  change-of-chart law.
* `SNCConeComparableIn Δ angle ω₀ χ C`, `IsQuasiIsometricSNCCone Δ angle ω₀`, alias
  `IsSNCConeAlong`. Shrinking (`SNCConeComparableIn.restrOpen`), constants (`.mono`) and
  localization (`IsQuasiIsometricSNCCone.exists_chart_subset`).
* `modelOnCoordSNC hk angle`: the model `ModelConeForm`-type form on `ℂⁿ \ {z_0 ⋯ z_{k-1} = 0}`.
  It is SNC-conical with `C = 1` (`modelOnCoordSNC_isSNCConeAlong`) and Ricci-flat, for all
  angles.
* `SNCConeKahlerForm`, `SNCConeKahlerForm.IsKahlerEinstein`, `standardSNCConeKahlerForm`.
* **Smooth case as a specialization**: `isConeAlong_iff_isSNCConeAlong`. For a smooth divisor `D`,
  `IsConeAlong D β ω₀` iff the SNC condition holds for `D.toSNC` with the constant angle `β`.
-/

@[expose] public section

open scoped Manifold ContDiff Topology ComplexOrder
open Set Filter

namespace ConicalKahler

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X]
  [IsManifold 𝓘(ℂ, E n) ω X] {ι : Type*}

/-! ### The metric in an SNC chart -/

section Metric

variable (Δ : SNCDivisor n X ι) (ω₀ : KahlerForm n Δ.complement) {p : X}
  (χ : SNCChart n X ι Δ.components p)

/-- The Hermitian coefficient matrix of `ω₀` in the SNC chart `χ`. -/
noncomputable def metricInSNCChart (z : E n) (hz : z ∈ χ.coord.target) (haway : χ.Away z) :
    Matrix (Fin n) (Fin n) ℂ :=
  metricInHolChart Δ.complement ω₀ χ.toHolChart z (χ.symm_notMem_iUnion hz haway)

/-- The Hermitian quadratic form `ω₀(v, Jv)/2` of `ω₀` in the SNC chart `χ`. -/
noncomputable def metricQuadraticInSNCChart (z : E n) (hz : z ∈ χ.coord.target)
    (haway : χ.Away z) (v : E n) : ℝ :=
  metricQuadraticInHolChart Δ.complement ω₀ χ.toHolChart z (χ.symm_notMem_iUnion hz haway) v

variable {Δ ω₀ χ}

theorem metricInSNCChart_posDef {z : E n} (hz : z ∈ χ.coord.target) (haway : χ.Away z) :
    (metricInSNCChart Δ ω₀ χ z hz haway).PosDef :=
  metricInHolChart_posDef (c := χ.toHolChart) hz _

theorem metricQuadraticInSNCChart_pos {z : E n} (hz : z ∈ χ.coord.target) (haway : χ.Away z)
    {v : E n} (hv : v ≠ 0) : 0 < metricQuadraticInSNCChart Δ ω₀ χ z hz haway v :=
  metricQuadraticInHolChart_pos (c := χ.toHolChart) hz _ hv

theorem metricQuadraticInSNCChart_nonneg {z : E n} (hz : z ∈ χ.coord.target) (haway : χ.Away z)
    (v : E n) : 0 ≤ metricQuadraticInSNCChart Δ ω₀ χ z hz haway v :=
  metricQuadraticInHolChart_nonneg (c := χ.toHolChart) hz _ v

/-- The quadratic form only depends on the coordinate map, so shrinking the chart does not change
it. -/
theorem metricQuadraticInSNCChart_restrOpen (s : Set X) (hs : IsOpen s) (hp : p ∈ s) {z : E n}
    (hz : z ∈ (χ.restrOpen s hs hp).coord.target) (haway : (χ.restrOpen s hs hp).Away z)
    (v : E n) :
    metricQuadraticInSNCChart Δ ω₀ (χ.restrOpen s hs hp) z hz haway v =
      metricQuadraticInSNCChart Δ ω₀ χ z (χ.restrOpen_target_subset s hs hp hz) haway v :=
  rfl

/-- **Change of SNC chart:** `q₁(z₁; v) = q₂(z₂; DΦ(z₁) v)` with `Φ = χ₂ ∘ χ₁⁻¹`. -/
theorem metricQuadraticInSNCChart_change {p₁ p₂ : X} {χ₁ : SNCChart n X ι Δ.components p₁}
    {χ₂ : SNCChart n X ι Δ.components p₂} {z₁ z₂ : E n} (hz₁ : z₁ ∈ χ₁.coord.target)
    (haway₁ : χ₁.Away z₁) (hz₂ : z₂ ∈ χ₂.coord.target) (haway₂ : χ₂.Away z₂)
    (hsame : χ₁.coord.symm z₁ = χ₂.coord.symm z₂) (v : E n) :
    metricQuadraticInSNCChart Δ ω₀ χ₁ z₁ hz₁ haway₁ v =
      metricQuadraticInSNCChart Δ ω₀ χ₂ z₂ hz₂ haway₂
        (fderiv ℂ (χ₂.coord ∘ χ₁.coord.symm) z₁ v) :=
  metricQuadraticInHolChart_change (c₁ := χ₁.toHolChart) (c₂ := χ₂.toHolChart) hz₁ _ hz₂ _
    hsame v

end Metric

/-! ### The cone condition -/

/-- The two-sided comparison with the local SNC model in the chart `χ`, for all chart points off
the active hyperplanes and all tangent vectors. -/
def SNCConeComparableIn (Δ : SNCDivisor n X ι) (angle : ι → ConeAngle)
    (ω₀ : KahlerForm n Δ.complement) {p : X} (χ : SNCChart n X ι Δ.components p) (C : ℝ) :
    Prop :=
  ∀ (z : E n) (hz : z ∈ χ.coord.target) (haway : χ.Away z) (v : E n),
    C⁻¹ * modelConeQuadratic (χ.localWeights angle) z v ≤
        metricQuadraticInSNCChart Δ ω₀ χ z hz haway v ∧
      metricQuadraticInSNCChart Δ ω₀ χ z hz haway v ≤
        C * modelConeQuadratic (χ.localWeights angle) z v

/-- **Quasi-isometric cone condition along an SNC divisor** with labelled cone angles: near every
point of the support there is an SNC chart in which `ω₀` is uniformly equivalent to the local
model `ModelConeForm (χ.localWeights angle)`. -/
def IsQuasiIsometricSNCCone (Δ : SNCDivisor n X ι) (angle : ι → ConeAngle)
    (ω₀ : KahlerForm n Δ.complement) : Prop :=
  ∀ p ∈ Δ.support, ∃ (χ : SNCChart n X ι Δ.components p) (C : ℝ), 1 ≤ C ∧
    SNCConeComparableIn Δ angle ω₀ χ C

/-- `IsSNCConeAlong Δ angle ω₀` means **quasi-isometric** cone angles along `Δ`, and nothing
stronger. -/
abbrev IsSNCConeAlong (Δ : SNCDivisor n X ι) (angle : ι → ConeAngle)
    (ω₀ : KahlerForm n Δ.complement) : Prop :=
  IsQuasiIsometricSNCCone Δ angle ω₀

section Basic

variable {Δ : SNCDivisor n X ι} {angle : ι → ConeAngle} {ω₀ : KahlerForm n Δ.complement} {p : X}
  {χ : SNCChart n X ι Δ.components p} {C : ℝ}

/-- **Shrinking.** -/
theorem SNCConeComparableIn.restrOpen (h : SNCConeComparableIn Δ angle ω₀ χ C) (s : Set X)
    (hs : IsOpen s) (hp : p ∈ s) : SNCConeComparableIn Δ angle ω₀ (χ.restrOpen s hs hp) C :=
  fun z hz haway v => by
    rw [metricQuadraticInSNCChart_restrOpen, χ.localWeights_restrOpen]
    exact h z _ haway v

/-- **Enlarging the constant.** -/
theorem SNCConeComparableIn.mono (h : SNCConeComparableIn Δ angle ω₀ χ C) (hC : 0 < C) {C' : ℝ}
    (hCC' : C ≤ C') : SNCConeComparableIn Δ angle ω₀ χ C' := fun z hz haway v => by
  obtain ⟨h1, h2⟩ := h z hz haway v
  have hq := modelConeQuadratic_nonneg (χ.localWeights angle) z v
  have hinv : C'⁻¹ ≤ C⁻¹ := inv_anti₀ hC hCC'
  exact ⟨le_trans (mul_le_mul_of_nonneg_right hinv hq) h1,
    le_trans h2 (mul_le_mul_of_nonneg_right hCC' hq)⟩

/-- **Localization.** The comparison charts can be chosen inside any neighbourhood of `p`. -/
theorem IsQuasiIsometricSNCCone.exists_chart_subset (h : IsQuasiIsometricSNCCone Δ angle ω₀)
    (hp : p ∈ Δ.support) (s : Set X) (hs : IsOpen s) (hps : p ∈ s) :
    ∃ (χ : SNCChart n X ι Δ.components p) (C : ℝ), 1 ≤ C ∧ χ.coord.source ⊆ s ∧
      SNCConeComparableIn Δ angle ω₀ χ C := by
  obtain ⟨χ, C, hC, hcomp⟩ := h p hp
  exact ⟨χ.restrOpen s hs hps, C, hC, fun x hx => hx.2, hcomp.restrOpen s hs hps⟩

end Basic

/-! ### Conical Kähler forms along SNC divisors -/

/-- A Kähler form on `X \ ⋃ᵢ Dᵢ` with quasi-isometric cone angle `angle i` along each labelled
component `Dᵢ`. -/
structure SNCConeKahlerForm (Δ : SNCDivisor n X ι) (angle : ι → ConeAngle) where
  /-- The Kähler form on the complement. -/
  form : KahlerForm n Δ.complement
  cone_condition : IsSNCConeAlong Δ angle form

/-- The Kähler–Einstein equation `Ric = λ ω` **on the complement** `X \ ⋃ᵢ Dᵢ`. -/
def SNCConeKahlerForm.IsKahlerEinstein {Δ : SNCDivisor n X ι} {angle : ι → ConeAngle}
    (g : SNCConeKahlerForm Δ angle) (lam : ℝ) : Prop :=
  g.form.ricciForm = lam • g.form.toFormField

/-! ### The model along coordinate hyperplanes -/

section CoordModel

variable {k : ℕ} (hk : k ≤ n) (angle : Fin k → ConeAngle)

/-- **The SNC model form**
`i ∑_{j<k} β_j² |z_j|^(2β_j-2) dz_j ∧ dz̄_j + i ∑_{j≥k} dz_j ∧ dz̄_j` on the complement of
`{z_0 ⋯ z_{k-1} = 0}`, for arbitrary angles `β_j > 0`. It is `modelConeFormOn` for the
weights `coordSNCWeights hk angle`. -/
noncomputable def modelOnCoordSNC : KahlerForm n (coordSNC n k hk).complement :=
  modelConeFormOn (coordSNCWeights hk angle) (coordSNC n k hk).complement
    (coordSNC_complement_subset hk angle)

/-- Its coefficient matrix is the diagonal model matrix. -/
theorem modelOnCoordSNC_coeffMatrix (x : (coordSNC n k hk).complement) :
    (modelOnCoordSNC hk angle x).coeffMatrix = modelConeMatrix (coordSNCWeights hk angle) x :=
  modelConeFormOn_coeffMatrix _ _ _ x

/-- The SNC model is Ricci-flat on the complement, for all angles. -/
theorem modelOnCoordSNC_ricciFlat : (modelOnCoordSNC hk angle).IsRicciFlat :=
  modelConeFormOn_ricciFlat _ _ _

/-- In the identity SNC chart, the SNC model is comparable to itself with `C = 1`. -/
theorem modelOnCoordSNC_sncConeComparableIn (p : E n) :
    SNCConeComparableIn (coordSNC n k hk) angle (modelOnCoordSNC hk angle)
      (coordSNCChart n k hk p) 1 := by
  intro z hz haway v
  have hzU : z ∈ (coordSNC n k hk).complement :=
    (coordSNCChart n k hk p).symm_notMem_iUnion hz haway
  have hq : metricQuadraticInSNCChart (coordSNC n k hk) (modelOnCoordSNC hk angle)
      (coordSNCChart n k hk p) z hz haway v = modelConeQuadratic (coordSNCWeights hk angle) z v := by
    refine (metricQuadraticInHolChart_refl _ (modelOnCoordSNC hk angle) hzU v).trans ?_
    rw [modelOnCoordSNC, modelConeFormOn_apply_I_smul]
    ring
  rw [hq]
  refine ⟨le_of_eq ?_, le_of_eq ?_⟩ <;> simp only [inv_one, one_mul] <;> rfl

/-- **The SNC model has cone angles `angle` along the coordinate hyperplanes**, for all angles
`β_j > 0`. -/
theorem modelOnCoordSNC_isSNCConeAlong :
    IsSNCConeAlong (coordSNC n k hk) angle (modelOnCoordSNC hk angle) := fun p _ =>
  ⟨coordSNCChart n k hk p, 1, le_rfl, modelOnCoordSNC_sncConeComparableIn hk angle p⟩

/-- The SNC model as a conical Kähler form. -/
noncomputable def standardSNCConeKahlerForm : SNCConeKahlerForm (coordSNC n k hk) angle where
  form := modelOnCoordSNC hk angle
  cone_condition := modelOnCoordSNC_isSNCConeAlong hk angle

/-- The SNC model is Kähler–Einstein with `λ = 0` on the complement. -/
theorem standardSNCConeKahlerForm_isKahlerEinstein :
    (standardSNCConeKahlerForm hk angle).IsKahlerEinstein 0 := by
  rw [SNCConeKahlerForm.IsKahlerEinstein, zero_smul]
  exact modelOnCoordSNC_ricciFlat hk angle

end CoordModel

/-! ### The smooth case is a specialization -/

section Specialization

variable [NeZero n] (D : SmoothDivisor n X)

/-- A Kähler form on `X \ D` as a Kähler form on the complement of the one-label SNC divisor. -/
noncomputable def SmoothDivisor.toSNCForm (ω₀ : KahlerForm n D.complement) :
    KahlerForm n D.toSNC.complement :=
  kahlerCast D.complement D.toSNC_complement.symm ω₀

/-- The SNC-chart metric of `D.toSNC` is the adapted-chart metric of `D`, for charts with the same
coordinate map. -/
theorem metricQuadraticInSNCChart_toSNC (ω₀ : KahlerForm n D.complement) {p : X}
    (χ' : SNCChart n X Unit D.toSNC.components p) (χ : DivisorChart n X D.carrier p)
    (hcoord : χ'.coord = χ.coord) {z : E n} (hz' : z ∈ χ'.coord.target) (haway' : χ'.Away z)
    (hz : z ∈ χ.coord.target) (haway : z 0 ≠ 0) (v : E n) :
    metricQuadraticInSNCChart D.toSNC (D.toSNCForm ω₀) χ' z hz' haway' v =
      metricQuadraticInAdaptedChart D ω₀ χ z hz haway v := by
  have hU : χ'.toHolChart.coord.symm z ∈ D.complement := by
    rw [χ'.toHolChart_coord, hcoord]
    exact χ.symm_notMem hz haway
  have e1 := formInHolChart_kahlerCast D.complement ω₀ χ'.toHolChart D.toSNC_complement.symm hU
    (χ'.symm_notMem_iUnion hz' haway')
  have e2 := formInHolChart_congr D.complement ω₀ χ'.toHolChart (c' := χ.toHolChart) hcoord hU
    (χ.symm_notMem hz haway)
  exact congrArg (fun α : E n [⋀^Fin 2]→L[ℝ] ℝ => α ![v, Complex.I • v] / 2) (e1.trans e2)

/-- **The smooth-divisor cone condition is the one-label case of the SNC cone condition.** -/
theorem isConeAlong_iff_isSNCConeAlong (β : ConeAngle) (ω₀ : KahlerForm n D.complement) :
    IsConeAlong D β ω₀ ↔ IsSNCConeAlong D.toSNC (fun _ => β) (D.toSNCForm ω₀) := by
  constructor
  · intro h p hp
    rw [D.toSNC_support] at hp
    obtain ⟨χ, C, hC, hcomp⟩ := h p hp
    refine ⟨χ.toSNCChart, C, hC, fun z hz haway v => ?_⟩
    have h0 : z 0 ≠ 0 :=
      (away_iff_of_k_eq_one (components := D.toSNC.components) χ.toSNCChart rfl).mp haway
    rw [metricQuadraticInSNCChart_toSNC D ω₀ _ χ rfl hz haway hz h0,
      localWeights_eq_singleConeWeights (components := D.toSNC.components) χ.toSNCChart rfl β]
    exact hcomp z hz h0 v
  · intro h p hp
    obtain ⟨χ', C, hC, hcomp⟩ := h p (by rw [D.toSNC_support]; exact hp)
    have hk := D.toSNC_chart_k hp χ'
    refine ⟨χ'.toDivisorChartOfSmooth hk, C, hC, fun z hz haway v => ?_⟩
    have haway' : χ'.Away z := (away_iff_of_k_eq_one χ' hk).mpr haway
    have h := hcomp z hz haway' v
    rw [metricQuadraticInSNCChart_toSNC D ω₀ χ' (χ'.toDivisorChartOfSmooth hk) rfl hz haway' hz
      haway, localWeights_eq_singleConeWeights χ' hk β] at h
    exact h

end Specialization

end ConicalKahler
