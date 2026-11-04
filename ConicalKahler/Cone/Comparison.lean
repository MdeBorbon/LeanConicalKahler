module

public import ConicalKahler.Cone.ChartMetric

/-!
# Quasi-isometric cone conditions

A Kähler form `ω₀` on `X \ D` has **quasi-isometric cone angle `2πβ` along `D`** if near each
point `p ∈ D` there is an adapted chart `χ` and a constant `C ≥ 1` with

  `C⁻¹ q_model(z; v) ≤ q^χ_{ω₀}(z; v) ≤ C q_model(z; v)`

for *all* `z ∈ χ.target` with `z_0 ≠ 0` and *all* `v ∈ ℂⁿ`, where `q^χ_{ω₀}` is the Hermitian
quadratic form of `ω₀` in `χ`-coordinates (`metricQuadraticInAdaptedChart`) and `q_model` that of
`ω_β` (`modelConeQuadratic (singleConeWeights β)`). Both sides are Hermitian quadratic forms, so
the convention factor `2` of the Riemannian metric cancels (`coneComparableIn_iff_riemannian`).

This is a **quasi-isometry** condition only. It does not assert a unique tangent cone, a
polyhomogeneous expansion or any weighted Hölder regularity; those are separate, stronger
interfaces (spec §3.5) and are deliberately not defined here.

For `β > 1` the condition is an *existence-of-a-compatible-chart* condition: the comparison is not
invariant under arbitrary adapted changes of chart (`ConicalKahler.not_coneComparableIn_shear`).

## Main declarations

* `ConeComparableIn D β ω₀ χ C`: the two-sided bound in the fixed chart `χ`.
* `IsQuasiIsometricCone D β ω₀`, with the alias `IsConeAlong`.
* `ConeComparableIn.restrOpen`, `ConeComparableIn.mono`: shrinking the chart, enlarging `C`.
* `IsQuasiIsometricCone.exists_chart_subset`: the charts can be taken inside any neighbourhood.
* `modelOnHyperplane β` and `modelOnHyperplane_isConeAlong`: the standard cone form on the
  complement of the coordinate hyperplane satisfies the condition with `C = 1`.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Set Filter

namespace ConicalKahler

variable {n : ℕ} [NeZero n] {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X]
  [IsManifold 𝓘(ℂ, E n) ω X]

/-- The two-sided comparison `C⁻¹ q_model ≤ q^χ_{ω₀} ≤ C q_model` in the adapted chart `χ`, for
all coordinate points off `{z_0 = 0}` and all tangent vectors. -/
def ConeComparableIn (D : SmoothDivisor n X) (β : ConeAngle) (ω₀ : KahlerForm n D.complement)
    {p : X} (χ : DivisorChart n X D.carrier p) (C : ℝ) : Prop :=
  ∀ (z : E n) (hz : z ∈ χ.coord.target) (haway : z 0 ≠ 0) (v : E n),
    C⁻¹ * modelConeQuadratic (singleConeWeights β) z v ≤
        metricQuadraticInAdaptedChart D ω₀ χ z hz haway v ∧
      metricQuadraticInAdaptedChart D ω₀ χ z hz haway v ≤
        C * modelConeQuadratic (singleConeWeights β) z v

/-- **Quasi-isometric cone condition** along a smooth divisor: near every point of `D` there is an
adapted chart in which `ω₀` is uniformly equivalent to the model `ω_β`. The chart and the constant
may depend on the point. -/
def IsQuasiIsometricCone (D : SmoothDivisor n X) (β : ConeAngle)
    (ω₀ : KahlerForm n D.complement) : Prop :=
  ∀ p : X, p ∈ D.carrier →
    ∃ (χ : DivisorChart n X D.carrier p) (C : ℝ), 1 ≤ C ∧ ConeComparableIn D β ω₀ χ C

/-- `IsConeAlong D β ω₀` means **quasi-isometric** cone angle `2πβ` along `D`
(`IsQuasiIsometricCone`), and nothing stronger: no asymptotic expansion, tangent-cone uniqueness or
weighted regularity is implied. -/
abbrev IsConeAlong (D : SmoothDivisor n X) (β : ConeAngle) (ω₀ : KahlerForm n D.complement) :
    Prop :=
  IsQuasiIsometricCone D β ω₀

/-- The definition, unfolded to the literal form of the specification. -/
theorem isQuasiIsometricCone_iff (D : SmoothDivisor n X) (β : ConeAngle)
    (ω₀ : KahlerForm n D.complement) :
    IsQuasiIsometricCone D β ω₀ ↔
      ∀ p : X, p ∈ D.carrier →
        ∃ (χ : DivisorChart n X D.carrier p) (C : ℝ), 1 ≤ C ∧
          ∀ (z : E n) (hz : z ∈ χ.coord.target) (haway : z 0 ≠ 0) (v : E n),
            C⁻¹ * modelConeQuadratic (singleConeWeights β) z v ≤
                metricQuadraticInAdaptedChart D ω₀ χ z hz haway v ∧
              metricQuadraticInAdaptedChart D ω₀ χ z hz haway v ≤
                C * modelConeQuadratic (singleConeWeights β) z v :=
  Iff.rfl

section Basic

variable {D : SmoothDivisor n X} {β : ConeAngle} {ω₀ : KahlerForm n D.complement} {p : X}
  {χ : DivisorChart n X D.carrier p} {C : ℝ}

/-- The adapted quadratic form only depends on the coordinate map, so it is unchanged by shrinking
the chart. -/
theorem metricQuadraticInAdaptedChart_restrOpen (s : Set X) (hs : IsOpen s) (hp : p ∈ s)
    {z : E n} (hz : z ∈ (χ.restrOpen s hs hp).coord.target) (haway : z 0 ≠ 0) (v : E n) :
    metricQuadraticInAdaptedChart D ω₀ (χ.restrOpen s hs hp) z hz haway v =
      metricQuadraticInAdaptedChart D ω₀ χ z (χ.restrOpen_target_subset s hs hp hz) haway v :=
  rfl

/-- **Shrinking.** A comparison in `χ` persists, with the same constant, on any smaller chart. -/
theorem ConeComparableIn.restrOpen (h : ConeComparableIn D β ω₀ χ C) (s : Set X) (hs : IsOpen s)
    (hp : p ∈ s) : ConeComparableIn D β ω₀ (χ.restrOpen s hs hp) C := fun z hz haway v => by
  rw [metricQuadraticInAdaptedChart_restrOpen]
  exact h z _ haway v

/-- **Enlarging the constant.** -/
theorem ConeComparableIn.mono (h : ConeComparableIn D β ω₀ χ C) (hC : 0 < C) {C' : ℝ}
    (hCC' : C ≤ C') : ConeComparableIn D β ω₀ χ C' := fun z hz haway v => by
  obtain ⟨h1, h2⟩ := h z hz haway v
  have hq := modelConeQuadratic_nonneg (singleConeWeights β) z v
  have hinv : C'⁻¹ ≤ C⁻¹ := inv_anti₀ hC hCC'
  exact ⟨le_trans (mul_le_mul_of_nonneg_right hinv hq) h1,
    le_trans h2 (mul_le_mul_of_nonneg_right hCC' hq)⟩

/-- **Localization.** If `ω₀` has quasi-isometric cone angle `2πβ` along `D`, the comparison
charts at `p` can be chosen inside any prescribed open neighbourhood of `p`. -/
theorem IsQuasiIsometricCone.exists_chart_subset (h : IsQuasiIsometricCone D β ω₀)
    (hp : p ∈ D.carrier) (s : Set X) (hs : IsOpen s) (hps : p ∈ s) :
    ∃ (χ : DivisorChart n X D.carrier p) (C : ℝ), 1 ≤ C ∧ χ.coord.source ⊆ s ∧
      ConeComparableIn D β ω₀ χ C := by
  obtain ⟨χ, C, hC, hcomp⟩ := h p hp
  exact ⟨χ.restrOpen s hs hps, C, hC, by rw [χ.restrOpen_source]; exact inter_subset_right,
    hcomp.restrOpen s hs hps⟩

/-- The comparison stated with the Riemannian quadratic forms `ω(v, Jv) = 2 q`: the factor `2`
cancels. -/
theorem coneComparableIn_iff_riemannian :
    ConeComparableIn D β ω₀ χ C ↔
      ∀ (z : E n) (hz : z ∈ χ.coord.target) (haway : z 0 ≠ 0) (v : E n),
        C⁻¹ * (2 * modelConeQuadratic (singleConeWeights β) z v) ≤
            formInAdaptedChart D ω₀ χ z hz haway ![v, Complex.I • v] ∧
          formInAdaptedChart D ω₀ χ z hz haway ![v, Complex.I • v] ≤
            C * (2 * modelConeQuadratic (singleConeWeights β) z v) := by
  unfold ConeComparableIn metricQuadraticInAdaptedChart
  refine forall_congr' fun z => forall_congr' fun hz => forall_congr' fun haway =>
    forall_congr' fun v => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

end Basic

/-! ### The model satisfies the cone condition -/

section Model

/-- The standard cone form `ω_β`, as a Kähler form on the complement of the coordinate
hyperplane `D = {z_0 = 0} ⊆ ℂⁿ`. -/
noncomputable def modelOnHyperplane (β : ConeAngle) :
    KahlerForm n (coordHyperplane n).complement :=
  modelConeFormOn (singleConeWeights β) (coordHyperplane n).complement
    (coordHyperplane_complement_subset n β)

/-- In the identity chart the model is comparable to itself with `C = 1`. -/
theorem modelOnHyperplane_coneComparableIn (β : ConeAngle) (p : E n) :
    ConeComparableIn (coordHyperplane n) β (modelOnHyperplane β) (coordHyperplaneChart n p) 1 :=
  fun z hz haway v => by
    rw [modelOnHyperplane, metricQuadraticInAdaptedChart_model]
    simp

/-- **The standard cone form has cone angle `2πβ` along the coordinate hyperplane**, for every
`β > 0`. -/
theorem modelOnHyperplane_isConeAlong (β : ConeAngle) :
    IsConeAlong (coordHyperplane n) β (modelOnHyperplane β) := fun p _ =>
  ⟨coordHyperplaneChart n p, 1, le_rfl, modelOnHyperplane_coneComparableIn β p⟩

end Model

end ConicalKahler
