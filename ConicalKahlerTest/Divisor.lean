module

public import ConicalKahler

/-!
# Tests for smooth divisors, adapted charts and the cone condition

* Kähler forms on the complement of an arbitrary smooth divisor are well-typed.
* The standard cone form is a `ConeKahlerForm` and is Kähler–Einstein (`λ = 0`) off `D`.
* The shear test of spec §4.1: failure for `β > 1`, success for `β ≤ 1`.
* Chart invariance for `β ≤ 1` applied to the standard cone form and the shear chart.
* `z₀ ↦ z₀²` is not an adapted chart at `0` (it is not injective near `0`).
-/

namespace ConicalKahler.Test

open ConicalKahler
open scoped Manifold ContDiff

/-! ### Typing: Kähler forms on `X \ D` -/

example {n : ℕ} [NeZero n] {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X]
    [IsManifold 𝓘(ℂ, E n) ω X] (D : SmoothDivisor n X) : Type _ :=
  KahlerForm n D.complement

/-! ### The standard cone form as a conical Kähler form -/

example (β : ConeAngle) : (standardConeKahlerForm (n := 3) β).IsKahlerEinstein 0 :=
  standardConeKahlerForm_isKahlerEinstein β

example (β : ConeAngle) : IsConeAlong (coordHyperplane 3) β (modelOnHyperplane β) :=
  modelOnHyperplane_isConeAlong β

/-! ### The shear test -/

/-- `β = 2` (cone angle `4π`): the shear chart fails at the origin, for every neighbourhood and
every constant. -/
example (s : Set (E 2)) (hs : IsOpen s) (h0 : (0 : E 2) ∈ s) (C : ℝ) :
    ¬ ConeComparableIn (coordHyperplane 2) ⟨2, two_pos⟩ (modelOnHyperplane ⟨2, two_pos⟩)
      ((shearChart 0).restrOpen s hs h0) C :=
  not_coneComparableIn_shear (by norm_num) (by simp) s hs h0 C

/-- `β = 1/2` (cone angle `π`): the shear chart works on `{|z₀| < 1}`. -/
example (h0 : (0 : E 2) ∈ unitSlab) :
    ConeComparableIn (coordHyperplane 2) ⟨1 / 2, by norm_num⟩
      (modelOnHyperplane ⟨1 / 2, by norm_num⟩)
      ((shearChart 0).restrOpen unitSlab isOpen_unitSlab h0) (2 + 2 / (1 / 2 : ℝ) ^ 2) :=
  coneComparableIn_shear_of_le_one (by norm_num) h0

/-- For `β ≤ 1`, the general chart-invariance theorem applies to the shear chart. -/
example (β : ConeAngle) (hβ : β.beta ≤ 1) :
    ∃ (s : Set (E 2)) (hs : IsOpen s) (hps : (0 : E 2) ∈ s) (C : ℝ), 1 ≤ C ∧
      ConeComparableIn (coordHyperplane 2) β (modelOnHyperplane β)
        ((shearChart 0).restrOpen s hs hps) C :=
  (modelOnHyperplane_isConeAlong β).forall_chart_of_le_one hβ (by simp) (shearChart 0)

/-! ### `z₀ ↦ z₀²` is not an adapted chart -/

/-- `(z₀, z₁) ↦ (z₀², z₁)`. -/
noncomputable def squareMap (z : E 2) : E 2 :=
  z + (z 0 ^ 2 - z 0) • EuclideanSpace.single 0 1

/-- No adapted chart at the origin has coordinate map `(z₀, z₁) ↦ (z₀², z₁)` on its domain. -/
example (D : Set (E 2)) :
    ¬ ∃ χ : DivisorChart 2 (E 2) D 0, ∀ x ∈ χ.coord.source, χ.coord x = squareMap x := by
  rintro ⟨χ, hχ⟩
  -- `±t e₀` lie in the (open) source for small `t ≠ 0`
  have hsrc : χ.coord.source ∈ nhds (0 : E 2) := χ.coord.open_source.mem_nhds χ.center_mem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hsrc
  set t : ℂ := ((ε / 2 : ℝ) : ℂ)
  have ht : t ≠ 0 := by
    simp only [t, ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hnorm : ‖t‖ < ε := by
    simp only [t, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  set a : E 2 := t • EuclideanSpace.single 0 1
  set b : E 2 := (-t) • EuclideanSpace.single 0 1
  have ha : a ∈ χ.coord.source := hball (by simpa [a, norm_smul] using hnorm)
  have hb : b ∈ χ.coord.source := hball (by simpa [b, norm_smul] using hnorm)
  have hab : χ.coord a = χ.coord b := by
    rw [hχ a ha, hχ b hb]
    ext i
    fin_cases i <;> simp [squareMap, a, b]
  have := χ.coord.injOn ha hb hab
  have h0 := congrArg (fun z : E 2 => z 0) this
  simp only [a, b, PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul, mul_one] at h0
  exact ht (by linear_combination h0 / 2)

end ConicalKahler.Test
