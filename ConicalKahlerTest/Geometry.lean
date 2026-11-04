module

public import ConicalKahler

/-!
# Tests for the metric geometry of the model cone

* The transverse metric of `ω_β` in polar coordinates is `dρ² + ρ² dφ²` with `ρ = r^β`,
  `φ = βθ` (Hermitian normalisation) and with `ρ = √2 r^β` for the Riemannian metric of the
  upstream Kähler form.
* `β = 1/2` (angle `π`) and `β = 2` (angle `4π`): circumference / radius `= 2πβ`.
* `β = 1`: the radial change is the identity, the holonomy is trivial.
* The quasi-isometric condition is strictly weaker: a conical metric that is not Ricci-flat.
-/

namespace ConicalKahler.Test

open ConicalKahler
open scoped Real

/-- The Hermitian transverse metric, explicitly: `β² r^(2β-2) (dr² + r² dθ²)`. -/
example (β : ConeAngle) {x : ℝ × ℝ} (hx : 0 < x.1) (u : ℝ × ℝ) :
    transverseConeMetric β (polarMap x) (fderiv ℝ polarMap x u) =
      β.beta ^ 2 * x.1 ^ (2 * β.beta - 2) * (u.1 ^ 2 + x.1 ^ 2 * u.2 ^ 2) := by
  rw [transverseConeMetric_polar β hx, flatConeMetric_coneRadialChange hx]
  ring

/-- The Riemannian metric `ω_β(v, Jv)` on the slice through the origin of `ℂ²`. -/
example (β : ConeAngle) {x : ℝ × ℝ} (hx : 0 < x.1) (u : ℝ × ℝ) :
    standardConeForm (n := 2) β ⟨transverseSlice 0 (polarMap x),
        transverseSlice_mem_modelDomain β 0 hx⟩
        ![fderiv ℝ (transverseSlice 0 ∘ polarMap) x u,
          Complex.I • fderiv ℝ (transverseSlice 0 ∘ polarMap) x u] =
      2 * β.beta ^ 2 * x.1 ^ (2 * β.beta - 2) * (u.1 ^ 2 + x.1 ^ 2 * u.2 ^ 2) := by
  rw [standardConeForm_polar_riemannian β 0 hx, flatConeMetric_coneRadialChange hx,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Angle `π` (`β = 1/2`): the circle `|z| = 1` has length `π` and radius `1`. -/
example : coneCircleLength ⟨1 / 2, by norm_num⟩ 1 = π := by
  rw [coneCircleLength_eq _ one_pos]
  simp only [Real.one_rpow, mul_one]
  ring

/-- Angle `4π` (`β = 2`): the circle `|z| = r` has length `4π r²`. -/
example {r : ℝ} (hr : 0 < r) : coneCircleLength ⟨2, by norm_num⟩ r = 4 * π * r ^ (2 : ℝ) := by
  rw [coneCircleLength_eq _ hr]
  ring

/-- For `β = 1` the radial change of variables is the identity on polar coordinates. -/
example (x : ℝ × ℝ) : coneRadialChange 1 1 x = x := by
  simp [coneRadialChange]

/-- Integer angles have trivial holonomy; `β = 1/2` does not. -/
example : Complex.exp ((2 * π * (3 : ℝ) : ℝ) * Complex.I) = 1 :=
  (exp_two_pi_mul_I_eq_one_iff 3).mpr ⟨3, by norm_num⟩

example : Complex.exp ((2 * π * (1 / 2 : ℝ) : ℝ) * Complex.I) ≠ 1 := by
  rw [Ne, exp_two_pi_mul_I_eq_one_iff]
  rintro ⟨m, hm⟩
  have h1 : (0 : ℝ) < m := by rw [← hm]; norm_num
  have h2 : (m : ℝ) < 1 := by rw [← hm]; norm_num
  have h1' : (0 : ℤ) < m := by exact_mod_cast h1
  have h2' : m < (1 : ℤ) := by exact_mod_cast h2
  omega

/-- `IsConeAlong` does not imply Ricci-flatness, for any angle, in `ℂ²`. -/
example (β : ConeAngle) :
    ∃ ω₀ : KahlerForm 2 (coordHyperplane 2).complement,
      IsConeAlong (coordHyperplane 2) β ω₀ ∧ ¬ ω₀.IsRicciFlat :=
  exists_isConeAlong_not_ricciFlat β

/-- The model itself is Ricci-flat. -/
example (β : ConeAngle) : (modelOnHyperplane (n := 2) β).IsRicciFlat :=
  modelConeFormOn_ricciFlat _ _ _

end ConicalKahler.Test
