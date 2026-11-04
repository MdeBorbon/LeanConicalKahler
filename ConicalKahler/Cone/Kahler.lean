module

public import ConicalKahler.Cone.Comparison
public import ConicalKahler.Cone.ModelRicci

/-!
# Conical Kähler forms and the Kähler–Einstein equation on `X \ D`

A **conical Kähler form** with cone angle `2πβ` along a smooth divisor `D` is an ordinary upstream
`KahlerForm` on the open complex manifold `X \ D` satisfying the quasi-isometric cone condition
`IsConeAlong D β`.

The Kähler–Einstein condition `ConeKahlerForm.IsKahlerEinstein g λ` is the equation
`Ric(ω) = λ ω` **on `X \ D` only**. It is not the current equation
`Ric(ω) = λ ω + 2π (1 - β) [D]` on `X`, which would require currents and a Poincaré–Lelong
formula (spec §6).

## Main declarations

* `ConeKahlerForm D β`, `ConeKahlerForm.IsKahlerEinstein`.
* `standardConeKahlerForm β`: the standard cone metric along the coordinate hyperplane of `ℂⁿ`,
  as a `ConeKahlerForm`; it is Kähler–Einstein with `λ = 0`
  (`standardConeKahlerForm_isKahlerEinstein`).
-/

@[expose] public section

open scoped Manifold ContDiff

namespace ConicalKahler

variable {n : ℕ} [NeZero n] {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X]
  [IsManifold 𝓘(ℂ, E n) ω X]

/-- A Kähler form on `X \ D` with quasi-isometric cone angle `2πβ` along `D`. -/
structure ConeKahlerForm (D : SmoothDivisor n X) (β : ConeAngle) where
  /-- The Kähler form on the complement. -/
  form : KahlerForm n D.complement
  cone_condition : IsConeAlong D β form

namespace ConeKahlerForm

variable {D : SmoothDivisor n X} {β : ConeAngle}

/-- `Ric(ω) = λ ω` on the complement `X \ D`. -/
def IsKahlerEinstein (g : ConeKahlerForm D β) (lam : ℝ) : Prop :=
  g.form.ricciForm = lam • g.form.toFormField

/-- Kähler–Einstein with `λ = 0` is Ricci-flatness on `X \ D`. -/
theorem isKahlerEinstein_zero_iff (g : ConeKahlerForm D β) :
    g.IsKahlerEinstein 0 ↔ g.form.IsRicciFlat := by
  rw [IsKahlerEinstein, zero_smul]
  rfl

/-- Two conical Kähler forms with the same underlying Kähler form are equal. -/
@[ext]
theorem ext {g h : ConeKahlerForm D β} (hgh : g.form = h.form) : g = h := by
  cases g
  cases h
  cases hgh
  rfl

/-- Transport along an equality of Kähler forms (the cone condition is a property of the form). -/
def ofEq (g : ConeKahlerForm D β) (ω₀ : KahlerForm n D.complement) (h : g.form = ω₀) :
    ConeKahlerForm D β :=
  ⟨ω₀, h ▸ g.cone_condition⟩

end ConeKahlerForm

/-- **The standard cone metric along the coordinate hyperplane of `ℂⁿ`** as a conical Kähler
form, for any cone angle `2πβ`, `β > 0`. -/
noncomputable def standardConeKahlerForm (β : ConeAngle) :
    ConeKahlerForm (coordHyperplane n) β :=
  ⟨modelOnHyperplane β, modelOnHyperplane_isConeAlong β⟩

/-- The standard cone metric is Ricci-flat, i.e. Kähler–Einstein with `λ = 0`, on the
complement of the hyperplane. -/
theorem standardConeKahlerForm_isKahlerEinstein (β : ConeAngle) :
    (standardConeKahlerForm (n := n) β).IsKahlerEinstein 0 :=
  (ConeKahlerForm.isKahlerEinstein_zero_iff _).mpr
    (modelConeFormOn_ricciFlat _ _ (coordHyperplane_complement_subset n β))

end ConicalKahler
