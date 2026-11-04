module

public import ConicalKahler.Cone.Weights
public import CalabiYau.Geometry.Complex.Basic

/-!
# Smooth divisors via adapted holomorphic charts

A smooth divisor `D` in a complex manifold `X` of dimension `n` is described analytically: near
each point `p ∈ D` there is a biholomorphic chart `χ` of `X` (not necessarily the chart selected
by `chartAt`) with `D ∩ dom χ = {x | χ(x)_0 = 0}`. No line bundles, sheaves or currents are used.

## Main declarations

* `DivisorChart n X D p`: an adapted holomorphic chart at `p` (a biholomorphism
  `OpenPartialHomeomorph X (E n)`, holomorphic with holomorphic inverse, cutting `D` out by
  `z_0 = 0`).
* `DivisorChart.restrOpen`: shrinking an adapted chart to an open neighbourhood of `p`.
* `SmoothDivisor n X`: a closed set admitting adapted charts at each of its points.
* `SmoothDivisor.complement : TopologicalSpace.Opens X`; via Mathlib's induced open-submanifold
  atlas it is a complex manifold, so `KahlerForm n D.complement` makes sense.
* `coordHyperplane n : SmoothDivisor n (E n)`: the hyperplane `{z_0 = 0}` with the identity chart;
  `coordHyperplane_complement` identifies its complement with the model domain of
  `singleConeWeights β`.

## Notes

* "Holomorphic" is `ContMDiffOn 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞`. Over `ℂ` this is equivalent to complex
  differentiability (and to analyticity) on open sets.
* The adapted chart is *data*, carried explicitly; it need not belong to the maximal atlas
  selected by `ChartedSpace`. Compatibility with the manifold structure is exactly the two
  holomorphy fields.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Set

namespace ConicalKahler

/-- An **adapted holomorphic chart** at `p` for a set `D ⊆ X`: a biholomorphic coordinate map
`coord` defined near `p` such that `x ∈ D ↔ coord x 0 = 0` on its domain. -/
structure DivisorChart (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace (E n) X]
    [NeZero n] (D : Set X) (p : X) where
  /-- The coordinate map. -/
  coord : OpenPartialHomeomorph X (E n)
  center_mem : p ∈ coord.source
  holomorphic : ContMDiffOn 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ coord coord.source
  inverse_holomorphic : ContMDiffOn 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ coord.symm coord.target
  cutsOut : ∀ x ∈ coord.source, x ∈ D ↔ coord x 0 = 0

namespace DivisorChart

variable {n : ℕ} [NeZero n] {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X]
  {D : Set X} {p : X}

theorem coord_center_zero (χ : DivisorChart n X D p) (hp : p ∈ D) : χ.coord p 0 = 0 :=
  (χ.cutsOut p χ.center_mem).mp hp

/-- In an adapted chart, a coordinate point off `{z_0 = 0}` corresponds to a point off `D`. -/
theorem symm_notMem (χ : DivisorChart n X D p) {z : E n} (hz : z ∈ χ.coord.target)
    (haway : z 0 ≠ 0) : χ.coord.symm z ∉ D := by
  intro hD
  apply haway
  have h := (χ.cutsOut _ (χ.coord.map_target hz)).mp hD
  rwa [χ.coord.right_inv hz] at h

/-- Conversely, a chart point off `D` has `z_0 ≠ 0`. -/
theorem coord_ne_zero (χ : DivisorChart n X D p) {x : X} (hx : x ∈ χ.coord.source)
    (hD : x ∉ D) : χ.coord x 0 ≠ 0 := fun h => hD ((χ.cutsOut x hx).mpr h)

/-- Restrict an adapted chart to an open neighbourhood `s` of `p`. -/
noncomputable def restrOpen (χ : DivisorChart n X D p) (s : Set X) (hs : IsOpen s)
    (hp : p ∈ s) : DivisorChart n X D p where
  coord := χ.coord.restrOpen s hs
  center_mem := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨χ.center_mem, hp⟩
  holomorphic := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact χ.holomorphic.mono inter_subset_left
  inverse_holomorphic := by
    have hsub : (χ.coord.restrOpen s hs).target ⊆ χ.coord.target := fun _ hz => hz.1
    exact χ.inverse_holomorphic.mono hsub
  cutsOut x hx := by
    rw [OpenPartialHomeomorph.restrOpen_source] at hx
    exact χ.cutsOut x hx.1

@[simp]
theorem restrOpen_coord_apply (χ : DivisorChart n X D p) (s : Set X) (hs : IsOpen s)
    (hp : p ∈ s) (x : X) : (χ.restrOpen s hs hp).coord x = χ.coord x :=
  rfl

theorem restrOpen_source (χ : DivisorChart n X D p) (s : Set X) (hs : IsOpen s) (hp : p ∈ s) :
    (χ.restrOpen s hs hp).coord.source = χ.coord.source ∩ s :=
  rfl

theorem restrOpen_target_subset (χ : DivisorChart n X D p) (s : Set X) (hs : IsOpen s)
    (hp : p ∈ s) : (χ.restrOpen s hs hp).coord.target ⊆ χ.coord.target := fun _ hz => hz.1

end DivisorChart

/-- A **smooth divisor**: a closed subset `D` of `X` admitting an adapted holomorphic chart at
each of its points. -/
structure SmoothDivisor (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace (E n) X]
    [NeZero n] where
  /-- The underlying closed set. -/
  carrier : Set X
  isClosed : IsClosed carrier
  exists_chart : ∀ p ∈ carrier, Nonempty (DivisorChart n X carrier p)

namespace SmoothDivisor

variable {n : ℕ} [NeZero n] {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X]

/-- The complement `X \ D`, an open subset of `X`. With Mathlib's induced atlas it is a complex
manifold, and `KahlerForm n D.complement` is the type of Kähler forms on `X \ D`. -/
noncomputable def complement (D : SmoothDivisor n X) : TopologicalSpace.Opens X :=
  ⟨D.carrierᶜ, D.isClosed.isOpen_compl⟩

@[simp]
theorem mem_complement {D : SmoothDivisor n X} {x : X} : x ∈ D.complement ↔ x ∉ D.carrier :=
  Iff.rfl

/-- A chosen adapted chart at a point of the divisor. -/
noncomputable def chartAtDivisor (D : SmoothDivisor n X) {p : X} (hp : p ∈ D.carrier) :
    DivisorChart n X D.carrier p :=
  (D.exists_chart p hp).some

end SmoothDivisor

/-- The point of `D.complement` corresponding to a chart point off `{z_0 = 0}`. -/
noncomputable def DivisorChart.symmComplement {n : ℕ} [NeZero n] {X : Type*} [TopologicalSpace X]
    [ChartedSpace (E n) X] {D : SmoothDivisor n X} {p : X} (χ : DivisorChart n X D.carrier p)
    {z : E n} (hz : z ∈ χ.coord.target) (haway : z 0 ≠ 0) : D.complement :=
  ⟨χ.coord.symm z, χ.symm_notMem hz haway⟩

@[simp]
theorem DivisorChart.coe_symmComplement {n : ℕ} [NeZero n] {X : Type*} [TopologicalSpace X]
    [ChartedSpace (E n) X] {D : SmoothDivisor n X} {p : X} (χ : DivisorChart n X D.carrier p)
    {z : E n} (hz : z ∈ χ.coord.target) (haway : z 0 ≠ 0) :
    (χ.symmComplement hz haway : X) = χ.coord.symm z :=
  rfl

/-! ### The coordinate hyperplane -/

section Hyperplane

variable (n : ℕ) [NeZero n]

/-- The coordinate hyperplane `{z_0 = 0}` as a smooth divisor in `ℂⁿ`, with the identity chart
as adapted chart at every point. -/
noncomputable def coordHyperplane : SmoothDivisor n (E n) where
  carrier := {z | z 0 = 0}
  isClosed := isClosed_eq (EuclideanSpace.proj (0 : Fin n) : E n →L[ℂ] ℂ).continuous
    continuous_const
  exists_chart p _ := ⟨{
    coord := OpenPartialHomeomorph.refl (E n)
    center_mem := mem_univ p
    holomorphic := contMDiffOn_id
    inverse_holomorphic := contMDiffOn_id
    cutsOut := fun _ _ => Iff.rfl }⟩

@[simp]
theorem mem_coordHyperplane_carrier {z : E n} : z ∈ (coordHyperplane n).carrier ↔ z 0 = 0 :=
  Iff.rfl

/-- The identity chart of `ℂⁿ`, adapted to `{z_0 = 0}` at every point. -/
noncomputable def coordHyperplaneChart (p : E n) :
    DivisorChart n (E n) (coordHyperplane n).carrier p where
  coord := OpenPartialHomeomorph.refl (E n)
  center_mem := mem_univ p
  holomorphic := contMDiffOn_id
  inverse_holomorphic := contMDiffOn_id
  cutsOut _ _ := Iff.rfl

@[simp]
theorem coordHyperplaneChart_coord (p : E n) :
    (coordHyperplaneChart n p).coord = OpenPartialHomeomorph.refl (E n) :=
  rfl

/-- The complement of the coordinate hyperplane is the model domain of the single-cone weights,
for every cone angle. -/
theorem coordHyperplane_complement (β : ConeAngle) :
    (coordHyperplane n).complement = modelDomain (singleConeWeights (n := n) β) := by
  ext z
  change z ∈ (coordHyperplane n).complement ↔ z ∈ modelDomain (singleConeWeights β)
  rw [mem_modelDomain_single]
  rfl

theorem coordHyperplane_complement_subset (β : ConeAngle) :
    ((coordHyperplane n).complement : Set (E n)) ⊆ modelDomain (singleConeWeights (n := n) β) :=
  by rw [coordHyperplane_complement n β]

end Hyperplane

end ConicalKahler
