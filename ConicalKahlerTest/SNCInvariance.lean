module

public import ConicalKahler

/-!
# Tests for chart invariance of the SNC cone condition

Two crossing components with **different** cone angles:

* the axes `{z₀ = 0}` (label `0`, angle `π`, `β₀ = 1/2`) and `{z₁ = 0}` (label `1`, angle `2π/3`,
  `β₁ = 1/3`) in `ℂ²`;
* the same two components inside `ℂ³`, with a smooth third direction.

The alternative SNC charts **permute the active components**: the swapped chart lists the
component labelled `1` first. In `ℂ³` the chart also shears both singular directions into the
smooth one, `(z₀, z₁, z₂) ↦ (z₁, z₀, z₂ + z₀ + z₁)`. Chart invariance
(`IsQuasiIsometricSNCCone.forall_chart_of_le_one`) shows that the SNC model, which is comparable to
itself in the identity chart, is comparable to its local model in these charts after shrinking.
The local weights follow the labels, not the slots.
-/

namespace ConicalKahler.Test

open ConicalKahler
open scoped Manifold

/-! ### Two crossing lines in `ℂ²` -/

/-- The axes `{z₀ = 0}` and `{z₁ = 0}` of `ℂ²`, labelled `0` and `1`. -/
noncomputable abbrev crossingAxes : SNCDivisor 2 (E 2) (Fin 2) := coordSNC 2 2 le_rfl

/-- Cone angles `π` along the axis labelled `0` and `2π/3` along the axis labelled `1`. -/
noncomputable def crossingAngles : Fin 2 → ConeAngle :=
  ![⟨1 / 2, by norm_num⟩, ⟨1 / 3, by norm_num⟩]

theorem crossingAngles_le_one : ∀ i, (crossingAngles i).beta ≤ 1 := by
  intro i
  fin_cases i <;> norm_num [crossingAngles]

/-- The two angles are different. -/
example : (crossingAngles 0).beta ≠ (crossingAngles 1).beta := by
  norm_num [crossingAngles]

/-- The SNC chart with the two coordinates exchanged: slot `0` is the axis labelled `1`. -/
noncomputable def swapAxesChart (p : E 2) : SNCChart 2 (E 2) (Fin 2) crossingAxes.components p where
  k := 2
  le_dim := le_rfl
  active := (Equiv.swap (0 : Fin 2) 1).toEmbedding
  coord := ((HolChart.refl 2).transCLE (swapCoord 0 1)).coord
  center_mem := Set.mem_univ p
  holomorphic := ((HolChart.refl 2).transCLE (swapCoord 0 1)).holomorphic
  inverse_holomorphic := ((HolChart.refl 2).transCLE (swapCoord 0 1)).inverse_holomorphic
  coordinate_zero_iff x _ j := by
    change x (Fin.castLE le_rfl (Equiv.swap 0 1 j)) = 0 ↔
      swapCoord 0 1 x (Fin.castLE le_rfl j) = 0
    rw [swapCoord_apply]
    fin_cases j <;> rfl
  other_components_absent _ _ i hi := absurd ⟨Equiv.swap 0 1 i, by simp⟩ hi

/-- In the swapped chart slot `0` carries the angle of label `1`, and slot `1` the angle of
label `0`: the local model is `diag(β₁² |ζ₀|^(2β₁-2), β₀² |ζ₁|^(2β₀-2))`. -/
example (p : E 2) :
    ((swapAxesChart p).localWeights crossingAngles).angle 0 = some (crossingAngles 1) ∧
      ((swapAxesChart p).localWeights crossingAngles).angle 1 = some (crossingAngles 0) :=
  ⟨(swapAxesChart p).localWeights_angle_slot crossingAngles ⟨0, Nat.zero_lt_two⟩,
    (swapAxesChart p).localWeights_angle_slot crossingAngles ⟨1, Nat.one_lt_two⟩⟩

/-- The crossing point lies on the support. -/
theorem zero_mem_crossingAxes_support : (0 : E 2) ∈ crossingAxes.support :=
  SNCDivisor.mem_support_of_mem (i := 0) (show (0 : E 2) (Fin.castLE le_rfl 0) = 0 from rfl)

/-- **Chart invariance with permuted components, `ℂ²`.** Near any point of the axes, the SNC
model with angles `π` and `2π/3` is comparable to its local model in the swapped chart, after
shrinking. -/
example (p : E 2) (hp : p ∈ crossingAxes.support) :
    ∃ (s : Set (E 2)) (hs : IsOpen s) (hps : p ∈ s) (C : ℝ), 1 ≤ C ∧
      SNCConeComparableIn crossingAxes crossingAngles (modelOnCoordSNC le_rfl crossingAngles)
        ((swapAxesChart p).restrOpen s hs hps) C :=
  (modelOnCoordSNC_isSNCConeAlong le_rfl crossingAngles).forall_chart_of_le_one
    crossingAngles_le_one hp (swapAxesChart p)

/-- In particular at the crossing point `0`. -/
example :
    ∃ (s : Set (E 2)) (hs : IsOpen s) (hps : (0 : E 2) ∈ s) (C : ℝ), 1 ≤ C ∧
      SNCConeComparableIn crossingAxes crossingAngles (modelOnCoordSNC le_rfl crossingAngles)
        ((swapAxesChart 0).restrOpen s hs hps) C :=
  (modelOnCoordSNC_isSNCConeAlong le_rfl crossingAngles).forall_chart_of_le_one
    crossingAngles_le_one zero_mem_crossingAxes_support (swapAxesChart 0)

/-- The same from a comparison in the identity chart with constant `1`, by the chart-level
theorem. -/
example (p : E 2) :
    ∃ (s : Set (E 2)) (hs : IsOpen s) (hps : p ∈ s) (C : ℝ), 1 ≤ C ∧
      SNCConeComparableIn crossingAxes crossingAngles (modelOnCoordSNC le_rfl crossingAngles)
        ((swapAxesChart p).restrOpen s hs hps) C :=
  (modelOnCoordSNC_sncConeComparableIn le_rfl crossingAngles p).exists_restrOpen_of_le_one
    crossingAngles_le_one le_rfl (swapAxesChart p)

/-! ### Two crossing hyperplanes in `ℂ³`, mixed into the smooth direction -/

/-- The hyperplanes `{z₀ = 0}` (label `0`) and `{z₁ = 0}` (label `1`) of `ℂ³`. -/
noncomputable abbrev crossingPlanes : SNCDivisor 3 (E 3) (Fin 2) := coordSNC 3 2 (by norm_num)

/-- `(z₀, z₁, z₂) ↦ (z₀, z₁, z₂ + z₀ + z₁)`. -/
noncomputable def shear3CLM : E 3 →L[ℂ] E 3 :=
  ContinuousLinearMap.id ℂ (E 3) +
    ((EuclideanSpace.proj (0 : Fin 3) : E 3 →L[ℂ] ℂ) + EuclideanSpace.proj (1 : Fin 3)).smulRight
      (EuclideanSpace.single 2 1)

/-- `(z₀, z₁, z₂) ↦ (z₀, z₁, z₂ - z₀ - z₁)`. -/
noncomputable def unshear3CLM : E 3 →L[ℂ] E 3 :=
  ContinuousLinearMap.id ℂ (E 3) -
    ((EuclideanSpace.proj (0 : Fin 3) : E 3 →L[ℂ] ℂ) + EuclideanSpace.proj (1 : Fin 3)).smulRight
      (EuclideanSpace.single 2 1)

theorem unshear3CLM_shear3CLM (z : E 3) : unshear3CLM (shear3CLM z) = z := by
  ext i
  fin_cases i <;> simp [shear3CLM, unshear3CLM]

theorem shear3CLM_unshear3CLM (z : E 3) : shear3CLM (unshear3CLM z) = z := by
  ext i
  fin_cases i <;> simp [shear3CLM, unshear3CLM]

/-- The shear as a continuous linear equivalence. -/
noncomputable def shear3 : E 3 ≃L[ℂ] E 3 :=
  ContinuousLinearEquiv.equivOfInverse shear3CLM unshear3CLM unshear3CLM_shear3CLM
    shear3CLM_unshear3CLM

/-- The holomorphic chart `(z₀, z₁, z₂) ↦ (z₁, z₀, z₂ + z₀ + z₁)`. -/
noncomputable def mixedHolChart : HolChart 3 (E 3) :=
  ((HolChart.refl 3).transCLE shear3).transCLE (swapCoord 0 1)

theorem mixedHolChart_apply (x : E 3) (i : Fin 3) :
    mixedHolChart.coord x i = shear3CLM x (Equiv.swap 0 1 i) := by
  change swapCoord 0 1 (shear3CLM x) i = _
  rw [swapCoord_apply]

/-- An SNC chart that exchanges the two components and shears them into the smooth direction. -/
noncomputable def mixedChart (p : E 3) : SNCChart 3 (E 3) (Fin 2) crossingPlanes.components p where
  k := 2
  le_dim := by norm_num
  active := (Equiv.swap (0 : Fin 2) 1).toEmbedding
  coord := mixedHolChart.coord
  center_mem := Set.mem_univ p
  holomorphic := mixedHolChart.holomorphic
  inverse_holomorphic := mixedHolChart.inverse_holomorphic
  coordinate_zero_iff x _ j := by
    change x (Fin.castLE (by norm_num) (Equiv.swap 0 1 j)) = 0 ↔
      mixedHolChart.coord x (Fin.castLE (by norm_num) j) = 0
    rw [mixedHolChart_apply]
    fin_cases j <;> simp [shear3CLM, Equiv.swap_apply_def]
  other_components_absent _ _ i hi := absurd ⟨Equiv.swap 0 1 i, by simp⟩ hi

/-- **Chart invariance with permuted components and mixing, `ℂ³`.** Near any point of the two
hyperplanes, the SNC model with angles `π` and `2π/3` is comparable to its local model in the mixed
chart, after shrinking. -/
example (p : E 3) (hp : p ∈ crossingPlanes.support) :
    ∃ (s : Set (E 3)) (hs : IsOpen s) (hps : p ∈ s) (C : ℝ), 1 ≤ C ∧
      SNCConeComparableIn crossingPlanes crossingAngles
        (modelOnCoordSNC (by norm_num) crossingAngles) ((mixedChart p).restrOpen s hs hps) C :=
  (modelOnCoordSNC_isSNCConeAlong (by norm_num) crossingAngles).forall_chart_of_le_one
    crossingAngles_le_one hp (mixedChart p)

/-- In the mixed chart the third coordinate is smooth, and the first two carry the angles of the
labels `1` and `0`. -/
example (p : E 3) :
    ((mixedChart p).localWeights crossingAngles).angle 0 = some (crossingAngles 1) ∧
      ((mixedChart p).localWeights crossingAngles).angle 1 = some (crossingAngles 0) ∧
      ((mixedChart p).localWeights crossingAngles).angle 2 = none :=
  ⟨(mixedChart p).localWeights_angle_slot crossingAngles ⟨0, Nat.zero_lt_two⟩,
    (mixedChart p).localWeights_angle_slot crossingAngles ⟨1, Nat.one_lt_two⟩,
    (mixedChart p).localWeights_angle_of_le crossingAngles (show (2 : ℕ) ≤ 2 from le_rfl)⟩

end ConicalKahler.Test
