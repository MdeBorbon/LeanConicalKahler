module

public import ConicalKahler.Divisors.AdaptedChart

/-!
# Simple normal crossing divisors with labelled components

An SNC divisor in `X` is a locally finite family `components : ι → Set X` of closed sets, indexed
by **labels** `i : ι`, such that near each point `p` of the support there is a holomorphic chart
(`SNCChart`) in which the components through the chart domain are exactly some coordinate
hyperplanes `{z_{j} = 0}`, `j < k`, with pairwise distinct labels `active j`. Every other
component misses the chart domain. This is spec §4. The labels are what a cone angle
`angle : ι → ConeAngle` is attached to (`ConicalKahler.Cone.SNCComparison`).

## Main declarations

* `SNCChart n X ι components p`, `SNCChart.slot j = j` (the coordinate of the `j`-th active
  component, as an element of `Fin n`), `SNCChart.Away z` (all active coordinates nonzero),
  `SNCChart.localWeights angle : ConeWeights n` (`some (angle (active j))` in slot `j < k`,
  `none` otherwise), and `mem_modelDomain_localWeights` (the model domain of these weights is
  exactly `Away`).
* `SNCDivisor n X ι`, `SNCDivisor.support`, `SNCDivisor.complement : Opens X`.
* `SNCChart.toDivisorChart`, `SNCDivisor.component`: **each labelled component is a smooth
  divisor** (`SmoothDivisor`). The adapted chart moves the relevant coordinate to position `0`.
* `coordSNC n k hk`: the coordinate hyperplanes `{z_j = 0}`, `j < k`, labelled by `Fin k`;
  `coordSNC_complement` identifies its complement with the model domain of `coordSNCWeights`.
* `SmoothDivisor.toSNC`, `DivisorChart.toSNCChart`: a smooth divisor is an SNC divisor with one
  label. Its local weights are `singleConeWeights` (`DivisorChart.localWeights_toSNCChart`) and
  its complement is unchanged (`SmoothDivisor.toSNC_complement`).

Only simple normal crossings are covered. A divisor whose components meet non-transversally, or
a self-intersecting component, has no SNC chart at the bad points. It is not silently accepted
(spec §4).
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Set

namespace ConicalKahler

/-- An **SNC chart** at `p` for the labelled family `components`: a biholomorphic coordinate map
in which the components meeting the domain are the coordinate hyperplanes `{z_j = 0}`, `j < k`,
the `j`-th carrying the label `active j`. -/
structure SNCChart (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace (E n) X] (ι : Type*)
    (components : ι → Set X) (p : X) where
  /-- The number of active components. -/
  k : ℕ
  le_dim : k ≤ n
  /-- The labels of the active components, in coordinate order. -/
  active : Fin k ↪ ι
  /-- The coordinate map. -/
  coord : OpenPartialHomeomorph X (E n)
  center_mem : p ∈ coord.source
  holomorphic : ContMDiffOn 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ coord coord.source
  inverse_holomorphic : ContMDiffOn 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ coord.symm coord.target
  coordinate_zero_iff : ∀ x ∈ coord.source, ∀ j : Fin k,
    x ∈ components (active j) ↔ coord x (Fin.castLE le_dim j) = 0
  other_components_absent : ∀ x ∈ coord.source, ∀ i : ι, i ∉ Set.range active → x ∉ components i

namespace SNCChart

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X] {ι : Type*}
  {components : ι → Set X} {p : X} (χ : SNCChart n X ι components p)

/-- The underlying holomorphic chart. -/
def toHolChart : HolChart n X :=
  ⟨χ.coord, χ.holomorphic, χ.inverse_holomorphic⟩

@[simp]
theorem toHolChart_coord : χ.toHolChart.coord = χ.coord :=
  rfl

/-- The coordinate of the `j`-th active component. -/
abbrev slot (j : Fin χ.k) : Fin n :=
  Fin.castLE χ.le_dim j

/-- `z` lies off all the active coordinate hyperplanes. -/
def Away (z : E n) : Prop :=
  ∀ j : Fin χ.k, z (χ.slot j) ≠ 0

/-- In an SNC chart, a point lies on the support iff one of its active coordinates vanishes. -/
theorem mem_iUnion_iff {x : X} (hx : x ∈ χ.coord.source) :
    x ∈ ⋃ i, components i ↔ ∃ j : Fin χ.k, χ.coord x (χ.slot j) = 0 := by
  rw [mem_iUnion]
  constructor
  · rintro ⟨i, hxi⟩
    by_cases hi : i ∈ range χ.active
    · obtain ⟨j, rfl⟩ := hi
      exact ⟨j, (χ.coordinate_zero_iff x hx j).mp hxi⟩
    · exact absurd hxi (χ.other_components_absent x hx i hi)
  · rintro ⟨j, hj⟩
    exact ⟨χ.active j, (χ.coordinate_zero_iff x hx j).mpr hj⟩

/-- A chart point off the active hyperplanes corresponds to a point off the support. -/
theorem symm_notMem_iUnion {z : E n} (hz : z ∈ χ.coord.target) (haway : χ.Away z) :
    χ.coord.symm z ∉ ⋃ i, components i := by
  rw [χ.mem_iUnion_iff (χ.coord.map_target hz), χ.coord.right_inv hz]
  rintro ⟨j, hj⟩
  exact haway j hj

/-- Conversely, a point of the chart domain off the support has all active coordinates nonzero. -/
theorem away_coord {x : X} (hx : x ∈ χ.coord.source) (hD : x ∉ ⋃ i, components i) :
    χ.Away (χ.coord x) := fun j hj => hD ((χ.mem_iUnion_iff hx).mpr ⟨j, hj⟩)

/-- Restrict an SNC chart to an open neighbourhood `s` of `p`. -/
noncomputable def restrOpen (s : Set X) (hs : IsOpen s) (hp : p ∈ s) :
    SNCChart n X ι components p where
  k := χ.k
  le_dim := χ.le_dim
  active := χ.active
  coord := χ.coord.restrOpen s hs
  center_mem := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨χ.center_mem, hp⟩
  holomorphic := (χ.toHolChart.restrOpen s hs).holomorphic
  inverse_holomorphic := (χ.toHolChart.restrOpen s hs).inverse_holomorphic
  coordinate_zero_iff x hx := χ.coordinate_zero_iff x hx.1
  other_components_absent x hx := χ.other_components_absent x hx.1

theorem restrOpen_target_subset (s : Set X) (hs : IsOpen s) (hp : p ∈ s) :
    (χ.restrOpen s hs hp).coord.target ⊆ χ.coord.target := fun _ hz => hz.1

/-! ### Local cone weights -/

/-- The **local cone weights** of the chart for labelled angles `angle : ι → ConeAngle`: the
`j`-th active coordinate carries the angle of its label, the other coordinates are smooth. -/
def localWeights (angle : ι → ConeAngle) : ConeWeights n :=
  ⟨fun j => if h : (j : ℕ) < χ.k then some (angle (χ.active ⟨j, h⟩)) else none⟩

theorem localWeights_angle_slot (angle : ι → ConeAngle) (j : Fin χ.k) :
    (χ.localWeights angle).angle (χ.slot j) = some (angle (χ.active j)) := by
  simp [localWeights, slot, j.isLt]

theorem localWeights_angle_of_le (angle : ι → ConeAngle) {j : Fin n} (hj : χ.k ≤ j) :
    (χ.localWeights angle).angle j = none := by
  simp [localWeights, not_lt.mpr hj]

/-- The model domain of the local weights is the set of chart points off the active hyperplanes,
whatever the angles. -/
theorem mem_modelDomain_localWeights (angle : ι → ConeAngle) {z : E n} :
    z ∈ modelDomain (χ.localWeights angle) ↔ χ.Away z := by
  rw [mem_modelDomain]
  constructor
  · intro h j
    exact h (χ.slot j) _ (χ.localWeights_angle_slot angle j)
  · intro h j β hj
    by_cases hjk : (j : ℕ) < χ.k
    · exact h ⟨j, hjk⟩
    · rw [χ.localWeights_angle_of_le angle (not_lt.mp hjk)] at hj
      cases hj

/-- The local model weight of the `j`-th active coordinate is `β² |z|^(2β-2)` for the angle `β` of
its label. -/
theorem modelWeight_localWeights_slot (angle : ι → ConeAngle) (z : E n) (j : Fin χ.k) :
    modelWeight (χ.localWeights angle) z (χ.slot j) =
      (angle (χ.active j)).beta ^ 2 * ‖z (χ.slot j)‖ ^ (2 * (angle (χ.active j)).beta - 2) :=
  modelWeight_of_some (χ.localWeights_angle_slot angle j) z

theorem localWeights_restrOpen (angle : ι → ConeAngle) (s : Set X) (hs : IsOpen s) (hp : p ∈ s) :
    (χ.restrOpen s hs hp).localWeights angle = χ.localWeights angle :=
  rfl

/-! ### Each active component is a smooth divisor near `p` -/

/-- The `j`-th active component, in the chart `χ` followed by the swap of coordinates `0` and
`slot j`, is cut out by the first coordinate: an adapted chart for that component. -/
noncomputable def toDivisorChart [NeZero n] (j : Fin χ.k) :
    DivisorChart n X (components (χ.active j)) p where
  coord := (χ.toHolChart.transCLE (swapCoord 0 (χ.slot j))).coord
  center_mem := χ.center_mem
  holomorphic := (χ.toHolChart.transCLE (swapCoord 0 (χ.slot j))).holomorphic
  inverse_holomorphic := (χ.toHolChart.transCLE (swapCoord 0 (χ.slot j))).inverse_holomorphic
  cutsOut x hx := by
    rw [χ.coordinate_zero_iff x hx j, HolChart.transCLE_coord_apply, swapCoord_apply,
      Equiv.swap_apply_left]
    rfl

end SNCChart

/-- An **SNC divisor** with components labelled by `ι`: a locally finite family of closed sets,
with an SNC chart at every point of their union. -/
structure SNCDivisor (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace (E n) X]
    (ι : Type*) where
  /-- The labelled components. -/
  components : ι → Set X
  isClosed : ∀ i, IsClosed (components i)
  locallyFinite : LocallyFinite components
  exists_chart : ∀ p ∈ ⋃ i, components i, Nonempty (SNCChart n X ι components p)

namespace SNCDivisor

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X] {ι : Type*}
  (Δ : SNCDivisor n X ι)

/-- The support `⋃ᵢ Dᵢ`. -/
def support : Set X :=
  ⋃ i, Δ.components i

theorem isClosed_support : IsClosed Δ.support :=
  Δ.locallyFinite.isClosed_iUnion Δ.isClosed

/-- The complement `X \ ⋃ᵢ Dᵢ`, an open subset of `X`; `KahlerForm n Δ.complement` is the type of
Kähler forms on it. -/
def complement : TopologicalSpace.Opens X :=
  ⟨Δ.supportᶜ, Δ.isClosed_support.isOpen_compl⟩

variable {Δ}

@[simp]
theorem mem_complement {x : X} : x ∈ Δ.complement ↔ x ∉ Δ.support :=
  Iff.rfl

theorem mem_complement_iff_forall {x : X} : x ∈ Δ.complement ↔ ∀ i, x ∉ Δ.components i := by
  simp [support]

theorem mem_support_of_mem {x : X} {i : ι} (hx : x ∈ Δ.components i) : x ∈ Δ.support :=
  mem_iUnion_of_mem i hx

/-- A chosen SNC chart at a point of the support. -/
noncomputable def sncChartAt {p : X} (hp : p ∈ Δ.support) : SNCChart n X ι Δ.components p :=
  (Δ.exists_chart p hp).some

/-- In an SNC chart, every component through the centre is active. -/
theorem mem_range_active_of_mem {p : X} (χ : SNCChart n X ι Δ.components p) {i : ι}
    (hp : p ∈ Δ.components i) : i ∈ range χ.active := by
  by_contra h
  exact χ.other_components_absent p χ.center_mem i h hp

variable (Δ)

/-- **Each labelled component of an SNC divisor is a smooth divisor.** -/
noncomputable def component [NeZero n] (i : ι) : SmoothDivisor n X where
  carrier := Δ.components i
  isClosed := Δ.isClosed i
  exists_chart p hp := by
    let χ := Δ.sncChartAt (mem_support_of_mem hp)
    obtain ⟨j, hj⟩ := mem_range_active_of_mem χ hp
    exact ⟨hj ▸ χ.toDivisorChart j⟩

@[simp]
theorem component_carrier [NeZero n] (i : ι) : (Δ.component i).carrier = Δ.components i :=
  rfl

end SNCDivisor

/-- The point of `Δ.complement` corresponding to a chart point off the active hyperplanes. -/
noncomputable def SNCChart.symmComplement {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (E n) X] {ι : Type*} {Δ : SNCDivisor n X ι} {p : X}
    (χ : SNCChart n X ι Δ.components p) {z : E n} (hz : z ∈ χ.coord.target) (haway : χ.Away z) :
    Δ.complement :=
  ⟨χ.coord.symm z, χ.symm_notMem_iUnion hz haway⟩

/-! ### Coordinate hyperplanes -/

section Coordinate

variable (n k : ℕ) (hk : k ≤ n)

/-- The coordinate hyperplanes `{z_j = 0}`, `j < k`, labelled by `j : Fin k`. -/
def coordSNCComponents : Fin k → Set (E n) :=
  fun j => {z | z (Fin.castLE hk j) = 0}

/-- The identity chart is an SNC chart for the coordinate hyperplanes at every point. -/
noncomputable def coordSNCChart (p : E n) : SNCChart n (E n) (Fin k) (coordSNCComponents n k hk) p
    where
  k := k
  le_dim := hk
  active := Function.Embedding.refl _
  coord := OpenPartialHomeomorph.refl (E n)
  center_mem := mem_univ p
  holomorphic := contMDiffOn_id
  inverse_holomorphic := contMDiffOn_id
  coordinate_zero_iff _ _ _ := Iff.rfl
  other_components_absent _ _ i hi := absurd ⟨i, rfl⟩ hi

/-- **The coordinate SNC divisor** `{z_0 ⋯ z_{k-1} = 0} ⊆ ℂⁿ`, components labelled by `Fin k`. -/
noncomputable def coordSNC : SNCDivisor n (E n) (Fin k) where
  components := coordSNCComponents n k hk
  isClosed j := isClosed_eq (EuclideanSpace.proj (Fin.castLE hk j) : E n →L[ℂ] ℂ).continuous
    continuous_const
  locallyFinite := locallyFinite_of_finite _
  exists_chart p _ := ⟨coordSNCChart n k hk p⟩

variable {n k}

/-- The model weights of the coordinate SNC divisor: angle `angle j` along `{z_j = 0}`, `j < k`. -/
noncomputable def coordSNCWeights (angle : Fin k → ConeAngle) : ConeWeights n :=
  (coordSNCChart n k hk 0).localWeights angle

theorem coordSNCChart_localWeights (angle : Fin k → ConeAngle) (p : E n) :
    (coordSNCChart n k hk p).localWeights angle = coordSNCWeights hk angle :=
  rfl

theorem coordSNC_components (j : Fin k) :
    (coordSNC n k hk).components j = {z | z (Fin.castLE hk j) = 0} :=
  rfl

/-- The complement of the coordinate SNC divisor is the model domain of its weights, for all
angles. -/
theorem coordSNC_complement (angle : Fin k → ConeAngle) :
    (coordSNC n k hk).complement = modelDomain (coordSNCWeights hk angle) := by
  ext z
  change z ∈ (coordSNC n k hk).complement ↔ z ∈ modelDomain (coordSNCWeights hk angle)
  rw [coordSNCWeights, SNCChart.mem_modelDomain_localWeights, SNCDivisor.mem_complement_iff_forall]
  rfl

theorem coordSNC_complement_subset (angle : Fin k → ConeAngle) :
    ((coordSNC n k hk).complement : Set (E n)) ⊆ modelDomain (coordSNCWeights hk angle) := by
  rw [coordSNC_complement hk angle]

end Coordinate

/-! ### A smooth divisor is an SNC divisor with one label -/

section Smooth

variable {n : ℕ} [NeZero n] {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X]

/-- The unique embedding `Fin 1 ↪ Unit`. -/
def unitEmbedding : Fin 1 ↪ Unit :=
  ⟨fun _ => (), fun a b _ => Subsingleton.elim a b⟩

theorem castLE_fin_one (j : Fin 1) : Fin.castLE (NeZero.one_le : 1 ≤ n) j = 0 := by
  ext
  simp

/-- An adapted chart of a smooth divisor is an SNC chart with one active component. -/
noncomputable def DivisorChart.toSNCChart {D : Set X} {p : X} (χ : DivisorChart n X D p) :
    SNCChart n X Unit (fun _ => D) p where
  k := 1
  le_dim := NeZero.one_le
  active := unitEmbedding
  coord := χ.coord
  center_mem := χ.center_mem
  holomorphic := χ.holomorphic
  inverse_holomorphic := χ.inverse_holomorphic
  coordinate_zero_iff x hx j := by
    rw [castLE_fin_one]
    exact χ.cutsOut x hx
  other_components_absent _ _ i hi := absurd ⟨0, Subsingleton.elim _ i⟩ hi

@[simp]
theorem DivisorChart.toSNCChart_coord {D : Set X} {p : X} (χ : DivisorChart n X D p) :
    χ.toSNCChart.coord = χ.coord :=
  rfl

/-- The local weights of a chart with one active component and a constant angle are the
single-cone weights. -/
theorem localWeights_eq_singleConeWeights {ι : Type*} {components : ι → Set X} {p : X}
    (χ : SNCChart n X ι components p) (hk : χ.k = 1) (β : ConeAngle) :
    χ.localWeights (fun _ => β) = singleConeWeights β := by
  ext1
  funext j
  simp only [SNCChart.localWeights, singleConeWeights]
  by_cases hj : j = 0
  · subst hj
    simp [hk]
  · have : ¬ ((j : ℕ) < χ.k) := by
      rw [hk, Nat.lt_one_iff]
      exact fun h => hj (Fin.ext h)
    simp [this, hj]

theorem DivisorChart.localWeights_toSNCChart {D : Set X} {p : X} (χ : DivisorChart n X D p)
    (β : ConeAngle) : χ.toSNCChart.localWeights (fun _ => β) = singleConeWeights β :=
  localWeights_eq_singleConeWeights _ rfl β

/-- For one active component, `Away` is `z_0 ≠ 0`. -/
theorem away_iff_of_k_eq_one {ι : Type*} {components : ι → Set X} {p : X}
    (χ : SNCChart n X ι components p) (hk : χ.k = 1) {z : E n} : χ.Away z ↔ z 0 ≠ 0 := by
  have hslot : ∀ j : Fin χ.k, χ.slot j = 0 := fun j => by
    ext
    have := j.isLt
    simp only [SNCChart.slot, Fin.val_castLE, Fin.val_zero]
    omega
  constructor
  · intro h
    have := h ⟨0, by omega⟩
    rwa [hslot] at this
  · intro h j
    rwa [hslot]

/-- **A smooth divisor is an SNC divisor with a single label.** -/
noncomputable def SmoothDivisor.toSNC (D : SmoothDivisor n X) : SNCDivisor n X Unit where
  components _ := D.carrier
  isClosed _ := D.isClosed
  locallyFinite := locallyFinite_of_finite _
  exists_chart p hp := by
    have hp' : p ∈ D.carrier := by simpa using hp
    exact ⟨(D.exists_chart p hp').some.toSNCChart⟩

theorem SmoothDivisor.toSNC_support (D : SmoothDivisor n X) : D.toSNC.support = D.carrier :=
  Set.iUnion_const _

theorem SmoothDivisor.toSNC_complement (D : SmoothDivisor n X) :
    D.toSNC.complement = D.complement := by
  ext x
  change x ∉ D.toSNC.support ↔ x ∉ D.carrier
  rw [D.toSNC_support]

/-- In any SNC chart of `D.toSNC` centred on `D`, exactly one component is active. -/
theorem SmoothDivisor.toSNC_chart_k (D : SmoothDivisor n X) {p : X} (hp : p ∈ D.carrier)
    (χ : SNCChart n X Unit D.toSNC.components p) : χ.k = 1 := by
  have h1 : () ∈ range χ.active :=
    SNCDivisor.mem_range_active_of_mem (Δ := D.toSNC) χ (i := ()) hp
  obtain ⟨j, -⟩ := h1
  have hle : χ.k ≤ 1 := by
    simpa using Fintype.card_le_of_embedding χ.active
  have := j.isLt
  omega

/-- An SNC chart of `D.toSNC` with one active component is an adapted chart of `D`. -/
noncomputable def SNCChart.toDivisorChartOfSmooth {D : SmoothDivisor n X} {p : X}
    (χ : SNCChart n X Unit D.toSNC.components p) (hk : χ.k = 1) :
    DivisorChart n X D.carrier p where
  coord := χ.coord
  center_mem := χ.center_mem
  holomorphic := χ.holomorphic
  inverse_holomorphic := χ.inverse_holomorphic
  cutsOut x hx := by
    have h := χ.coordinate_zero_iff x hx ⟨0, by omega⟩
    have hslot : Fin.castLE χ.le_dim ⟨0, by omega⟩ = (0 : Fin n) := by
      ext
      simp
    rw [hslot] at h
    exact h

end Smooth

end ConicalKahler
