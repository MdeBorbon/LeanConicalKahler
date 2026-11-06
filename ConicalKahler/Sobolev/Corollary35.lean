module

public import ConicalKahler.Sobolev.ExplicitHarmonic

/-!
# The paper's list of harmonic functions of degree `≤ 2` and Corollary 3.5

Proposition 3.4 of the paper states that `𝓗_{≤2}` (homogeneous harmonic functions of degree
`≤ 2`) is spanned by

1. `1` and `s_i`;
2. `r_a^{1/β_a} cos θ_a` and `r_a^{1/β_a} sin θ_a` for those `a` with `β_a ≥ 1/2`;
3. `𝓗_2(ℝ^{m−2n})`, `r_a² − r_b²` and `r_a² − 2 s_i²`.

`explicitH2 β` is **the span of this list** (`h2Generators`). That it is all of `𝓗_{≤2}` is the
completeness part of Proposition 3.4, which is **not** proved here. Item 3 spans exactly the
quadratics `∑ c_a r_a² + ∑ Q_{ij} s_i s_j` with `2 ∑ c_a + tr Q = 0` (`quadFn_mem_explicitH2`).

## Results

* `explicitH2_le_classicalHarmonic`, `isWeakSolution_of_mem_explicitH2`: for `β_a ≤ 1` every
  element is classically harmonic and **weakly harmonic** on every bounded open set.
* `finiteDimensional_explicitH2`.
* **Corollary 3.5** for `explicitH2`:
  - `D2Op.apply_const_of_mem_explicitH2`: for every `D ∈ 𝒟₂` and `P ∈ explicitH2 β`, `D P` is
    constant on the regular part;
  - `corollary_3_5`: moreover `|τ| ≤ C ‖P‖_{L²(B_1)}` with `C` depending only on `D` (and `β`),
    where `B_1` is the unit ball centred at the vertex (eq. (3.3)). The paper's `dV_g` is a constant
    multiple of Lebesgue measure, which only changes `C`.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace ConicalKahler.Sobolev

open RealConeModel

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-! ### The paper's spanning list -/

/-- **The paper's spanning list of `𝓗_{≤2}`** (Prop. 3.4): `1`, `s_i`, `r_a^{1/β_a} cos θ_a`,
`r_a^{1/β_a} sin θ_a` for `β_a ≥ 1/2`, and the quadratics `∑ c_a r_a² + ∑ Q_{ij} s_i s_j` with
`2 ∑ c_a + tr Q = 0`, which span `𝓗_2(ℝ^{m−2n})`, `r_a² − r_b²` and `r_a² − 2 s_i²`. -/
def h2Generators (β : κ → ConeAngle) : Set (RealConeModel κ ι → ℝ) :=
  {fun _ => 1} ∪ range (fun i (y : RealConeModel κ ι) => y.eucl i) ∪
    {P | ∃ a, 1 / 2 ≤ (β a).beta ∧
      (P = harmCosFn (β a).beta 1 a ∨ P = harmSinFn (β a).beta 1 a)} ∪
    {P | ∃ (cc : κ → ℝ) (Q : ι → ι → ℝ), 2 * ∑ a, cc a + ∑ i, Q i i = 0 ∧ P = quadFn cc Q}

/-- **The span of the paper's list of harmonic functions of degree `≤ 2`.** -/
def explicitH2 (β : κ → ConeAngle) : Submodule ℝ (RealConeModel κ ι → ℝ) :=
  Submodule.span ℝ (h2Generators β)

variable {β : κ → ConeAngle}

theorem one_mem_explicitH2 : (fun _ => 1 : RealConeModel κ ι → ℝ) ∈ explicitH2 β :=
  Submodule.subset_span (Or.inl (Or.inl (Or.inl rfl)))

theorem eucl_mem_explicitH2 (i : ι) : (fun y : RealConeModel κ ι => y.eucl i) ∈ explicitH2 β :=
  Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))

theorem harmCos_mem_explicitH2 {a : κ} (ha : 1 / 2 ≤ (β a).beta) :
    harmCosFn (ι := ι) (β a).beta 1 a ∈ explicitH2 β :=
  Submodule.subset_span (Or.inl (Or.inr ⟨a, ha, Or.inl rfl⟩))

theorem harmSin_mem_explicitH2 {a : κ} (ha : 1 / 2 ≤ (β a).beta) :
    harmSinFn (ι := ι) (β a).beta 1 a ∈ explicitH2 β :=
  Submodule.subset_span (Or.inl (Or.inr ⟨a, ha, Or.inr rfl⟩))

theorem quadFn_mem_explicitH2 {cc : κ → ℝ} {Q : ι → ι → ℝ} (h : 2 * ∑ a, cc a + ∑ i, Q i i = 0) :
    quadFn cc Q ∈ explicitH2 β :=
  Submodule.subset_span (Or.inr ⟨cc, Q, h, rfl⟩)

/-- `r_a² − r_b²`. -/
theorem rsq_sub_rsq_mem_explicitH2 (a b : κ) :
    (fun y : RealConeModel κ ι => ‖y.cone a‖ ^ 2 - ‖y.cone b‖ ^ 2) ∈ explicitH2 β := by
  have h := quadFn_mem_explicitH2 (β := β) (cc := Pi.single a 1 - Pi.single b 1)
    (Q := fun _ _ : ι => 0) (by simp)
  convert h using 1
  funext y
  simp [quadFn, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]

/-- `r_a² − 2 s_i²`. -/
theorem rsq_sub_two_ssq_mem_explicitH2 (a : κ) (i : ι) :
    (fun y : RealConeModel κ ι => ‖y.cone a‖ ^ 2 - 2 * y.eucl i ^ 2) ∈ explicitH2 β := by
  have h := quadFn_mem_explicitH2 (β := β) (cc := Pi.single a 1)
    (Q := fun i' j' => if i' = i ∧ j' = i then -2 else 0) (by simp)
  convert h using 1
  funext y
  simp only [quadFn, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_eq_single i (fun i' _ hi' => Finset.sum_eq_zero fun j' _ => by simp [hi'])
    (by simp), Finset.sum_eq_single i (fun j' _ hj' => by simp [hj']) (by simp)]
  simp only [and_self, ↓reduceIte]
  ring

/-- `𝓗_2(ℝ^{m−2n})`: the harmonic quadratic forms `∑ Q_{ij} s_i s_j`, `tr Q = 0`. -/
theorem quadS_mem_explicitH2 {Q : ι → ι → ℝ} (hQ : ∑ i, Q i i = 0) :
    (fun y : RealConeModel κ ι => ∑ i, ∑ j, Q i j * (y.eucl i * y.eucl j)) ∈ explicitH2 β := by
  have h := quadFn_mem_explicitH2 (β := β) (cc := 0) (Q := Q) (by simp [hQ])
  convert h using 1
  funext y
  simp [quadFn]

/-! ### Weak harmonicity -/

theorem h2Generators_subset_classicalHarmonic (hβ : ∀ a, (β a).beta ≤ 1) :
    h2Generators (ι := ι) β ⊆ (classicalHarmonic (ι := ι) β : Set (RealConeModel κ ι → ℝ)) := by
  rintro P (((rfl | ⟨i, rfl⟩) | ⟨a, -, rfl | rfl⟩) | ⟨cc, Q, h, rfl⟩)
  · exact isClassicalHarmonic_const β 1
  · exact isClassicalHarmonic_eucl β i
  · exact isClassicalHarmonic_harmCos β (k := 1) (by exact_mod_cast hβ a)
  · exact isClassicalHarmonic_harmSin β (k := 1) (by exact_mod_cast hβ a)
  · exact isClassicalHarmonic_quadFn β h

/-- Every element of the span of the paper's list is classically harmonic (`β_a ≤ 1`). -/
theorem explicitH2_le_classicalHarmonic (hβ : ∀ a, (β a).beta ≤ 1) :
    explicitH2 (ι := ι) β ≤ classicalHarmonic β :=
  Submodule.span_le.mpr (h2Generators_subset_classicalHarmonic hβ)

/-- **Every element of the span of the paper's list is weakly harmonic** on every bounded open
`Ω ⊆ ℝ^d` (in the real coordinates numbered by `e`), for `β_a ≤ 1`. -/
theorem isWeakSolution_of_mem_explicitH2 {d : ℕ} [NeZero d] (hβ : ∀ a, (β a).beta ≤ 1)
    {P : RealConeModel κ ι → ℝ} (hP : P ∈ explicitH2 β) (e : RealConeIndex κ ι ≃ Fin d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∃ (hu : MemLp (fun x => P ((coordIso e).symm x)) 2 (volume.restrict Ω))
      (hg : MemLp (gradient fun x => P ((coordIso e).symm x)) 2 (volume.restrict Ω)),
      (coneCoeff β e).IsWeakSolution 0 (classicalPair hu hg) :=
  have hP' : IsClassicalHarmonic β P := explicitH2_le_classicalHarmonic hβ hP
  ⟨hP'.memLp e hΩ hb, hP'.memLp_gradient e hΩ hb, hP'.isWeakSolution e hΩ hb⟩

/-! ### Finite dimensionality -/

/-- A finite set of functions whose span contains the paper's list. -/
def h2Monomials (β : κ → ConeAngle) : Set (RealConeModel κ ι → ℝ) :=
  {fun _ => 1} ∪ range (fun i (y : RealConeModel κ ι) => y.eucl i) ∪
    range (fun a => harmCosFn (ι := ι) (β a).beta 1 a) ∪
    range (fun a => harmSinFn (ι := ι) (β a).beta 1 a) ∪
    range (fun a (y : RealConeModel κ ι) => ‖y.cone a‖ ^ 2) ∪
    range (fun p : ι × ι => fun y : RealConeModel κ ι => y.eucl p.1 * y.eucl p.2)

theorem finite_h2Monomials : (h2Monomials (ι := ι) β).Finite :=
  ((((((finite_singleton _).union (finite_range _)).union (finite_range _)).union
    (finite_range _)).union (finite_range _)).union (finite_range _))

theorem quadFn_mem_span_h2Monomials (cc : κ → ℝ) (Q : ι → ι → ℝ) :
    quadFn cc Q ∈ Submodule.span ℝ (h2Monomials (ι := ι) β) := by
  have hm : ∀ a, (fun y : RealConeModel κ ι => ‖y.cone a‖ ^ 2) ∈
      Submodule.span ℝ (h2Monomials (ι := ι) β) := fun a =>
    Submodule.subset_span (Or.inl (Or.inr ⟨a, rfl⟩))
  have hn : ∀ i j, (fun y : RealConeModel κ ι => y.eucl i * y.eucl j) ∈
      Submodule.span ℝ (h2Monomials (ι := ι) β) := fun i j =>
    Submodule.subset_span (Or.inr ⟨(i, j), rfl⟩)
  have h : quadFn cc Q = ∑ a, cc a • (fun y : RealConeModel κ ι => ‖y.cone a‖ ^ 2) +
      ∑ i, ∑ j, Q i j • (fun y : RealConeModel κ ι => y.eucl i * y.eucl j) := by
    funext y
    simp [quadFn, Finset.sum_apply]
  rw [h]
  exact Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hm a))
    (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hn i j))

theorem explicitH2_le_span_h2Monomials :
    explicitH2 (ι := ι) β ≤ Submodule.span ℝ (h2Monomials β) := by
  refine Submodule.span_le.mpr ?_
  rintro P (((rfl | ⟨i, rfl⟩) | ⟨a, -, rfl | rfl⟩) | ⟨cc, Q, -, rfl⟩)
  · exact Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl rfl)))))
  · exact Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))))
  · exact Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩))))
  · exact Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩)))
  · exact quadFn_mem_span_h2Monomials cc Q

instance finiteDimensional_explicitH2 : FiniteDimensional ℝ (explicitH2 (ι := ι) β) :=
  haveI := FiniteDimensional.span_of_finite ℝ (finite_h2Monomials (ι := ι) (β := β))
  Submodule.finiteDimensional_of_le explicitH2_le_span_h2Monomials

/-! ### Corollary 3.5: `D P` is constant -/

/-- Polar functions that are `C²` on the regular part and on which every operator of `𝒟₂` is
constant there. -/
def d2ConstSpace (β : κ → ConeAngle) : Submodule ℝ (PolarPoint κ ι → ℝ) where
  carrier := {U | ContDiffOn ℝ 2 U (regularPolar κ ι) ∧
    ∀ D : D2Op β ι, ∃ τ, ∀ c ∈ regularPolar κ ι, D.apply U c = τ}
  zero_mem' := ⟨contDiffOn_const, fun D => ⟨0, fun c _ => D.apply_zero c⟩⟩
  add_mem' := by
    rintro U V ⟨hU, hU'⟩ ⟨hV, hV'⟩
    refine ⟨hU.add hV, fun D => ?_⟩
    obtain ⟨τ₁, h₁⟩ := hU' D
    obtain ⟨τ₂, h₂⟩ := hV' D
    refine ⟨τ₁ + τ₂, fun c hc => ?_⟩
    have hn := isOpen_regularPolar.mem_nhds hc
    rw [D2Op.apply_add (hU.contDiffAt hn) (hV.contDiffAt hn), h₁ c hc, h₂ c hc]
  smul_mem' := by
    rintro r U ⟨hU, hU'⟩
    refine ⟨hU.const_smul r, fun D => ?_⟩
    obtain ⟨τ, h⟩ := hU' D
    refine ⟨r * τ, fun c hc => ?_⟩
    rw [D2Op.apply_const_smul (hU.contDiffAt (isOpen_regularPolar.mem_nhds hc)), h c hc]

theorem rsq_mem_d2ConstSpace (b : κ) :
    (fun c : PolarPoint κ ι => c (.r b) ^ 2) ∈ d2ConstSpace β := by
  refine ⟨((contDiff_apply ℝ ℝ _).pow 2).contDiffOn, fun D => ?_⟩
  cases D
  case lap a =>
    refine ⟨if b = a then 4 else 0, fun c hc => ?_⟩
    simp only [D2Op.apply, coneLaplacian, pd_pd_coord_sq]
    simp only [pd_coord_sq]
    by_cases h : b = a
    · subst h
      have := (hc b).ne'
      simp only [and_self, ↓reduceIte, reduceCtorEq, mul_zero, add_zero]
      field_simp
      norm_num
    · simp [h]
  case rrPure a _ =>
    exact ⟨if b = a then 2 else 0, fun c _ => by
      simp only [D2Op.apply, pd_pd_coord_sq, ConeVar.r.injEq, and_self]⟩
  case rr a a' hab =>
    refine ⟨0, fun c _ => ?_⟩
    simp only [D2Op.apply, pd_pd_coord_sq, ConeVar.r.injEq]
    split_ifs with h
    · exact absurd (h.2.symm.trans h.1) hab
    · rfl
  all_goals exact ⟨0, fun c _ => by simp [D2Op.apply, pd_pd_coord_sq]⟩

theorem smul_mem_d2ConstSpace (i j : ι) :
    (fun c : PolarPoint κ ι => c (.s i) * c (.s j)) ∈ d2ConstSpace β := by
  refine ⟨((contDiff_apply ℝ ℝ _).mul (contDiff_apply ℝ ℝ _)).contDiffOn, fun D => ?_⟩
  cases D
  case ss i' j' => exact ⟨_, fun c _ => pd_pd_coord_mul _ _ _ _ c⟩
  case lap a =>
    refine ⟨0, fun c _ => ?_⟩
    simp only [D2Op.apply, coneLaplacian, pd_pd_coord_mul]
    simp [pd_coord_mul]
  all_goals exact ⟨0, fun c _ => by simp [D2Op.apply, pd_pd_coord_mul]⟩

theorem contDiffOn_harmCosFn (b : ℝ) (k : ℕ) (a : κ) :
    ContDiffOn ℝ 2 (harmCosFn (ι := ι) b k a) (regularModel κ ι) := fun y hy =>
  ((contDiffAt_harmCosC b k (hy a)).comp y (coneProj (ι := ι) a).contDiff.contDiffAt).contDiffWithinAt

theorem contDiffOn_harmSinFn (b : ℝ) (k : ℕ) (a : κ) :
    ContDiffOn ℝ 2 (harmSinFn (ι := ι) b k a) (regularModel κ ι) := fun y hy =>
  ((contDiffAt_harmSinC b k (hy a)).comp y (coneProj (ι := ι) a).contDiff.contDiffAt).contDiffWithinAt

/-- The polar expression `P ↦ P ∘ toModel`. -/
abbrev toPolar : (RealConeModel κ ι → ℝ) →ₗ[ℝ] (PolarPoint κ ι → ℝ) :=
  LinearMap.funLeft ℝ ℝ PolarPoint.toModel

theorem h2Generators_subset_comap :
    h2Generators (ι := ι) β ⊆
      ((d2ConstSpace (ι := ι) β).comap toPolar : Set (RealConeModel κ ι → ℝ)) := by
  rintro P (((rfl | ⟨i, rfl⟩) | ⟨a, ha, rfl | rfl⟩) | ⟨cc, Q, -, rfl⟩)
  · refine ⟨contDiffOn_const, fun D => ⟨0, fun c _ => ?_⟩⟩
    change D.apply (fun _ => (1 : ℝ)) c = 0
    cases D <;> simp [D2Op.apply, coneLaplacian]
  · refine ⟨?_, fun D => ⟨0, fun c _ => ?_⟩⟩
    · simpa [LinearMap.funLeft, Function.comp_def] using
        (contDiff_apply ℝ ℝ (ConeVar.s i : ConeVar κ ι)).contDiffOn
    · simp only [LinearMap.funLeft, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_def,
        PolarPoint.eucl_toModel]
      cases D <;> simp [D2Op.apply, coneLaplacian, pd_coord]
  · refine ⟨fun c hc => (contDiffAt_comp_toModel (contDiffOn_harmCosFn _ 1 a) hc).contDiffWithinAt,
      fun D => ⟨0, fun c hc => ?_⟩⟩
    change D.apply (fun c' : PolarPoint κ ι => harmCosFn (β a).beta 1 a c'.toModel) c = 0
    rw [D.apply_congr (harmCosFn_toModel_eventuallyEq _ 1 a (hc a))]
    exact D2Op.apply_factor_eq_zero (coneHarmonicCos (β a).beta 1) a c ha
      (coneLaplacian_harmonicCos (β a).pos 1 a (hc a)) D
  · refine ⟨fun c hc => (contDiffAt_comp_toModel (contDiffOn_harmSinFn _ 1 a) hc).contDiffWithinAt,
      fun D => ⟨0, fun c hc => ?_⟩⟩
    change D.apply (fun c' : PolarPoint κ ι => harmSinFn (β a).beta 1 a c'.toModel) c = 0
    rw [D.apply_congr (harmSinFn_toModel_eventuallyEq _ 1 a (hc a))]
    exact D2Op.apply_factor_eq_zero (coneHarmonicSin (β a).beta 1) a c ha
      (coneLaplacian_harmonicSin (β a).pos 1 a (hc a)) D
  · show toPolar (quadFn cc Q) ∈ d2ConstSpace β
    have h : toPolar (quadFn cc Q) = ∑ a, cc a • (fun c : PolarPoint κ ι => c (.r a) ^ 2) +
        ∑ i, ∑ j, Q i j • (fun c : PolarPoint κ ι => c (.s i) * c (.s j)) := by
      change (fun c' : PolarPoint κ ι => quadFn cc Q c'.toModel) = _
      rw [quadFn_toModel]
      funext c
      simp [Finset.sum_apply]
    rw [h]
    exact Submodule.add_mem _
      (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (rsq_mem_d2ConstSpace a))
      (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (smul_mem_d2ConstSpace i j))

theorem explicitH2_le_comap_d2ConstSpace :
    explicitH2 (ι := ι) β ≤ (d2ConstSpace β).comap toPolar :=
  Submodule.span_le.mpr h2Generators_subset_comap

/-- **Corollary 3.5 (constancy).** For every `D ∈ 𝒟₂` and every `P` in the span of the paper's
list, `D P` is constant on the regular part. -/
theorem corollary_3_5_const {P : RealConeModel κ ι → ℝ} (hP : P ∈ explicitH2 β)
    (D : D2Op β ι) : ∃ τ, ∀ c ∈ regularPolar κ ι, D.apply (fun c' => P c'.toModel) c = τ :=
  (explicitH2_le_comap_d2ConstSpace hP).2 D

theorem contDiffOn_toPolar_of_mem_explicitH2 {P : RealConeModel κ ι → ℝ} (hP : P ∈ explicitH2 β) :
    ContDiffOn ℝ 2 (fun c : PolarPoint κ ι => P c.toModel) (regularPolar κ ι) :=
  (explicitH2_le_comap_d2ConstSpace hP).1

/-! ### Corollary 3.5: the bound `|τ| ≤ C ‖P‖_{L²(B_1)}` -/

/-- A regular point in the unit ball: `r_a = 1/(#κ + 1)`, `θ_a = 0`, `s_i = 0`. -/
def basePolar (κ ι : Type) [Fintype κ] : PolarPoint κ ι
  | .r _ => 1 / (Fintype.card κ + 1)
  | .θ _ => 0
  | .s _ => 0

theorem basePolar_mem : basePolar κ ι ∈ regularPolar κ ι := fun _ => by
  simp only [basePolar]
  positivity

theorem norm_basePolar_toModel_lt : ‖(basePolar κ ι).toModel‖ < 1 := by
  have h := norm_sq_eq (basePolar κ ι).toModel
  simp only [PolarPoint.cone_toModel, PolarPoint.eucl_toModel, norm_polarMap, basePolar,
    sq_abs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at h
  have hn : (0 : ℝ) ≤ Fintype.card κ := Nat.cast_nonneg _
  have hlt : (Fintype.card κ : ℝ) * (1 / (Fintype.card κ + 1)) ^ 2 < 1 := by
    rw [div_pow, one_pow, mul_one_div, div_lt_one (by positivity)]
    nlinarith
  exact (sq_lt_one_iff₀ (norm_nonneg _)).mp (h ▸ hlt)

theorem memLp_ball_of_mem_explicitH2 (hβ : ∀ a, (β a).beta ≤ 1) {P : RealConeModel κ ι → ℝ}
    (hP : P ∈ explicitH2 β) :
    MemLp P 2 (volume.restrict (Metric.ball (0 : RealConeModel κ ι) 1)) := by
  have hP' : IsClassicalHarmonic β P := explicitH2_le_classicalHarmonic hβ hP
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : RealConeModel κ ι) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨C, hC⟩ := hP'.bounded 1
  refine MemLp.of_bound hP'.measurable.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  rw [Real.norm_eq_abs]
  exact hC y (mem_ball_zero_iff.mp hy).le

/-- The inclusion of the span of the paper's list into `L²(B_1)`. -/
def toBallLp (hβ : ∀ a, (β a).beta ≤ 1) :
    explicitH2 (ι := ι) β →ₗ[ℝ] Lp ℝ 2 (volume.restrict (Metric.ball (0 : RealConeModel κ ι) 1))
    where
  toFun P := (memLp_ball_of_mem_explicitH2 hβ P.2).toLp P
  map_add' P Q := by
    rw [← MemLp.toLp_add]
    rfl
  map_smul' r P := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    rfl

/-- The value of `D P` at the base point. -/
def d2Functional (D : D2Op β ι) : explicitH2 (ι := ι) β →ₗ[ℝ] ℝ where
  toFun P := D.apply (fun c => (P : RealConeModel κ ι → ℝ) c.toModel) (basePolar κ ι)
  map_add' P Q := by
    have hn := isOpen_regularPolar.mem_nhds (basePolar_mem (κ := κ) (ι := ι))
    exact D2Op.apply_add ((contDiffOn_toPolar_of_mem_explicitH2 P.2).contDiffAt hn)
      ((contDiffOn_toPolar_of_mem_explicitH2 Q.2).contDiffAt hn) D
  map_smul' r P := by
    have hn := isOpen_regularPolar.mem_nhds (basePolar_mem (κ := κ) (ι := ι))
    exact D2Op.apply_const_smul ((contDiffOn_toPolar_of_mem_explicitH2 P.2).contDiffAt hn) r D

/-- **An element of the span of the paper's list that vanishes in `L²(B_1)` has `D P = 0`.** It
is continuous on the regular part, so it vanishes on `B_1` away from the singular set, and `D` is
local. -/
theorem d2Functional_eq_zero (hβ : ∀ a, (β a).beta ≤ 1) (D : D2Op β ι)
    {P : explicitH2 (ι := ι) β} (h : toBallLp hβ P = 0) : d2Functional D P = 0 := by
  have hP' : IsClassicalHarmonic β (P : RealConeModel κ ι → ℝ) :=
    explicitH2_le_classicalHarmonic hβ P.2
  set B := Metric.ball (0 : RealConeModel κ ι) 1
  have hae : (P : RealConeModel κ ι → ℝ) =ᵐ[volume.restrict B] 0 := by
    have h1 := Lp.eq_zero_iff_ae_eq_zero.mp h
    filter_upwards [h1, (memLp_ball_of_mem_explicitH2 hβ P.2).coeFn_toLp] with y hy1 hy2
    rw [← hy2]
    exact hy1
  set U := B ∩ regularModel κ ι
  have hU : IsOpen U := Metric.isOpen_ball.inter isOpen_regularModel
  have heq : EqOn (P : RealConeModel κ ι → ℝ) 0 U :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset inter_subset_left hae) hU
      (hP'.contDiffOn.continuousOn.mono inter_subset_right) continuousOn_const
  have hbase : (basePolar κ ι).toModel ∈ U :=
    ⟨mem_ball_zero_iff.mpr norm_basePolar_toModel_lt,
      toModel_mem_regularModel basePolar_mem⟩
  have hev : (fun c : PolarPoint κ ι => (P : RealConeModel κ ι → ℝ) c.toModel) =ᶠ[𝓝 (basePolar κ ι)]
      0 := by
    filter_upwards [(PolarPoint.contDiff_toModel (n := 0)).continuous.continuousAt.preimage_mem_nhds
      (hU.mem_nhds hbase)] with c hc
    exact heq hc
  change D.apply _ (basePolar κ ι) = 0
  rw [D.apply_congr hev, D.apply_zero]

/-- **Corollary 3.5** (for the span of the paper's list, `β_a ≤ 1`). For every `D ∈ 𝒟₂` there is
`C` such that for every `P ∈ explicitH2 β`, `D P` is a constant `τ` on the regular part with

  `|τ| ≤ C ‖P‖_{L²(B_1)}`,

where `B_1` is the unit ball centred at the vertex (Lebesgue measure; `dV_g` is a constant multiple
of it). The proof is the paper's: `P ↦ τ` is linear on a finite-dimensional space, and vanishes
when `‖P‖_{L²(B_1)} = 0`. -/
theorem corollary_3_5 (hβ : ∀ a, (β a).beta ≤ 1) (D : D2Op β ι) :
    ∃ C, ∀ P ∈ explicitH2 (ι := ι) β, ∃ τ : ℝ,
      (∀ c ∈ regularPolar κ ι, D.apply (fun c' => P c'.toModel) c = τ) ∧
        |τ| ≤ C * Real.sqrt (∫ y in Metric.ball (0 : RealConeModel κ ι) 1, P y ^ 2) := by
  set L := toBallLp (ι := ι) hβ
  set T := d2Functional (ι := ι) D
  have hker : LinearMap.ker L ≤ LinearMap.ker T := fun P hP =>
    d2Functional_eq_zero hβ D (LinearMap.mem_ker.mp hP)
  let q := (LinearMap.ker L).liftQ T hker
  let σ : LinearMap.range L →ₗ[ℝ] ℝ := q ∘ₗ L.quotKerEquivRange.symm.toLinearMap
  have hσ : ∀ P, σ ⟨L P, LinearMap.mem_range_self L P⟩ = T P := fun P => by
    simp only [σ, q, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have : FiniteDimensional ℝ (LinearMap.range L) := LinearMap.finiteDimensional_range L
  let σc := LinearMap.toContinuousLinearMap σ
  refine ⟨‖σc‖, fun P hP => ?_⟩
  obtain ⟨τ, hτ⟩ := corollary_3_5_const hP D
  refine ⟨τ, hτ, ?_⟩
  have hT : T ⟨P, hP⟩ = τ := hτ _ basePolar_mem
  have hnorm : ‖L ⟨P, hP⟩‖ = Real.sqrt (∫ y in Metric.ball (0 : RealConeModel κ ι) 1, P y ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    congr 1
    change ‖(memLp_ball_of_mem_explicitH2 hβ hP).toLp P‖ ^ 2 = _
    rw [norm_toLp_sq]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [← hT, ← hσ, ← hnorm]
  calc |σ ⟨L ⟨P, hP⟩, _⟩| = ‖σc ⟨L ⟨P, hP⟩, LinearMap.mem_range_self L _⟩‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖σc‖ * ‖(⟨L ⟨P, hP⟩, LinearMap.mem_range_self L _⟩ : LinearMap.range L)‖ :=
        σc.le_opNorm _
    _ = ‖σc‖ * ‖L ⟨P, hP⟩‖ := rfl

end ConicalKahler.Sobolev
