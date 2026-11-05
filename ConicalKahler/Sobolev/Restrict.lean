module

public import ConicalKahler.Sobolev.Elliptic
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Restriction to subdomains and smooth cut-off functions

For `U ⊆ Ω` the restriction `L²(Ω) → L²(U)` is a contraction (`restrictLp`). It acts on pairs
(`L2Pair.restrict`), preserves `W^{1,2}` (`restrict_mem_W12`) and weak solutions
(`IsWeakSolution.restrict`): test functions on `U` are test functions on `Ω`, and integrals of
functions vanishing off `U` are the same over `U` and over `Ω`.

`exists_cutoff` gives smooth cut-off functions `0 ≤ η ≤ 1` on `Ω` equal to `1` on a compact
`K ⊆ Ω` (Mathlib's smooth Urysohn lemma).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set
open scoped ContDiff ENNReal

namespace ConicalKahler.Sobolev

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-! ### Restriction of `L²` functions -/

section Lp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure F} {U Ω : Set F}

theorem memLp_restrict_of_subset (hUΩ : U ⊆ Ω) (f : Lp E 2 (μ.restrict Ω)) :
    MemLp f 2 (μ.restrict U) :=
  (Lp.memLp f).mono_measure (Measure.restrict_mono hUΩ le_rfl)

/-- **Restriction** `L²(Ω) → L²(U)` for `U ⊆ Ω`, a contraction. -/
def restrictLp (hUΩ : U ⊆ Ω) : Lp E 2 (μ.restrict Ω) →L[ℝ] Lp E 2 (μ.restrict U) :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_restrict_of_subset hUΩ f).toLp f
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (ae_restrict_of_ae_restrict_of_subset hUΩ (Lp.coeFn_add f g))
      map_smul' := fun r f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _
          (ae_restrict_of_ae_restrict_of_subset hUΩ (Lp.coeFn_smul r f)) }
    1 fun f => by
      rw [one_mul]
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
        (eLpNorm_mono_measure _ (Measure.restrict_mono hUΩ le_rfl))

theorem restrictLp_ae (hUΩ : U ⊆ Ω) (f : Lp E 2 (μ.restrict Ω)) :
    restrictLp hUΩ f =ᵐ[μ.restrict U] f :=
  (memLp_restrict_of_subset hUΩ f).coeFn_toLp

theorem norm_restrictLp_le (hUΩ : U ⊆ Ω) (f : Lp E 2 (μ.restrict Ω)) :
    ‖restrictLp hUΩ f‖ ≤ ‖f‖ := by
  show ‖(memLp_restrict_of_subset hUΩ f).toLp f‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_mono_measure _ (Measure.restrict_mono hUΩ le_rfl))

/-- Integrals of functions vanishing off `U ⊆ Ω` are the same over `U` and over `Ω`. -/
theorem setIntegral_eq_of_forall_notMem_eq_zero (hUΩ : U ⊆ Ω) {g : F → ℝ}
    (hz : ∀ x ∉ U, g x = 0) : ∫ x in U, g x ∂μ = ∫ x in Ω, g x ∂μ := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hz x fun h => hx (hUΩ h)]

end Lp

theorem inner_restrictLp_toLp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure F} {U Ω : Set F} (hUΩ : U ⊆ Ω) (g : Lp E 2 (μ.restrict Ω)) {h : F → E}
    (hU : MemLp h 2 (μ.restrict U)) (hΩ : MemLp h 2 (μ.restrict Ω)) (hz : ∀ x ∉ U, h x = 0) :
    ⟪restrictLp hUΩ g, hU.toLp h⟫_ℝ = ⟪g, hΩ.toLp h⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  have e1 : ∫ x in U, ⟪restrictLp hUΩ g x, hU.toLp h x⟫_ℝ ∂μ = ∫ x in U, ⟪g x, h x⟫_ℝ ∂μ :=
    integral_congr_ae (by
      filter_upwards [restrictLp_ae hUΩ g, hU.coeFn_toLp] with x h1 h2
      rw [h1, h2])
  have e2 : ∫ x in Ω, ⟪g x, hΩ.toLp h x⟫_ℝ ∂μ = ∫ x in Ω, ⟪g x, h x⟫_ℝ ∂μ :=
    integral_congr_ae (by
      filter_upwards [hΩ.coeFn_toLp] with x h2
      rw [h2])
  rw [e1, e2]
  exact setIntegral_eq_of_forall_notMem_eq_zero hUΩ fun x hx => by simp [hz x hx]

/-! ### Restriction of pairs -/

variable {μ : Measure F} {U Ω : Set F}

/-- **Restriction of pairs** `L²(Ω) × L²(Ω; F) → L²(U) × L²(U; F)` for `U ⊆ Ω`. -/
def L2Pair.restrict (hUΩ : U ⊆ Ω) : L2Pair μ Ω →L[ℝ] L2Pair μ U :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 (μ.restrict U)) (Lp F 2 (μ.restrict U))).symm.toContinuousLinearMap ∘L
    ((restrictLp hUΩ).prodMap (restrictLp hUΩ)) ∘L
      (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 (μ.restrict Ω)) (Lp F 2 (μ.restrict Ω))).toContinuousLinearMap

@[simp] theorem L2Pair.restrict_fst (hUΩ : U ⊆ Ω) (v : L2Pair μ Ω) :
    (L2Pair.restrict hUΩ v).fst = restrictLp hUΩ v.fst := rfl

@[simp] theorem L2Pair.restrict_snd (hUΩ : U ⊆ Ω) (v : L2Pair μ Ω) :
    (L2Pair.restrict hUΩ v).snd = restrictLp hUΩ v.snd := rfl

theorem L2Pair.norm_restrict_le (hUΩ : U ⊆ Ω) (v : L2Pair μ Ω) :
    ‖L2Pair.restrict hUΩ v‖ ≤ ‖v‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2, L2Pair.restrict_fst,
    L2Pair.restrict_snd]
  gcongr
  · exact norm_restrictLp_le hUΩ _
  · exact norm_restrictLp_le hUΩ _

theorem fderiv_eq_zero_of_notMem_tsupport {φ : F → ℝ} {x : F} (hx : x ∉ tsupport φ) :
    fderiv ℝ φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_fderiv_subset ℝ h)

theorem gradient_eq_zero_of_notMem_tsupport {φ : F → ℝ} {x : F} (hx : x ∉ tsupport φ) :
    gradient φ x = 0 := by
  rw [gradient, fderiv_eq_zero_of_notMem_tsupport hx, map_zero]

variable [μ.IsAddHaarMeasure]

/-- **`W^{1,2}(Ω)` restricts to `W^{1,2}(U)`.** -/
theorem restrict_mem_W12 (hUΩ : U ⊆ Ω) {v : L2Pair μ Ω} (hv : v ∈ W12 μ Ω) :
    L2Pair.restrict hUΩ v ∈ W12 μ U := by
  intro φ hφ w
  have hφΩ := hφ.mono hUΩ
  have hout : ∀ x ∉ U, x ∉ tsupport φ := fun x hx h => hx (hφ.tsupport_subset h)
  have h := hv φ hφΩ w
  rw [L2Pair.restrict_fst, L2Pair.restrict_snd,
    inner_restrictLp_toLp hUΩ _ _ (hφΩ.memLp_fderiv_apply (μ := μ) w 2 Ω)
      fun x hx => by simp [fderiv_eq_zero_of_notMem_tsupport (hout x hx)],
    inner_restrictLp_toLp hUΩ _ _ (hφΩ.memLp_smul_vec (μ := μ) w 2 Ω)
      fun x hx => by simp [image_eq_zero_of_notMem_tsupport (hout x hx)]]
  exact h

/-- **Weak solutions restrict to weak solutions.** If `-div(A ∇u) = f` weakly on `Ω` and
`U ⊆ Ω`, then `-div(A ∇u) = f` weakly on `U`. -/
theorem CoeffField.IsWeakSolution.restrict {c : CoeffField F μ} (hUΩ : U ⊆ Ω)
    {f : Lp ℝ 2 (μ.restrict Ω)} {v : L2Pair μ Ω} (hv : c.IsWeakSolution f v) :
    c.IsWeakSolution (restrictLp hUΩ f) (L2Pair.restrict hUΩ v) := by
  rw [CoeffField.isWeakSolution_iff] at hv ⊢
  refine ⟨restrict_mem_W12 hUΩ hv.1, fun φ hφ => ?_⟩
  have hout : ∀ x ∉ U, x ∉ tsupport φ := fun x hx h => hx (hφ.tsupport_subset h)
  have h := hv.2 φ (hφ.mono hUΩ)
  have e1 : ∫ x in U, ⟪c.A x ((L2Pair.restrict hUΩ v).snd x), gradient φ x⟫_ℝ ∂μ =
      ∫ x in U, ⟪c.A x (v.snd x), gradient φ x⟫_ℝ ∂μ :=
    integral_congr_ae (by
      filter_upwards [restrictLp_ae hUΩ v.snd] with x hx
      rw [L2Pair.restrict_snd, hx])
  have e2 : ∫ x in U, restrictLp hUΩ f x * φ x ∂μ = ∫ x in U, f x * φ x ∂μ :=
    integral_congr_ae (by
      filter_upwards [restrictLp_ae hUΩ f] with x hx
      rw [hx])
  rw [e1, e2, setIntegral_eq_of_forall_notMem_eq_zero hUΩ fun x hx => by
      simp [gradient_eq_zero_of_notMem_tsupport (hout x hx)],
    setIntegral_eq_of_forall_notMem_eq_zero hUΩ fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport (hout x hx)]]
  exact h

/-! ### Smooth cut-off functions -/

omit [MeasurableSpace F] [BorelSpace F] in
/-- **Smooth cut-off functions.** For a compact `K` inside an open `Ω` there is a test function
`η` on `Ω` with `0 ≤ η ≤ 1` and `η = 1` on `K`. -/
theorem exists_cutoff {K Ω : Set F} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ η : F → ℝ, IsTestFn Ω η ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ ∀ x ∈ K, η x = 1 := by
  obtain ⟨V₁, hV₁o, hKV₁, hV₁Ω, hV₁c⟩ := exists_open_between_and_isCompact_closure hK hΩ hKΩ
  obtain ⟨V₂, hV₂o, hV₁V₂, hV₂Ω, hV₂c⟩ :=
    exists_open_between_and_isCompact_closure hV₁c hΩ hV₁Ω
  obtain ⟨η, hη, hrange, hsupp, hone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV₂o
    isClosed_closure hV₁V₂
  have hts : tsupport η = closure V₂ := by rw [tsupport, hsupp]
  refine ⟨η, ⟨hη, ?_, ?_⟩, fun x => ?_, fun x hx => (hone x).mp (subset_closure (hKV₁ hx))⟩
  · rw [HasCompactSupport, hts]
    exact hV₂c
  · rw [hts]
    exact hV₂Ω
  · have := hrange (Set.mem_range_self x)
    exact ⟨this.1, this.2⟩

end ConicalKahler.Sobolev
