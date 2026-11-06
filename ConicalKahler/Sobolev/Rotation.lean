module

public import ConicalKahler.Sobolev.Classical
public import ConicalKahler.Sobolev.Scaling
public import ConicalKahler.Sobolev.Spectral

/-!
# Rotations of the cone factors and the symmetry of the weak formulation

Each cone factor `C(S¹_{2πβ_a})` has the rotations `θ_a ↦ θ_a + t`; in the real coordinates they
multiply `x_a + i y_a` by `e^{it}` (`coneRot a t`). They are linear isometries of `ℝ^d` that preserve
the cone metric. This file shows that the weak formulation is invariant under them, as a first step
towards the decomposition of harmonic functions into Fourier modes in the angles `θ_a`.

## Results

* For a linear isometry `L` of `ℝ^d` and `Ω' = L⁻¹(Ω)`:
  - `isoLp`, `isoPair`: `u ↦ u ∘ L` on `L²` and `(u, G) ↦ (u ∘ L, L⁻¹ (G ∘ L))` on pairs;
  - `isoPair_graph`, `isoPair_mem_W12`, `isoPair_mem_H01`: graphs of test functions, `W^{1,2}` and
    `W^{1,2}_0` are preserved, with `∇(u ∘ L) = L⁻¹ (∇u ∘ L)`;
  - `CoeffField.IsWeakSolution.isoPair`: **if `A` is `L`-equivariant (`A(Lx) L = L A(x)`), weak
    solutions of `-div(A ∇u) = f` go to weak solutions with right-hand side `f ∘ L`.**
* `coneRot a t`: the rotation of the factor `a`; `coneInvOp_coneRot`: **`g⁻¹` is equivariant**
  (`g` is rotation invariant), and `coneCoeffA_rotE` in the real coordinates `ℝ^d`.
* `cone_isWeakSolution_rot`: rotations map weak solutions of the cone Laplacian to weak solutions.
* `cone_dirichlet_rot_invariant`: **symmetry of the Dirichlet problem.** If `Ω` and `f` are
  invariant under a rotation of a cone factor, so is the solution `u ∈ W^{1,2}_0(Ω)` of
  `-div(g⁻¹∇u) = f` (energy uniqueness). Balls centred at the vertex are invariant
  (`rotE_preimage_ball`).
* `dirichletG_isoLp`, `isoLp_mem_eigenspace_dirichletG`: **the Dirichlet solution operator `G`
  commutes with the rotations**, so its eigenspaces (the Dirichlet eigenfunctions of
  Milestone 10) are invariant under the rotations of each cone factor.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set
open scoped ContDiff ENNReal ComplexConjugate

namespace ConicalKahler.Sobolev

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### Transport by a linear isometry -/

section Isometry

variable [NeZero d] (L : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
  {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}

theorem measurePreserving_restrict_preimage (hΩ : MeasurableSet Ω) (hΩ' : L ⁻¹' Ω = Ω') :
    MeasurePreserving L (volume.restrict Ω') (volume.restrict Ω) := by
  subst hΩ'
  exact L.measurePreserving.restrict_preimage hΩ

/-- `u ↦ u ∘ L` from `L²(Ω)` to `L²(L⁻¹Ω)`. -/
def isoLp (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (hΩ : MeasurableSet Ω)
    (hΩ' : L ⁻¹' Ω = Ω') : Lp E 2 (volume.restrict Ω) →ₗᵢ[ℝ] Lp E 2 (volume.restrict Ω') :=
  Lp.compMeasurePreservingₗᵢ ℝ L (measurePreserving_restrict_preimage L hΩ hΩ')

theorem isoLp_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (hΩ : MeasurableSet Ω)
    (hΩ' : L ⁻¹' Ω = Ω') (f : Lp E 2 (volume.restrict Ω)) :
    isoLp L E hΩ hΩ' f =ᵐ[volume.restrict Ω'] fun x => f (L x) :=
  Lp.coeFn_compMeasurePreserving f _

/-- The transport of pairs: `(u, G) ↦ (u ∘ L, L⁻¹ (G ∘ L))`. -/
def isoPair (hΩ : MeasurableSet Ω) (hΩ' : L ⁻¹' Ω = Ω') (v : L2Pair volume Ω) :
    L2Pair volume Ω' :=
  WithLp.toLp 2 (isoLp L ℝ hΩ hΩ' v.fst,
    (L.symm.toContinuousLinearEquiv : 𝔼 →L[ℝ] 𝔼).compLp (isoLp L 𝔼 hΩ hΩ' v.snd))

@[simp] theorem isoPair_fst (hΩ : MeasurableSet Ω) (hΩ' : L ⁻¹' Ω = Ω') (v : L2Pair volume Ω) :
    (isoPair L hΩ hΩ' v).fst = isoLp L ℝ hΩ hΩ' v.fst := rfl

theorem isoPair_snd_ae (hΩ : MeasurableSet Ω) (hΩ' : L ⁻¹' Ω = Ω') (v : L2Pair volume Ω) :
    (isoPair L hΩ hΩ' v).snd =ᵐ[volume.restrict Ω'] fun x => L.symm (v.snd (L x)) := by
  filter_upwards [(L.symm.toContinuousLinearEquiv : 𝔼 →L[ℝ] 𝔼).coeFn_compLp
    (isoLp L 𝔼 hΩ hΩ' v.snd), isoLp_ae L hΩ hΩ' v.snd] with x h1 h2
  change ((L.symm.toContinuousLinearEquiv : 𝔼 →L[ℝ] 𝔼).compLp (isoLp L 𝔼 hΩ hΩ' v.snd)) x = _
  rw [h1, h2]
  rfl

theorem continuous_isoPair (hΩ : MeasurableSet Ω) (hΩ' : L ⁻¹' Ω = Ω') :
    Continuous (isoPair L hΩ hΩ') := by
  have hfst : Continuous fun v : L2Pair volume Ω => v.fst :=
    continuous_fst.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous
  have hsnd : Continuous fun v : L2Pair volume Ω => v.snd :=
    continuous_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.continuous.comp
    (((isoLp L ℝ hΩ hΩ').continuous.comp hfst).prodMk
      (((L.symm.toContinuousLinearEquiv : 𝔼 →L[ℝ] 𝔼).compLpL 2 _).continuous.comp
        ((isoLp L 𝔼 hΩ hΩ').continuous.comp hsnd)))

/-- Change of variables `∫_{L⁻¹Ω} g(L x) dx = ∫_Ω g`. -/
theorem setIntegral_comp_iso {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hΩ : MeasurableSet Ω) (hΩ' : L ⁻¹' Ω = Ω') (g : 𝔼 → E) :
    ∫ x in Ω', g (L x) = ∫ y in Ω, g y :=
  (measurePreserving_restrict_preimage L hΩ hΩ').integral_comp
    L.toHomeomorph.measurableEmbedding g

theorem IsTestFn.comp_iso {φ : 𝔼 → ℝ} (hφ : IsTestFn Ω φ) (hΩ' : L ⁻¹' Ω = Ω') :
    IsTestFn Ω' fun x => φ (L x) := by
  refine ⟨hφ.contDiff.comp L.contDiff, hφ.hasCompactSupport.comp_homeomorph L.toHomeomorph, ?_⟩
  intro x hx
  rw [← hΩ']
  exact hφ.tsupport_subset (tsupport_comp_subset_preimage φ L.continuous hx)

theorem IsTestFn.comp_iso_symm {ψ : 𝔼 → ℝ} (hψ : IsTestFn Ω' ψ) (hΩ' : L ⁻¹' Ω = Ω') :
    IsTestFn Ω fun y => ψ (L.symm y) := by
  refine ⟨hψ.contDiff.comp L.symm.contDiff,
    hψ.hasCompactSupport.comp_homeomorph L.symm.toHomeomorph, ?_⟩
  intro y hy
  have h := hψ.tsupport_subset (tsupport_comp_subset_preimage ψ L.symm.continuous hy)
  rw [← hΩ', mem_preimage, LinearIsometryEquiv.apply_symm_apply] at h
  exact h

theorem fderiv_comp_iso_symm_apply (ψ : 𝔼 → ℝ) (x w : 𝔼) :
    fderiv ℝ (fun y => ψ (L.symm y)) (L x) (L w) = fderiv ℝ ψ x w := by
  have h := L.symm.toContinuousLinearEquiv.comp_right_fderiv (𝕜 := ℝ) (f := ψ) (x := L x)
  have h' : fderiv ℝ (fun y => ψ (L.symm y)) (L x) = (fderiv ℝ ψ (L.symm (L x))).comp
      (L.symm.toContinuousLinearEquiv : 𝔼 →L[ℝ] 𝔼) := h
  rw [h']
  simp

/-- The graph of a test function goes to the graph of `φ ∘ L`. -/
theorem isoPair_graph (hΩ : MeasurableSet Ω) (hΩ' : L ⁻¹' Ω = Ω') {φ : 𝔼 → ℝ}
    (hφ : IsTestFn Ω φ) :
    isoPair L hΩ hΩ' (graph volume Ω hφ) = graph volume Ω' (hφ.comp_iso L hΩ') := by
  have hmp := (measurePreserving_restrict_preimage L hΩ hΩ').quasiMeasurePreserving
  refine L2Pair.ext volume ?_ ?_
  · refine Lp.ext ?_
    filter_upwards [isoLp_ae L hΩ hΩ' (graph volume Ω hφ).fst,
      hmp.ae_eq_comp (hφ.memLp (μ := volume) 2 Ω).coeFn_toLp,
      ((hφ.comp_iso L hΩ').memLp (μ := volume) 2 Ω').coeFn_toLp] with x h1 h2 h3
    rw [isoPair_fst, h1, graph_fst, graph_fst, h3]
    exact h2
  · refine Lp.ext ?_
    filter_upwards [isoPair_snd_ae L hΩ hΩ' (graph volume Ω hφ),
      hmp.ae_eq_comp (hφ.memLp_gradient (μ := volume) 2 Ω).coeFn_toLp,
      ((hφ.comp_iso L hΩ').memLp_gradient (μ := volume) 2 Ω').coeFn_toLp] with x h1 h2 h3
    rw [h1, graph_snd, graph_snd, h3, gradient_comp_linearIsometryEquiv]
    simp only [Function.comp_apply] at h2
    rw [h2]

/-- **`W^{1,2}` is invariant under linear isometries:** `∇(u ∘ L) = L⁻¹ (∇u ∘ L)`. -/
theorem isoPair_mem_W12 (hΩ : MeasurableSet Ω) (hΩ' : L ⁻¹' Ω = Ω') {v : L2Pair volume Ω}
    (hv : v ∈ W12 volume Ω) : isoPair L hΩ hΩ' v ∈ W12 volume Ω' := by
  refine mem_W12_of_integral fun ψ hψ w => ?_
  have hψL := hψ.comp_iso_symm L hΩ'
  have hW := integral_fst_mul_fderiv hv hψL (L w)
  have hmp := (measurePreserving_restrict_preimage L hΩ hΩ').quasiMeasurePreserving
  have e1 : ∫ x in Ω', (isoPair L hΩ hΩ' v).fst x * fderiv ℝ ψ x w =
      ∫ y in Ω, v.fst y * fderiv ℝ (fun y => ψ (L.symm y)) y (L w) := by
    rw [← setIntegral_comp_iso L hΩ hΩ']
    refine integral_congr_ae ?_
    filter_upwards [isoLp_ae L hΩ hΩ' v.fst] with x hx
    rw [isoPair_fst, hx, fderiv_comp_iso_symm_apply]
  have e2 : ∫ x in Ω', ψ x * ⟪(isoPair L hΩ hΩ' v).snd x, w⟫_ℝ =
      ∫ y in Ω, ψ (L.symm y) * ⟪v.snd y, L w⟫_ℝ := by
    rw [← setIntegral_comp_iso L hΩ hΩ']
    refine integral_congr_ae ?_
    filter_upwards [isoPair_snd_ae L hΩ hΩ' v] with x hx
    rw [hx, LinearIsometryEquiv.symm_apply_apply, ← L.inner_map_map,
      LinearIsometryEquiv.apply_symm_apply]
  rw [e1, e2, hW]

/-- **`W^{1,2}_0` is invariant under linear isometries.** -/
theorem isoPair_mem_H01 (hΩ : MeasurableSet Ω) (hΩ' : L ⁻¹' Ω = Ω') {v : L2Pair volume Ω}
    (hv : v ∈ H01 volume Ω) : isoPair L hΩ hΩ' v ∈ H01 volume Ω' := by
  have hv' : v ∈ closure (testSubmodule volume Ω Ω : Set (L2Pair volume Ω)) := by
    rwa [H01, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hv
  have hsub : isoPair L hΩ hΩ' '' (testSubmodule volume Ω Ω : Set (L2Pair volume Ω)) ⊆
      (H01 volume Ω' : Set (L2Pair volume Ω')) := by
    rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    rw [isoPair_graph]
    exact graph_mem_H01 Ω' _
  exact closure_minimal hsub (isClosed_H01 Ω')
    (image_closure_subset_closure_image (continuous_isoPair L hΩ hΩ') ⟨v, hv', rfl⟩)

/-- **Weak solutions are transported by equivariant isometries.** If `A(L x) (L v) = L (A(x) v)`
and `-div(A ∇u) = f` weakly on `Ω`, then `-div(A ∇(u ∘ L)) = f ∘ L` weakly on `L⁻¹Ω`. -/
theorem CoeffField.IsWeakSolution.isoPair {c : CoeffField 𝔼 volume}
    (hA : ∀ x v, c.A (L x) (L v) = L (c.A x v)) (hΩ : MeasurableSet Ω) (hΩ' : L ⁻¹' Ω = Ω')
    {f : Lp ℝ 2 (volume.restrict Ω)} {v : L2Pair volume Ω} (hv : c.IsWeakSolution f v) :
    c.IsWeakSolution (isoLp L ℝ hΩ hΩ' f) (Sobolev.isoPair L hΩ hΩ' v) := by
  rw [CoeffField.isWeakSolution_iff] at hv ⊢
  refine ⟨isoPair_mem_W12 L hΩ hΩ' hv.1, fun ψ hψ => ?_⟩
  have hψL := hψ.comp_iso_symm L hΩ'
  have hE := hv.2 _ hψL
  have e1 : ∫ x in Ω', ⟪c.A x ((Sobolev.isoPair L hΩ hΩ' v).snd x), gradient ψ x⟫_ℝ =
      ∫ y in Ω, ⟪c.A y (v.snd y), gradient (fun y => ψ (L.symm y)) y⟫_ℝ := by
    rw [← setIntegral_comp_iso L hΩ hΩ']
    refine integral_congr_ae ?_
    filter_upwards [isoPair_snd_ae L hΩ hΩ' v] with x hx
    have hg : gradient (fun y => ψ (L.symm y)) (L x) = L (gradient ψ x) := by
      rw [gradient_comp_linearIsometryEquiv, LinearIsometryEquiv.symm_symm,
        LinearIsometryEquiv.symm_apply_apply]
    have hAx := hA x (L.symm (v.snd (L x)))
    rw [LinearIsometryEquiv.apply_symm_apply] at hAx
    rw [hx, hg, hAx, L.inner_map_map]
  have e2 : ∫ x in Ω', (isoLp L ℝ hΩ hΩ' f) x * ψ x = ∫ y in Ω, f y * ψ (L.symm y) := by
    rw [← setIntegral_comp_iso L hΩ hΩ']
    refine integral_congr_ae ?_
    filter_upwards [isoLp_ae L hΩ hΩ' f] with x hx
    rw [hx, LinearIsometryEquiv.symm_apply_apply]
  rw [e1, e2, hE]

end Isometry

/-! ### Rotations of a cone factor -/

section Cone

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

open RealConeModel

/-- The rotation `θ_a ↦ θ_a + t` of the cone factor `a`, as a linear map of the real model. -/
def coneRotₗ (a : κ) (t : ℝ) : RealConeModel κ ι →ₗ[ℝ] RealConeModel κ ι where
  toFun y := ofCones (fun b => if b = a then Complex.exp (t * Complex.I) * y.cone b else y.cone b)
    y.eucl
  map_add' y z := ext_cone_eucl (fun b => by by_cases h : b = a <;> simp [h, mul_add])
    fun i => by simp
  map_smul' r y := ext_cone_eucl (fun b => by
      by_cases h : b = a
      · simp only [cone_ofCones, h, ↓reduceIte, cone_smul, RingHom.id_apply]
        ring
      · simp [h]) fun i => by simp

@[simp] theorem cone_coneRotₗ (a : κ) (t : ℝ) (y : RealConeModel κ ι) (b : κ) :
    (coneRotₗ a t y).cone b =
      if b = a then Complex.exp (t * Complex.I) * y.cone b else y.cone b := by
  simp [coneRotₗ]

@[simp] theorem eucl_coneRotₗ (a : κ) (t : ℝ) (y : RealConeModel κ ι) (i : ι) :
    (coneRotₗ a t y).eucl i = y.eucl i := by
  simp [coneRotₗ]

theorem coneRotₗ_coneRotₗ (a : κ) (t s : ℝ) (y : RealConeModel κ ι) :
    coneRotₗ a t (coneRotₗ a s y) = coneRotₗ a (t + s) y := by
  refine ext_cone_eucl (fun b => ?_) fun i => by simp
  by_cases h : b = a
  · simp only [cone_coneRotₗ, h, ↓reduceIte, ← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  · simp [h]

theorem coneRotₗ_zero (a : κ) (y : RealConeModel κ ι) : coneRotₗ a 0 y = y :=
  ext_cone_eucl (fun b => by by_cases h : b = a <;> simp [h]) fun i => by simp

theorem norm_coneRotₗ (a : κ) (t : ℝ) (y : RealConeModel κ ι) : ‖coneRotₗ a t y‖ = ‖y‖ := by
  have h : ‖coneRotₗ a t y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [norm_sq_eq, norm_sq_eq]
    congr 1
    · refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : b = a
      · simp only [cone_coneRotₗ, hb, ↓reduceIte, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      · simp [hb]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **The rotation of the cone factor `a` by the angle `t`**, a linear isometry of the real model. -/
def coneRot (a : κ) (t : ℝ) : RealConeModel κ ι ≃ₗᵢ[ℝ] RealConeModel κ ι :=
  { coneRotₗ a t with
    invFun := coneRotₗ a (-t)
    left_inv := fun y => by
      change coneRotₗ a (-t) (coneRotₗ a t y) = y
      rw [coneRotₗ_coneRotₗ, neg_add_cancel, coneRotₗ_zero]
    right_inv := fun y => by
      change coneRotₗ a t (coneRotₗ a (-t) y) = y
      rw [coneRotₗ_coneRotₗ, add_neg_cancel, coneRotₗ_zero]
    norm_map' := norm_coneRotₗ a t }

theorem coneRot_apply (a : κ) (t : ℝ) (y : RealConeModel κ ι) : coneRot a t y = coneRotₗ a t y :=
  rfl

theorem coneInvFactor_rot (b : ℝ) {u : ℂ} (hu : ‖u‖ = 1) (w z : ℂ) :
    coneInvFactor b (u * w) (u * z) = u * coneInvFactor b w z := by
  have hc : conj (u * w) * (u * z) = conj w * z := by
    have h1 : conj u * u = 1 := by
      rw [Complex.conj_mul', hu]
      simp
    calc conj (u * w) * (u * z) = (conj u * u) * (conj w * z) := by rw [map_mul]; ring
      _ = conj w * z := by rw [h1, one_mul]
  have hn : Complex.normSq (u * w) = Complex.normSq w := by
    rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq u, hu]
    ring
  rw [coneInvFactor, coneInvFactor, hc, hn]
  simp only [Complex.real_smul]
  ring

@[simp] theorem cone_coneInvOp (β : κ → ConeAngle) (p v : RealConeModel κ ι) (b : κ) :
    (coneInvOp β p v).cone b = coneInvFactor (β b).beta (p.cone b) (v.cone b) := by
  simp [coneInvOp, coneInvOpₗ]

@[simp] theorem eucl_coneInvOp (β : κ → ConeAngle) (p v : RealConeModel κ ι) (i : ι) :
    (coneInvOp β p v).eucl i = v.eucl i := by
  simp [coneInvOp, coneInvOpₗ]

/-- **`g⁻¹` is invariant under the rotations of the cone factors:**
`g⁻¹_{R y}(R ξ) = R (g⁻¹_y ξ)`. -/
theorem coneInvOp_coneRot (β : κ → ConeAngle) (a : κ) (t : ℝ) (y ξ : RealConeModel κ ι) :
    coneInvOp β (coneRot a t y) (coneRot a t ξ) = coneRot a t (coneInvOp β y ξ) := by
  refine ext_cone_eucl (fun b => ?_) fun i => by simp [coneRot_apply]
  simp only [coneRot_apply, cone_coneInvOp, cone_coneRotₗ]
  by_cases h : b = a
  · simp only [h, ↓reduceIte]
    exact coneInvFactor_rot _ (Complex.norm_exp_ofReal_mul_I t) _ _
  · simp [h]

/-- The rotation of the cone factor `a` in the real coordinates `ℝ^d` numbered by `e`. -/
def rotE (e : RealConeIndex κ ι ≃ Fin d) (a : κ) (t : ℝ) : 𝔼 ≃ₗᵢ[ℝ] 𝔼 :=
  ((coordIso e).symm.trans (coneRot a t)).trans (coordIso e)

theorem rotE_apply (e : RealConeIndex κ ι ≃ Fin d) (a : κ) (t : ℝ) (x : 𝔼) :
    rotE e a t x = coordIso e (coneRot a t ((coordIso e).symm x)) := rfl

/-- **The cone coefficients are rotation equivariant** in the real coordinates. -/
theorem coneCoeffA_rotE (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (a : κ) (t : ℝ)
    (x v : 𝔼) : coneCoeffA β e (rotE e a t x) (rotE e a t v) = rotE e a t (coneCoeffA β e x v) := by
  simp only [coneCoeffA, rotE_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply, coneInvOp_coneRot]

/-- Balls centred at the vertex are rotation invariant. -/
theorem rotE_preimage_ball (e : RealConeIndex κ ι ≃ Fin d) (a : κ) (t r : ℝ) :
    rotE e a t ⁻¹' Metric.ball (0 : 𝔼) r = Metric.ball 0 r := by
  ext x
  simp only [mem_preimage, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]

variable [NeZero d]

/-- **Rotations of a cone factor map weak solutions of the cone Laplacian to weak solutions.** -/
theorem cone_isWeakSolution_rot (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (a : κ)
    (t : ℝ) {Ω Ω' : Set 𝔼} (hΩ : MeasurableSet Ω) (hΩ' : rotE e a t ⁻¹' Ω = Ω')
    {f : Lp ℝ 2 (volume.restrict Ω)} {v : L2Pair volume Ω}
    (hv : (coneCoeff β e).IsWeakSolution f v) :
    (coneCoeff β e).IsWeakSolution (isoLp (rotE e a t) ℝ hΩ hΩ' f)
      (isoPair (rotE e a t) hΩ hΩ' v) :=
  hv.isoPair (rotE e a t) (coneCoeffA_rotE β e a t) hΩ hΩ'

/-- **Symmetry of the Dirichlet problem.** If `Ω` (bounded) and `f` are invariant under the
rotation of the cone factor `a` by `t`, then so is the solution `u ∈ W^{1,2}_0(Ω)` of
`-div(g⁻¹ ∇u) = f`: `(u ∘ R, ∇(u ∘ R)) = (u, ∇u)`. -/
theorem cone_dirichlet_rot_invariant (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (a : κ)
    (t : ℝ) {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) (hΩL : rotE e a t ⁻¹' Ω = Ω) {x₀ : 𝔼} {R : ℝ}
    (hR : 0 ≤ R) (hΩb : Ω ⊆ Metric.closedBall x₀ R) {f : Lp ℝ 2 (volume.restrict Ω)}
    (hf : isoLp (rotE e a t) ℝ hΩ hΩL f = f) {v : L2Pair volume Ω}
    (hv : (coneCoeff β e).IsWeakSolution f v) (hv0 : v ∈ H01 volume Ω) :
    isoPair (rotE e a t) hΩ hΩL v = v := by
  have h1 := cone_isWeakSolution_rot β e a t hΩ hΩL hv
  rw [hf] at h1
  exact eq_of_isWeakSolution_of_sub_mem_H01 _ hR hΩb h1 hv
    (Submodule.sub_mem _ (isoPair_mem_H01 _ hΩ hΩL hv0) hv0)

/-- The same, pointwise: `u(R x) = u(x)` for almost every `x ∈ Ω`. -/
theorem cone_dirichlet_rot_invariant_ae (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d)
    (a : κ) (t : ℝ) {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) (hΩL : rotE e a t ⁻¹' Ω = Ω) {x₀ : 𝔼}
    {R : ℝ} (hR : 0 ≤ R) (hΩb : Ω ⊆ Metric.closedBall x₀ R) {f : Lp ℝ 2 (volume.restrict Ω)}
    (hf : isoLp (rotE e a t) ℝ hΩ hΩL f = f) {v : L2Pair volume Ω}
    (hv : (coneCoeff β e).IsWeakSolution f v) (hv0 : v ∈ H01 volume Ω) :
    (fun x => v.fst (rotE e a t x)) =ᵐ[volume.restrict Ω] v.fst := by
  have h := cone_dirichlet_rot_invariant β e a t hΩ hΩL hR hΩb hf hv hv0
  have h1 := congrArg (fun w : L2Pair volume Ω => w.fst) h
  simp only [isoPair_fst] at h1
  filter_upwards [isoLp_ae (rotE e a t) hΩ hΩL v.fst] with x hx
  rw [← hx, h1]

/-- **The Dirichlet solution operator commutes with the rotations** of a cone factor on a
rotation-invariant bounded domain: `G(f ∘ R) = (G f) ∘ R`. -/
theorem dirichletG_isoLp (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (a : κ) (t : ℝ)
    {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) (hΩL : rotE e a t ⁻¹' Ω = Ω) {x₀ : 𝔼} {R : ℝ}
    (hR : 0 ≤ R) (hΩb : Ω ⊆ Metric.closedBall x₀ R) (f : Lp ℝ 2 (volume.restrict Ω)) :
    (coneCoeff β e).dirichletG hR hΩb (isoLp (rotE e a t) ℝ hΩ hΩL f) =
      isoLp (rotE e a t) ℝ hΩ hΩL ((coneCoeff β e).dirichletG hR hΩb f) := by
  set u := (coneCoeff β e).solution hR hΩb f
  have h1 := cone_isWeakSolution_rot β e a t hΩ hΩL ((coneCoeff β e).solution_spec hR hΩb f)
  have h2 := (coneCoeff β e).eq_solution hR hΩb
    (w := ⟨isoPair (rotE e a t) hΩ hΩL u, isoPair_mem_H01 _ hΩ hΩL u.2⟩) h1
  rw [CoeffField.dirichletG_apply, CoeffField.dirichletG_apply, ← h2]
  rfl

/-- **The eigenspaces of `G` are invariant under the rotations of the cone factors.** -/
theorem isoLp_mem_eigenspace_dirichletG (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d)
    (a : κ) (t : ℝ) {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) (hΩL : rotE e a t ⁻¹' Ω = Ω) {x₀ : 𝔼}
    {R : ℝ} (hR : 0 ≤ R) (hΩb : Ω ⊆ Metric.closedBall x₀ R) {μ : ℝ}
    {f : Lp ℝ 2 (volume.restrict Ω)}
    (hf : f ∈ Module.End.eigenspace ((coneCoeff β e).dirichletG hR hΩb).toLinearMap μ) :
    isoLp (rotE e a t) ℝ hΩ hΩL f ∈
      Module.End.eigenspace ((coneCoeff β e).dirichletG hR hΩb).toLinearMap μ := by
  rw [Module.End.mem_eigenspace_iff] at hf ⊢
  simp only [ContinuousLinearMap.coe_coe] at hf ⊢
  rw [dirichletG_isoLp β e a t hΩ hΩL hR hΩb, hf, LinearIsometry.map_smul]

end Cone

end ConicalKahler.Sobolev
