module

public import ConicalKahler.Sobolev.ConePolyDense
public import ConicalKahler.Sobolev.ConeLink

/-!
# Completeness of the explicit homogeneous harmonic functions (Proposition 3.4)

**Abstract part** (any conical coefficient field, `d ≥ 2`).

* `inner_eq_zero_of_degree_ne`: if `u` is weakly harmonic on `B_1` and homogeneous of degree `D`
  with link function `φ`, then `φ ⊥ ψ` for every link eigenfunction `ψ` whose indicial root
  `δ' ≠ D`. This comes from the radial ODE of Lemma 3.3 (`rayCoeff_eq`), tested against
  `ρ^0 ψ` and `ρ^1 ψ`.
* `mem_span_of_harmonic`: let `X D` be a family of link functions of weakly harmonic functions
  homogeneous of degree `D`, whose union spans a dense subspace of `L²(S)`. Then every link
  eigenfunction, and every link function of a homogeneous harmonic function of degree `D`, lies in
  the span of `X D`. In particular `X` contains all homogeneous harmonic functions.

**The cone.** For `0 < β_a ≤ 1`, the harmonic cone polynomials
`∏_a r_a^{k_a/β_a} (cos | sin)(k_a θ_a) · h(r², s)` (`L_q h = 0`, `h` weighted homogeneous of
degree `m`, total degree `∑ k_a/β_a + m`) form such a family: they are weakly harmonic
(`isClassicalHarmonic_conePoly`) and dense (`dense_span_linkPolyLp` and the Fischer
decomposition). Hence (`cone_homogeneous_mem_span`): **every weakly harmonic `u ∈ W^{1,2}(B_1)`
homogeneous of degree `δ` is a harmonic cone polynomial of degree `δ`**. In particular the possible
degrees are exactly `∑_a k_a/β_a + m`.

**Proposition 3.4** (`prop_3_4`, `0 < β_a < 1`): such a `u` with `δ ≤ 2` is in the span of the
paper's list (`explicitH2`), and there is none with `2 < δ < 2 + μ`. The expansion of Lemma 3.3
therefore has degrees `δ_i ≤ 2` (terms in `explicitH2`) or `δ_i ≥ 2 + μ` (`cone_expansion_gap`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set Metric MvPolynomial
open scoped ContDiff ENNReal

namespace ConicalKahler.Sobolev

variable {d : ℕ} [NeZero d]

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### Orthogonality of homogeneous harmonic functions of different degrees -/

section Abstract

variable {c : CoeffField (EuclideanSpace ℝ (Fin d)) volume}

/-- **Different degrees give orthogonal link functions.** Let `u` be weakly harmonic on `B_1` and
`u = |x|^D φ(x/|x|)` a.e., `D ≥ 0`. If `(ψ, Γ)` is a link eigenfunction with `λ = δ'(δ' + d - 2)`,
`δ' ≥ 0`, `δ' ≠ D`, then `⟪φ, ψ⟫ = 0`. -/
theorem inner_eq_zero_of_degree_ne (hd : 2 ≤ d) (hc : c.IsConical)
    {u : L2Pair volume (ball (0 : 𝔼) 1)} (hu : c.IsWeakSolution 0 u) {D : ℝ} (hD : 0 ≤ D)
    {φ : Lp ℝ 2 (sphMeasure d)}
    (hφ : (u.fst : 𝔼 → ℝ) =ᵐ[volume.restrict (ball (0 : 𝔼) 1)] homFun D fun w => φ w)
    {lam δ' : ℝ} {v : LinkPair d} (hE : IsLinkEigen hc lam v) (hlam : lam = δ' * (δ' + d - 2))
    (hδ' : 0 ≤ δ') (hne : D ≠ δ') : ⟪φ, v.fst⟫_ℝ = 0 := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hP : MemLp (homP δ' v) 2 (volume.restrict (ball (0 : 𝔼) 1)) :=
    memLp_homFun_ball δ' (Lp.memLp v.fst) 1 (by linarith)
  have hG := memLp_homG_of_isLinkEigen hd hE hlam hδ'
  obtain ⟨C, hC⟩ := rayCoeff_eq hd hc hE hlam hP hG hu
  set A := ⟪φ, v.fst⟫_ℝ
  set vφ : LinkPair d := WithLp.toLp 2 (φ, 0)
  have hI : ∀ γ : ℝ, 0 ≤ γ → C / (γ + δ' + d) = A / (D + γ + d) := by
    intro γ hγ
    have h1 := integral_ball_mul_homP_of_rayCoeff' (Lp.memLp u.fst) hγ hδ' v hC
    have h2 : ∫ x in ball (0 : 𝔼) 1, u.fst x * homP γ v x =
        ∫ x in ball (0 : 𝔼) 1, homP D vφ x * homP γ v x := by
      refine integral_congr_ae ?_
      filter_upwards [hφ] with x hx
      rw [hx]
      rfl
    rw [h2, integral_ball_homP_mul_homP hD hγ vφ v] at h1
    exact h1.symm
  have h0 := hI 0 le_rfl
  have h1 := hI 1 zero_le_one
  have hp0 : (0 : ℝ) < 0 + δ' + d := by linarith
  have hq0 : (0 : ℝ) < D + 0 + d := by linarith
  have hp1 : (0 : ℝ) < 1 + δ' + d := by linarith
  have hq1 : (0 : ℝ) < D + 1 + d := by linarith
  rw [div_eq_div_iff hp0.ne' hq0.ne'] at h0
  rw [div_eq_div_iff hp1.ne' hq1.ne'] at h1
  have hCA : C = A := by linarith
  rw [hCA] at h0
  have : A * (D - δ') = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hne

/-- A vector orthogonal to all basis vectors outside a finite set lies in their span. -/
theorem mem_span_of_inner_eq_zero {s : Set (Lp ℝ 2 (sphMeasure d))}
    (B : HilbertBasis s ℝ (Lp ℝ 2 (sphMeasure d))) (hB : ⇑B = ((↑) : s → Lp ℝ 2 (sphMeasure d)))
    {F : Set s} (hF : F.Finite) {x : Lp ℝ 2 (sphMeasure d)}
    (hx : ∀ i, i ∉ F → ⟪(i : Lp ℝ 2 (sphMeasure d)), x⟫_ℝ = 0) :
    x ∈ Submodule.span ℝ (((↑) : s → Lp ℝ 2 (sphMeasure d)) '' F) := by
  classical
  have hsum := B.hasSum_repr x
  have hzero : ∀ i ∉ hF.toFinset, B.repr x i • B i = 0 := fun i hi => by
    rw [B.repr_apply_apply, hB, hx i (by simpa using hi), zero_smul]
  have hx' : x = ∑ i ∈ hF.toFinset, B.repr x i • B i :=
    hsum.unique (hasSum_sum_of_ne_finset_zero hzero)
  rw [hx']
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [hB]
  exact ⟨i, by simpa using hi, rfl⟩

/-- **Completeness of a dense family of homogeneous harmonic functions.** Let `X D` (`D ∈ ℝ`) be
sets of link functions of weakly harmonic functions on `B_1`, homogeneous of degree `D ≥ 0`, whose
union spans a dense subspace of `L²(S)`. Then the link function of every weakly harmonic `u`
homogeneous of degree `δ ≥ 0` lies in the span of `X δ`. -/
theorem mem_span_of_harmonic (hd : 2 ≤ d) (hc : c.IsConical)
    (X : ℝ → Set (Lp ℝ 2 (sphMeasure d)))
    (hX : ∀ D, ∀ x ∈ X D, 0 ≤ D ∧ ∃ u : L2Pair volume (ball (0 : 𝔼) 1), c.IsWeakSolution 0 u ∧
      (u.fst : 𝔼 → ℝ) =ᵐ[volume.restrict (ball (0 : 𝔼) 1)] homFun D fun w => x w)
    (hdense : Dense (Submodule.span ℝ (⋃ D, X D) : Set (Lp ℝ 2 (sphMeasure d))))
    {u : L2Pair volume (ball (0 : 𝔼) 1)} (hu : c.IsWeakSolution 0 u) {δ : ℝ} (hδ : 0 ≤ δ)
    {φ : Lp ℝ 2 (sphMeasure d)}
    (hφ : (u.fst : 𝔼 → ℝ) =ᵐ[volume.restrict (ball (0 : 𝔼) 1)] homFun δ fun w => φ w) :
    φ ∈ Submodule.span ℝ (X δ) := by
  classical
  obtain ⟨s, B, Γ, lam, hB, heig, hfin⟩ := link_spectral hc
  set V : s → LinkPair d := fun i => WithLp.toLp 2 ((i : Lp ℝ 2 (sphMeasure d)), Γ i)
  set δ' : s → ℝ := fun i => indicialRoot d (lam i)
  have hδ0 : ∀ i, 0 ≤ δ' i := fun i => indicialRoot_nonneg hd (heig i).1
  have hroot : ∀ i, lam i = δ' i * (δ' i + d - 2) := fun i => indicialRoot_spec _ (heig i).1
  -- the indices of a given degree form a finite set
  have hF : ∀ D, {i : s | δ' i = D}.Finite := fun D =>
    (hfin (D * (D + d - 2))).subset fun i hi => by
      simp only [mem_ofPred_eq] at hi ⊢
      rw [hroot i, hi]
  -- orthogonality to eigenfunctions of other degrees
  have horth : ∀ {u' : L2Pair volume (ball (0 : 𝔼) 1)}, c.IsWeakSolution 0 u' → ∀ {D : ℝ},
      0 ≤ D → ∀ {φ' : Lp ℝ 2 (sphMeasure d)},
      ((u'.fst : 𝔼 → ℝ) =ᵐ[volume.restrict (ball (0 : 𝔼) 1)] homFun D fun w => φ' w) →
      ∀ i, δ' i ≠ D → ⟪(i : Lp ℝ 2 (sphMeasure d)), φ'⟫_ℝ = 0 := by
    intro u' hu' D hD φ' hφ' i hi
    rw [real_inner_comm]
    exact inner_eq_zero_of_degree_ne hd hc hu' hD hφ' (heig i).2 (hroot i) (hδ0 i) (Ne.symm hi)
  have hspanF : ∀ {u' : L2Pair volume (ball (0 : 𝔼) 1)}, c.IsWeakSolution 0 u' → ∀ {D : ℝ},
      0 ≤ D → ∀ {φ' : Lp ℝ 2 (sphMeasure d)},
      ((u'.fst : 𝔼 → ℝ) =ᵐ[volume.restrict (ball (0 : 𝔼) 1)] homFun D fun w => φ' w) →
      φ' ∈ Submodule.span ℝ (((↑) : s → Lp ℝ 2 (sphMeasure d)) '' {i | δ' i = D}) :=
    fun hu' D hD φ' hφ' =>
      mem_span_of_inner_eq_zero B hB (hF D) fun i hi => horth hu' hD hφ' i hi
  -- every element of `X D` lies in the span of the eigenfunctions of degree `D`
  have hXF : ∀ D, Submodule.span ℝ (X D) ≤
      Submodule.span ℝ (((↑) : s → Lp ℝ 2 (sphMeasure d)) '' {i | δ' i = D}) := fun D =>
    Submodule.span_le.mpr fun x hx => by
      obtain ⟨hD, u', hu', hx'⟩ := hX D x hx
      exact hspanF hu' hD hx'
  -- each eigenfunction lies in the span of `X` of its degree
  have heigX : ∀ i, (i : Lp ℝ 2 (sphMeasure d)) ∈ Submodule.span ℝ (X (δ' i)) := by
    intro i₀
    set D := δ' i₀
    set W := Submodule.span ℝ (X D)
    have : FiniteDimensional ℝ
        (Submodule.span ℝ (((↑) : s → Lp ℝ 2 (sphMeasure d)) '' {i | δ' i = D})) :=
      FiniteDimensional.span_of_finite ℝ ((hF D).image _)
    have : FiniteDimensional ℝ W :=
      Submodule.finiteDimensional_of_le (hXF D)
    set ψ := (i₀ : Lp ℝ 2 (sphMeasure d)) - W.starProjection (i₀ : Lp ℝ 2 (sphMeasure d))
    have hψW : ψ ∈ Wᗮ := Submodule.sub_starProjection_mem_orthogonal _
    have hPF : W.starProjection (i₀ : Lp ℝ 2 (sphMeasure d)) ∈
        Submodule.span ℝ (((↑) : s → Lp ℝ 2 (sphMeasure d)) '' {i | δ' i = D}) :=
      hXF D (Submodule.starProjection_apply_mem W _)
    have hψX : ∀ y ∈ ⋃ D', X D', ⟪y, ψ⟫_ℝ = 0 := by
      intro y hy
      obtain ⟨D', hy⟩ := mem_iUnion.mp hy
      by_cases hDD : D' = D
      · subst hDD
        have h := (Submodule.mem_orthogonal' W ψ).mp hψW y (Submodule.subset_span hy)
        rw [real_inner_comm]
        exact h
      · obtain ⟨hD', u', hu', hy'⟩ := hX D' y hy
        have hi₀ : ⟪y, (i₀ : Lp ℝ 2 (sphMeasure d))⟫_ℝ = 0 := by
          rw [real_inner_comm]
          exact horth hu' hD' hy' i₀ (Ne.symm hDD)
        have hyF : ∀ z ∈ Submodule.span ℝ (((↑) : s → Lp ℝ 2 (sphMeasure d)) '' {i | δ' i = D}),
            ⟪y, z⟫_ℝ = 0 := by
          intro z hz
          induction hz using Submodule.span_induction with
          | mem z hz =>
            obtain ⟨j, hj, rfl⟩ := hz
            rw [real_inner_comm]
            exact horth hu' hD' hy' j (by rw [hj]; exact Ne.symm hDD)
          | zero => simp
          | add z z' _ _ h h' => rw [inner_add_right, h, h', add_zero]
          | smul r z _ h => rw [real_inner_smul_right, h, mul_zero]
        rw [inner_sub_right, hi₀, hyF _ hPF, sub_zero]
    have hψ0 : ψ = 0 := by
      have hdense' : (Submodule.span ℝ (⋃ D, X D)).topologicalClosure = ⊤ := by
        rw [← SetLike.coe_set_eq, Submodule.topologicalClosure_coe, Submodule.top_coe]
        exact hdense.closure_eq
      rw [Submodule.topologicalClosure_eq_top_iff] at hdense'
      have hmem : ψ ∈ (Submodule.span ℝ (⋃ D, X D))ᗮ := by
        rw [Submodule.mem_orthogonal]
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy => exact hψX y hy
        | zero => simp
        | add y y' _ _ h h' => rw [inner_add_left, h, h', add_zero]
        | smul r y _ h => rw [real_inner_smul_left, h, mul_zero]
      rw [hdense'] at hmem
      exact (Submodule.mem_bot ℝ).mp hmem
    have : (i₀ : Lp ℝ 2 (sphMeasure d)) = W.starProjection (i₀ : Lp ℝ 2 (sphMeasure d)) :=
      sub_eq_zero.mp hψ0
    rw [this]
    exact Submodule.starProjection_apply_mem W _
  -- conclusion for `φ`
  have hφF := hspanF hu hδ hφ
  refine Submodule.span_le.mpr ?_ hφF
  rintro _ ⟨i, hi, rfl⟩
  have hi' : δ' i = δ := hi
  rw [← hi']
  exact heigX i

end Abstract

/-! ### The harmonic cone polynomials -/

section Cone

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

theorem homFun_add {Ψ Ψ' : Sph d → ℝ} (D : ℝ) :
    homFun D (Ψ + Ψ') = homFun D Ψ + homFun D Ψ' := by
  funext x
  simp [homFun, mul_add]

theorem homFun_const_smul {Ψ : Sph d → ℝ} (D r : ℝ) :
    homFun D (r • Ψ) = r • homFun D Ψ := by
  funext x
  simp only [homFun, Pi.smul_apply, smul_eq_mul]
  ring

/-- **A cone polynomial is the homogeneous extension of its link restriction.** -/
theorem conePoly_ae_eq_homFun (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (k : κ → ℕ)
    (ε : κ → Bool) {h : MvPolynomial (κ ⊕ ι) ℝ} {m : ℕ} (hh : IsWeightedHomogeneous polyWt h m) :
    homFun (modeDeg β k + m)
        (fun w => (ContinuousMap.toLp 2 (sphMeasure d) ℝ (linkPoly β e k ε h) : Sph d → ℝ) w)
      =ᵐ[volume] fun x : 𝔼 => conePoly β k ε h ((coordIso e).symm x) := by
  filter_upwards [homFun_congr_ae (ContinuousMap.coeFn_toLp (p := 2) (μ := sphMeasure d) (𝕜 := ℝ)
    (linkPoly β e k ε h)) (modeDeg β k + m), ae_ne_zero] with x hx hx0
  rw [hx, homFun, linkPoly_apply, sphProj_coe hx0, map_smul,
    conePoly_smul_point β k ε hh (inv_pos.mpr (norm_pos_iff.mpr hx0)), smul_eq_mul, ← mul_assoc,
    Real.inv_rpow (norm_nonneg _), mul_inv_cancel₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx0) _).ne',
    one_mul]

/-- The link functions of the harmonic cone polynomials of total degree `D`. -/
def harmConeLink (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (D : ℝ) :
    Set (Lp ℝ 2 (sphMeasure d)) :=
  {x | ∃ (k : κ → ℕ) (ε : κ → Bool) (h : MvPolynomial (κ ⊕ ι) ℝ) (m : ℕ),
    formalLap (modeQ β k) h = 0 ∧ IsWeightedHomogeneous polyWt h m ∧ modeDeg β k + m = D ∧
    x = ContinuousMap.toLp 2 (sphMeasure d) ℝ (linkPoly β e k ε h)}

/-- The harmonic cone polynomials of total degree `D`, as functions on the real model. -/
def harmConePolys (β : κ → ConeAngle) (D : ℝ) : Set (RealConeModel κ ι → ℝ) :=
  {P | ∃ (k : κ → ℕ) (ε : κ → Bool) (h : MvPolynomial (κ ⊕ ι) ℝ) (m : ℕ),
    formalLap (modeQ β k) h = 0 ∧ IsWeightedHomogeneous polyWt h m ∧ modeDeg β k + m = D ∧
    P = conePoly β k ε h}

theorem harmConeLink_spec (β : κ → ConeAngle) (hβ : ∀ a, (β a).beta ≤ 1)
    (e : RealConeIndex κ ι ≃ Fin d) (D : ℝ) :
    ∀ x ∈ harmConeLink β e D, 0 ≤ D ∧ ∃ u : L2Pair volume (ball (0 : 𝔼) 1),
      (coneCoeff β e).IsWeakSolution 0 u ∧
      (u.fst : 𝔼 → ℝ) =ᵐ[volume.restrict (ball (0 : 𝔼) 1)] homFun D fun w => x w := by
  rintro x ⟨k, ε, h, m, hL, hh, rfl, rfl⟩
  refine ⟨add_nonneg (modeDeg_nonneg β k) (Nat.cast_nonneg m), ?_⟩
  have hP := isClassicalHarmonic_conePoly hβ k ε hL
  refine ⟨_, hP.isWeakSolution e isOpen_ball isBounded_ball, ?_⟩
  rw [classicalPair_fst]
  filter_upwards [MemLp.coeFn_toLp (hP.memLp e isOpen_ball isBounded_ball),
    ae_restrict_of_ae (conePoly_ae_eq_homFun β e k ε hh)] with x hx hx'
  rw [hx, hx']

theorem nonempty_polyVar (e : RealConeIndex κ ι ≃ Fin d) : Nonempty (κ ⊕ ι) := by
  rcases e.symm ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ with ⟨_, a⟩ | i
  · exact ⟨Sum.inl a⟩
  · exact ⟨Sum.inr i⟩

/-- **The harmonic cone polynomials are dense on the link** (density of all cone polynomials and
the Fischer decomposition). -/
theorem dense_span_harmConeLink (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) :
    Dense (Submodule.span ℝ (⋃ D, harmConeLink β e D) : Set (Lp ℝ 2 (sphMeasure d))) := by
  refine (dense_span_linkPolyLp β e).mono (Submodule.span_le.mpr ?_)
  rintro _ ⟨_, ⟨k, ε, p, rfl⟩, rfl⟩
  set L : MvPolynomial (κ ⊕ ι) ℝ →ₗ[ℝ] Lp ℝ 2 (sphMeasure d) :=
    (ContinuousMap.toLp 2 (sphMeasure d) ℝ (E := ℝ)).toLinearMap ∘ₗ linkPolyL β e k ε
  have hp := mem_span_harmonicGen (modeQ β k)
    (fischerConst_modeQ_pos β k (nonempty_polyVar e)) p
  have hmap : Submodule.span ℝ (harmonicGen (κ := κ) (ι := ι) (modeQ β k)) ≤
      (Submodule.span ℝ (⋃ D, harmConeLink β e D)).comap L := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, m, h, hL, hh, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    refine Submodule.subset_span (mem_iUnion.mpr ⟨modeDeg β k + m, k, ε, h, m, hL, hh, rfl, ?_⟩)
    show ContinuousMap.toLp 2 (sphMeasure d) ℝ (linkPoly β e k ε (rhoSq ^ j * h)) = _
    rw [linkPoly_rhoSq_pow_mul]
  exact Submodule.mem_comap.mp (hmap hp)

/-- **Every weakly harmonic function on `B_1` homogeneous of degree `δ` has its link function in the
span of the harmonic cone polynomials of degree `δ`.** -/
theorem cone_link_mem_span (hd : 2 ≤ d) (β : κ → ConeAngle) (hβ : ∀ a, (β a).beta ≤ 1)
    (e : RealConeIndex κ ι ≃ Fin d) {u : L2Pair volume (ball (0 : 𝔼) 1)}
    (hu : (coneCoeff β e).IsWeakSolution 0 u) {δ : ℝ} (hδ : 0 ≤ δ) {φ : Lp ℝ 2 (sphMeasure d)}
    (hφ : (u.fst : 𝔼 → ℝ) =ᵐ[volume.restrict (ball (0 : 𝔼) 1)] homFun δ fun w => φ w) :
    φ ∈ Submodule.span ℝ (harmConeLink β e δ) :=
  mem_span_of_harmonic hd (coneCoeff_isConical β e) (harmConeLink β e)
    (harmConeLink_spec β hβ e) (dense_span_harmConeLink β e) hu hδ hφ

/-- **Homogeneous weakly harmonic functions are harmonic cone polynomials.** A weakly harmonic
`u ∈ W^{1,2}(B_1)` for the cone Laplacian (`β_a ≤ 1`), homogeneous of degree `δ`, is a.e. on `B_1` a
linear combination of harmonic cone polynomials of degree `δ`. -/
theorem cone_homogeneous_mem_span (hd : 2 ≤ d) (β : κ → ConeAngle) (hβ : ∀ a, (β a).beta ≤ 1)
    (e : RealConeIndex κ ι ≃ Fin d) {u : L2Pair volume (ball (0 : 𝔼) 1)}
    (hu : (coneCoeff β e).IsWeakSolution 0 u) {δ : ℝ} (hδ : 0 ≤ δ) {φ : Lp ℝ 2 (sphMeasure d)}
    (hφ : (u.fst : 𝔼 → ℝ) =ᵐ[volume.restrict (ball (0 : 𝔼) 1)] homFun δ fun w => φ w) :
    ∃ P ∈ Submodule.span ℝ (harmConePolys β δ),
      (u.fst : 𝔼 → ℝ) =ᵐ[volume.restrict (ball (0 : 𝔼) 1)] fun x => P ((coordIso e).symm x) := by
  have hmem := cone_link_mem_span hd β hβ e hu hδ hφ
  have key : ∀ ψ ∈ Submodule.span ℝ (harmConeLink β e δ), ∃ P ∈ Submodule.span ℝ (harmConePolys β δ),
      (homFun δ fun w => (ψ : Sph d → ℝ) w) =ᵐ[volume] fun x => P ((coordIso e).symm x) := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, ε, h, m, hL, hh, hD, rfl⟩ := hx
      refine ⟨_, Submodule.subset_span ⟨k, ε, h, m, hL, hh, hD, rfl⟩, ?_⟩
      rw [← hD]
      exact conePoly_ae_eq_homFun β e k ε hh
    | zero =>
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      filter_upwards [homFun_congr_ae (Lp.coeFn_zero ℝ 2 (sphMeasure d)) δ] with x hx
      rw [hx]
      simp [homFun]
    | add ψ ψ' _ _ h h' =>
      obtain ⟨P, hP, hPe⟩ := h
      obtain ⟨P', hP', hPe'⟩ := h'
      refine ⟨P + P', Submodule.add_mem _ hP hP', ?_⟩
      filter_upwards [homFun_congr_ae (Lp.coeFn_add ψ ψ') δ, hPe, hPe'] with x hx hx1 hx2
      rw [hx, homFun_add, Pi.add_apply, hx1, hx2, Pi.add_apply]
    | smul r ψ _ h =>
      obtain ⟨P, hP, hPe⟩ := h
      refine ⟨r • P, Submodule.smul_mem _ r hP, ?_⟩
      filter_upwards [homFun_congr_ae (Lp.coeFn_smul r ψ) δ, hPe] with x hx hx1
      rw [hx, homFun_const_smul, Pi.smul_apply, hx1, Pi.smul_apply]
  obtain ⟨P, hP, hPe⟩ := key φ hmem
  exact ⟨P, hP, hφ.trans (ae_restrict_of_ae hPe)⟩

end Cone

end ConicalKahler.Sobolev
