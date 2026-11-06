module

public import ConicalKahler.Sobolev.HarmonicExpansion

/-!
# The link of a product of cones: Lemmas 3.1 and 3.3 for the cone Laplacian

The cone Laplacian `A = g⁻¹` (`coneCoeff`) is a conical coefficient field
(`coneCoeff_isConical`): it is invariant under dilations (`coneCoeffA_smul`) and fixes the radial
direction, `g⁻¹(x) x = x` (`coneCoeffA_self`), because in each cone factor the radial vector is a
unit vector of `g` orthogonal to the angular one. So the results of `Link.lean`,
`LinkSpectral.lean`, `Homogeneous.lean`, `Expansion.lean` and `HarmonicExpansion.lean` apply.

* `cone_link_spectral` (**Lemma 3.1**): `L²` of the link of `C(β_1) × ⋯ × ℝ^k` has a Hilbert basis
  of eigenfunctions of `-Δ_ḡ`, with eigenvalues `λ_i ≥ 0`, finitely many below any bound.
* `cone_homogeneous_harmonic` (§3.2): `ρ^δ φ` is weakly harmonic away from the vertex when `φ` is a
  link eigenfunction with `λ = δ(δ + m - 2)`; on balls `homPair_isWeakSolution`.
* `cone_expansion` (**Lemma 3.3**): every weakly harmonic `u ∈ W^{1,2}(B_1)` is the
  `L²(B_1)`-sum `∑ a_i ρ^{δ_i} φ_i` of homogeneous harmonic functions, `δ_i ≥ 0`.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set Metric
open scoped ContDiff ENNReal ComplexConjugate

namespace ConicalKahler.Sobolev

open RealConeModel

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-- The radial direction of one cone factor is fixed by `g⁻¹`. -/
theorem coneInvFactor_self (b : ℝ) (w : ℂ) : coneInvFactor b w w = w := by
  by_cases hw : w = 0
  · simp [coneInvFactor, hw]
  have hn : Complex.normSq w ≠ 0 := Complex.normSq_eq_zero.not.mpr hw
  have hc : conj w * w = (Complex.normSq w : ℂ) := (Complex.normSq_eq_conj_mul_self).symm
  rw [coneInvFactor, hc, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_smul, add_zero,
    smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem coneInvOp_self (β : κ → ConeAngle) (p : RealConeModel κ ι) : coneInvOp β p p = p := by
  refine ext_cone_eucl (fun a => ?_) (fun i => ?_)
  · simp only [coneInvOp, LinearMap.coe_toContinuousLinearMap', coneInvOpₗ, LinearMap.coe_mk,
      AddHom.coe_mk, cone_ofCones]
    exact coneInvFactor_self _ _
  · simp [coneInvOp, coneInvOpₗ]

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **`g⁻¹(x) x = x`**: the radial vector field is fixed by the inverse cone metric. -/
theorem coneCoeffA_self (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (x : 𝔼) :
    coneCoeffA β e x x = x := by
  simp only [coneCoeffA, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    coneInvOp_self, LinearIsometryEquiv.apply_symm_apply]

variable [NeZero d]

/-- **The cone Laplacian is conical.** -/
theorem coneCoeff_isConical (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) :
    (coneCoeff β e).IsConical where
  smul ht x := coneCoeffA_smul β e ht.ne' x
  radial := coneCoeffA_self β e

/-- **Lemma 3.1 for products of cones** (spectral decomposition on the link). -/
theorem cone_link_spectral (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) :
    ∃ (s : Set (Lp ℝ 2 (sphMeasure d))) (B : HilbertBasis s ℝ (Lp ℝ 2 (sphMeasure d)))
      (Γ : s → Lp 𝔼 2 (sphMeasure d)) (lam : s → ℝ),
      ⇑B = ((↑) : s → Lp ℝ 2 (sphMeasure d)) ∧
      (∀ i, 0 ≤ lam i ∧ IsLinkEigen (coneCoeff_isConical β e) (lam i)
        (WithLp.toLp 2 ((i : Lp ℝ 2 (sphMeasure d)), Γ i))) ∧
      ∀ Λ : ℝ, {i | lam i ≤ Λ}.Finite :=
  link_spectral (coneCoeff_isConical β e)

/-- **Homogeneous harmonic functions on products of cones** (§3.2): `ρ^δ φ` is weakly harmonic
away from the vertex when `φ` is a link eigenfunction with `λ = δ (δ + m - 2)`. -/
theorem cone_homogeneous_harmonic (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d)
    {δ lam : ℝ} {v : LinkPair d} (hE : IsLinkEigen (coneCoeff_isConical β e) lam v)
    (hlam : lam = δ * (δ + d - 2)) {ϑ : 𝔼 → ℝ} (hϑ : IsTestFn {0}ᶜ ϑ) :
    ∫ x, ⟪coneCoeffA β e x (homG δ v x), gradient ϑ x⟫_ℝ = 0 :=
  homogeneous_harmonic (coneCoeff_isConical β e) hE hlam hϑ

/-- **Lemma 3.3 for products of cones** (expansion of harmonic functions). A weakly harmonic
`u ∈ W^{1,2}(B_1)` for the cone Laplacian is the `L²(B_1)`-sum `∑ a_i ρ^{δ_i} φ_i` of homogeneous
harmonic functions of degrees `δ_i ≥ 0`, mutually orthogonal in `L²(B_1)`. -/
theorem cone_expansion (hd : 2 ≤ d) (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d)
    {u : L2Pair volume (ball (0 : 𝔼) 1)} (hu : (coneCoeff β e).IsWeakSolution 0 u) :
    ∃ (s : Set (Lp ℝ 2 (sphMeasure d))) (B : HilbertBasis s ℝ (Lp ℝ 2 (sphMeasure d)))
      (Γ : s → Lp 𝔼 2 (sphMeasure d)) (lam δ a : s → ℝ)
      (P : s → Lp ℝ 2 (volume.restrict (ball (0 : 𝔼) 1))),
      ⇑B = ((↑) : s → Lp ℝ 2 (sphMeasure d)) ∧
      (∀ i, 0 ≤ δ i ∧ lam i = δ i * (δ i + d - 2) ∧
        IsLinkEigen (coneCoeff_isConical β e) (lam i)
          (WithLp.toLp 2 ((i : Lp ℝ 2 (sphMeasure d)), Γ i)) ∧
        (P i : 𝔼 → ℝ) =ᵐ[volume.restrict (ball (0 : 𝔼) 1)]
          homP (δ i) (WithLp.toLp 2 ((i : Lp ℝ 2 (sphMeasure d)), Γ i)) ∧
        ∃ Q : L2Pair volume (ball (0 : 𝔼) 1), (coneCoeff β e).IsWeakSolution 0 Q ∧ Q.fst = P i) ∧
      (∀ i j, i ≠ j → ⟪P i, P j⟫_ℝ = 0) ∧
      HasSum (fun i => a i • P i) u.fst :=
  expansion hd (coneCoeff_isConical β e) hu

end ConicalKahler.Sobolev
