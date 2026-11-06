module

public import ConicalKahler

/-!
# Tests for Milestone 12: the link and Lemma 3.3

The model `C(S¹_{4π/3}) × ℝ` (`β = 2/3`), with real coordinates `(x, y, s)` of `ℝ³`; its link is
the unit sphere `S²` with the metric induced by `g`.
-/

namespace ConicalKahler.Test

open ConicalKahler ConicalKahler.Sobolev MeasureTheory Metric
open scoped Real InnerProductSpace

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- One cone of angle `4π/3` (`β = 2/3`). -/
noncomputable def lCone : Fin 1 → ConeAngle := fun _ => ⟨2 / 3, by norm_num⟩

/-- A numbering of the three real coordinates `(x, y, s)`. -/
noncomputable def lCoords : RealConeIndex (Fin 1) (Fin 1) ≃ Fin 3 :=
  Fintype.equivFinOfCardEq (by simp)

/-- **The cone Laplacian is conical**: `g⁻¹(t x) = g⁻¹(x)` and `g⁻¹(x) x = x`. -/
example : (coneCoeff lCone lCoords).IsConical := coneCoeff_isConical lCone lCoords

example (x : ℝ³) : coneCoeffA lCone lCoords x x = x := coneCoeffA_self lCone lCoords x

/-- **Polar coordinates** on `ℝ³`. -/
example {g : ℝ³ → ℝ} (hg : Integrable g) :
    ∫ x, g x = ∫ w, (∫ r in Set.Ioi (0 : ℝ), r ^ (3 - 1) • g (r • (w : ℝ³))) ∂(sphMeasure 3) :=
  integral_polar_iter hg

/-- **The link Sobolev space embeds compactly into `L²(S²)`** (Rellich on the shell
`{1 < |x| < 4}`). -/
example : IsCompactOperator (linkFst 3) := isCompactOperator_linkFst

/-- **The constant function is a link eigenfunction with eigenvalue `0`.** -/
example : IsLinkEigen (coneCoeff_isConical lCone lCoords) 0
    (smoothLinkPair (fun _ : ℝ³ => (1 : ℝ)) contDiff_const) :=
  linkEigen_const _

/-- **Lemma 3.1** on the link of `C(S¹_{4π/3}) × ℝ`: a Hilbert basis of eigenfunctions of
`-Δ_ḡ`, with eigenvalues `λ_i ≥ 0`, finitely many below any bound. -/
example : ∃ (s : Set (Lp ℝ 2 (sphMeasure 3))) (B : HilbertBasis s ℝ (Lp ℝ 2 (sphMeasure 3)))
    (Γ : s → Lp ℝ³ 2 (sphMeasure 3)) (lam : s → ℝ),
    ⇑B = ((↑) : s → Lp ℝ 2 (sphMeasure 3)) ∧
    (∀ i, 0 ≤ lam i ∧ IsLinkEigen (coneCoeff_isConical lCone lCoords) (lam i)
      (WithLp.toLp 2 ((i : Lp ℝ 2 (sphMeasure 3)), Γ i))) ∧
    ∀ Λ : ℝ, {i | lam i ≤ Λ}.Finite :=
  cone_link_spectral lCone lCoords

/-- The indicial root of `λ = 2` in dimension `3` is `δ = 1`: `δ (δ + 1) = 2`. -/
example : indicialRoot 3 2 = 1 := by
  unfold indicialRoot
  rw [show ((3 : ℕ) : ℝ) = 3 by norm_num,
    show ((3 : ℝ) - 2) ^ 2 + 4 * 2 = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- **Homogeneous harmonic functions**: `ρ^δ φ` is weakly harmonic off the vertex when
`λ = δ(δ + 1)`. -/
example {δ lam : ℝ} {v : LinkPair 3} (hE : IsLinkEigen (coneCoeff_isConical lCone lCoords) lam v)
    (hlam : lam = δ * (δ + 3 - 2)) {ϑ : ℝ³ → ℝ} (hϑ : IsTestFn {0}ᶜ ϑ) :
    ∫ x, ⟪coneCoeffA lCone lCoords x (homG δ v x), gradient ϑ x⟫_ℝ = 0 := by
  have := cone_homogeneous_harmonic lCone lCoords hE (by exact_mod_cast hlam) hϑ
  exact this

/-- **The radial ODE**: the ray coefficients of a weakly harmonic `u` on `B_1` are `C r^δ`. -/
example {lam δ : ℝ} {v : LinkPair 3} (hE : IsLinkEigen (coneCoeff_isConical lCone lCoords) lam v)
    (hlam : lam = δ * (δ + 3 - 2))
    (hP : MemLp (homP δ v) 2 (volume.restrict (ball (0 : ℝ³) 1)))
    (hG : MemLp (homG δ v) 2 (volume.restrict (ball (0 : ℝ³) 1)))
    {u : L2Pair volume (ball (0 : ℝ³) 1)} (hu : (coneCoeff lCone lCoords).IsWeakSolution 0 u) :
    ∃ C, ∀ᵐ r ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      rayCoeff u.fst (fun w => v.fst w) r = C * r ^ δ :=
  rayCoeff_eq (by norm_num) (coneCoeff_isConical lCone lCoords) hE (by exact_mod_cast hlam) hP hG hu

/-- **Lemma 3.3**: a weakly harmonic `u ∈ W^{1,2}(B_1)` is the `L²(B_1)`-sum of homogeneous harmonic
functions `ρ^{δ_i} φ_i`, `δ_i ≥ 0`. -/
example {u : L2Pair volume (ball (0 : ℝ³) 1)} (hu : (coneCoeff lCone lCoords).IsWeakSolution 0 u) :
    ∃ (s : Set (Lp ℝ 2 (sphMeasure 3))) (P : s → Lp ℝ 2 (volume.restrict (ball (0 : ℝ³) 1)))
      (a : s → ℝ), (∀ i j, i ≠ j → ⟪P i, P j⟫_ℝ = 0) ∧ HasSum (fun i => a i • P i) u.fst := by
  obtain ⟨s, -, -, -, -, a, P, -, -, horth, hsum⟩ := cone_expansion (by norm_num) lCone lCoords hu
  exact ⟨s, P, a, horth, hsum⟩

end ConicalKahler.Test
