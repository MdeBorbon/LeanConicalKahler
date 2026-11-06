module

public import ConicalKahler.Sobolev.ConePolyFn
public import ConicalKahler.Sobolev.LinkSpectral
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Density of cone polynomials on the link

The restrictions to the unit sphere `S ⊆ ℝ^d` of the cone polynomials
`∏_a r_a^{k_a/β_a} (cos | sin)(k_a θ_a) · p(r², s)` are **dense in `C(S)` and in `L²(S)`**
(`dense_linkPolySpan`, `dense_span_linkPolyLp`), for angles `0 < β_a ≤ 1`.

The proof is by Stone–Weierstrass, applied to the closure `W` of the span of these restrictions:

* `W` is stable under multiplication by `G(r_a²)` for every continuous `G`: polynomials in `r_a²`
  preserve the span, and the univariate Weierstrass theorem approximates `G` on `[0, 1]`
  (`mul_comp_tA_mem`);
* products of two generators are in `W`. In each cone factor
  `(r^{k/β} T(kθ))(r^{k'/β} T'(k'θ))` is a combination of `r^{(k+k')/β} T''((k+k')θ)` and
  `r^{|k-k'|/β} T''(|k-k'| θ) · (r²)^{min(k,k')/β}` (`modeFn_mul`), and the last factor is a
  continuous function of `r²`;
* hence `W` is a closed subalgebra. It separates points, because
  `w ↦ |w|^{1/β - 1} w` is injective (`injective_zetaMap`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set MvPolynomial ComplexConjugate
open scoped ContDiff

namespace ConicalKahler.Sobolev

open RealConeModel

/-! ### Products of angular modes in one cone factor -/

/-- `Re` (`ε = true`) or `Im` (`ε = false`). -/
def reIm (ε : Bool) (z : ℂ) : ℝ := bif ε then z.re else z.im

/-- The coefficient of `T((k+k')θ)` in `T_ε(kθ) T_{ε'}(k'θ)`. -/
def prodCoeff₁ (ε ε' : Bool) : ℝ := bif (!ε && !ε') then -1 / 2 else 1 / 2

/-- The coefficient of `T((k-k')θ)` in `T_ε(kθ) T_{ε'}(k'θ)`. -/
def prodCoeff₂ (ε ε' : Bool) : ℝ := bif (ε && !ε') then -1 / 2 else 1 / 2

theorem reIm_mul_reIm (ε ε' : Bool) (a b : ℂ) :
    reIm ε a * reIm ε' b = prodCoeff₁ ε ε' * reIm (ε == ε') (a * b) +
      prodCoeff₂ ε ε' * reIm (ε == ε') (a * conj b) := by
  cases ε <;> cases ε' <;>
    simp [reIm, prodCoeff₁, prodCoeff₂, Complex.mul_re, Complex.mul_im] <;> ring

theorem reIm_ofReal_mul (ε : Bool) (r : ℝ) (z : ℂ) : reIm ε ((r : ℂ) * z) = r * reIm ε z := by
  cases ε <;> simp [reIm]

theorem modeFn_eq_reIm (b : ℝ) (k : ℕ) (ε : Bool) (w : ℂ) :
    modeFn b k ε w = ‖w‖ ^ ((k : ℝ) / b - k) * reIm ε (w ^ k) := by
  cases ε <;> rfl

theorem modeFn_zero_point (b : ℝ) {k : ℕ} (hk : 1 ≤ k) (ε : Bool) : modeFn b k ε 0 = 0 := by
  rw [modeFn_eq_reIm, zero_pow (by omega)]
  cases ε <;> simp [reIm]

theorem pow_mul_conj_pow (w : ℂ) {k k' : ℕ} (h : k' ≤ k) :
    w ^ k * conj (w ^ k') = (((‖w‖ ^ 2) ^ k' : ℝ) : ℂ) * w ^ (k - k') := by
  rw [show w ^ k = w ^ (k - k') * w ^ k' by rw [← pow_add, Nat.sub_add_cancel h], mul_assoc,
    map_pow, ← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **The product of two angular modes of one cone factor** (`k' ≤ k`):
`T_ε(k) T_{ε'}(k') = c₁ T((k+k')) + c₂ T((k-k')) (|w|²)^{k'/b}`. -/
theorem modeFn_mul {b : ℝ} (hb : 0 < b) {k k' : ℕ} (h : k' ≤ k) (ε ε' : Bool) (w : ℂ) :
    modeFn b k ε w * modeFn b k' ε' w =
      prodCoeff₁ ε ε' * modeFn b (k + k') (ε == ε') w +
        prodCoeff₂ ε ε' * modeFn b (k - k') (ε == ε') w * (‖w‖ ^ 2) ^ ((k' : ℝ) / b) := by
  rcases Nat.eq_zero_or_pos k' with rfl | hk'
  · simp only [Nat.cast_zero, zero_div, Real.rpow_zero, mul_one, add_zero, Nat.sub_zero,
      modeFn_zero]
    cases ε <;> cases ε' <;> simp [prodCoeff₁, prodCoeff₂] <;> ring
  by_cases hw : w = 0
  · subst hw
    rw [modeFn_zero_point b (by omega) ε, modeFn_zero_point b (by omega : 1 ≤ k + k'), norm_zero,
      zero_pow two_ne_zero, Real.zero_rpow (div_pos (Nat.cast_pos.mpr hk') hb).ne', mul_zero,
      zero_mul]
    simp
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hprod := reIm_mul_reIm ε ε' (w ^ k) (w ^ k')
  rw [← pow_add, pow_mul_conj_pow w h, reIm_ofReal_mul] at hprod
  simp only [modeFn_eq_reIm]
  have e1 : ‖w‖ ^ ((k : ℝ) / b - k) * ‖w‖ ^ ((k' : ℝ) / b - k') =
      ‖w‖ ^ (((k + k' : ℕ) : ℝ) / b - ((k + k' : ℕ) : ℝ)) := by
    rw [← Real.rpow_add hn]
    push_cast
    ring_nf
  have e2 : ‖w‖ ^ ((k : ℝ) / b - k) * ‖w‖ ^ ((k' : ℝ) / b - k') * (‖w‖ ^ 2) ^ k' =
      ‖w‖ ^ (((k - k' : ℕ) : ℝ) / b - ((k - k' : ℕ) : ℝ)) * (‖w‖ ^ 2) ^ ((k' : ℝ) / b) := by
    rw [← Real.rpow_natCast (‖w‖ ^ 2), ← Real.rpow_natCast ‖w‖ 2, ← Real.rpow_mul hn.le,
      ← Real.rpow_mul hn.le, ← Real.rpow_add hn, ← Real.rpow_add hn, ← Real.rpow_add hn,
      Nat.cast_sub h]
    push_cast
    ring_nf
  calc ‖w‖ ^ ((k : ℝ) / b - k) * reIm ε (w ^ k) * (‖w‖ ^ ((k' : ℝ) / b - k') * reIm ε' (w ^ k'))
      = ‖w‖ ^ ((k : ℝ) / b - k) * ‖w‖ ^ ((k' : ℝ) / b - k') *
          (reIm ε (w ^ k) * reIm ε' (w ^ k')) := by ring
    _ = _ := by
        rw [hprod]
        linear_combination (prodCoeff₁ ε ε' * reIm (ε == ε') (w ^ (k + k'))) * e1 +
          (prodCoeff₂ ε ε' * reIm (ε == ε') (w ^ (k - k'))) * e2

/-- The product of two modes in either order. -/
theorem exists_modeFn_mul {b : ℝ} (hb : 0 < b) (k k' : ℕ) (ε ε' : Bool) :
    ∃ (c₁ c₂ : ℝ) (k₁ k₂ m : ℕ) (ε₁ : Bool), ∀ w : ℂ,
      modeFn b k ε w * modeFn b k' ε' w =
        c₁ * modeFn b k₁ ε₁ w + c₂ * modeFn b k₂ ε₁ w * (‖w‖ ^ 2) ^ ((m : ℝ) / b) := by
  rcases le_total k' k with h | h
  · exact ⟨_, _, _, _, _, _, modeFn_mul hb h ε ε'⟩
  · exact ⟨_, _, _, _, _, _, fun w => by rw [mul_comm]; exact modeFn_mul hb h ε' ε w⟩

/-! ### Continuity for all angles -/

theorem continuous_modeFn' {b : ℝ} (hb : 0 < b) (k : ℕ) (ε : Bool) :
    Continuous (modeFn b k ε) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [show modeFn b 0 ε = fun _ => bif ε then 1 else 0 from funext (modeFn_zero b ε)]
    exact continuous_const
  refine continuous_iff_continuousAt.mpr fun w => ?_
  by_cases hw : w = 0
  · subst hw
    have hbound : ∀ z : ℂ, |modeFn b k ε z| ≤ ‖z‖ ^ ((k : ℝ) / b) := by
      intro z
      cases ε
      · exact abs_harmSinC_le b k z
      · exact abs_harmCosC_le b k z
    have hq : 0 < (k : ℝ) / b := div_pos (Nat.cast_pos.mpr hk) hb
    have hlim : Tendsto (fun z : ℂ => ‖z‖ ^ ((k : ℝ) / b)) (𝓝 0) (𝓝 0) := by
      have h0 := Real.continuousAt_rpow_const 0 ((k : ℝ) / b) (Or.inr hq.le)
      rw [← norm_zero (E := ℂ)] at h0
      have h := (h0.comp (continuous_norm (E := ℂ)).continuousAt).tendsto
      simpa [Function.comp_def, Real.zero_rpow hq.ne'] using h
    rw [ContinuousAt, modeFn_zero_point b hk ε]
    exact squeeze_zero_norm (fun z => by rw [Real.norm_eq_abs]; exact hbound z) hlim
  · have hd : ContDiffOn ℝ 0 (modeFn b k ε) {0}ᶜ := by
      cases ε
      · exact contDiffOn_harmSinC b k
      · exact contDiffOn_harmCosC b k
    exact (hd.continuousOn.continuousAt (isOpen_compl_singleton.mem_nhds hw))

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

theorem continuous_conePoly' (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool)
    (p : MvPolynomial (κ ⊕ ι) ℝ) : Continuous (conePoly β k ε p) :=
  (continuous_finsetProd _ fun a _ =>
    (continuous_modeFn' (β a).pos (k a) (ε a)).comp (continuous_cone a)).mul
    (contDiff_eval_polyArg (n := 0) p).continuous

theorem conePoly_mul_eval (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool)
    (p q : MvPolynomial (κ ⊕ ι) ℝ) (y : RealConeModel κ ι) :
    conePoly β k ε (q * p) y = eval (polyArg y) q * conePoly β k ε p y := by
  rw [conePoly, conePoly, eval_mul]
  ring

/-! ### Restrictions to the link -/

variable {d : ℕ} [NeZero d]

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **The restriction of a cone polynomial to the link** (the unit sphere of `ℝ^d`, in the real
coordinates numbered by `e`). -/
def linkPoly (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (k : κ → ℕ) (ε : κ → Bool)
    (p : MvPolynomial (κ ⊕ ι) ℝ) : C(Sph d, ℝ) :=
  sphRestrict (fun x => conePoly β k ε p ((coordIso e).symm x))
    ((continuous_conePoly' β k ε p).comp (coordIso e).symm.continuous)

theorem linkPoly_apply (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (k : κ → ℕ)
    (ε : κ → Bool) (p : MvPolynomial (κ ⊕ ι) ℝ) (w : Sph d) :
    linkPoly β e k ε p w = conePoly β k ε p ((coordIso e).symm w) := rfl

/-- `linkPoly` is linear in the polynomial. -/
def linkPolyL (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (k : κ → ℕ) (ε : κ → Bool) :
    MvPolynomial (κ ⊕ ι) ℝ →ₗ[ℝ] C(Sph d, ℝ) where
  toFun := linkPoly β e k ε
  map_add' p q := by
    ext w
    simp [linkPoly_apply, conePoly_add]
  map_smul' c p := by
    ext w
    simp [linkPoly_apply, conePoly_smul]

theorem norm_symm_sph (e : RealConeIndex κ ι ≃ Fin d) (w : Sph d) :
    ‖(coordIso e).symm (w : 𝔼)‖ = 1 := by
  rw [LinearIsometryEquiv.norm_map]
  exact norm_eq_of_mem_sphere w

/-- On the link `ρ = 1`, so `ρ^{2j} p` and `p` have the same restriction. -/
theorem linkPoly_rhoSq_pow_mul (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (k : κ → ℕ)
    (ε : κ → Bool) (p : MvPolynomial (κ ⊕ ι) ℝ) (j : ℕ) :
    linkPoly β e k ε (rhoSq ^ j * p) = linkPoly β e k ε p := by
  ext w
  rw [linkPoly_apply, linkPoly_apply, conePoly_rhoSq_pow_mul, norm_symm_sph, one_pow, one_pow,
    one_mul]

/-- The function `r_a²` on the link. -/
def tA (e : RealConeIndex κ ι ≃ Fin d) (a : κ) : C(Sph d, ℝ) :=
  sphRestrict (fun x => ‖((coordIso e).symm x).cone a‖ ^ 2)
    (((continuous_norm.comp (continuous_cone a)).pow 2).comp (coordIso e).symm.continuous)

theorem tA_mem_Icc (e : RealConeIndex κ ι ≃ Fin d) (a : κ) (w : Sph d) : tA e a w ∈ Icc 0 1 := by
  refine ⟨sq_nonneg _, ?_⟩
  have h := norm_cone_le ((coordIso e).symm (w : 𝔼)) a
  rw [norm_symm_sph] at h
  exact pow_le_one₀ (norm_nonneg _) h

theorem linkPoly_mul_tA (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) (k : κ → ℕ)
    (ε : κ → Bool) (p : MvPolynomial (κ ⊕ ι) ℝ) (a : κ) :
    linkPoly β e k ε p * tA e a = linkPoly β e k ε (X (Sum.inl a) * p) := by
  ext w
  rw [ContinuousMap.mul_apply, linkPoly_apply, linkPoly_apply, conePoly_mul_eval, eval_X]
  simp only [tA, sphRestrict, ContinuousMap.coe_mk, polyArg, Sum.elim_inl]
  ring

/-- The generators: restrictions of all cone polynomials. -/
def linkPolyGens (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) : Set C(Sph d, ℝ) :=
  {f | ∃ (k : κ → ℕ) (ε : κ → Bool) (p : MvPolynomial (κ ⊕ ι) ℝ), f = linkPoly β e k ε p}

/-- The span of the restrictions of cone polynomials. -/
def linkPolySpan (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d) : Submodule ℝ C(Sph d, ℝ) :=
  Submodule.span ℝ (linkPolyGens β e)

section Closure

variable (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d)

theorem linkPoly_mem_span (k : κ → ℕ) (ε : κ → Bool) (p : MvPolynomial (κ ⊕ ι) ℝ) :
    linkPoly β e k ε p ∈ linkPolySpan β e :=
  Submodule.subset_span ⟨k, ε, p, rfl⟩

theorem mul_tA_mem_span {f : C(Sph d, ℝ)} (hf : f ∈ linkPolySpan β e) (a : κ) :
    f * tA e a ∈ linkPolySpan β e := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, ε, p, rfl⟩ := hf
    rw [linkPoly_mul_tA]
    exact linkPoly_mem_span β e _ _ _
  | zero => simp
  | add f g _ _ hf hg => rw [add_mul]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hf

theorem mul_poly_tA_mem_span {f : C(Sph d, ℝ)} (hf : f ∈ linkPolySpan β e) (a : κ)
    (P : Polynomial ℝ) : f * P.toContinuousMap.comp (tA e a) ∈ linkPolySpan β e := by
  induction P using Polynomial.induction_on with
  | C c =>
    have : f * (Polynomial.C c).toContinuousMap.comp (tA e a) = c • f := by
      ext w
      simp [mul_comm]
    rw [this]
    exact Submodule.smul_mem _ c hf
  | add P Q hP hQ =>
    have : f * (P + Q).toContinuousMap.comp (tA e a) =
        f * P.toContinuousMap.comp (tA e a) + f * Q.toContinuousMap.comp (tA e a) := by
      ext w
      simp [mul_add]
    rw [this]
    exact Submodule.add_mem _ hP hQ
  | monomial n c ih =>
    have : f * (Polynomial.C c * Polynomial.X ^ (n + 1)).toContinuousMap.comp (tA e a) =
        f * (Polynomial.C c * Polynomial.X ^ n).toContinuousMap.comp (tA e a) * tA e a := by
      ext w
      simp [pow_succ]
      ring
    rw [this]
    exact mul_tA_mem_span β e ih a

/-- The closure `W` of the span. -/
abbrev linkPolyClosure : Submodule ℝ C(Sph d, ℝ) := (linkPolySpan β e).topologicalClosure

theorem span_le_closure : linkPolySpan β e ≤ linkPolyClosure β e :=
  Submodule.le_topologicalClosure _

theorem isClosed_closure : IsClosed (linkPolyClosure β e : Set C(Sph d, ℝ)) :=
  Submodule.isClosed_topologicalClosure _

/-- If `f ↦ T f` is continuous and maps the span into `W`, it maps `W` into `W`. -/
theorem map_closure_mem {T : C(Sph d, ℝ) → C(Sph d, ℝ)} (hT : Continuous T)
    (h : ∀ f ∈ linkPolySpan β e, T f ∈ linkPolyClosure β e) {f : C(Sph d, ℝ)}
    (hf : f ∈ linkPolyClosure β e) : T f ∈ linkPolyClosure β e := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hf
  have := map_mem_closure hT hf (t := (linkPolyClosure β e : Set C(Sph d, ℝ))) h
  rwa [(isClosed_closure β e).closure_eq] at this

/-- **`W` is stable under multiplication by `G(r_a²)`** for every continuous `G`. -/
theorem mul_comp_tA_mem (G : C(ℝ, ℝ)) (a : κ) {f : C(Sph d, ℝ)}
    (hf : f ∈ linkPolyClosure β e) : f * G.comp (tA e a) ∈ linkPolyClosure β e := by
  refine map_closure_mem β e (T := fun f => f * G.comp (tA e a)) (continuous_id.mul continuous_const)
    (fun f hf => ?_) hf
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  intro δ hδ
  set C := ‖f‖ + 1
  have hC : 0 < C := by positivity
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn 0 1 G G.continuous.continuousOn
    (δ / (2 * C)) (by positivity)
  refine ⟨f * P.toContinuousMap.comp (tA e a), mul_poly_tA_mem_span β e hf a P, ?_⟩
  rw [dist_eq_norm, ← mul_sub]
  have hb : ‖G.comp (tA e a) - P.toContinuousMap.comp (tA e a)‖ ≤ δ / (2 * C) := by
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun w => ?_
    simp only [ContinuousMap.sub_apply, ContinuousMap.comp_apply, Polynomial.toContinuousMap_apply,
      Real.norm_eq_abs]
    rw [abs_sub_comm]
    exact (hP _ (tA_mem_Icc e a w)).le
  calc ‖f * (G.comp (tA e a) - P.toContinuousMap.comp (tA e a))‖
      ≤ ‖f‖ * ‖G.comp (tA e a) - P.toContinuousMap.comp (tA e a)‖ := norm_mul_le _ _
    _ ≤ C * (δ / (2 * C)) :=
        mul_le_mul (by simp [C]) hb (norm_nonneg _) hC.le
    _ < δ := by
        rw [show C * (δ / (2 * C)) = δ / 2 by field_simp]
        linarith

theorem mul_prod_comp_tA_mem (G : κ → C(ℝ, ℝ)) (s : Finset κ) {f : C(Sph d, ℝ)}
    (hf : f ∈ linkPolyClosure β e) :
    f * ∏ a ∈ s, (G a).comp (tA e a) ∈ linkPolyClosure β e := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hf
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, show f * ((G a).comp (tA e a) * ∏ a ∈ s, (G a).comp (tA e a)) =
      (f * ∏ a ∈ s, (G a).comp (tA e a)) * (G a).comp (tA e a) by ring]
    exact mul_comp_tA_mem β e (G a) a ih

end Closure

end ConicalKahler.Sobolev
