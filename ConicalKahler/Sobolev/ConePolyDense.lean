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

section Algebra

variable (β : κ → ConeAngle) (e : RealConeIndex κ ι ≃ Fin d)

/-- `t ↦ t^q` as a continuous map, `q ≥ 0`. -/
def rpowCM {q : ℝ} (hq : 0 ≤ q) : C(ℝ, ℝ) := ⟨fun t => t ^ q, Real.continuous_rpow_const hq⟩

/-- **Products of two generators lie in `W`.** -/
theorem linkPoly_mul_mem (k k' : κ → ℕ) (ε ε' : κ → Bool) (p p' : MvPolynomial (κ ⊕ ι) ℝ) :
    linkPoly β e k ε p * linkPoly β e k' ε' p' ∈ linkPolyClosure β e := by
  classical
  choose c₁ c₂ k₁ k₂ m ε₁ hmul using fun a => exists_modeFn_mul (β a).pos (k a) (k' a) (ε a) (ε' a)
  have hq : ∀ a, 0 ≤ (m a : ℝ) / (β a).beta := fun a => div_nonneg (Nat.cast_nonneg _) (β a).pos.le
  set Gf : κ → Bool → C(ℝ, ℝ) := fun a j => bif j then 1 else rpowCM (hq a)
  set Kf : (κ → Bool) → κ → ℕ := fun J a => bif J a then k₁ a else k₂ a
  set Cf : (κ → Bool) → ℝ := fun J => ∏ a, (bif J a then c₁ a else c₂ a)
  have hclaim : linkPoly β e k ε p * linkPoly β e k' ε' p' =
      ∑ J : κ → Bool, Cf J • (linkPoly β e (Kf J) ε₁ (p * p') * ∏ a, (Gf a (J a)).comp (tA e a)) := by
    ext w
    set y := (coordIso e).symm (w : 𝔼)
    simp only [ContinuousMap.mul_apply, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.smul_apply, ContinuousMap.coe_prod, Finset.prod_apply, ContinuousMap.comp_apply,
      linkPoly_apply, smul_eq_mul]
    rw [conePoly, conePoly]
    have hfac : modeProd β k ε y * modeProd β k' ε' y =
        ∏ a, ∑ j : Bool, (bif j then c₁ a * modeFn (β a).beta (k₁ a) (ε₁ a) (y.cone a) else
          c₂ a * modeFn (β a).beta (k₂ a) (ε₁ a) (y.cone a) *
            (‖y.cone a‖ ^ 2) ^ ((m a : ℝ) / (β a).beta)) := by
      rw [modeProd, modeProd, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [hmul a, Fintype.sum_bool]
      simp only [Bool.cond_true, Bool.cond_false]
    have hterm : ∀ J : κ → Bool, ∏ a, (bif J a then c₁ a * modeFn (β a).beta (k₁ a) (ε₁ a) (y.cone a)
        else c₂ a * modeFn (β a).beta (k₂ a) (ε₁ a) (y.cone a) *
          (‖y.cone a‖ ^ 2) ^ ((m a : ℝ) / (β a).beta)) =
        Cf J * (modeProd β (Kf J) ε₁ y * ∏ a, (Gf a (J a)) (tA e a w)) := by
      intro J
      rw [modeProd, ← mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      simp only [Kf, Gf]
      cases J a
      · simp [rpowCM, tA, sphRestrict, y]
      · simp
    calc modeProd β k ε y * eval (polyArg y) p * (modeProd β k' ε' y * eval (polyArg y) p')
        = (modeProd β k ε y * modeProd β k' ε' y) * eval (polyArg y) (p * p') := by
          rw [eval_mul]
          ring
      _ = ∑ J : κ → Bool, Cf J * (modeProd β (Kf J) ε₁ y * eval (polyArg y) (p * p') *
            ∏ a, (Gf a (J a)) (tA e a w)) := by
          rw [hfac, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.sum_mul]
          refine Finset.sum_congr rfl fun J _ => ?_
          rw [hterm J]
          ring
  rw [hclaim]
  refine Submodule.sum_mem _ fun J _ => Submodule.smul_mem _ _ ?_
  exact mul_prod_comp_tA_mem β e (fun a => Gf a (J a)) Finset.univ
    (span_le_closure β e (linkPoly_mem_span β e _ _ _))

theorem span_mul_span_mem {f g : C(Sph d, ℝ)} (hf : f ∈ linkPolySpan β e)
    (hg : g ∈ linkPolySpan β e) : f * g ∈ linkPolyClosure β e := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, ε, p, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨k', ε', p', rfl⟩ := hg
      exact linkPoly_mul_mem β e k k' ε ε' p p'
    | zero => simp
    | add g g' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
    | smul c g _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => simp
  | add f f' _ _ h h' => rw [add_mul]; exact Submodule.add_mem _ h h'
  | smul c f _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

/-- **`W` is closed under multiplication.** -/
theorem closure_mul_mem {f g : C(Sph d, ℝ)} (hf : f ∈ linkPolyClosure β e)
    (hg : g ∈ linkPolyClosure β e) : f * g ∈ linkPolyClosure β e := by
  have h1 : ∀ f ∈ linkPolySpan β e, f * g ∈ linkPolyClosure β e := fun f hf =>
    map_closure_mem β e (T := fun g => f * g) (continuous_const.mul continuous_id)
      (fun g hg => span_mul_span_mem β e hf hg) hg
  exact map_closure_mem β e (T := fun f => f * g) (continuous_id.mul continuous_const) h1 hf

theorem linkPoly_one : linkPoly β e (fun _ => 0) (fun _ => true) (1 : MvPolynomial (κ ⊕ ι) ℝ) = 1 := by
  ext w
  simp [linkPoly_apply, conePoly, modeProd, modeFn_zero]

/-- `W` as a subalgebra of `C(S, ℝ)`. -/
def linkPolyAlg : Subalgebra ℝ C(Sph d, ℝ) where
  carrier := linkPolyClosure β e
  mul_mem' := closure_mul_mem β e
  add_mem' := Submodule.add_mem _
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one, ← linkPoly_one β e]
    exact Submodule.smul_mem _ r (span_le_closure β e (linkPoly_mem_span β e _ _ _))

/-- `ζ(w) = |w|^{1/b - 1} w`, the complex coordinate of a cone factor. -/
def zetaMap (b : ℝ) (w : ℂ) : ℂ := ((‖w‖ ^ (1 / b - 1) : ℝ) : ℂ) * w

theorem norm_zetaMap {b : ℝ} (hb : 0 < b) (w : ℂ) : ‖zetaMap b w‖ = ‖w‖ ^ (1 / b) := by
  by_cases hw : w = 0
  · subst hw
    simp [zetaMap]
    rw [Real.zero_rpow (inv_pos.mpr hb).ne']
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [zetaMap, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hn.le _), ← Real.rpow_add_one hn.ne']
  ring_nf

theorem injective_zetaMap {b : ℝ} (hb : 0 < b) : Function.Injective (zetaMap b) := by
  intro w w' h
  have hn : ‖w‖ = ‖w'‖ := by
    have h1 := norm_zetaMap hb w
    rw [h, norm_zetaMap hb w'] at h1
    exact (Real.rpow_left_injOn (one_div_pos.mpr hb).ne' (norm_nonneg w') (norm_nonneg w) h1).symm
  by_cases hw : w = 0
  · subst hw
    rw [norm_zero, eq_comm, norm_eq_zero] at hn
    exact hn.symm
  have hn0 : (‖w‖ ^ (1 / b - 1) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (norm_pos_iff.mpr hw) _).ne'
  rw [zetaMap, zetaMap, ← hn] at h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hn0) h

theorem harmCosC_one (b : ℝ) (w : ℂ) : harmCosC b 1 w = (zetaMap b w).re := by
  simp [harmCosC, zetaMap, one_div]

theorem harmSinC_one (b : ℝ) (w : ℂ) : harmSinC b 1 w = (zetaMap b w).im := by
  simp [harmSinC, zetaMap, one_div]

theorem modeProd_single (a : κ) (ε : κ → Bool) (hε : ∀ a', a' ≠ a → ε a' = true)
    (y : RealConeModel κ ι) :
    modeProd β (Pi.single a 1) ε y = modeFn (β a).beta 1 (ε a) (y.cone a) := by
  rw [modeProd, Finset.prod_eq_single a (fun a' _ h => by
      rw [Pi.single_eq_of_ne h, modeFn_zero, hε a' h]; rfl) (fun h => (h (Finset.mem_univ a)).elim),
    Pi.single_eq_same]

theorem linkPolyAlg_separatesPoints : (linkPolyAlg β e).SeparatesPoints := by
  intro w w' hww'
  have hy : (coordIso e).symm (w : 𝔼) ≠ (coordIso e).symm (w' : 𝔼) := fun h =>
    hww' (Subtype.ext ((coordIso e).symm.injective h))
  set y := (coordIso e).symm (w : 𝔼)
  set y' := (coordIso e).symm (w' : 𝔼)
  have hmem : ∀ k ε (p : MvPolynomial (κ ⊕ ι) ℝ),
      (⇑(linkPoly β e k ε p)) ∈ (fun f : C(Sph d, ℝ) => (f : Sph d → ℝ)) ''
        (linkPolyAlg β e : Set C(Sph d, ℝ)) := fun k ε p =>
    ⟨_, span_le_closure β e (linkPoly_mem_span β e k ε p), rfl⟩
  by_cases hc : ∀ a, y.cone a = y'.cone a
  · have hi : ∃ i, y.eucl i ≠ y'.eucl i := by
      by_contra! h
      exact hy (ext_cone_eucl hc h)
    obtain ⟨i, hi⟩ := hi
    refine ⟨_, hmem (fun _ => 0) (fun _ => true) (X (Sum.inr i)), ?_⟩
    simpa [linkPoly_apply, conePoly, modeProd, modeFn_zero, polyArg] using hi
  · simp only [not_forall] at hc
    obtain ⟨a, ha⟩ := hc
    have hz : zetaMap (β a).beta (y.cone a) ≠ zetaMap (β a).beta (y'.cone a) := fun h =>
      ha (injective_zetaMap (β a).pos h)
    by_cases hre : (zetaMap (β a).beta (y.cone a)).re = (zetaMap (β a).beta (y'.cone a)).re
    · have him : (zetaMap (β a).beta (y.cone a)).im ≠ (zetaMap (β a).beta (y'.cone a)).im :=
        fun h => hz (Complex.ext hre h)
      refine ⟨_, hmem (Pi.single a 1) (Function.update (fun _ => true) a false) 1, ?_⟩
      simp only [linkPoly_apply, conePoly, map_one, mul_one]
      rw [modeProd_single β a _ (fun a' h => by simp [Function.update_of_ne h]),
        modeProd_single β a _ (fun a' h => by simp [Function.update_of_ne h])]
      simp only [Function.update_self, modeFn, Bool.cond_false]
      rw [harmSinC_one, harmSinC_one]
      exact him
    · refine ⟨_, hmem (Pi.single a 1) (fun _ => true) 1, ?_⟩
      simp only [linkPoly_apply, conePoly, map_one, mul_one]
      rw [modeProd_single β a _ (fun _ _ => rfl), modeProd_single β a _ (fun _ _ => rfl)]
      simp only [modeFn, Bool.cond_true]
      rw [harmCosC_one, harmCosC_one]
      exact hre

/-- **The restrictions of cone polynomials are dense in `C(S)`** (Stone–Weierstrass). -/
theorem dense_linkPolySpan : Dense (linkPolySpan β e : Set C(Sph d, ℝ)) := by
  have h := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (linkPolyAlg_separatesPoints β e)
  have hc : IsClosed (linkPolyAlg β e : Set C(Sph d, ℝ)) := isClosed_closure β e
  have h' : (linkPolyClosure β e : Set C(Sph d, ℝ)) = univ := by
    have := congrArg (fun A : Subalgebra ℝ C(Sph d, ℝ) => (A : Set C(Sph d, ℝ))) h
    simp only [Subalgebra.topologicalClosure_coe, hc.closure_eq, Algebra.coe_top] at this
    exact this
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe]
  exact h'

/-- **The restrictions of cone polynomials span a dense subspace of `L²(S)`.** -/
theorem dense_span_linkPolyLp :
    Dense (Submodule.span ℝ (ContinuousMap.toLp 2 (sphMeasure d) ℝ '' linkPolyGens β e) :
      Set (Lp ℝ 2 (sphMeasure d))) := by
  have hT := ContinuousMap.toLp_denseRange (p := 2) (μ := sphMeasure d) (𝕜 := ℝ) (E := ℝ)
    (α := Sph d) (by norm_num)
  have hD := hT.dense_image (ContinuousMap.toLp 2 (sphMeasure d) ℝ).continuous
    (dense_linkPolySpan β e)
  refine hD.mono ?_
  rintro _ ⟨f, hf, rfl⟩
  have : ContinuousMap.toLp 2 (sphMeasure d) ℝ f ∈
      (linkPolySpan β e).map (ContinuousMap.toLp 2 (sphMeasure d) ℝ (E := ℝ)).toLinearMap :=
    ⟨f, hf, rfl⟩
  rw [linkPolySpan, Submodule.map_span] at this
  exact this

end Algebra

end ConicalKahler.Sobolev
