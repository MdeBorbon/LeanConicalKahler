module

public import ConicalKahler.Sobolev.ConePoly
public import ConicalKahler.Sobolev.ExplicitHarmonic
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Cone polynomials as functions on the real model

For angular data `k : κ → ℕ`, `ε : κ → Bool` and a polynomial `p ∈ ℝ[t_a, s_i]`, the **cone
polynomial**

  `conePoly β k ε p (y) = ∏_a r_a^{k_a/β_a} (cos | sin)(k_a θ_a) · p(r_1², …, r_n², s)`

is a function on the real model (`modeFn`, `modeProd`, `polyArg`). This file establishes:

* linearity in `p`, the rule `conePoly(ρ² p) = |y|² conePoly(p)` (`conePoly_rhoSq_mul`);
* **homogeneity**: for `p` of weighted degree `m`, `conePoly p` is homogeneous of degree
  `∑_a k_a/β_a + m` (`conePoly_smul`);
* **the Laplacian**: at every regular point, `Δ conePoly(p) = conePoly(L_q p)` with
  `q_a = 1 + k_a/β_a` (`paperLaplacian_conePoly`). The proof expands `p` into monomials, whose
  polar expressions are products of one-variable functions (`prodFn`, `paperLaplacian_prodFn`);
* **harmonicity**: if `L_q p = 0` and `β_a ≤ 1`, then `conePoly p` is classically harmonic in
  the sense of `IsClassicalHarmonic`, hence weakly harmonic on every bounded open set
  (`isClassicalHarmonic_conePoly`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set MvPolynomial
open scoped ContDiff

namespace ConicalKahler.Sobolev

open RealConeModel

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-! ### Definitions -/

/-- `cos` or `sin`. -/
def trigB (ε : Bool) (x : ℝ) : ℝ := bif ε then Real.cos x else Real.sin x

/-- `r^{k/b} cos kθ` (`ε = true`) or `r^{k/b} sin kθ` (`ε = false`) in the coordinate `w` of a
cone factor. -/
def modeFn (b : ℝ) (k : ℕ) (ε : Bool) (w : ℂ) : ℝ := bif ε then harmCosC b k w else harmSinC b k w

/-- The angular factor `∏_a r_a^{k_a/β_a} (cos | sin)(k_a θ_a)`. -/
def modeProd (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool) (y : RealConeModel κ ι) : ℝ :=
  ∏ a, modeFn (β a).beta (k a) (ε a) (y.cone a)

/-- The arguments `(r_a², s_i)` of the polynomial factor. -/
def polyArg (y : RealConeModel κ ι) : κ ⊕ ι → ℝ := Sum.elim (fun a => ‖y.cone a‖ ^ 2) y.eucl

/-- **The cone polynomial** `∏_a r_a^{k_a/β_a} (cos | sin)(k_a θ_a) · p(r², s)`. -/
def conePoly (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool) (p : MvPolynomial (κ ⊕ ι) ℝ)
    (y : RealConeModel κ ι) : ℝ :=
  modeProd β k ε y * eval (polyArg y) p

/-- The mode constants `q_a = 1 + k_a/β_a` of the formal Laplacian. -/
def modeQ (β : κ → ConeAngle) (k : κ → ℕ) (a : κ) : ℝ := 1 + (k a : ℝ) / (β a).beta

/-- The angular degree `∑_a k_a/β_a`. -/
def modeDeg (β : κ → ConeAngle) (k : κ → ℕ) : ℝ := ∑ a, (k a : ℝ) / (β a).beta

theorem modeDeg_nonneg (β : κ → ConeAngle) (k : κ → ℕ) : 0 ≤ modeDeg β k :=
  Finset.sum_nonneg fun a _ => div_nonneg (Nat.cast_nonneg _) (β a).pos.le

theorem fischerConst_modeQ_pos (β : κ → ConeAngle) (k : κ → ℕ) (hne : Nonempty (κ ⊕ ι)) :
    0 < fischerConst ι (modeQ β k) := by
  unfold fischerConst modeQ
  have h1 : ∀ a, 0 < 1 + (k a : ℝ) / (β a).beta := fun a =>
    add_pos_of_pos_of_nonneg one_pos (div_nonneg (Nat.cast_nonneg _) (β a).pos.le)
  rcases hne with ⟨a⟩ | ⟨i⟩
  · have : 0 < ∑ a, (1 + (k a : ℝ) / (β a).beta) :=
      Finset.sum_pos (fun a _ => h1 a) ⟨a, Finset.mem_univ a⟩
    positivity
  · have : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)
    have : 0 ≤ ∑ a, (1 + (k a : ℝ) / (β a).beta) := Finset.sum_nonneg fun a _ => (h1 a).le
    positivity

/-! ### Linearity, `ρ²` and homogeneity -/

theorem conePoly_add (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool)
    (p p' : MvPolynomial (κ ⊕ ι) ℝ) :
    conePoly β k ε (p + p') = conePoly β k ε p + conePoly β k ε p' := by
  funext y
  simp [conePoly, mul_add]

theorem conePoly_smul (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool) (c : ℝ)
    (p : MvPolynomial (κ ⊕ ι) ℝ) : conePoly β k ε (c • p) = c • conePoly β k ε p := by
  funext y
  simp only [conePoly, smul_eval, Pi.smul_apply, smul_eq_mul]
  ring

/-- The cone polynomials of fixed angular data, as a linear map in `p`. -/
def conePolyL (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool) :
    MvPolynomial (κ ⊕ ι) ℝ →ₗ[ℝ] (RealConeModel κ ι → ℝ) where
  toFun := conePoly β k ε
  map_add' := conePoly_add β k ε
  map_smul' := conePoly_smul β k ε

theorem eval_rhoSq_polyArg (y : RealConeModel κ ι) :
    eval (polyArg y) (rhoSq (κ := κ) (ι := ι)) = ‖y‖ ^ 2 := by
  rw [norm_sq_eq]
  simp [rhoSq, polyArg]

/-- `conePoly(ρ² p) = |y|² conePoly(p)`. -/
theorem conePoly_rhoSq_mul (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool)
    (p : MvPolynomial (κ ⊕ ι) ℝ) (y : RealConeModel κ ι) :
    conePoly β k ε (rhoSq * p) y = ‖y‖ ^ 2 * conePoly β k ε p y := by
  rw [conePoly, conePoly, eval_mul, eval_rhoSq_polyArg]
  ring

theorem conePoly_rhoSq_pow_mul (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool)
    (p : MvPolynomial (κ ⊕ ι) ℝ) (j : ℕ) (y : RealConeModel κ ι) :
    conePoly β k ε (rhoSq ^ j * p) y = (‖y‖ ^ 2) ^ j * conePoly β k ε p y := by
  rw [conePoly, conePoly, eval_mul, eval_pow, eval_rhoSq_polyArg]
  ring

/-- Scaling a weighted homogeneous polynomial. -/
theorem eval_weight_smul {σ : Type} [Fintype σ] {w : σ → ℕ} {p : MvPolynomial σ ℝ} {m : ℕ}
    (hp : IsWeightedHomogeneous w p m) (t : ℝ) (x : σ → ℝ) :
    eval (fun v => t ^ w v * x v) p = t ^ m * eval x p := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw := hp (mem_support_iff.mp hd)
  rw [Finsupp.weight_eq_sum] at hw
  simp_rw [mul_pow, ← pow_mul, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hw]
  simp only [smul_eq_mul, mul_comm (d _) (w _)]
  ring

theorem modeFn_smul (b : ℝ) (k : ℕ) (ε : Bool) {t : ℝ} (ht : 0 < t) (w : ℂ) :
    modeFn b k ε (t • w) = t ^ ((k : ℝ) / b) * modeFn b k ε w := by
  cases ε
  · exact harmSinC_smul b k ht w
  · exact harmCosC_smul b k ht w

theorem modeFn_ofReal_mul (b : ℝ) (k : ℕ) (ε : Bool) {t : ℝ} (ht : 0 < t) (w : ℂ) :
    modeFn b k ε ((t : ℂ) * w) = t ^ ((k : ℝ) / b) * modeFn b k ε w := by
  rw [← Complex.real_smul]
  exact modeFn_smul b k ε ht w

theorem polyArg_smul {t : ℝ} (ht : 0 < t) (y : RealConeModel κ ι) :
    polyArg (t • y) = fun v => t ^ polyWt v * polyArg y v := by
  funext v
  rcases v with a | i
  · simp [polyArg, mul_pow, abs_of_pos ht]
  · simp [polyArg]

/-- **Cone polynomials are homogeneous**: degree `∑ k_a/β_a + m` for `p` of weighted degree
`m`. -/
theorem conePoly_smul_point (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool)
    {p : MvPolynomial (κ ⊕ ι) ℝ} {m : ℕ} (hp : IsWeightedHomogeneous polyWt p m) {t : ℝ}
    (ht : 0 < t) (y : RealConeModel κ ι) :
    conePoly β k ε p (t • y) = t ^ (modeDeg β k + m) * conePoly β k ε p y := by
  rw [conePoly, conePoly, polyArg_smul ht, eval_weight_smul hp, modeProd, modeProd]
  simp only [cone_smul, modeFn_ofReal_mul _ _ _ ht, Finset.prod_mul_distrib]
  rw [← Real.rpow_sum_of_pos ht, Real.rpow_add ht, Real.rpow_natCast, modeDeg]
  ring

/-! ### Continuity and smoothness -/

theorem continuous_modeFn {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (k : ℕ) (ε : Bool) :
    Continuous (modeFn b k ε) := by
  have hexp : 0 ≤ (k : ℝ) / b - k := by
    rw [sub_nonneg, le_div_iff₀ hb]
    exact mul_le_of_le_one_right (Nat.cast_nonneg k) hb1
  have h := (Real.continuous_rpow_const hexp).comp (continuous_norm : Continuous fun w : ℂ => ‖w‖)
  cases ε
  · exact h.mul (Complex.continuous_im.comp (continuous_pow k))
  · exact h.mul (Complex.continuous_re.comp (continuous_pow k))

theorem continuous_polyArg (v : κ ⊕ ι) :
    Continuous fun y : RealConeModel κ ι => polyArg y v := by
  rcases v with a | i
  · exact (continuous_norm.comp (continuous_cone a)).pow 2
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (Sum.inr i : RealConeIndex κ ι)).continuous

theorem contDiff_polyArg {n : WithTop ℕ∞} (v : κ ⊕ ι) :
    ContDiff ℝ n fun y : RealConeModel κ ι => polyArg y v := by
  rcases v with a | i
  · exact (contDiff_norm_sq ℝ).comp (coneProj (ι := ι) a).contDiff
  · exact contDiff_eucl i

/-- Polynomials of smooth functions are smooth. -/
theorem contDiff_eval_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {σ : Type}
    {n : WithTop ℕ∞} {g : E → σ → ℝ} (hg : ∀ v, ContDiff ℝ n fun y => g y v)
    (p : MvPolynomial σ ℝ) : ContDiff ℝ n fun y => eval (g y) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p v hp => simpa using hp.mul (hg v)

theorem contDiff_eval_polyArg {n : WithTop ℕ∞} (p : MvPolynomial (κ ⊕ ι) ℝ) :
    ContDiff ℝ n fun y : RealConeModel κ ι => eval (polyArg y) p :=
  contDiff_eval_comp contDiff_polyArg p

theorem continuous_conePoly {β : κ → ConeAngle} (hβ : ∀ a, (β a).beta ≤ 1) (k : κ → ℕ)
    (ε : κ → Bool) (p : MvPolynomial (κ ⊕ ι) ℝ) : Continuous (conePoly β k ε p) :=
  (continuous_finsetProd _ fun a _ =>
    (continuous_modeFn (β a).pos (hβ a) (k a) (ε a)).comp (continuous_cone a)).mul
    (contDiff_eval_polyArg (n := 0) p).continuous

/-! ### Polar coordinates: products of one-variable functions -/

/-- A product `∏_v u_v(c_v)` of one-variable functions of the polar coordinates. -/
def prodFn (u : ConeVar κ ι → ℝ → ℝ) (c : PolarPoint κ ι) : ℝ := ∏ v, u v (c v)

theorem prodFn_update (u : ConeVar κ ι → ℝ → ℝ) (v : ConeVar κ ι) (f : ℝ → ℝ)
    (c : PolarPoint κ ι) :
    prodFn (Function.update u v f) c = f (c v) * ∏ w ∈ Finset.univ.erase v, u w (c w) := by
  rw [prodFn, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]

theorem prodFn_eq_mul (u : ConeVar κ ι → ℝ → ℝ) (v : ConeVar κ ι) (c : PolarPoint κ ι) :
    prodFn u c = u v (c v) * ∏ w ∈ Finset.univ.erase v, u w (c w) := by
  rw [← prodFn_update u v (u v) c, Function.update_eq_self]

/-- **Coordinate derivatives of products**: `∂_v ∏_w u_w(c_w) = u_v'(c_v) ∏_{w ≠ v} u_w(c_w)`. -/
theorem pd_prodFn (u : ConeVar κ ι → ℝ → ℝ) (v : ConeVar κ ι) :
    pd v (prodFn u) = prodFn (Function.update u v (deriv (u v))) := by
  funext c
  have h : (fun t => prodFn u (Function.update c v t)) =
      fun t => u v t * ∏ w ∈ Finset.univ.erase v, u w (c w) := by
    funext t
    rw [prodFn_eq_mul u v, Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  rw [pd, h, deriv_mul_const_field, prodFn_update]

theorem pd_pd_prodFn (u : ConeVar κ ι → ℝ → ℝ) (v : ConeVar κ ι) :
    pd v (pd v (prodFn u)) = prodFn (Function.update u v (deriv (deriv (u v)))) := by
  rw [pd_prodFn, pd_prodFn, Function.update_idem, Function.update_self]

/-- **The Laplacian of a product of one-variable functions.** -/
theorem paperLaplacian_prodFn (β : κ → ConeAngle) (u : ConeVar κ ι → ℝ → ℝ)
    (c : PolarPoint κ ι) :
    paperLaplacian β (prodFn u) c =
      ∑ a, (prodFn (Function.update u (.r a) (deriv (deriv (u (.r a))))) c +
        (c (.r a))⁻¹ * prodFn (Function.update u (.r a) (deriv (u (.r a)))) c +
        ((β a).beta * c (.r a))⁻¹ ^ 2 *
          prodFn (Function.update u (.θ a) (deriv (deriv (u (.θ a))))) c) +
      ∑ i, prodFn (Function.update u (.s i) (deriv (deriv (u (.s i))))) c := by
  simp only [paperLaplacian, coneLaplacian, pd_prodFn, Function.update_idem, Function.update_self]

/-! ### Cone monomials in polar coordinates -/

/-- The one-variable factors of the polar expression of the cone monomial with exponents `μ`:
`r_a^{k_a/β_a + 2μ_a}`, `(cos | sin)(k_a θ_a)`, `s_i^{μ_i}`. -/
def monoU (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool) (μ : κ ⊕ ι →₀ ℕ) :
    ConeVar κ ι → ℝ → ℝ
  | .r a => fun t => t ^ ((k a : ℝ) / (β a).beta + 2 * (μ (Sum.inl a) : ℝ))
  | .θ a => fun t => trigB (ε a) ((k a : ℝ) * t)
  | .s i => fun t => t ^ μ (Sum.inr i)

theorem modeFn_polarMap (b : ℝ) (k : ℕ) (ε : Bool) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    modeFn b k ε (polarMap (r, θ)) = r ^ ((k : ℝ) / b) * trigB ε ((k : ℝ) * θ) := by
  cases ε
  · simp only [modeFn, trigB, Bool.cond_false]
    rw [harmSinC_polarMap b k hr θ, coneHarmonicSin]
  · simp only [modeFn, trigB, Bool.cond_true]
    rw [harmCosC_polarMap b k hr θ, coneHarmonicCos]

theorem prod_coneVar {M : Type*} [CommMonoid M] (f : ConeVar κ ι → M) :
    ∏ v, f v = (∏ a, f (.r a)) * ((∏ a, f (.θ a)) * ∏ i, f (.s i)) := by
  rw [Fintype.prod_equiv ConeVar.equivSum f (fun x => f (ConeVar.equivSum.symm x))
    (fun v => by rw [Equiv.symm_apply_apply]), Fintype.prod_sum_type, Fintype.prod_sum_type]
  rfl

theorem rpow_add_two_mul {r : ℝ} (hr : 0 < r) (x : ℝ) (n : ℕ) :
    r ^ (x + 2 * (n : ℝ)) = r ^ x * (r ^ 2) ^ n := by
  rw [Real.rpow_add hr, ← pow_mul, ← Real.rpow_natCast r (2 * n)]
  push_cast
  ring_nf

/-- **The polar expression of a cone monomial** at regular points. -/
theorem conePoly_monomial_toModel (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool)
    (μ : κ ⊕ ι →₀ ℕ) {c : PolarPoint κ ι} (hc : c ∈ regularPolar κ ι) :
    conePoly β k ε (monomial μ 1) c.toModel = prodFn (monoU β k ε μ) c := by
  rw [conePoly, eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_sum_type, prodFn, prod_coneVar, modeProd]
  have hr : ∀ a, monoU β k ε μ (.r a) (c (.r a)) =
      c (.r a) ^ ((k a : ℝ) / (β a).beta) * (c (.r a) ^ 2) ^ μ (Sum.inl a) := fun a =>
    rpow_add_two_mul (hc a) _ _
  have hm : ∀ a, modeFn (β a).beta (k a) (ε a) (polarMap (c (.r a), c (.θ a))) =
      c (.r a) ^ ((k a : ℝ) / (β a).beta) * trigB (ε a) ((k a : ℝ) * c (.θ a)) := fun a =>
    modeFn_polarMap _ _ _ (hc a) _
  have hn : ∀ a, ‖polarMap (c (.r a), c (.θ a))‖ = c (.r a) := fun a => by
    rw [norm_polarMap, abs_of_pos (hc a)]
  simp only [polyArg, Sum.elim_inl, Sum.elim_inr, PolarPoint.cone_toModel, PolarPoint.eucl_toModel,
    hn, hm, hr, Finset.prod_mul_distrib]
  simp only [monoU]
  ring

/-! ### The Laplacian of a cone monomial -/

theorem deriv_npow_fun (n : ℕ) : deriv (fun t : ℝ => t ^ n) = fun t => (n : ℝ) * t ^ (n - 1) :=
  funext fun t => (hasDerivAt_pow n t).deriv

theorem deriv_deriv_npow (n : ℕ) (x : ℝ) :
    deriv (deriv fun t : ℝ => t ^ n) x = (n : ℝ) * (((n - 1 : ℕ) : ℝ) * x ^ (n - 2)) := by
  rw [deriv_npow_fun, deriv_const_mul_field', deriv_npow_fun, Nat.sub_sub]

theorem deriv_deriv_rpow (γ x : ℝ) :
    deriv (deriv fun t : ℝ => t ^ γ) x = γ * ((γ - 1) * x ^ (γ - 1 - 1)) := by
  rw [Real.deriv_rpow_const', deriv_const_mul_field', Real.deriv_rpow_const']

theorem deriv_deriv_trigB (ε : Bool) (K x : ℝ) :
    deriv (deriv fun t => trigB ε (K * t)) x = -K ^ 2 * trigB ε (K * x) := by
  have hl : ∀ t, HasDerivAt (fun t : ℝ => K * t) K t := fun t => by
    simpa using (hasDerivAt_id t).const_mul K
  cases ε
  · have h1 : deriv (fun t => trigB false (K * t)) = fun t => Real.cos (K * t) * K :=
      funext fun t => ((hl t).sin).deriv
    rw [h1]
    have h2 : HasDerivAt (fun t => Real.cos (K * t) * K) (-Real.sin (K * x) * K * K) x :=
      ((hl x).cos).mul_const K
    rw [h2.deriv]
    simp only [trigB, Bool.cond_false]
    ring
  · have h1 : deriv (fun t => trigB true (K * t)) = fun t => -Real.sin (K * t) * K :=
      funext fun t => ((hl t).cos).deriv
    rw [h1]
    have h2 : HasDerivAt (fun t => -Real.sin (K * t) * K) (-(Real.cos (K * x) * K) * K) x :=
      ((hl x).sin).neg.mul_const K
    rw [h2.deriv]
    simp only [trigB, Bool.cond_true]
    ring

theorem monoU_sub_inl_of_ne (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool) (μ : κ ⊕ ι →₀ ℕ)
    (a : κ) {w : ConeVar κ ι} (hw : w ≠ .r a) :
    monoU β k ε (μ - Finsupp.single (Sum.inl a) 1) w = monoU β k ε μ w := by
  rcases w with b | b | i
  · have hb : b ≠ a := fun h => hw (h ▸ rfl)
    simp [monoU, Ne.symm hb]
  · rfl
  · simp [monoU]

theorem monoU_sub_inr_of_ne (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool) (μ : κ ⊕ ι →₀ ℕ)
    (i : ι) {w : ConeVar κ ι} (hw : w ≠ .s i) :
    monoU β k ε (μ - Finsupp.single (Sum.inr i) 2) w = monoU β k ε μ w := by
  rcases w with b | b | j
  · simp [monoU]
  · rfl
  · have hj : j ≠ i := fun h => hw (h ▸ rfl)
    simp [monoU, Ne.symm hj]

theorem prod_erase_monoU_inl (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool) (μ : κ ⊕ ι →₀ ℕ)
    (a : κ) (c : PolarPoint κ ι) :
    ∏ w ∈ Finset.univ.erase (.r a), monoU β k ε (μ - Finsupp.single (Sum.inl a) 1) w (c w) =
      ∏ w ∈ Finset.univ.erase (.r a), monoU β k ε μ w (c w) :=
  Finset.prod_congr rfl fun w hw => by
    rw [monoU_sub_inl_of_ne β k ε μ a (Finset.ne_of_mem_erase hw)]

theorem prod_erase_monoU_inr (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool) (μ : κ ⊕ ι →₀ ℕ)
    (i : ι) (c : PolarPoint κ ι) :
    ∏ w ∈ Finset.univ.erase (.s i), monoU β k ε (μ - Finsupp.single (Sum.inr i) 2) w (c w) =
      ∏ w ∈ Finset.univ.erase (.s i), monoU β k ε μ w (c w) :=
  Finset.prod_congr rfl fun w hw => by
    rw [monoU_sub_inr_of_ne β k ε μ i (Finset.ne_of_mem_erase hw)]

/-- **The Laplacian of a cone monomial** (polar form), at regular points:
`Δ(r^{γ_a} ⋯) = ∑_a 4 μ_a (μ_a + k_a/β_a) (μ - e_a) + ∑_i μ_i (μ_i - 1) (μ - 2 e_i)`. -/
theorem paperLaplacian_monoU (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool) (μ : κ ⊕ ι →₀ ℕ)
    {c : PolarPoint κ ι} (hc : c ∈ regularPolar κ ι) :
    paperLaplacian β (prodFn (monoU β k ε μ)) c =
      ∑ a, 4 * (μ (Sum.inl a) : ℝ) * (μ (Sum.inl a) + (k a : ℝ) / (β a).beta) *
          prodFn (monoU β k ε (μ - Finsupp.single (Sum.inl a) 1)) c +
        ∑ i, (μ (Sum.inr i) : ℝ) * ((μ (Sum.inr i) - 1 : ℕ) : ℝ) *
          prodFn (monoU β k ε (μ - Finsupp.single (Sum.inr i) 2)) c := by
  rw [paperLaplacian_prodFn]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    set u := monoU β k ε μ
    set r := c (.r a)
    have hr : 0 < r := hc a
    set K : ℝ := (k a : ℝ) / (β a).beta
    set γ : ℝ := K + 2 * (μ (Sum.inl a) : ℝ)
    set Er := ∏ w ∈ Finset.univ.erase (.r a), u w (c w)
    set Eθ := ∏ w ∈ Finset.univ.erase (.θ a), u w (c w)
    have hu_r : u (.r a) = fun t => t ^ γ := rfl
    have hu_θ : u (.θ a) = fun t => trigB (ε a) ((k a : ℝ) * t) := rfl
    have hrel : trigB (ε a) ((k a : ℝ) * c (.θ a)) * Eθ = r ^ γ * Er := by
      have h1 := prodFn_eq_mul u (.θ a) c
      have h2 := prodFn_eq_mul u (.r a) c
      rw [h1] at h2
      exact h2
    rw [prodFn_update, prodFn_update, prodFn_update, hu_r, hu_θ, deriv_deriv_rpow,
      Real.deriv_rpow_const', deriv_deriv_trigB]
    simp only
    rw [show -(k a : ℝ) ^ 2 * trigB (ε a) ((k a : ℝ) * c (.θ a)) * Eθ =
      -(k a : ℝ) ^ 2 * (trigB (ε a) ((k a : ℝ) * c (.θ a)) * Eθ) by ring, hrel]
    have hβ : (β a).beta ≠ 0 := (β a).pos.ne'
    have hp1 : r ^ (γ - 1) = r ^ (γ - 1 - 1) * r := by
      rw [← Real.rpow_add_one hr.ne']
      ring_nf
    have hp2 : r ^ γ = r ^ (γ - 1 - 1) * r ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr]
      push_cast
      ring_nf
    rw [prodFn_eq_mul _ (.r a) c, prod_erase_monoU_inl]
    rcases Nat.eq_zero_or_pos (μ (Sum.inl a)) with h0 | hpos
    · have hγ : γ = K := by simp [γ, h0]
      rw [h0, hp1, hp2]
      simp only [Nat.cast_zero, mul_zero, zero_mul]
      rw [hγ]
      simp only [K]
      field_simp
      ring
    · have hm : (monoU β k ε (μ - Finsupp.single (Sum.inl a) 1) (.r a)) r = r ^ (γ - 1 - 1) := by
        simp only [monoU, Finsupp.tsub_apply, Finsupp.single_eq_same]
        congr 1
        rw [Nat.cast_sub (by omega)]
        simp only [γ, K]
        push_cast
        ring
      rw [hm, hp1, hp2]
      simp only [γ, K]
      field_simp
      ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hu_s : monoU β k ε μ (.s i) = fun t => t ^ μ (Sum.inr i) := rfl
    rw [prodFn_update, hu_s, deriv_deriv_npow, prodFn_eq_mul _ (.s i) c, prod_erase_monoU_inr]
    simp only [monoU, Finsupp.tsub_apply, Finsupp.single_eq_same]
    ring

/-! ### The formal Laplacian on monomials -/

theorem single_add_tsub_tsub {σ : Type} [DecidableEq σ] (μ : σ →₀ ℕ) (v : σ) (h : 2 ≤ μ v) :
    Finsupp.single v 1 + (μ - Finsupp.single v 1 - Finsupp.single v 1) =
      μ - Finsupp.single v 1 := by
  ext w
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  split_ifs with hw
  · subst hw
    omega
  · omega

theorem tsub_single_tsub_single {σ : Type} [DecidableEq σ] (μ : σ →₀ ℕ) (v : σ) :
    μ - Finsupp.single v 1 - Finsupp.single v 1 = μ - Finsupp.single v 2 := by
  ext w
  simp only [Finsupp.tsub_apply, Finsupp.single_apply]
  split_ifs <;> omega

/-- **The formal Laplacian of a monomial.** -/
theorem formalLap_monomial (β : κ → ConeAngle) (k : κ → ℕ) (μ : κ ⊕ ι →₀ ℕ) :
    formalLap (modeQ β k) (monomial μ (1 : ℝ)) =
      ∑ a, monomial (μ - Finsupp.single (Sum.inl a) 1)
          (4 * (μ (Sum.inl a) : ℝ) * (μ (Sum.inl a) + (k a : ℝ) / (β a).beta)) +
        ∑ i, monomial (μ - Finsupp.single (Sum.inr i) 2)
          ((μ (Sum.inr i) : ℝ) * ((μ (Sum.inr i) - 1 : ℕ) : ℝ)) := by
  rw [formalLap_apply]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp only [pderiv_monomial, X, monomial_mul_monomial, C_mul_monomial, one_mul,
      Finsupp.tsub_apply, Finsupp.single_eq_same]
    rcases Nat.lt_or_ge (μ (Sum.inl a)) 2 with h | h
    · have h0 : (μ (Sum.inl a) : ℝ) * ((μ (Sum.inl a) - 1 : ℕ) : ℝ) = 0 := by
        rcases Nat.lt_or_ge (μ (Sum.inl a)) 1 with h1 | h1
        · simp [show μ (Sum.inl a) = 0 by omega]
        · simp [show μ (Sum.inl a) - 1 = 0 by omega]
      rw [mul_assoc (4 : ℝ), h0, mul_zero, monomial_zero, zero_add]
      congr 1
      rcases Nat.lt_or_ge (μ (Sum.inl a)) 1 with h1 | h1
      · simp [show μ (Sum.inl a) = 0 by omega]
      · rw [show μ (Sum.inl a) = 1 by omega, modeQ]
        push_cast
        ring
    · rw [single_add_tsub_tsub μ _ h, ← map_add, modeQ, Nat.cast_sub (by omega : 1 ≤ μ (Sum.inl a))]
      congr 1
      push_cast
      ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [pderiv_monomial, one_mul, Finsupp.tsub_apply, Finsupp.single_eq_same,
      tsub_single_tsub_single]

theorem conePoly_monomial (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool) (μ : κ ⊕ ι →₀ ℕ)
    (r : ℝ) : conePoly β k ε (monomial μ r) = r • conePoly β k ε (monomial μ 1) := by
  rw [← conePoly_smul, smul_monomial, smul_eq_mul, mul_one]

theorem contDiff_trigB {n : WithTop ℕ∞} (ε : Bool) (K : ℝ) :
    ContDiff ℝ n fun t => trigB ε (K * t) := by
  cases ε
  · exact Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  · exact Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)

theorem contDiffAt_prodFn_monoU (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool)
    (μ : κ ⊕ ι →₀ ℕ) {c : PolarPoint κ ι} (hc : c ∈ regularPolar κ ι) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (prodFn (monoU β k ε μ)) c := by
  refine contDiffAt_prod (fun v _ => ?_)
  rcases v with a | a | i
  · exact (Real.contDiffAt_rpow_const_of_ne (hc a).ne').comp c
      (contDiff_apply ℝ ℝ (ConeVar.r a)).contDiffAt
  · exact ((contDiff_trigB (ε a) (k a : ℝ)).comp (contDiff_apply ℝ ℝ (ConeVar.θ a))).contDiffAt
  · exact ((contDiff_id.pow _).comp (contDiff_apply ℝ ℝ (ConeVar.s i))).contDiffAt

/-- **The Laplacian of a cone polynomial.** At every regular point,
`Δ conePoly(p) = conePoly(L_q p)` with `q_a = 1 + k_a/β_a`. -/
theorem paperLaplacian_conePoly (β : κ → ConeAngle) (k : κ → ℕ) (ε : κ → Bool)
    (p : MvPolynomial (κ ⊕ ι) ℝ) {c : PolarPoint κ ι} (hc : c ∈ regularPolar κ ι) :
    paperLaplacian β (fun c' => conePoly β k ε p c'.toModel) c =
      conePoly β k ε (formalLap (modeQ β k) p) c.toModel := by
  classical
  have hp : p = ∑ μ ∈ p.support, p.coeff μ • monomial μ (1 : ℝ) := by
    conv_lhs => rw [as_sum p]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [smul_monomial, smul_eq_mul, mul_one]
  have hcp : ∀ q : MvPolynomial (κ ⊕ ι) ℝ, ∀ y : RealConeModel κ ι,
      conePoly β k ε q y = conePolyL β k ε q y := fun _ _ => rfl
  have hsum : conePolyL β k ε p =
      ∑ μ ∈ p.support, p.coeff μ • conePolyL β k ε (monomial μ (1 : ℝ)) := by
    conv_lhs => rw [hp]
    rw [map_sum]
    simp only [map_smul]
  have hsumL : conePolyL β k ε (formalLap (modeQ β k) p) =
      ∑ μ ∈ p.support, p.coeff μ • conePolyL β k ε (formalLap (modeQ β k) (monomial μ (1 : ℝ))) := by
    conv_lhs => rw [hp]
    rw [map_sum, map_sum]
    simp only [map_smul]
  have hev : (fun c' : PolarPoint κ ι => conePoly β k ε p c'.toModel) =ᶠ[𝓝 c]
      fun c' => ∑ μ ∈ p.support, p.coeff μ * prodFn (monoU β k ε μ) c' := by
    filter_upwards [isOpen_regularPolar.mem_nhds hc] with c' hc'
    rw [hcp, hsum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, ← hcp, conePoly_monomial_toModel β k ε μ hc']
  rw [paperLaplacian_congr β hev, paperLaplacian_sum β _ fun μ _ =>
    contDiffAt_const.mul (contDiffAt_prodFn_monoU β k ε μ hc)]
  simp_rw [paperLaplacian_const_mul β (contDiffAt_prodFn_monoU β k ε _ hc),
    paperLaplacian_monoU β k ε _ hc]
  rw [hcp, hsumL, Finset.sum_apply]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, formalLap_monomial, map_add, map_sum,
    map_sum, Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcp, conePoly_monomial, Pi.smul_apply, smul_eq_mul,
      conePoly_monomial_toModel β k ε _ hc]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hcp, conePoly_monomial, Pi.smul_apply, smul_eq_mul,
      conePoly_monomial_toModel β k ε _ hc]

end ConicalKahler.Sobolev
