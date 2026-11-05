module

public import ConicalKahler.Sobolev.ConeLaplacian
public import ConicalKahler.Real.D2

/-!
# The divergence-form operator `div(g⁻¹ ∇u)` is the paper's Laplacian

The weak formulation used since Milestone 9 is `-div(A ∇u) = f` with `A = g⁻¹` (`coneInvOp`,
`coneCoeff`). Here we check that on smooth functions **away from the singular set** this operator
is the paper's Laplacian `Δ = ∑_a Δ_{β_a} + Δ_{ℝ^ι}` (`paperLaplacian`), written in the polar
coordinates `(r_a, θ_a, s_i)`. By `laplaceBeltrami_eq_half_coneLaplacian` (Milestone 8) this is in
turn `2 Δ_g`, twice the Laplace–Beltrami operator of the Kähler cone metric (for one factor).

## Method

On the regular part, `g⁻¹ = I + ∑_a (β_a⁻² - 1) P_a`, where `P_a` is the orthogonal projection onto
the rotation field `J_a y` of the factor `a` (`coneInvOp_eq_add_sum`). So
`g⁻¹ ∇u = ∇u + ∑_a (β_a⁻² - 1) h_a(y) J_a y` with `h_a = (∂_{θ_a} u) / r_a²`. Since `J_a` is skew
(`tr J_a = 0`),

  `div(g⁻¹ ∇u) = Δ_E u + ∑_a (β_a⁻² - 1) r_a⁻² ∂²_{θ_a} u`.

The Euclidean Laplacian of a factor in polar coordinates is `∂²_r + r⁻¹ ∂_r + r⁻² ∂²_θ`. Both are
computed from second derivatives along the coordinate curves `t ↦ toModel (c[k := t])`
(`deriv_deriv_comp_curve`).

## Results

* `divergence V x = ∑_k ∂_k V_k (x)`, the Euclidean divergence (trace of `DV(x)`).
* `divergence_coneInvOp_gradient`: **for `u` of class `C²` near a regular point with polar
  coordinates `c` (`r_a > 0`), `div(g⁻¹ ∇u) = paperLaplacian β (u ∘ toModel) c`.**
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set
open scoped ContDiff ENNReal ComplexConjugate Real

namespace ConicalKahler.Sobolev

open RealConeModel

/-! ### Second derivatives along curves -/

section Curve

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Second derivative along a curve.** If `u` is `C²` at `p = γ(t₀)`, then `(u ∘ γ)'(t) =
Du(γ t)(γ' t)` near `t₀`, and this has derivative `D²u(p)(γ', γ') + Du(p)(γ'')` at `t₀`. -/
theorem hasDerivAt_fderiv_comp_curve {u : X → ℝ} {p : X} (hu : ContDiffAt ℝ 2 u p)
    {γ γ' : ℝ → X} {γ'' : X} {t₀ : ℝ} (hγ0 : γ t₀ = p)
    (hγ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (γ' t) t) (hγ' : HasDerivAt γ' γ'' t₀) :
    (deriv (fun t => u (γ t)) =ᶠ[𝓝 t₀] fun t => fderiv ℝ u (γ t) (γ' t)) ∧
      HasDerivAt (fun t => fderiv ℝ u (γ t) (γ' t))
        (fderiv ℝ (fderiv ℝ u) p (γ' t₀) (γ' t₀) + fderiv ℝ u p γ'') t₀ := by
  have hcont : ContinuousAt γ t₀ := hγ.self_of_nhds.continuousAt
  have hev : ∀ᶠ y in 𝓝 p, DifferentiableAt ℝ u y :=
    (hu.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  rw [← hγ0] at hev
  have hevt : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ u (γ t) := hcont.eventually hev
  refine ⟨?_, ?_⟩
  · filter_upwards [hevt, hγ] with t h1 h2
    exact (h1.hasFDerivAt.comp_hasDerivAt t h2).deriv
  · have hD : DifferentiableAt ℝ (fderiv ℝ u) p :=
      (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    rw [← hγ0] at hD ⊢
    have h1 : HasDerivAt (fun t => fderiv ℝ u (γ t)) (fderiv ℝ (fderiv ℝ u) (γ t₀) (γ' t₀)) t₀ :=
      hD.hasFDerivAt.comp_hasDerivAt t₀ hγ.self_of_nhds
    exact h1.clm_apply hγ'

theorem deriv_deriv_comp_curve {u : X → ℝ} {p : X} (hu : ContDiffAt ℝ 2 u p)
    {γ γ' : ℝ → X} {γ'' : X} {t₀ : ℝ} (hγ0 : γ t₀ = p)
    (hγ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (γ' t) t) (hγ' : HasDerivAt γ' γ'' t₀) :
    deriv (deriv fun t => u (γ t)) t₀ =
      fderiv ℝ (fderiv ℝ u) p (γ' t₀) (γ' t₀) + fderiv ℝ u p γ'' := by
  obtain ⟨h1, h2⟩ := hasDerivAt_fderiv_comp_curve hu hγ0 hγ hγ'
  rw [h1.deriv_eq, h2.deriv]

end Curve

/-! ### Coordinate maps of the real model -/

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-- The `a`-th cone coordinate as a continuous `ℝ`-linear map `RealConeModel κ ι → ℂ`. -/
def coneProj (a : κ) : RealConeModel κ ι →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => q.cone a
      map_add' := fun q w => cone_add q w a
      map_smul' := fun t q => by rw [cone_smul, RingHom.id_apply, Complex.real_smul] }

@[simp] theorem coneProj_apply (a : κ) (q : RealConeModel κ ι) : coneProj a q = q.cone a := rfl

/-- The inclusion of the `a`-th cone factor `ℂ → RealConeModel κ ι`. -/
def coneIncl (a : κ) : ℂ →L[ℝ] RealConeModel κ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => ofCones (Pi.single a z) 0
      map_add' := fun z w => ext_cone_eucl (fun b => by
          by_cases h : b = a
          · subst h; simp
          · simp [h]) fun i => by simp
      map_smul' := fun t z => ext_cone_eucl (fun b => by
          by_cases h : b = a
          · subst h; simp [Complex.real_smul]
          · simp [h]) fun i => by simp }

@[simp] theorem cone_coneIncl (a b : κ) (z : ℂ) :
    (coneIncl (ι := ι) a z).cone b = if b = a then z else 0 := by
  simp [coneIncl, Pi.single_apply]

@[simp] theorem eucl_coneIncl (a : κ) (z : ℂ) (i : ι) : (coneIncl (ι := ι) a z).eucl i = 0 := by
  simp [coneIncl]

/-- The rotation field of the factor `a`: `J_a q` multiplies the `a`-th cone coordinate by `i`
and kills the others. -/
def rotJ (a : κ) : RealConeModel κ ι →L[ℝ] RealConeModel κ ι :=
  (coneIncl a).comp ((ContinuousLinearMap.mul ℝ ℂ Complex.I).comp (coneProj a))

theorem rotJ_apply (a : κ) (q : RealConeModel κ ι) :
    rotJ a q = coneIncl a (Complex.I * q.cone a) := rfl

@[simp] theorem cone_rotJ (a b : κ) (q : RealConeModel κ ι) :
    (rotJ a q).cone b = if b = a then Complex.I * q.cone a else 0 := by
  rw [rotJ_apply, cone_coneIncl]

@[simp] theorem eucl_rotJ (a : κ) (q : RealConeModel κ ι) (i : ι) : (rotJ a q).eucl i = 0 := by
  rw [rotJ_apply, eucl_coneIncl]

theorem inner_rotJ (a : κ) (w q : RealConeModel κ ι) :
    ⟪w, rotJ a q⟫_ℝ = ⟪w.cone a, Complex.I * q.cone a⟫_ℝ := by
  rw [inner_eq_cone_eucl]
  simp only [cone_rotJ, eucl_rotJ, mul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single a (fun b _ hb => by rw [ite_eq_right hb, inner_zero_right])
    (by simp), ite_eq_left rfl]

/-- **`J_a` is skew:** `⟨J_a q, q⟩ = 0`. -/
theorem inner_rotJ_self (a : κ) (q : RealConeModel κ ι) : ⟪rotJ a q, q⟫_ℝ = 0 := by
  rw [real_inner_comm, inner_rotJ, Complex.inner]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.I_re,
    Complex.I_im]
  ring

theorem cone_sum {α : Type*} (s : Finset α) (v : α → RealConeModel κ ι) (b : κ) :
    (∑ x ∈ s, v x).cone b = ∑ x ∈ s, (v x).cone b :=
  map_sum (coneProj (ι := ι) b) v s

theorem eucl_sum {α : Type*} (s : Finset α) (v : α → RealConeModel κ ι) (i : ι) :
    (∑ x ∈ s, v x).eucl i = ∑ x ∈ s, (v x).eucl i := by
  exact map_sum (EuclideanSpace.proj (𝕜 := ℝ) (Sum.inr i : RealConeIndex κ ι)) v s

/-! ### `g⁻¹ = I + ∑_a (β_a⁻² - 1) P_a` on the regular part -/

theorem coneInvFactor_eq_add (b : ℝ) {w : ℂ} (hw : w ≠ 0) (z : ℂ) :
    coneInvFactor b w z =
      z + ((b⁻¹ ^ 2 - 1) * (⟪z, Complex.I * w⟫_ℝ / ‖w‖ ^ 2)) • (Complex.I * w) := by
  have hn : w.re ^ 2 + w.im ^ 2 ≠ 0 := by
    have := Complex.normSq_eq_zero.not.mpr hw
    rwa [Complex.normSq_apply, ← sq, ← sq] at this
  rw [Complex.inner, Complex.sq_norm, Complex.normSq_apply]
  apply Complex.ext <;>
    simp only [coneInvFactor, Complex.real_smul, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.conj_re, Complex.conj_im, Complex.normSq_apply] <;>
    field_simp <;> ring

/-- **`g⁻¹ ξ = ξ + ∑_a (β_a⁻² - 1) ⟨ξ, J_a y⟩ / r_a² · J_a y`** at regular points `y`. -/
theorem coneInvOp_eq_add_sum (β : κ → ConeAngle) {y : RealConeModel κ ι}
    (hy : ∀ a, y.cone a ≠ 0) (ξ : RealConeModel κ ι) :
    coneInvOp β y ξ = ξ + ∑ a, (((β a).beta⁻¹ ^ 2 - 1) *
      (⟪ξ, rotJ a y⟫_ℝ / ‖y.cone a‖ ^ 2)) • rotJ a y := by
  refine ext_cone_eucl (fun b => ?_) (fun i => ?_)
  · rw [cone_add, cone_sum]
    simp only [cone_smul, cone_rotJ, mul_ite, mul_zero]
    rw [Finset.sum_eq_single b (fun a _ hab => by rw [ite_eq_right (Ne.symm hab)]) (by simp),
      ite_eq_left rfl, inner_rotJ]
    simp only [coneInvOp, LinearMap.coe_toContinuousLinearMap', coneInvOpₗ, LinearMap.coe_mk,
      AddHom.coe_mk, cone_ofCones]
    rw [coneInvFactor_eq_add _ (hy b), Complex.real_smul]
  · rw [eucl_add, eucl_sum]
    simp [coneInvOp, coneInvOpₗ]

theorem isOpen_regular : IsOpen {y : RealConeModel κ ι | ∀ a, y.cone a ≠ 0} := by
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun a => isOpen_ne_fun (continuous_cone a) continuous_const

/-! ### The polar coordinate curves -/

/-- The unit radial vector `e_r` of the factor `a` at the angle `θ`. -/
def radialVec (a : κ) (θ : ℝ) : RealConeModel κ ι := coneIncl a (Complex.exp (θ * Complex.I))

/-- The unit angular vector `e_θ` of the factor `a` at the angle `θ`. -/
def angularVec (a : κ) (θ : ℝ) : RealConeModel κ ι :=
  coneIncl a (Complex.I * Complex.exp (θ * Complex.I))

theorem toModel_update_r (c : PolarPoint κ ι) (a : κ) (t : ℝ) :
    PolarPoint.toModel (Function.update c (.r a) t) = c.toModel + (t - c (.r a)) • radialVec a (c (.θ a)) := by
  refine ext_cone_eucl (fun b => ?_) (fun i => ?_)
  · rw [cone_add, cone_smul, radialVec, cone_coneIncl, PolarPoint.cone_toModel,
      PolarPoint.cone_toModel]
    by_cases h : b = a
    · subst h
      simp only [Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true,
        Function.update_of_ne, ite_true, polarMap]
      push_cast
      ring
    · simp [h]
  · simp [radialVec]

theorem toModel_update_θ (c : PolarPoint κ ι) (a : κ) (t : ℝ) :
    PolarPoint.toModel (Function.update c (.θ a) t) =
      c.toModel + coneIncl a (polarMap (c (.r a), t) - polarMap (c (.r a), c (.θ a))) := by
  refine ext_cone_eucl (fun b => ?_) (fun i => ?_)
  · rw [cone_add, cone_coneIncl, PolarPoint.cone_toModel, PolarPoint.cone_toModel]
    by_cases h : b = a
    · subst h
      simp only [Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true,
        Function.update_of_ne, ite_true]
      ring
    · simp [h]
  · simp

theorem toModel_update_s (c : PolarPoint κ ι) (i : ι) (t : ℝ) :
    PolarPoint.toModel (Function.update c (.s i) t) =
      c.toModel + (t - c (.s i)) • (EuclideanSpace.single (Sum.inr i) 1 : RealConeModel κ ι) := by
  refine ext_cone_eucl (fun b => ?_) (fun j => ?_)
  · rw [cone_add, cone_smul, cone_single_inr]
    simp
  · rw [eucl_add, eucl_smul, eucl_single_inr]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]

theorem pd_pd (k : ConeVar κ ι) (U : PolarPoint κ ι → ℝ) (c : PolarPoint κ ι) :
    pd k (pd k U) c = deriv (deriv fun t => U (Function.update c k t)) (c k) := by
  simp only [pd, Function.update_idem, Function.update_self]

theorem hasDerivAt_polarMap_snd (r t : ℝ) :
    HasDerivAt (fun t : ℝ => polarMap (r, t))
      ((r : ℂ) * (Complex.exp (t * Complex.I) * Complex.I)) t := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).cexp.const_mul (r : ℂ)
  simpa [polarMap] using h

theorem polarMap_mul_I (r t : ℝ) :
    (r : ℂ) * (Complex.exp (t * Complex.I) * Complex.I) = polarMap (r, t) * Complex.I := by
  simp only [polarMap]
  ring

/-! ### Polar second derivatives of a `C²` function -/

section Polar

variable {u : RealConeModel κ ι → ℝ} {c : PolarPoint κ ι}

theorem pd_r_eq (hu : ContDiffAt ℝ 2 u c.toModel) (a : κ) :
    pd (.r a) (fun c' : PolarPoint κ ι => u c'.toModel) c =
      fderiv ℝ u c.toModel (radialVec a (c (.θ a))) := by
  simp only [pd]
  simp_rw [toModel_update_r]
  have hγ : HasDerivAt (fun t : ℝ => c.toModel + (t - c (.r a)) • radialVec a (c (.θ a)))
      (radialVec a (c (.θ a))) (c (.r a)) := by
    simpa using (((hasDerivAt_id (c (.r a))).sub_const (c (.r a))).smul_const
      (radialVec (ι := ι) a (c (.θ a)))).const_add c.toModel
  exact ((hu.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq (c (.r a)) hγ
    (by simp)).deriv

theorem pd_r_pd_r_eq (hu : ContDiffAt ℝ 2 u c.toModel) (a : κ) :
    pd (.r a) (pd (.r a) fun c' : PolarPoint κ ι => u c'.toModel) c =
      fderiv ℝ (fderiv ℝ u) c.toModel (radialVec a (c (.θ a))) (radialVec a (c (.θ a))) := by
  rw [pd_pd]
  simp_rw [toModel_update_r]
  rw [deriv_deriv_comp_curve hu (γ' := fun _ => radialVec a (c (.θ a))) (γ'' := 0) (by simp)
    (Eventually.of_forall fun t => by
      simpa using (((hasDerivAt_id t).sub_const (c (.r a))).smul_const
        (radialVec (ι := ι) a (c (.θ a)))).const_add c.toModel)
    (hasDerivAt_const _ _), map_zero, add_zero]

theorem pd_s_pd_s_eq (hu : ContDiffAt ℝ 2 u c.toModel) (i : ι) :
    pd (.s i) (pd (.s i) fun c' : PolarPoint κ ι => u c'.toModel) c =
      fderiv ℝ (fderiv ℝ u) c.toModel (EuclideanSpace.single (Sum.inr i) 1)
        (EuclideanSpace.single (Sum.inr i) 1) := by
  rw [pd_pd]
  simp_rw [toModel_update_s]
  rw [deriv_deriv_comp_curve hu (γ' := fun _ => EuclideanSpace.single (Sum.inr i) 1) (γ'' := 0)
    (by simp) (Eventually.of_forall fun t => by
      simpa using (((hasDerivAt_id t).sub_const (c (.s i))).smul_const
        (EuclideanSpace.single (Sum.inr i) 1 : RealConeModel κ ι)).const_add c.toModel)
    (hasDerivAt_const _ _), map_zero, add_zero]

/-- The angular curve `t ↦ toModel (c[θ_a := t])`. -/
def angularCurve (c : PolarPoint κ ι) (a : κ) (t : ℝ) : RealConeModel κ ι :=
  c.toModel + coneIncl a (polarMap (c (.r a), t) - polarMap (c (.r a), c (.θ a)))

theorem hasDerivAt_angularCurve (c : PolarPoint κ ι) (a : κ) (t : ℝ) :
    HasDerivAt (angularCurve c a) (coneIncl a (polarMap (c (.r a), t) * Complex.I)) t := by
  have h := ((coneIncl (ι := ι) a).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_polarMap_snd (c (.r a)) t).sub_const (polarMap (c (.r a), c (.θ a))))).const_add
      c.toModel
  rw [polarMap_mul_I] at h
  exact h

theorem hasDerivAt_angularCurve_deriv (c : PolarPoint κ ι) (a : κ) (t : ℝ) :
    HasDerivAt (fun t => coneIncl (ι := ι) a (polarMap (c (.r a), t) * Complex.I))
      (coneIncl a (polarMap (c (.r a), t) * Complex.I * Complex.I)) t := by
  have h := (coneIncl (ι := ι) a).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_polarMap_snd (c (.r a)) t).mul_const Complex.I)
  rw [polarMap_mul_I] at h
  exact h

theorem angularCurve_self (c : PolarPoint κ ι) (a : κ) : angularCurve c a (c (.θ a)) = c.toModel := by
  simp [angularCurve]

theorem cone_angularCurve (c : PolarPoint κ ι) (a : κ) (t : ℝ) :
    (angularCurve c a t).cone a = polarMap (c (.r a), t) := by
  simp [angularCurve]

/-- **The rotation field is the velocity of the angular curve:** `J_a γ(t) = γ'(t)`. -/
theorem rotJ_angularCurve (c : PolarPoint κ ι) (a : κ) (t : ℝ) :
    rotJ a (angularCurve c a t) = coneIncl a (polarMap (c (.r a), t) * Complex.I) := by
  rw [rotJ_apply, cone_angularCurve, mul_comm]

theorem polarMap_mul_I_self (c : PolarPoint κ ι) (a : κ) :
    coneIncl (ι := ι) a (polarMap (c (.r a), c (.θ a)) * Complex.I) =
      c (.r a) • angularVec a (c (.θ a)) := by
  rw [angularVec, ← map_smul, Complex.real_smul, polarMap]
  ring_nf

theorem polarMap_mul_I_I (c : PolarPoint κ ι) (a : κ) :
    coneIncl (ι := ι) a (polarMap (c (.r a), c (.θ a)) * Complex.I * Complex.I) =
      -(c (.r a) • radialVec a (c (.θ a))) := by
  rw [radialVec, ← map_smul, ← map_neg, Complex.real_smul, polarMap]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

theorem pd_θ_pd_θ_eq (hu : ContDiffAt ℝ 2 u c.toModel) (a : κ) :
    pd (.θ a) (pd (.θ a) fun c' : PolarPoint κ ι => u c'.toModel) c =
      c (.r a) ^ 2 * fderiv ℝ (fderiv ℝ u) c.toModel (angularVec a (c (.θ a)))
        (angularVec a (c (.θ a))) - c (.r a) * fderiv ℝ u c.toModel (radialVec a (c (.θ a))) := by
  rw [pd_pd]
  have hfun : (fun t => u (PolarPoint.toModel (Function.update c (.θ a) t))) =
      fun t => u (angularCurve c a t) := by
    funext t
    rw [toModel_update_θ]
    rfl
  rw [hfun, deriv_deriv_comp_curve hu (angularCurve_self c a)
    (Eventually.of_forall fun t => hasDerivAt_angularCurve c a t)
    (hasDerivAt_angularCurve_deriv c a _), polarMap_mul_I_self, polarMap_mul_I_I]
  simp only [map_smul, map_neg, _root_.smul_apply, smul_eq_mul]
  ring

end Polar

/-! ### The divergence of `g⁻¹ ∇u` -/

/-- **The Euclidean divergence** `div V (x) = ∑_k ∂_k V_k (x)` of a vector field on `ℝ^n`. -/
def divergence {n : Type*} [Fintype n] [DecidableEq n]
    (V : EuclideanSpace ℝ n → EuclideanSpace ℝ n) (x : EuclideanSpace ℝ n) : ℝ :=
  ∑ k, fderiv ℝ (fun y => V y k) x (EuclideanSpace.single k 1)

/-- The angular coefficient `h_a = r_a⁻² ∂_{θ_a} u`, where `∂_{θ_a} u (y) = Du(y)(J_a y)`. -/
def angularCoeff (u : RealConeModel κ ι → ℝ) (a : κ) (y : RealConeModel κ ι) : ℝ :=
  fderiv ℝ u y (rotJ a y) / ‖y.cone a‖ ^ 2

theorem gradient_apply_single_eq {n : Type*} [Fintype n] [DecidableEq n]
    (φ : EuclideanSpace ℝ n → ℝ) (x : EuclideanSpace ℝ n) (k : n) :
    gradient φ x k = fderiv ℝ φ x (EuclideanSpace.single k 1) := by
  rw [← inner_gradient, EuclideanSpace.inner_single_right]
  simp

theorem sum_apply_eq (v : κ → RealConeModel κ ι) (k : RealConeIndex κ ι) :
    (∑ a, v a) k = ∑ a, v a k :=
  map_sum (EuclideanSpace.proj (𝕜 := ℝ) k) v Finset.univ

/-- The components of `g⁻¹ ∇u` at a regular point. -/
theorem coneInvOp_gradient_apply (β : κ → ConeAngle) (u : RealConeModel κ ι → ℝ)
    {y : RealConeModel κ ι} (hy : ∀ a, y.cone a ≠ 0) (k : RealConeIndex κ ι) :
    coneInvOp β y (gradient u y) k = fderiv ℝ u y (EuclideanSpace.single k 1) +
      ∑ a, ((β a).beta⁻¹ ^ 2 - 1) * angularCoeff u a y * rotJ a y k := by
  rw [coneInvOp_eq_add_sum β hy, PiLp.add_apply, gradient_apply_single_eq, sum_apply_eq]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [PiLp.smul_apply, smul_eq_mul, inner_gradient, angularCoeff]

theorem rotJ_single_apply (a : κ) (k : RealConeIndex κ ι) :
    rotJ a (EuclideanSpace.single k 1) k = 0 := by
  have h := inner_rotJ_self (ι := ι) a (EuclideanSpace.single k 1)
  simpa [EuclideanSpace.inner_single_right] using h

theorem sum_fderiv_mul_apply (L : RealConeModel κ ι →L[ℝ] ℝ) (w : RealConeModel κ ι) :
    ∑ k, L (EuclideanSpace.single k 1) * w k = L w := by
  have hw : w = ∑ k, w k • EuclideanSpace.single k (1 : ℝ) := by
    have := ((EuclideanSpace.basisFun (RealConeIndex κ ι) ℝ).sum_repr w).symm
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using this
  conv_rhs => rw [hw]
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smul, smul_eq_mul, mul_comm]

theorem differentiableAt_angularCoeff {u : RealConeModel κ ι → ℝ} {p : RealConeModel κ ι}
    (hu : ContDiffAt ℝ 2 u p) {a : κ} (hp : p.cone a ≠ 0) :
    DifferentiableAt ℝ (angularCoeff u a) p := by
  have hD : DifferentiableAt ℝ (fderiv ℝ u) p :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hnum : DifferentiableAt ℝ (fun y => fderiv ℝ u y (rotJ a y)) p :=
    hD.clm_apply (rotJ a).differentiableAt
  have hden : DifferentiableAt ℝ (fun y : RealConeModel κ ι => ‖y.cone a‖ ^ 2) p :=
    DifferentiableAt.norm_sq ℝ (coneProj (ι := ι) a).differentiableAt
  have heq : angularCoeff u a = fun y => fderiv ℝ u y (rotJ a y) * (‖y.cone a‖ ^ 2)⁻¹ := by
    funext y
    rw [angularCoeff, div_eq_mul_inv]
  rw [heq]
  exact hnum.mul (hden.fun_inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hp)))

/-- `cos θ e_0 + sin θ e_1`. -/
theorem radialVec_eq (a : κ) (θ : ℝ) :
    radialVec (ι := ι) a θ = Real.cos θ • coneIncl a 1 + Real.sin θ • coneIncl a Complex.I := by
  rw [radialVec, ← map_smul, ← map_smul, ← map_add]
  congr 1
  apply Complex.ext <;> simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- `-sin θ e_0 + cos θ e_1`. -/
theorem angularVec_eq (a : κ) (θ : ℝ) :
    angularVec (ι := ι) a θ = (-Real.sin θ) • coneIncl a 1 + Real.cos θ • coneIncl a Complex.I := by
  rw [angularVec, ← map_smul, ← map_smul, ← map_add]
  congr 1
  apply Complex.ext <;> simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem coneIncl_one (a : κ) :
    coneIncl (ι := ι) a 1 = EuclideanSpace.single (Sum.inl (0, a)) 1 := by
  refine ext_cone_eucl (fun b => ?_) (fun i => by rw [eucl_coneIncl, eucl_single_inl])
  rw [cone_coneIncl, cone_single_inl]
  by_cases h : b = a
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

theorem coneIncl_I (a : κ) :
    coneIncl (ι := ι) a Complex.I = EuclideanSpace.single (Sum.inl (1, a)) 1 := by
  refine ext_cone_eucl (fun b => ?_) (fun i => by rw [eucl_coneIncl, eucl_single_inl])
  rw [cone_coneIncl, cone_single_inl]
  by_cases h : b = a
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- **The trace of a bilinear form in the polar frame:** `B(e_r, e_r) + B(e_θ, e_θ) =
B(e_0, e_0) + B(e_1, e_1)` on each cone factor. -/
theorem bilin_radial_add_angular (B : RealConeModel κ ι →L[ℝ] RealConeModel κ ι →L[ℝ] ℝ)
    (a : κ) (θ : ℝ) :
    B (radialVec a θ) (radialVec a θ) + B (angularVec a θ) (angularVec a θ) =
      B (coneIncl a 1) (coneIncl a 1) + B (coneIncl a Complex.I) (coneIncl a Complex.I) := by
  rw [radialVec_eq, angularVec_eq]
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  linear_combination (B (coneIncl a 1) (coneIncl a 1) +
    B (coneIncl a Complex.I) (coneIncl a Complex.I)) * Real.sin_sq_add_cos_sq θ

theorem sum_bilin_single (B : RealConeModel κ ι →L[ℝ] RealConeModel κ ι →L[ℝ] ℝ) (c : PolarPoint κ ι) :
    ∑ k, B (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) =
      ∑ a, (B (radialVec a (c (.θ a))) (radialVec a (c (.θ a))) +
        B (angularVec a (c (.θ a))) (angularVec a (c (.θ a)))) +
      ∑ i, B (EuclideanSpace.single (Sum.inr i) 1) (EuclideanSpace.single (Sum.inr i) 1) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type_right]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_two, bilin_radial_add_angular, coneIncl_one, coneIncl_I]

/-- **The divergence-form cone operator is the paper's Laplacian.** Let `u` be `C²` near a
regular point of the real model, with polar coordinates `c` (`r_a > 0`). Then
`div(g⁻¹ ∇u) = ∑_a Δ_{β_a} U + ∑_i ∂²_{s_i} U` at `c`, where `U = u ∘ toModel` is `u` in polar
coordinates. -/
theorem divergence_coneInvOp_gradient (β : κ → ConeAngle) {u : RealConeModel κ ι → ℝ}
    {c : PolarPoint κ ι} (hc : ∀ a, 0 < c (.r a)) (hu : ContDiffAt ℝ 2 u c.toModel) :
    divergence (fun y => coneInvOp β y (gradient u y)) c.toModel =
      paperLaplacian β (fun c' : PolarPoint κ ι => u c'.toModel) c := by
  have hreg : ∀ a, c.toModel.cone a ≠ 0 := fun a => by
    rw [PolarPoint.cone_toModel]
    exact polarMap_ne_zero (hc a)
  have hD : DifferentiableAt ℝ (fderiv ℝ u) c.toModel :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hh : ∀ a, DifferentiableAt ℝ (angularCoeff u a) c.toModel := fun a =>
    differentiableAt_angularCoeff hu (hreg a)
  -- each partial derivative
  have hk : ∀ k, fderiv ℝ (fun y => coneInvOp β y (gradient u y) k) c.toModel
      (EuclideanSpace.single k 1) =
      fderiv ℝ (fderiv ℝ u) c.toModel (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) +
        ∑ a, ((β a).beta⁻¹ ^ 2 - 1) *
          (fderiv ℝ (angularCoeff u a) c.toModel (EuclideanSpace.single k 1) *
            rotJ a c.toModel k) := by
    intro k
    have hev : (fun y => coneInvOp β y (gradient u y) k) =ᶠ[𝓝 c.toModel]
        fun y => fderiv ℝ u y (EuclideanSpace.single k 1) +
          ∑ a, ((β a).beta⁻¹ ^ 2 - 1) * angularCoeff u a y * rotJ a y k := by
      filter_upwards [isOpen_regular.mem_nhds hreg] with y hy
      exact coneInvOp_gradient_apply β u hy k
    have h1 : HasFDerivAt (fun y => fderiv ℝ u y (EuclideanSpace.single k 1))
        ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single k (1 : ℝ))).comp
          (fderiv ℝ (fderiv ℝ u) c.toModel)) c.toModel :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single k (1 : ℝ))).hasFDerivAt.comp _
        hD.hasFDerivAt
    have h2 : ∀ a ∈ Finset.univ, HasFDerivAt
        (fun y => ((β a).beta⁻¹ ^ 2 - 1) * angularCoeff u a y * rotJ a y k)
        ((((β a).beta⁻¹ ^ 2 - 1) * angularCoeff u a c.toModel) •
            ((EuclideanSpace.proj (𝕜 := ℝ) k).comp (rotJ a)) +
          rotJ a c.toModel k • (((β a).beta⁻¹ ^ 2 - 1) •
            fderiv ℝ (angularCoeff u a) c.toModel)) c.toModel := fun a _ =>
      ((hh a).hasFDerivAt.const_mul ((β a).beta⁻¹ ^ 2 - 1)).mul
        ((EuclideanSpace.proj (𝕜 := ℝ) k).comp (rotJ (ι := ι) a)).hasFDerivAt
    have hproj : ∀ v : RealConeModel κ ι, EuclideanSpace.proj (𝕜 := ℝ) k v = v k := fun v => rfl
    rw [hev.fderiv_eq, (h1.fun_add (HasFDerivAt.fun_sum h2)).fderiv]
    simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.apply_apply, FunLike.coe_sum, Finset.sum_apply,
      _root_.smul_apply, smul_eq_mul, hproj, rotJ_single_apply, mul_zero, zero_add]
    congr 1
    exact Finset.sum_congr rfl fun a _ => by ring
  -- the angular coefficient along the angular curve
  have hang : ∀ a, ((β a).beta⁻¹ ^ 2 - 1) *
      fderiv ℝ (angularCoeff u a) c.toModel (rotJ a c.toModel) =
      ((β a).beta⁻¹ ^ 2 - 1) * (pd (.θ a) (pd (.θ a) fun c' : PolarPoint κ ι => u c'.toModel) c /
        c (.r a) ^ 2) := by
    intro a
    congr 1
    obtain ⟨hF, hF'⟩ := hasDerivAt_fderiv_comp_curve hu (angularCurve_self c a)
      (Eventually.of_forall fun t => hasDerivAt_angularCurve c a t)
      (hasDerivAt_angularCurve_deriv c a (c (.θ a)))
    have hpd : pd (.θ a) (pd (.θ a) fun c' : PolarPoint κ ι => u c'.toModel) c =
        deriv (deriv fun t => u (angularCurve c a t)) (c (.θ a)) := by
      rw [pd_pd]
      congr 2
      funext t
      rw [toModel_update_θ]
      rfl
    rw [hpd, hF.deriv_eq, hF'.deriv]
    have hr2 : ∀ t, ‖(angularCurve c a t).cone a‖ ^ 2 = c (.r a) ^ 2 := fun t => by
      rw [cone_angularCurve, polarMap, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hc a)]
    have hcomp : (fun t => angularCoeff u a (angularCurve c a t)) =
        fun t => fderiv ℝ u (angularCurve c a t) (coneIncl a (polarMap (c (.r a), t) *
          Complex.I)) / c (.r a) ^ 2 := by
      funext t
      rw [angularCoeff, hr2, rotJ_angularCurve]
    have hA : HasDerivAt (fun t => angularCoeff u a (angularCurve c a t))
        (fderiv ℝ (angularCoeff u a) c.toModel
          (coneIncl a (polarMap (c (.r a), c (.θ a)) * Complex.I))) (c (.θ a)) :=
      (hh a).hasFDerivAt.comp_hasDerivAt_of_eq (c (.θ a)) (hasDerivAt_angularCurve c a _)
        (angularCurve_self c a).symm
    rw [hcomp] at hA
    have hB := hF'.div_const (c (.r a) ^ 2)
    have hJ : rotJ a c.toModel = coneIncl a (polarMap (c (.r a), c (.θ a)) * Complex.I) := by
      rw [← rotJ_angularCurve, angularCurve_self]
    rw [hJ, hA.unique hB]
  -- assemble
  have hA : ∀ a, coneLaplacian (β a).beta a (fun c' : PolarPoint κ ι => u c'.toModel) c =
      (fderiv ℝ (fderiv ℝ u) c.toModel (radialVec a (c (.θ a))) (radialVec a (c (.θ a))) +
        fderiv ℝ (fderiv ℝ u) c.toModel (angularVec a (c (.θ a))) (angularVec a (c (.θ a)))) +
      ((β a).beta⁻¹ ^ 2 - 1) * (pd (.θ a) (pd (.θ a) fun c' : PolarPoint κ ι => u c'.toModel) c /
        c (.r a) ^ 2) := by
    intro a
    rw [coneLaplacian, pd_r_pd_r_eq hu, pd_r_eq hu, pd_θ_pd_θ_eq hu]
    have hr := (hc a).ne'
    have hb := (β a).pos.ne'
    field_simp
    ring
  rw [divergence]
  simp_rw [hk]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_fderiv_mul_apply, hang]
  rw [sum_bilin_single _ c, paperLaplacian]
  simp_rw [hA, pd_s_pd_s_eq hu, Finset.sum_add_distrib]
  ring

end ConicalKahler.Sobolev
