module

public import ConicalKahler.Sobolev.Link
public import ConicalKahler.Sobolev.Classical
public import ConicalKahler.Sobolev.Scaling
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Lemma 3.1: the spectral theorem on the link

Let `c` be a conical coefficient field on `ℝ^d` (`CoeffField.IsConical`; the cone Laplacian is
the example, `ConeLink.lean`). On the link `S = S^{d-1}` consider the link form
`b((φ, Γ), (ψ, Θ)) = ∫_S ⟨A Γ, Θ⟩ + ∫_S φ ψ` on `W^{1,2}(link)` (`Link.lean`).

* `smoothLinkPair_mem`: for `ψ ∈ C¹(ℝ^d)`, the restriction `ψ|_S` with its tangential gradient
  `∇ψ - ⟨∇ψ, w⟩ w` is a link pair. The `0`-homogeneous extension `ψ(x/|x|)` is `C¹` off `0`, and its
  gradient is `|x|^{-1}` times the tangential gradient at `x/|x|` (`fderiv_comp_normalize`).
* `denseRange_linkFst`: the functions `φ` of link pairs are **dense** in `L²(S)` (Stone–Weierstrass
  for the restrictions of smooth functions, and density of `C(S)` in `L²(S)`).
* `linkK`: the operator `K = ι ∘ S` of `FormSpectral.lean` for the link form; compact, symmetric,
  positive and injective.
* **Lemma 3.1** (`link_spectral`): `L²(S)` has a Hilbert basis `{φ_i}` of **link eigenfunctions**,
  `φ_i ∈ W^{1,2}(link)` with `∫_S ⟨A Γ_i, Θ⟩ = λ_i ∫_S φ_i ψ` for every link pair `(ψ, Θ)`, where
  `λ_i ≥ 0`, and for every `Λ` only finitely many `λ_i` are `≤ Λ` (so `λ_i → ∞`).
  The constant function is an eigenfunction with `λ = 0` (`linkEigen_const`).

The paper's `0 = λ_0 < λ_1` (multiplicity one of `0`) needs the link to be connected; it is not
claimed here (`PAPER_REVIEW.md` S6).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology InnerProductSpace Set Metric
open scoped ContDiff ENNReal

namespace ConicalKahler.Sobolev

variable {d : ℕ} [NeZero d]

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### Calculus of `x / |x|` -/

theorem hasFDerivAt_norm_of_ne {x : 𝔼} (hx : x ≠ 0) :
    HasFDerivAt (fun y : 𝔼 => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hx2 : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have h2 := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt hx2
  have he : (fun y : 𝔼 => √(‖y‖ ^ 2)) = fun y => ‖y‖ :=
    funext fun y => Real.sqrt_sq (norm_nonneg y)
  rw [he, Real.sqrt_sq (norm_nonneg x)] at h2
  convert h2 using 1
  ext v
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat]
  field_simp

/-- The derivative of `y ↦ y / |y|` at `x ≠ 0`, applied to `w`:
`|x|^{-1} w - |x|^{-3} ⟨x, w⟩ x`. -/
theorem hasFDerivAt_normalize {x : 𝔼} (hx : x ≠ 0) :
    ∃ L : 𝔼 →L[ℝ] 𝔼, HasFDerivAt (fun y : 𝔼 => ‖y‖⁻¹ • y) L x ∧
      ∀ w, L w = ‖x‖⁻¹ • w - ((‖x‖ ^ 3)⁻¹ * ⟪x, w⟫_ℝ) • x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h1 : HasFDerivAt (fun y : 𝔼 => ‖y‖⁻¹) ((-(‖x‖ ^ 2)⁻¹) • (‖x‖⁻¹ • innerSL ℝ x)) x :=
    (hasDerivAt_inv hn).comp_hasFDerivAt x (hasFDerivAt_norm_of_ne hx)
  have h2 := h1.smul (hasFDerivAt_id x)
  refine ⟨_, h2, fun w => ?_⟩
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, id_eq]
  rw [sub_eq_add_neg, ← neg_smul]
  congr 2
  field_simp

/-- The tangential part `∇ψ(w) - ⟨∇ψ(w), w⟩ w` of the gradient at a point `w` of the sphere. -/
def tangGrad (ψ : 𝔼 → ℝ) (w : 𝔼) : 𝔼 := gradient ψ w - ⟪gradient ψ w, w⟫_ℝ • w

/-- **The derivative of a `0`-homogeneous extension**: for `y ↦ ψ(y / |y|)` at `x ≠ 0`,
`∂_w = ⟨|x|^{-1} (∇ψ - ⟨∇ψ, x̂⟩ x̂)(x̂), w⟩` with `x̂ = x / |x|`. -/
theorem fderiv_comp_normalize {ψ : 𝔼 → ℝ} (hψ : Differentiable ℝ ψ) {x : 𝔼} (hx : x ≠ 0)
    (w : 𝔼) :
    fderiv ℝ (fun y : 𝔼 => ψ (‖y‖⁻¹ • y)) x w =
      ⟪‖x‖⁻¹ • tangGrad ψ (‖x‖⁻¹ • x), w⟫_ℝ := by
  obtain ⟨L, hL, hLw⟩ := hasFDerivAt_normalize hx
  have hcomp := HasFDerivAt.comp (g := ψ) (f := fun y : 𝔼 => ‖y‖⁻¹ • y) x
    (hψ (‖x‖⁻¹ • x)).hasFDerivAt hL
  rw [show (fun y : 𝔼 => ψ (‖y‖⁻¹ • y)) = ψ ∘ fun y : 𝔼 => ‖y‖⁻¹ • y from rfl, hcomp.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hLw, tangGrad]
  rw [← inner_gradient]
  set g := gradient ψ (‖x‖⁻¹ • x)
  simp only [inner_sub_right, inner_sub_left, real_inner_smul_left, real_inner_smul_right]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp

theorem contDiffOn_normalize : ContDiffOn ℝ ∞ (fun y : 𝔼 => ‖y‖⁻¹ • y) {0}ᶜ := by
  intro x hx
  have hx' : x ≠ 0 := hx
  exact (((contDiffAt_norm ℝ hx').inv (norm_ne_zero_iff.mpr hx')).smul
    contDiffAt_id).contDiffWithinAt

/-! ### Link pairs of smooth functions -/

theorem continuous_tangGrad {ψ : 𝔼 → ℝ} (hψ : ContDiff ℝ 1 ψ) : Continuous (tangGrad ψ) := by
  have hg : Continuous (gradient ψ) :=
    (toDual ℝ 𝔼).symm.continuous.comp (hψ.continuous_fderiv one_ne_zero)
  unfold tangGrad
  exact hg.sub (Continuous.smul (f := fun w => ⟪gradient ψ w, w⟫_ℝ) (g := fun w : 𝔼 => w)
    (hg.inner continuous_id) continuous_id)

/-- The restriction of a continuous function to the sphere. -/
def sphRestrict {E : Type*} [TopologicalSpace E] (ψ : 𝔼 → E) (hψ : Continuous ψ) : C(Sph d, E) :=
  ⟨fun w => ψ w, hψ.comp continuous_subtype_val⟩

/-- **The link pair of a `C¹` function** `ψ`: its restriction to the sphere and its tangential
gradient. -/
def smoothLinkPair (ψ : 𝔼 → ℝ) (hψ : ContDiff ℝ 1 ψ) : LinkPair d :=
  WithLp.toLp 2 (ContinuousMap.toLp 2 (sphMeasure d) ℝ (sphRestrict ψ hψ.continuous),
    ContinuousMap.toLp 2 (sphMeasure d) ℝ (sphRestrict (tangGrad ψ) (continuous_tangGrad hψ)))

theorem smoothLinkPair_fst (ψ : 𝔼 → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    (smoothLinkPair ψ hψ).fst = ContinuousMap.toLp 2 (sphMeasure d) ℝ (sphRestrict ψ hψ.continuous) :=
  rfl

theorem smoothLinkPair_snd (ψ : 𝔼 → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    (smoothLinkPair ψ hψ).snd =
      ContinuousMap.toLp 2 (sphMeasure d) ℝ (sphRestrict (tangGrad ψ) (continuous_tangGrad hψ)) :=
  rfl

/-- **Smooth functions give link pairs**: `ψ(x/|x|)` has weak gradient `|x|^{-1}` times the
tangential gradient at `x/|x|`, on every shell. -/
theorem smoothLinkPair_mem {ψ : 𝔼 → ℝ} (hψ : ContDiff ℝ 1 ψ) : smoothLinkPair ψ hψ ∈ linkW12 d := by
  rw [mem_linkW12]
  intro n
  set Ω := shellN d n
  have hΩ0 : ∀ᵐ x ∂(volume.restrict Ω), x ≠ 0 := by
    filter_upwards [ae_restrict_mem (measurableSet_shell (d := d) _ _)] with x hx
    exact ne_zero_of_mem_shell (shellN_pos n).le hx
  have h1 : (linkEmbN d n (smoothLinkPair ψ hψ)).fst =ᵐ[volume.restrict Ω]
      fun x => ψ (‖x‖⁻¹ • x) := by
    filter_upwards [linkEmb_fst_ae (a := ((n : ℝ) + 1)⁻¹) (b := (n : ℝ) + 1) (shellN_pos n)
        subset_rfl (smoothLinkPair ψ hψ),
      ae_restrict_of_ae (homFun_congr_ae (ContinuousMap.coeFn_toLp (p := 2) (μ := sphMeasure d)
        (𝕜 := ℝ) (sphRestrict ψ hψ.continuous)) 0), hΩ0] with x hx hx' hx0
    rw [hx, smoothLinkPair_fst, hx', homFun, Real.rpow_zero, one_smul]
    simp [sphRestrict, sphProj_coe hx0]
  have h2 : (linkEmbN d n (smoothLinkPair ψ hψ)).snd =ᵐ[volume.restrict Ω]
      fun x => ‖x‖⁻¹ • tangGrad ψ (‖x‖⁻¹ • x) := by
    filter_upwards [linkEmb_snd_ae (a := ((n : ℝ) + 1)⁻¹) (b := (n : ℝ) + 1) (shellN_pos n)
        subset_rfl (smoothLinkPair ψ hψ),
      ae_restrict_of_ae (homFun_congr_ae (ContinuousMap.coeFn_toLp (p := 2) (μ := sphMeasure d)
        (𝕜 := ℝ) (sphRestrict (tangGrad ψ) (continuous_tangGrad hψ))) (-1)), hΩ0]
      with x hx hx' hx0
    rw [hx, smoothLinkPair_snd, hx', homFun, Real.rpow_neg_one]
    simp [sphRestrict, sphProj_coe hx0]
  have hF : ContDiffOn ℝ 1 (fun x : 𝔼 => ψ (‖x‖⁻¹ • x)) Ω :=
    hψ.comp_contDiffOn ((contDiffOn_normalize.of_le (by simp)).mono fun x hx =>
      ne_zero_of_mem_shell (shellN_pos n).le hx)
  refine mem_W12_of_integral fun φ hφ e => ?_
  calc ∫ x in Ω, (linkEmbN d n (smoothLinkPair ψ hψ)).fst x * fderiv ℝ φ x e
      = ∫ x in Ω, ψ (‖x‖⁻¹ • x) * fderiv ℝ φ x e := by
        refine integral_congr_ae ?_
        filter_upwards [h1] with x hx
        rw [hx]
    _ = -∫ x in Ω, fderiv ℝ (fun x : 𝔼 => ψ (‖x‖⁻¹ • x)) x e * φ x :=
        setIntegral_mul_fderiv_eq_neg_of_contDiffOn (isOpen_shell _ _) subset_rfl hF hφ e
    _ = -∫ x in Ω, φ x * ⟪(linkEmbN d n (smoothLinkPair ψ hψ)).snd x, e⟫_ℝ := by
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [h2, hΩ0] with x hx hx0
        rw [hx, fderiv_comp_normalize (hψ.differentiable one_ne_zero) hx0, mul_comm]

/-! ### Density -/

/-- The restrictions of smooth functions to the sphere, a subalgebra of `C(S, ℝ)`. -/
def smoothSubalgebra (d : ℕ) [NeZero d] : Subalgebra ℝ C(Sph d, ℝ) where
  carrier := {f | ∃ ψ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ ψ ∧ ∀ w, f w = ψ w}
  mul_mem' := by
    rintro f g ⟨ψ₁, h₁, e₁⟩ ⟨ψ₂, h₂, e₂⟩
    exact ⟨ψ₁ * ψ₂, h₁.mul h₂, fun w => by simp [e₁, e₂]⟩
  add_mem' := by
    rintro f g ⟨ψ₁, h₁, e₁⟩ ⟨ψ₂, h₂, e₂⟩
    exact ⟨ψ₁ + ψ₂, h₁.add h₂, fun w => by simp [e₁, e₂]⟩
  algebraMap_mem' r := ⟨fun _ => r, contDiff_const, fun w => rfl⟩

theorem smoothSubalgebra_separatesPoints : (smoothSubalgebra d).SeparatesPoints := by
  intro w w' hww'
  set v : 𝔼 := (w : 𝔼) - w'
  have hψ : ContDiff ℝ ∞ fun x : 𝔼 => ⟪v, x⟫_ℝ := (innerSL ℝ v).contDiff
  refine ⟨_, ⟨sphRestrict (fun x : 𝔼 => ⟪v, x⟫_ℝ) hψ.continuous, ⟨_, hψ, fun _ => rfl⟩, rfl⟩, ?_⟩
  simp only [sphRestrict, ContinuousMap.coe_mk]
  intro h
  have hv : v ≠ 0 := sub_ne_zero.mpr (Subtype.coe_injective.ne hww')
  have : ⟪v, v⟫_ℝ = 0 := by
    simp only [v, inner_sub_right] at h ⊢
    linarith
  exact hv (inner_self_eq_zero.mp this)

/-- **The functions of link pairs are dense in `L²(S)`** (Stone–Weierstrass). -/
theorem denseRange_linkFst : DenseRange (linkFst d) := by
  have hA : Dense (smoothSubalgebra d : Set C(Sph d, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe,
      ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
        smoothSubalgebra_separatesPoints]
    rfl
  have hT := ContinuousMap.toLp_denseRange (p := 2) (μ := sphMeasure d) (𝕜 := ℝ) (E := ℝ)
    (α := Sph d) (by norm_num)
  have hD := hT.dense_image (ContinuousMap.toLp 2 (sphMeasure d) ℝ).continuous hA
  refine hD.mono ?_
  rintro _ ⟨f, ⟨ψ, hψ, hf⟩, rfl⟩
  refine ⟨⟨smoothLinkPair ψ (hψ.of_le (by simp)), smoothLinkPair_mem _⟩, ?_⟩
  rw [linkFst_apply, smoothLinkPair_fst]
  congr 1
  ext w
  simp [sphRestrict, hf]

/-! ### The link operator and Lemma 3.1 -/

variable {c : CoeffField (EuclideanSpace ℝ (Fin d)) volume}

/-- **The link operator** `K = (−Δ_ḡ + 1)⁻¹` on `L²(S)`, the operator of `FormSpectral.lean` for
the link form. -/
def linkK (hc : c.IsConical) : Lp ℝ 2 (sphMeasure d) →L[ℝ] Lp ℝ 2 (sphMeasure d) :=
  formK (linkFst d) (isCoercive_linkForm₀ hc)

theorem isCompactOperator_linkK (hc : c.IsConical) : IsCompactOperator (linkK hc) :=
  isCompactOperator_formK _ _ isCompactOperator_linkFst

theorem isSymmetric_linkK (hc : c.IsConical) : (linkK hc).IsSymmetric :=
  isSymmetric_formK _ _ (linkForm₀_comm hc)

/-- `(φ, Γ)` is a **link eigenfunction** with eigenvalue `λ`: a link pair with
`∫_S ⟨A Γ, Θ⟩ dσ = λ ∫_S φ ψ dσ` for every link pair `(ψ, Θ)`; i.e. `-Δ_ḡ φ = λ φ` weakly. -/
def IsLinkEigen (hc : c.IsConical) (lam : ℝ) (v : LinkPair d) : Prop :=
  v ∈ linkW12 d ∧ ∀ w ∈ linkW12 d,
    ⟪CoeffField.sphMulOp hc v.snd, w.snd⟫_ℝ = lam * ⟪v.fst, w.fst⟫_ℝ

/-- Link eigenvalues are nonnegative. -/
theorem IsLinkEigen.nonneg {hc : c.IsConical} {lam : ℝ} {v : LinkPair d}
    (h : IsLinkEigen hc lam v) (hv : v.fst ≠ 0) : 0 ≤ lam := by
  have h1 := h.2 v h.1
  have h2 := CoeffField.lam_mul_norm_sq_le_sphMulOp hc v.snd
  rw [h1, real_inner_self_eq_norm_sq] at h2
  have h3 : 0 < ‖v.fst‖ ^ 2 := by positivity
  have h4 : 0 ≤ c.lam * ‖v.snd‖ ^ 2 := mul_nonneg c.lam_pos.le (sq_nonneg _)
  exact nonneg_of_mul_nonneg_left (h4.trans h2) h3

/-- **The constant function is a link eigenfunction, with eigenvalue `0`.** -/
theorem linkEigen_const (hc : c.IsConical) :
    IsLinkEigen hc 0 (smoothLinkPair (fun _ : 𝔼 => (1 : ℝ)) contDiff_const) := by
  refine ⟨smoothLinkPair_mem _, fun w _ => ?_⟩
  have h0 : (smoothLinkPair (fun _ : 𝔼 => (1 : ℝ)) contDiff_const).snd = 0 := by
    rw [smoothLinkPair_snd]
    have : sphRestrict (tangGrad (fun _ : 𝔼 => (1 : ℝ))) (continuous_tangGrad contDiff_const) = 0 := by
      ext w
      simp [sphRestrict, tangGrad, gradient]
    rw [this, map_zero]
  rw [h0, map_zero, inner_zero_left, zero_mul]

/-- The eigenvalue relation of the link form gives a link eigenfunction. -/
theorem isLinkEigen_of_form (hc : c.IsConical) {μ : ℝ} (hμ : 0 < μ) {f : Lp ℝ 2 (sphMeasure d)}
    {S : linkW12 d} (hι : linkFst d S = μ • f)
    (hb : ∀ ψ : linkW12 d, linkForm₀ hc S ψ = μ⁻¹ * ⟪linkFst d S, linkFst d ψ⟫_ℝ) :
    IsLinkEigen hc (μ⁻¹ - 1) (μ⁻¹ • (S : LinkPair d)) ∧ (μ⁻¹ • (S : LinkPair d)).fst = f := by
  have hμ0 : μ ≠ 0 := hμ.ne'
  rw [linkFst_apply] at hι
  have hP : (μ⁻¹ • (S : LinkPair d)).fst = f := by
    rw [WithLp.smul_fst, hι, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  refine ⟨⟨(linkW12 d).smul_mem _ S.2, fun w hw => ?_⟩, hP⟩
  have h := hb ⟨w, hw⟩
  rw [linkForm₀_apply, linkFst_apply, linkFst_apply, linkForm_apply, hι,
    real_inner_smul_left] at h
  simp only at h
  generalize hX : ⟪CoeffField.sphMulOp hc (S : LinkPair d).snd, w.snd⟫_ℝ = X at h
  generalize hY : ⟪f, w.fst⟫_ℝ = Y at h
  have hX' : X = (1 - μ) * Y := by
    have : μ⁻¹ * (μ * Y) = Y := by rw [← mul_assoc, inv_mul_cancel₀ hμ0, one_mul]
    linarith
  rw [hP, WithLp.smul_snd, map_smul, real_inner_smul_left, hX, hY, hX']
  calc μ⁻¹ * ((1 - μ) * Y) = (μ⁻¹ - μ⁻¹ * μ) * Y := by ring
    _ = (μ⁻¹ - 1) * Y := by rw [inv_mul_cancel₀ hμ0]

/-- **Eigenvectors of the link operator are link eigenfunctions.** If `K f = μ f` with `f ≠ 0`,
then `μ > 0` and there is a link pair `(f, Γ)` which is a link eigenfunction with eigenvalue
`μ⁻¹ - 1`. -/
theorem linkK_eigen (hc : c.IsConical) {μ : ℝ} {f : Lp ℝ 2 (sphMeasure d)} (hf : f ≠ 0)
    (hKf : linkK hc f = μ • f) :
    0 < μ ∧ ∃ Γ : Lp 𝔼 2 (sphMeasure d), IsLinkEigen hc (μ⁻¹ - 1) (WithLp.toLp 2 (f, Γ)) := by
  obtain ⟨hμ, hι, hb⟩ := formK_eigen (linkFst d) (isCoercive_linkForm₀ hc) denseRange_linkFst hf hKf
  obtain ⟨hE, hP⟩ := isLinkEigen_of_form hc hμ hι hb
  refine ⟨hμ, (μ⁻¹ • ((formSol (linkFst d) (isCoercive_linkForm₀ hc) f : linkW12 d) :
    LinkPair d)).snd, ?_⟩
  convert hE using 1
  exact WithLp.ofLp_injective _ (Prod.ext hP.symm rfl)

/-- **Lemma 3.1 (spectral decomposition on the link).** `L²(S)` has a Hilbert basis `{φ_i}` of
link eigenfunctions: there are vector fields `Γ_i` and eigenvalues `λ_i ≥ 0` with `(φ_i, Γ_i)` a
link eigenfunction for `λ_i`, and for every `Λ` only finitely many `λ_i ≤ Λ`. -/
theorem link_spectral (hc : c.IsConical) :
    ∃ (s : Set (Lp ℝ 2 (sphMeasure d))) (B : HilbertBasis s ℝ (Lp ℝ 2 (sphMeasure d)))
      (Γ : s → Lp 𝔼 2 (sphMeasure d)) (lam : s → ℝ),
      ⇑B = ((↑) : s → Lp ℝ 2 (sphMeasure d)) ∧
      (∀ i, 0 ≤ lam i ∧ IsLinkEigen hc (lam i) (WithLp.toLp 2 ((i : Lp ℝ 2 (sphMeasure d)), Γ i))) ∧
      ∀ Λ : ℝ, {i | lam i ≤ Λ}.Finite := by
  obtain ⟨s, B, hB, heig⟩ := exists_hilbertBasis_eigenvectors (isCompactOperator_linkK hc)
    (isSymmetric_linkK hc)
  have hne : ∀ i : s, (i : Lp ℝ 2 (sphMeasure d)) ≠ 0 := fun i => by
    have h1 := B.orthonormal.1 i
    rw [hB] at h1
    exact ne_zero_of_norm_ne_zero (by rw [h1]; norm_num)
  choose μ hμ using fun i : s => heig i i.2
  have hspec := fun i : s => linkK_eigen hc (hne i) (hμ i)
  choose hμpos Γ hΓ using hspec
  refine ⟨s, B, Γ, fun i => (μ i)⁻¹ - 1, hB, fun i => ⟨(hΓ i).nonneg (hne i), hΓ i⟩,
    fun Λ => ?_⟩
  · -- only finitely many eigenvalues `λ_i ≤ Λ`, since `K` is compact
    by_contra hinf
    have hinf' : {i | (μ i)⁻¹ - 1 ≤ Λ}.Infinite := hinf
    set e := hinf'.natEmbedding
    set u : ℕ → Lp ℝ 2 (sphMeasure d) := fun n => ((e n : s) : Lp ℝ 2 (sphMeasure d))
    have hon : Orthonormal ℝ ((↑) : s → Lp ℝ 2 (sphMeasure d)) := hB ▸ B.orthonormal
    have hnorm : ∀ n, ‖u n‖ = 1 := fun n => hon.1 (e n)
    have horth : ∀ n m, n ≠ m → ⟪u n, u m⟫_ℝ = 0 := fun n m hnm =>
      hon.2 fun h => hnm (e.injective (Subtype.ext h))
    -- the eigenvalues of `K` along the sequence are bounded below
    have hΛ : ∀ n, (μ (e n))⁻¹ ≤ Λ + 1 := fun n => by
      have := (e n).2
      simp only [mem_ofPred_eq] at this
      linarith
    have hΛpos : 0 < Λ + 1 := lt_of_lt_of_le (inv_pos.mpr (hμpos (e 0))) (hΛ 0)
    set ε := (Λ + 1)⁻¹
    have hεpos : 0 < ε := inv_pos.mpr hΛpos
    have hμε : ∀ n, ε ≤ μ (e n) := fun n => by
      have h := hΛ n
      have hp := hμpos (e n)
      rw [inv_le_comm₀ hp hΛpos] at h
      exact h
    have hKu : ∀ n, linkK hc (u n) = μ (e n) • u n := fun n => hμ (e n)
    have hsep : ∀ n m, n ≠ m → ε ≤ dist (linkK hc (u n)) (linkK hc (u m)) := by
      intro n m hnm
      rw [dist_eq_norm, hKu, hKu]
      have h2 : ‖μ (e n) • u n - μ (e m) • u m‖ ^ 2 = μ (e n) ^ 2 + μ (e m) ^ 2 := by
        rw [norm_sub_sq_real, norm_smul, norm_smul, hnorm, hnorm, real_inner_smul_left,
          real_inner_smul_right, horth n m hnm, Real.norm_eq_abs, Real.norm_eq_abs, mul_one,
          mul_one, sq_abs, sq_abs]
        ring
      have h3 : ε ^ 2 ≤ ‖μ (e n) • u n - μ (e m) • u m‖ ^ 2 := by
        rw [h2]
        nlinarith [hμε n, sq_nonneg (μ (e m))]
      exact (pow_le_pow_iff_left₀ hεpos.le (norm_nonneg _) two_ne_zero).mp h3
    -- compactness gives a convergent subsequence
    have hcpt := (isCompactOperator_linkK hc).isCompact_closure_image_closedBall 1
    have hmem : ∀ n, linkK hc (u n) ∈ closure (linkK hc '' Metric.closedBall 0 1) := fun n =>
      subset_closure ⟨u n, by simp [hnorm n], rfl⟩
    obtain ⟨a, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq hmem
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hlim.cauchySeq ε hεpos
    have h1 := hN (N + 1) (Nat.le_succ N)
    have h2 := hsep (φ (N + 1)) (φ N) (hφ.injective.ne (Nat.succ_ne_self N))
    simp only [Function.comp_apply] at h1
    linarith

end ConicalKahler.Sobolev
