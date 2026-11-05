module

public import ConicalKahler.Cone.FlatCone

/-!
# The flat Laplacian of one complex coordinate in polar and cone coordinates

For `f : ℂⁿ → ℝ` and a coordinate `j`, the flat Laplacian in the complex variable `z_j` is

  `Δ_{z_j} f = ∂²f/∂x_j² + ∂²f/∂y_j²`  (`coordLaplacian`).

This file expresses it in polar coordinates `z_j = r e^{iθ}` and in the cone coordinates
`ρ = r^β`, with all other coordinates frozen (`coordSlice`). Partial derivatives in `r`, `ρ`, `θ`
are one-variable derivatives `deriv` of the corresponding slices of `G(r, θ) = f(r e^{iθ})` or
`F(ρ, θ) = f(ρ^{1/β} e^{iθ})`.

* `coordLaplacian_polar`: `G_rr + r⁻¹ G_r + r⁻² G_θθ = Δ_{z_j} f`.
* `coordLaplacian_conePolar`:
  `F_ρρ + ρ⁻¹ F_ρ + (βρ)⁻² F_θθ = β⁻² ρ^(2/β - 2) Δ_{z_j} f`.

These are exact identities for functions that are `C²` at the point. They combine with the
formula for the Laplace–Beltrami operator of the cone models (`ConicalKahler.Laplacian.Model`) to
give the polar form of the cone Laplacian.

The analytic tool is the second-order chain rule along a curve (`deriv_deriv_comp_curve`):
`(f ∘ γ)'' = D²f(γ', γ') + Df(γ'')`.
-/

@[expose] public section

open scoped Topology ContDiff Real
open Filter Set

namespace ConicalKahler

variable {n : ℕ}

/-! ### The flat Laplacian in one complex coordinate -/

/-- The flat Laplacian in the complex coordinate `z_j`: `∂²f/∂x_j² + ∂²f/∂y_j²`. -/
noncomputable def coordLaplacian (j : Fin n) (f : E n → ℝ) (z : E n) : ℝ :=
  fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) +
    fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
      (Complex.I • EuclideanSpace.single j 1)

/-- The unit vector `e^{iθ} e_j`. -/
noncomputable def polarDir (j : Fin n) (θ : ℝ) : E n :=
  Complex.exp (θ * Complex.I) • EuclideanSpace.single j 1

/-- **Rotation invariance.** For the unit vector `u = e^{iθ} e_j`,
`D²f(u, u) + D²f(iu, iu) = Δ_{z_j} f`. -/
theorem coordLaplacian_eq_rotate (j : Fin n) (f : E n → ℝ) (z : E n) (θ : ℝ) :
    fderiv ℝ (fderiv ℝ f) z (polarDir j θ) (polarDir j θ) +
      fderiv ℝ (fderiv ℝ f) z (Complex.I • polarDir j θ) (Complex.I • polarDir j θ) =
      coordLaplacian j f z := by
  set A := fderiv ℝ (fderiv ℝ f) z
  set e : E n := EuclideanSpace.single j 1
  have hu : polarDir j θ = Real.cos θ • e + Real.sin θ • (Complex.I • e) := by
    rw [polarDir, Complex.exp_mul_I, add_smul, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      mul_smul, Complex.coe_smul, Complex.coe_smul]
  have hiu : Complex.I • polarDir j θ = Real.cos θ • (Complex.I • e) - Real.sin θ • e := by
    rw [hu, smul_add, smul_comm Complex.I (Real.cos θ), smul_comm Complex.I (Real.sin θ),
      smul_smul Complex.I Complex.I, Complex.I_mul_I, neg_one_smul, smul_neg]
    abel
  rw [hiu, hu, coordLaplacian]
  simp only [map_add, map_sub, map_smul, _root_.add_apply,
    _root_.sub_apply, _root_.smul_apply, smul_eq_mul]
  have hcs := Real.cos_sq_add_sin_sq θ
  linear_combination (A e e + A (Complex.I • e) (Complex.I • e)) * hcs

/-! ### Coordinate slices -/

/-- The coordinate slice through `w` in the direction `j`: `ζ ↦ w` with `z_j` replaced by `ζ`. -/
noncomputable def coordSlice (j : Fin n) (w : E n) (ζ : ℂ) : E n :=
  w + (ζ - w j) • EuclideanSpace.single j 1

@[simp]
theorem coordSlice_apply_self (j : Fin n) (w : E n) (ζ : ℂ) : coordSlice j w ζ j = ζ := by
  simp [coordSlice]

theorem coordSlice_apply_of_ne (j : Fin n) (w : E n) (ζ : ℂ) {k : Fin n} (hk : k ≠ j) :
    coordSlice j w ζ k = w k := by
  simp [coordSlice, hk]

theorem transverseSlice_eq_coordSlice [NeZero n] (w : E n) :
    transverseSlice w = coordSlice 0 w :=
  rfl

/-- The slice is affine: `coordSlice j w ζ = (w - w_j e_j) + ζ • e_j`. -/
theorem coordSlice_eq (j : Fin n) (w : E n) (ζ : ℂ) :
    coordSlice j w ζ = (w - w j • EuclideanSpace.single j 1) + ζ • EuclideanSpace.single j 1 := by
  rw [coordSlice, sub_smul]
  abel

/-! ### The second-order chain rule along a curve -/

section Curve

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Second derivative along a curve.** If `f` is `C²` at `γ s`, `γ` has derivative `γ' t` near
`s`, and `γ'` has derivative `γ''` at `s`, then
`(f ∘ γ)''(s) = D²f(γ s)(γ' s, γ' s) + Df(γ s)(γ'')`. -/
theorem deriv_deriv_comp_curve {f : F → ℝ} {γ γ' : ℝ → F} {γ'' : F} {s : ℝ}
    (hf : ContDiffAt ℝ 2 f (γ s)) (hγ : ∀ᶠ t in 𝓝 s, HasDerivAt γ (γ' t) t)
    (hγ' : HasDerivAt γ' γ'' s) :
    deriv (deriv fun t => f (γ t)) s =
      fderiv ℝ (fderiv ℝ f) (γ s) (γ' s) (γ' s) + fderiv ℝ f (γ s) γ'' := by
  have hγc : ContinuousAt γ s := hγ.self_of_nhds.continuousAt
  have hfd : ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ f (γ t) :=
    hγc.eventually ((hf.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num))
  have hd1 : deriv (fun t => f (γ t)) =ᶠ[𝓝 s] fun t => fderiv ℝ f (γ t) (γ' t) := by
    filter_upwards [hfd, hγ] with t h1 h2
    exact (h1.hasFDerivAt.comp_hasDerivAt t h2).deriv
  rw [hd1.deriv_eq]
  have hD : DifferentiableAt ℝ (fderiv ℝ f) (γ s) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasDerivAt (fun t => fderiv ℝ f (γ t)) (fderiv ℝ (fderiv ℝ f) (γ s) (γ' s)) s :=
    hD.hasFDerivAt.comp_hasDerivAt s hγ.self_of_nhds
  exact (hc.clm_apply hγ').deriv

/-- First derivative along a curve. -/
theorem deriv_comp_curve {f : F → ℝ} {γ : ℝ → F} {γ' : F} {s : ℝ}
    (hf : DifferentiableAt ℝ f (γ s)) (hγ : HasDerivAt γ γ' s) :
    deriv (fun t => f (γ t)) s = fderiv ℝ f (γ s) γ' :=
  (hf.hasFDerivAt.comp_hasDerivAt s hγ).deriv

end Curve

/-! ### Polar coordinates in one complex coordinate -/

section Polar

variable (j : Fin n) (w : E n)

/-- `coordSlice j w (r e^{iθ}) = (w - w_j e_j) + r • e^{iθ} e_j`. -/
theorem coordSlice_polarMap (r θ : ℝ) :
    coordSlice j w (polarMap (r, θ)) =
      (w - w j • EuclideanSpace.single j 1) + r • polarDir j θ := by
  rw [coordSlice_eq, polarMap, polarDir, mul_smul, Complex.coe_smul]

/-- The radial curve `s ↦ coordSlice j w (s^a e^{iθ})` has velocity `a s^(a-1) e^{iθ} e_j`. -/
theorem hasDerivAt_coordSlice_rpow (θ a : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => coordSlice j w (polarMap (t ^ a, θ)))
      ((a * s ^ (a - 1)) • polarDir j θ) s := by
  simp_rw [coordSlice_polarMap]
  exact ((Real.hasDerivAt_rpow_const (Or.inl hs.ne')).smul_const (polarDir j θ)).const_add _

/-- The derivative of `θ ↦ e^{iθ} e_j` is `i e^{iθ} e_j`. -/
theorem hasDerivAt_polarDir (θ : ℝ) :
    HasDerivAt (polarDir j) (Complex.I • polarDir j θ) θ := by
  have h : HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I))
      (Complex.exp (θ * Complex.I) * Complex.I) θ :=
    ((hasDerivAt_id θ).ofReal_comp.mul_const Complex.I).cexp.congr_deriv (by simp)
  have h2 := h.smul_const (EuclideanSpace.single j (1 : ℂ))
  unfold polarDir
  convert h2 using 1
  rw [smul_smul, mul_comm]

/-- The angular curve `t ↦ coordSlice j w (r e^{it})` has velocity `r i e^{it} e_j`. -/
theorem hasDerivAt_coordSlice_angle (r : ℝ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => coordSlice j w (polarMap (r, t)))
      (r • Complex.I • polarDir j θ) θ := by
  simp_rw [coordSlice_polarMap]
  exact ((hasDerivAt_polarDir j θ).const_smul r).const_add _

/-- The angular velocity `t ↦ r i e^{it} e_j` has derivative `-r e^{iθ} e_j`. -/
theorem hasDerivAt_angle_velocity (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => r • Complex.I • polarDir j t) (-(r • polarDir j θ)) θ := by
  have h := ((hasDerivAt_polarDir j θ).const_smul Complex.I).const_smul r
  convert h using 1
  rw [smul_smul Complex.I Complex.I, Complex.I_mul_I, neg_one_smul, smul_neg]

variable {j w}

/-- **Radial second derivative** of `F(s) = f(coordSlice j w (s^a e^{iθ}))`. -/
theorem deriv_deriv_radial {f : E n → ℝ} {θ a s : ℝ} (hs : 0 < s)
    (hf : ContDiffAt ℝ 2 f (coordSlice j w (polarMap (s ^ a, θ)))) :
    deriv (deriv fun t : ℝ => f (coordSlice j w (polarMap (t ^ a, θ)))) s =
      (a * s ^ (a - 1)) ^ 2 *
          fderiv ℝ (fderiv ℝ f) (coordSlice j w (polarMap (s ^ a, θ))) (polarDir j θ)
            (polarDir j θ) +
        a * (a - 1) * s ^ (a - 2) *
          fderiv ℝ f (coordSlice j w (polarMap (s ^ a, θ))) (polarDir j θ) := by
  have hγ : ∀ᶠ t in 𝓝 s, HasDerivAt (fun t : ℝ => coordSlice j w (polarMap (t ^ a, θ)))
      ((a * t ^ (a - 1)) • polarDir j θ) t := by
    filter_upwards [lt_mem_nhds hs] with t ht
    exact hasDerivAt_coordSlice_rpow j w θ a ht
  have hγ' : HasDerivAt (fun t : ℝ => (a * t ^ (a - 1)) • polarDir j θ)
      ((a * ((a - 1) * s ^ (a - 1 - 1))) • polarDir j θ) s :=
    ((Real.hasDerivAt_rpow_const (Or.inl hs.ne')).const_mul a).smul_const _
  rw [deriv_deriv_comp_curve hf hγ hγ']
  simp only [map_smul, _root_.smul_apply, smul_eq_mul]
  rw [show a - 1 - 1 = a - 2 by ring]
  ring

/-- **Radial first derivative.** -/
theorem deriv_radial {f : E n → ℝ} {θ a s : ℝ} (hs : 0 < s)
    (hf : DifferentiableAt ℝ f (coordSlice j w (polarMap (s ^ a, θ)))) :
    deriv (fun t : ℝ => f (coordSlice j w (polarMap (t ^ a, θ)))) s =
      a * s ^ (a - 1) * fderiv ℝ f (coordSlice j w (polarMap (s ^ a, θ))) (polarDir j θ) := by
  rw [deriv_comp_curve hf (hasDerivAt_coordSlice_rpow j w θ a hs), map_smul, smul_eq_mul]

/-- **Angular second derivative** of `t ↦ f(coordSlice j w (r e^{it}))`. -/
theorem deriv_deriv_angle {f : E n → ℝ} {r θ : ℝ}
    (hf : ContDiffAt ℝ 2 f (coordSlice j w (polarMap (r, θ)))) :
    deriv (deriv fun t : ℝ => f (coordSlice j w (polarMap (r, t)))) θ =
      r ^ 2 * fderiv ℝ (fderiv ℝ f) (coordSlice j w (polarMap (r, θ)))
          (Complex.I • polarDir j θ) (Complex.I • polarDir j θ) -
        r * fderiv ℝ f (coordSlice j w (polarMap (r, θ))) (polarDir j θ) := by
  have hγ : ∀ᶠ t in 𝓝 θ, HasDerivAt (fun t : ℝ => coordSlice j w (polarMap (r, t)))
      (r • Complex.I • polarDir j t) t :=
    Eventually.of_forall fun t => hasDerivAt_coordSlice_angle j w r t
  rw [deriv_deriv_comp_curve hf hγ (hasDerivAt_angle_velocity j r θ)]
  simp only [map_smul, map_neg, _root_.smul_apply, smul_eq_mul]
  ring

/-- **The Euclidean Laplacian in polar coordinates.** For `G(r, θ) = f(coordSlice j w (r e^{iθ}))`
and `r > 0`: `G_rr + r⁻¹ G_r + r⁻² G_θθ = Δ_{z_j} f`. -/
theorem coordLaplacian_polar {f : E n → ℝ} {r θ : ℝ} (hr : 0 < r)
    (hf : ContDiffAt ℝ 2 f (coordSlice j w (polarMap (r, θ)))) :
    deriv (deriv fun s : ℝ => f (coordSlice j w (polarMap (s, θ)))) r +
        r⁻¹ * deriv (fun s : ℝ => f (coordSlice j w (polarMap (s, θ)))) r +
        r⁻¹ ^ 2 * deriv (deriv fun t : ℝ => f (coordSlice j w (polarMap (r, t)))) θ =
      coordLaplacian j f (coordSlice j w (polarMap (r, θ))) := by
  have hrpow : ∀ s : ℝ, s ^ (1 : ℝ) = s := fun s => Real.rpow_one s
  have h1 := deriv_deriv_radial (a := 1) (θ := θ) hr (f := f) (by rwa [hrpow])
  have h2 := deriv_radial (a := 1) (θ := θ) hr (f := f)
    (by rw [hrpow]; exact hf.differentiableAt (by norm_num))
  simp only [hrpow] at h1 h2
  rw [h1, h2, deriv_deriv_angle hf, ← coordLaplacian_eq_rotate j f _ θ]
  simp only [sub_self, Real.rpow_zero]
  field_simp
  ring

/-- **The cone Laplacian identity in one coordinate.** Let `F(ρ, θ) = f(coordSlice j w
(ρ^{1/β} e^{iθ}))` with `β > 0`, `ρ > 0`. Then
`F_ρρ + ρ⁻¹ F_ρ + (βρ)⁻² F_θθ = β⁻² ρ^(2/β - 2) Δ_{z_j} f`. -/
theorem coordLaplacian_conePolar {f : E n → ℝ} {β ρ θ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (hf : ContDiffAt ℝ 2 f (coordSlice j w (polarMap (ρ ^ β⁻¹, θ)))) :
    deriv (deriv fun s : ℝ => f (coordSlice j w (polarMap (s ^ β⁻¹, θ)))) ρ +
        ρ⁻¹ * deriv (fun s : ℝ => f (coordSlice j w (polarMap (s ^ β⁻¹, θ)))) ρ +
        (β * ρ)⁻¹ ^ 2 *
          deriv (deriv fun t : ℝ => f (coordSlice j w (polarMap (ρ ^ β⁻¹, t)))) θ =
      β⁻¹ ^ 2 * ρ ^ (2 * β⁻¹ - 2) * coordLaplacian j f (coordSlice j w (polarMap (ρ ^ β⁻¹, θ))) := by
  set p := coordSlice j w (polarMap (ρ ^ β⁻¹, θ))
  set a := β⁻¹ with ha_def
  have ha : 0 < a := inv_pos.mpr hβ
  rw [deriv_deriv_radial hρ hf, deriv_radial hρ (hf.differentiableAt (by norm_num)),
    deriv_deriv_angle hf, ← coordLaplacian_eq_rotate j f p θ]
  set A := fderiv ℝ (fderiv ℝ f) p (polarDir j θ) (polarDir j θ)
  set B := fderiv ℝ (fderiv ℝ f) p (Complex.I • polarDir j θ) (Complex.I • polarDir j θ)
  set D := fderiv ℝ f p (polarDir j θ)
  -- powers of `ρ`
  have hpow1 : ρ ^ (a - 1) = ρ ^ a * ρ⁻¹ := by
    rw [Real.rpow_sub hρ, Real.rpow_one, div_eq_mul_inv]
  have hpow2 : ρ ^ (a - 2) = ρ ^ a * ρ⁻¹ ^ 2 := by
    rw [Real.rpow_sub hρ, Real.rpow_two, div_eq_mul_inv, inv_pow]
  have hpow3 : ρ ^ (2 * a - 2) = (ρ ^ a) ^ 2 * ρ⁻¹ ^ 2 := by
    have e2 : ρ ^ (2 * a) = (ρ ^ a) ^ 2 := by
      rw [mul_comm, Real.rpow_mul hρ.le, Real.rpow_two]
    rw [Real.rpow_sub hρ, e2, Real.rpow_two, div_eq_mul_inv, inv_pow]
  have hβa : β = a⁻¹ := by rw [ha_def, inv_inv]
  rw [hpow1, hpow2, hpow3, hβa]
  field_simp
  ring

end Polar

end ConicalKahler
