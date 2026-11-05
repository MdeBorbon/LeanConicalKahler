module

public import ConicalKahler.Laplacian.Polar

/-!
# The basic harmonic functions of the cone

On the cone of angle `2πβ`, in the coordinates `(ρ, θ)` with `ρ = r^β`, the functions

  `u_k(ρ, θ) = ρ^{k/β} cos(kθ)`,  `v_k(ρ, θ) = ρ^{k/β} sin(kθ)`  (`k ∈ ℕ`)

are the separated-variable solutions of `F_ρρ + ρ⁻¹ F_ρ + (βρ)⁻² F_θθ = 0` that are `2π`-periodic
in `θ` and bounded at the vertex. In the complex coordinate `z = r e^{iθ}` they are `Re z^k` and
`Im z^k`.

## Main results

* `coneHarmonicCos_polar_eq_zero`, `coneHarmonicSin_polar_eq_zero`: the polar Laplace equation,
  by direct differentiation.
* `re_pow_coordSlice_conePolar`, `im_pow_coordSlice_conePolar`: in the complex coordinate `z_j`
  these are `Re z_j^k` and `Im z_j^k`.
* Homogeneity of degree `k/β`: `coneHarmonicCos_homogeneous` (`u_k(λρ, θ) = λ^{k/β} u_k(ρ, θ)`).
  In complex coordinates this is invariance under the cone dilation `z_j ↦ λ^{1/β} z_j`
  (`re_pow_coneDilate`). That dilation scales the model metric by `λ²`
  (`modelConeQuadratic_coneDilation`, for every product of cones and Euclidean factors).
* Derivatives and estimates (`ρ > 0`):
  - first and second derivatives in `ρ` and `θ` (`deriv_coneHarmonicCos_rho`, …);
  - the exact gradient norm `(∂_ρ u)² + (βρ)⁻² (∂_θ u)² = (k/β)² ρ^{2k/β - 2}`
    (`coneHarmonicCos_gradNormSq`);
  - the scale-invariant bounds `|u| ≤ ρ^{k/β}`, `|∂_ρ u| ≤ (k/β) ρ^{k/β-1}`,
    `|ρ⁻¹ ∂_θ u| ≤ k ρ^{k/β-1}`, `|∂²_ρ u| ≤ (k/β)|k/β - 1| ρ^{k/β-2}`,
    `|ρ⁻² ∂²_θ u| ≤ k² ρ^{k/β-2}` (`coneHarmonicCos_bounds`), and the same for `v_k`.

That `Re z_j^k` is annihilated by the Laplace–Beltrami operator of the cone model is proved in
`ConicalKahler.Laplacian.Model` (`laplaceBeltrami_re_pow_eq_zero`).
-/

@[expose] public section

open scoped Topology Real
open Filter Set

namespace ConicalKahler

/-! ### The functions -/

/-- `u_k(ρ, θ) = ρ^{k/β} cos(kθ)`. -/
noncomputable def coneHarmonicCos (β : ℝ) (k : ℕ) (ρ θ : ℝ) : ℝ :=
  ρ ^ ((k : ℝ) / β) * Real.cos (k * θ)

/-- `v_k(ρ, θ) = ρ^{k/β} sin(kθ)`. -/
noncomputable def coneHarmonicSin (β : ℝ) (k : ℕ) (ρ θ : ℝ) : ℝ :=
  ρ ^ ((k : ℝ) / β) * Real.sin (k * θ)

variable {β : ℝ} {k : ℕ}

/-! ### Derivatives -/

section Derivatives

variable {ρ θ : ℝ}

/-- One-variable derivatives of `s ↦ s^c K`. -/
theorem hasDerivAt_rpow_mul_const (c K : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => t ^ c * K) (c * s ^ (c - 1) * K) s :=
  (Real.hasDerivAt_rpow_const (Or.inl hs.ne')).mul_const K

theorem deriv_deriv_rpow_mul_const (c K : ℝ) {s : ℝ} (hs : 0 < s) :
    deriv (deriv fun t : ℝ => t ^ c * K) s = c * (c - 1) * s ^ (c - 2) * K := by
  have hev : deriv (fun t : ℝ => t ^ c * K) =ᶠ[𝓝 s] fun t => c * t ^ (c - 1) * K := by
    filter_upwards [lt_mem_nhds hs] with t ht
    exact (hasDerivAt_rpow_mul_const c K ht).deriv
  rw [hev.deriv_eq]
  have h := (((Real.hasDerivAt_rpow_const (p := c - 1) (Or.inl hs.ne')).const_mul c).mul_const K)
  rw [h.deriv, show c - 1 - 1 = c - 2 by ring]
  ring

theorem hasDerivAt_const_mul_cos (A : ℝ) (k θ : ℝ) :
    HasDerivAt (fun t : ℝ => A * Real.cos (k * t)) (-(A * k * Real.sin (k * θ))) θ := by
  have h := (((hasDerivAt_id' θ).const_mul k).cos).const_mul A
  convert h using 1
  ring

theorem hasDerivAt_const_mul_sin (A : ℝ) (k θ : ℝ) :
    HasDerivAt (fun t : ℝ => A * Real.sin (k * t)) (A * k * Real.cos (k * θ)) θ := by
  have h := (((hasDerivAt_id' θ).const_mul k).sin).const_mul A
  convert h using 1
  ring

theorem deriv_deriv_const_mul_cos (A k θ : ℝ) :
    deriv (deriv fun t : ℝ => A * Real.cos (k * t)) θ = -(A * k ^ 2 * Real.cos (k * θ)) := by
  have hd : deriv (fun t : ℝ => A * Real.cos (k * t)) = fun t => -(A * k) * Real.sin (k * t) :=
    funext fun t => by rw [(hasDerivAt_const_mul_cos A k t).deriv]; ring
  rw [hd, (hasDerivAt_const_mul_sin (-(A * k)) k θ).deriv]
  ring

theorem deriv_deriv_const_mul_sin (A k θ : ℝ) :
    deriv (deriv fun t : ℝ => A * Real.sin (k * t)) θ = -(A * k ^ 2 * Real.sin (k * θ)) := by
  have hd : deriv (fun t : ℝ => A * Real.sin (k * t)) = fun t => A * k * Real.cos (k * t) :=
    funext fun t => (hasDerivAt_const_mul_sin A k t).deriv
  rw [hd, (hasDerivAt_const_mul_cos (A * k) k θ).deriv]
  ring

/-- `∂_ρ u_k = (k/β) ρ^{k/β - 1} cos(kθ)`. -/
theorem deriv_coneHarmonicCos_rho (hρ : 0 < ρ) :
    deriv (fun s => coneHarmonicCos β k s θ) ρ =
      (k / β) * ρ ^ ((k : ℝ) / β - 1) * Real.cos (k * θ) :=
  (hasDerivAt_rpow_mul_const _ _ hρ).deriv

/-- `∂²_ρ u_k = (k/β)(k/β - 1) ρ^{k/β - 2} cos(kθ)`. -/
theorem deriv_deriv_coneHarmonicCos_rho (hρ : 0 < ρ) :
    deriv (deriv fun s => coneHarmonicCos β k s θ) ρ =
      (k / β) * ((k / β) - 1) * ρ ^ ((k : ℝ) / β - 2) * Real.cos (k * θ) :=
  deriv_deriv_rpow_mul_const _ _ hρ

/-- `∂_θ u_k = -k ρ^{k/β} sin(kθ)`. -/
theorem deriv_coneHarmonicCos_theta :
    deriv (fun t => coneHarmonicCos β k ρ t) θ = -(ρ ^ ((k : ℝ) / β) * k * Real.sin (k * θ)) :=
  (hasDerivAt_const_mul_cos _ _ θ).deriv

/-- `∂²_θ u_k = -k² ρ^{k/β} cos(kθ)`. -/
theorem deriv_deriv_coneHarmonicCos_theta :
    deriv (deriv fun t => coneHarmonicCos β k ρ t) θ =
      -(ρ ^ ((k : ℝ) / β) * (k : ℝ) ^ 2 * Real.cos (k * θ)) :=
  deriv_deriv_const_mul_cos _ _ θ

theorem deriv_coneHarmonicSin_rho (hρ : 0 < ρ) :
    deriv (fun s => coneHarmonicSin β k s θ) ρ =
      (k / β) * ρ ^ ((k : ℝ) / β - 1) * Real.sin (k * θ) :=
  (hasDerivAt_rpow_mul_const _ _ hρ).deriv

theorem deriv_deriv_coneHarmonicSin_rho (hρ : 0 < ρ) :
    deriv (deriv fun s => coneHarmonicSin β k s θ) ρ =
      (k / β) * ((k / β) - 1) * ρ ^ ((k : ℝ) / β - 2) * Real.sin (k * θ) :=
  deriv_deriv_rpow_mul_const _ _ hρ

theorem deriv_coneHarmonicSin_theta :
    deriv (fun t => coneHarmonicSin β k ρ t) θ = ρ ^ ((k : ℝ) / β) * k * Real.cos (k * θ) :=
  (hasDerivAt_const_mul_sin _ _ θ).deriv

theorem deriv_deriv_coneHarmonicSin_theta :
    deriv (deriv fun t => coneHarmonicSin β k ρ t) θ =
      -(ρ ^ ((k : ℝ) / β) * (k : ℝ) ^ 2 * Real.sin (k * θ)) :=
  deriv_deriv_const_mul_sin _ _ θ

/-- Powers of `ρ` used below. -/
theorem rpow_sub_one_mul_inv (c : ℝ) (hρ : 0 < ρ) : ρ⁻¹ * ρ ^ (c - 1) = ρ ^ (c - 2) := by
  rw [Real.rpow_sub hρ, Real.rpow_sub hρ, Real.rpow_one, Real.rpow_two]
  field_simp

theorem rpow_mul_inv_sq (c : ℝ) (hρ : 0 < ρ) : ρ ^ c * ρ⁻¹ ^ 2 = ρ ^ (c - 2) := by
  rw [Real.rpow_sub hρ, Real.rpow_two]
  field_simp

end Derivatives

/-! ### The polar Laplace equation -/

/-- **`u_k = ρ^{k/β} cos(kθ)` is harmonic** for the cone Laplacian in polar form:
`∂²_ρ u + ρ⁻¹ ∂_ρ u + (βρ)⁻² ∂²_θ u = 0` for `ρ > 0`. -/
theorem coneHarmonicCos_polar_eq_zero (hβ : 0 < β) {ρ θ : ℝ} (hρ : 0 < ρ) :
    deriv (deriv fun s => coneHarmonicCos β k s θ) ρ +
        ρ⁻¹ * deriv (fun s => coneHarmonicCos β k s θ) ρ +
        (β * ρ)⁻¹ ^ 2 * deriv (deriv fun t => coneHarmonicCos β k ρ t) θ = 0 := by
  rw [deriv_deriv_coneHarmonicCos_rho hρ, deriv_coneHarmonicCos_rho hρ,
    deriv_deriv_coneHarmonicCos_theta]
  have h1 := rpow_sub_one_mul_inv ((k : ℝ) / β) hρ
  have h2 := rpow_mul_inv_sq ((k : ℝ) / β) hρ
  have hβ0 := hβ.ne'
  calc (k / β) * ((k / β) - 1) * ρ ^ ((k : ℝ) / β - 2) * Real.cos (k * θ) +
        ρ⁻¹ * ((k / β) * ρ ^ ((k : ℝ) / β - 1) * Real.cos (k * θ)) +
        (β * ρ)⁻¹ ^ 2 * -(ρ ^ ((k : ℝ) / β) * (k : ℝ) ^ 2 * Real.cos (k * θ))
      = (k / β) * ((k / β) - 1) * ρ ^ ((k : ℝ) / β - 2) * Real.cos (k * θ) +
          (k / β) * (ρ⁻¹ * ρ ^ ((k : ℝ) / β - 1)) * Real.cos (k * θ) -
          (k : ℝ) ^ 2 / β ^ 2 * (ρ ^ ((k : ℝ) / β) * ρ⁻¹ ^ 2) * Real.cos (k * θ) := by
        rw [mul_inv, mul_pow]
        field_simp
        ring
    _ = 0 := by rw [h1, h2]; field_simp; ring

/-- **`v_k = ρ^{k/β} sin(kθ)` is harmonic** for the cone Laplacian in polar form. -/
theorem coneHarmonicSin_polar_eq_zero (hβ : 0 < β) {ρ θ : ℝ} (hρ : 0 < ρ) :
    deriv (deriv fun s => coneHarmonicSin β k s θ) ρ +
        ρ⁻¹ * deriv (fun s => coneHarmonicSin β k s θ) ρ +
        (β * ρ)⁻¹ ^ 2 * deriv (deriv fun t => coneHarmonicSin β k ρ t) θ = 0 := by
  rw [deriv_deriv_coneHarmonicSin_rho hρ, deriv_coneHarmonicSin_rho hρ,
    deriv_deriv_coneHarmonicSin_theta]
  have h1 := rpow_sub_one_mul_inv ((k : ℝ) / β) hρ
  have h2 := rpow_mul_inv_sq ((k : ℝ) / β) hρ
  have hβ0 := hβ.ne'
  calc (k / β) * ((k / β) - 1) * ρ ^ ((k : ℝ) / β - 2) * Real.sin (k * θ) +
        ρ⁻¹ * ((k / β) * ρ ^ ((k : ℝ) / β - 1) * Real.sin (k * θ)) +
        (β * ρ)⁻¹ ^ 2 * -(ρ ^ ((k : ℝ) / β) * (k : ℝ) ^ 2 * Real.sin (k * θ))
      = (k / β) * ((k / β) - 1) * ρ ^ ((k : ℝ) / β - 2) * Real.sin (k * θ) +
          (k / β) * (ρ⁻¹ * ρ ^ ((k : ℝ) / β - 1)) * Real.sin (k * θ) -
          (k : ℝ) ^ 2 / β ^ 2 * (ρ ^ ((k : ℝ) / β) * ρ⁻¹ ^ 2) * Real.sin (k * θ) := by
        rw [mul_inv, mul_pow]
        field_simp
        ring
    _ = 0 := by rw [h1, h2]; field_simp; ring

/-! ### Complex form: `Re z^k` and `Im z^k` -/

/-- `(r e^{iθ})^k = r^k e^{ikθ}`, so its real part is `r^k cos(kθ)`. -/
theorem re_polarMap_pow (r θ : ℝ) (k : ℕ) :
    (polarMap (r, θ) ^ k).re = r ^ k * Real.cos (k * θ) := by
  rw [polarMap, mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow]
  rw [show (k : ℂ) * (θ * Complex.I) = ((k * θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem im_polarMap_pow (r θ : ℝ) (k : ℕ) :
    (polarMap (r, θ) ^ k).im = r ^ k * Real.sin (k * θ) := by
  rw [polarMap, mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow]
  rw [show (k : ℂ) * (θ * Complex.I) = ((k * θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

theorem rpow_inv_pow {β ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) : (ρ ^ β⁻¹) ^ k = ρ ^ ((k : ℝ) / β) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
  congr 1
  ring

/-- In the cone coordinates of the complex coordinate `z_j`, `Re z_j^k = u_k(ρ, θ)`. -/
theorem re_pow_coordSlice_conePolar {n : ℕ} (j : Fin n) (w : E n) {ρ : ℝ} (hρ : 0 < ρ)
    (θ : ℝ) : ((coordSlice j w (polarMap (ρ ^ β⁻¹, θ)) j) ^ k).re = coneHarmonicCos β k ρ θ := by
  rw [coordSlice_apply_self, re_polarMap_pow, rpow_inv_pow hρ, coneHarmonicCos]

/-- In the cone coordinates of the complex coordinate `z_j`, `Im z_j^k = v_k(ρ, θ)`. -/
theorem im_pow_coordSlice_conePolar {n : ℕ} (j : Fin n) (w : E n) {ρ : ℝ} (hρ : 0 < ρ)
    (θ : ℝ) : ((coordSlice j w (polarMap (ρ ^ β⁻¹, θ)) j) ^ k).im = coneHarmonicSin β k ρ θ := by
  rw [coordSlice_apply_self, im_polarMap_pow, rpow_inv_pow hρ, coneHarmonicSin]

/-! ### Homogeneity -/

/-- **Homogeneity of degree `k/β`:** `u_k(λρ, θ) = λ^{k/β} u_k(ρ, θ)`. -/
theorem coneHarmonicCos_homogeneous {lam ρ : ℝ} (hlam : 0 ≤ lam) (hρ : 0 ≤ ρ) (θ : ℝ) :
    coneHarmonicCos β k (lam * ρ) θ = lam ^ ((k : ℝ) / β) * coneHarmonicCos β k ρ θ := by
  rw [coneHarmonicCos, coneHarmonicCos, Real.mul_rpow hlam hρ]
  ring

theorem coneHarmonicSin_homogeneous {lam ρ : ℝ} (hlam : 0 ≤ lam) (hρ : 0 ≤ ρ) (θ : ℝ) :
    coneHarmonicSin β k (lam * ρ) θ = lam ^ ((k : ℝ) / β) * coneHarmonicSin β k ρ θ := by
  rw [coneHarmonicSin, coneHarmonicSin, Real.mul_rpow hlam hρ]
  ring

/-- In complex coordinates: under the cone dilation `z ↦ λ^{1/β} z` (which multiplies `ρ` by
`λ`), `Re z^k` is multiplied by `λ^{k/β}`. -/
theorem re_pow_coneDilate {lam : ℝ} (hlam : 0 ≤ lam) (z : ℂ) :
    ((((lam ^ β⁻¹ : ℝ) : ℂ) * z) ^ k).re = lam ^ ((k : ℝ) / β) * (z ^ k).re := by
  rw [mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul, ← Real.rpow_natCast,
    ← Real.rpow_mul hlam]
  congr 2
  ring

theorem im_pow_coneDilate {lam : ℝ} (hlam : 0 ≤ lam) (z : ℂ) :
    ((((lam ^ β⁻¹ : ℝ) : ℂ) * z) ^ k).im = lam ^ ((k : ℝ) / β) * (z ^ k).im := by
  rw [mul_pow, ← Complex.ofReal_pow, Complex.im_ofReal_mul, ← Real.rpow_natCast,
    ← Real.rpow_mul hlam]
  congr 2
  ring

/-! ### Derivative identities and estimates -/

section Estimates

variable {ρ θ : ℝ}

/-- **Exact gradient norm** for the cone metric `dρ² + β² ρ² dθ²`:
`(∂_ρ u_k)² + (βρ)⁻² (∂_θ u_k)² = (k/β)² ρ^{2k/β - 2}`. -/
theorem coneHarmonicCos_gradNormSq (hβ : 0 < β) (hρ : 0 < ρ) :
    (deriv (fun s => coneHarmonicCos β k s θ) ρ) ^ 2 +
        (β * ρ)⁻¹ ^ 2 * (deriv (fun t => coneHarmonicCos β k ρ t) θ) ^ 2 =
      ((k : ℝ) / β) ^ 2 * ρ ^ (2 * ((k : ℝ) / β) - 2) := by
  rw [deriv_coneHarmonicCos_rho hρ, deriv_coneHarmonicCos_theta]
  have e1 : (ρ ^ ((k : ℝ) / β - 1)) ^ 2 = ρ ^ (2 * ((k : ℝ) / β) - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
    ring_nf
  have e2 : (ρ ^ ((k : ℝ) / β)) ^ 2 * ρ⁻¹ ^ 2 = ρ ^ (2 * ((k : ℝ) / β) - 2) := by
    rw [← mul_pow, ← e1, Real.rpow_sub_one hρ.ne']
    ring
  have hc := Real.cos_sq_add_sin_sq (k * θ)
  have hβ0 := hβ.ne'
  calc ((k / β) * ρ ^ ((k : ℝ) / β - 1) * Real.cos (k * θ)) ^ 2 +
        (β * ρ)⁻¹ ^ 2 * (-(ρ ^ ((k : ℝ) / β) * k * Real.sin (k * θ))) ^ 2
      = ((k : ℝ) / β) ^ 2 * ((ρ ^ ((k : ℝ) / β - 1)) ^ 2 * Real.cos (k * θ) ^ 2 +
          (ρ ^ ((k : ℝ) / β)) ^ 2 * ρ⁻¹ ^ 2 * Real.sin (k * θ) ^ 2) := by
        rw [mul_inv, mul_pow]
        field_simp
    _ = ((k : ℝ) / β) ^ 2 * ρ ^ (2 * ((k : ℝ) / β) - 2) := by
        rw [e1, e2]
        linear_combination ((k : ℝ) / β) ^ 2 * ρ ^ (2 * ((k : ℝ) / β) - 2) * hc

theorem coneHarmonicSin_gradNormSq (hβ : 0 < β) (hρ : 0 < ρ) :
    (deriv (fun s => coneHarmonicSin β k s θ) ρ) ^ 2 +
        (β * ρ)⁻¹ ^ 2 * (deriv (fun t => coneHarmonicSin β k ρ t) θ) ^ 2 =
      ((k : ℝ) / β) ^ 2 * ρ ^ (2 * ((k : ℝ) / β) - 2) := by
  rw [deriv_coneHarmonicSin_rho hρ, deriv_coneHarmonicSin_theta]
  have e1 : (ρ ^ ((k : ℝ) / β - 1)) ^ 2 = ρ ^ (2 * ((k : ℝ) / β) - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
    ring_nf
  have e2 : (ρ ^ ((k : ℝ) / β)) ^ 2 * ρ⁻¹ ^ 2 = ρ ^ (2 * ((k : ℝ) / β) - 2) := by
    rw [← mul_pow, ← e1, Real.rpow_sub_one hρ.ne']
    ring
  have hc := Real.cos_sq_add_sin_sq (k * θ)
  have hβ0 := hβ.ne'
  calc ((k / β) * ρ ^ ((k : ℝ) / β - 1) * Real.sin (k * θ)) ^ 2 +
        (β * ρ)⁻¹ ^ 2 * (ρ ^ ((k : ℝ) / β) * k * Real.cos (k * θ)) ^ 2
      = ((k : ℝ) / β) ^ 2 * ((ρ ^ ((k : ℝ) / β - 1)) ^ 2 * Real.sin (k * θ) ^ 2 +
          (ρ ^ ((k : ℝ) / β)) ^ 2 * ρ⁻¹ ^ 2 * Real.cos (k * θ) ^ 2) := by
        rw [mul_inv, mul_pow]
        field_simp
    _ = ((k : ℝ) / β) ^ 2 * ρ ^ (2 * ((k : ℝ) / β) - 2) := by
        rw [e1, e2]
        linear_combination ((k : ℝ) / β) ^ 2 * ρ ^ (2 * ((k : ℝ) / β) - 2) * hc

/-- **Scale-invariant bounds for `u_k`** (`ρ > 0`): `|u| ≤ ρ^{k/β}`,
`|∂_ρ u| ≤ (k/β) ρ^{k/β-1}`, `|ρ⁻¹ ∂_θ u| ≤ k ρ^{k/β-1}`,
`|∂²_ρ u| ≤ (k/β)|k/β - 1| ρ^{k/β-2}`, `|ρ⁻² ∂²_θ u| ≤ k² ρ^{k/β-2}`. -/
theorem coneHarmonicCos_bounds (hβ : 0 < β) (hρ : 0 < ρ) :
    |coneHarmonicCos β k ρ θ| ≤ ρ ^ ((k : ℝ) / β) ∧
      |deriv (fun s => coneHarmonicCos β k s θ) ρ| ≤ (k / β) * ρ ^ ((k : ℝ) / β - 1) ∧
      |ρ⁻¹ * deriv (fun t => coneHarmonicCos β k ρ t) θ| ≤ k * ρ ^ ((k : ℝ) / β - 1) ∧
      |deriv (deriv fun s => coneHarmonicCos β k s θ) ρ| ≤
        (k / β) * |(k / β) - 1| * ρ ^ ((k : ℝ) / β - 2) ∧
      |ρ⁻¹ ^ 2 * deriv (deriv fun t => coneHarmonicCos β k ρ t) θ| ≤
        (k : ℝ) ^ 2 * ρ ^ ((k : ℝ) / β - 2) := by
  have hc := Real.abs_cos_le_one (k * θ)
  have hpow0 := Real.rpow_pos_of_pos hρ ((k : ℝ) / β)
  have hpow1 := Real.rpow_pos_of_pos hρ ((k : ℝ) / β - 1)
  have hpow2 := Real.rpow_pos_of_pos hρ ((k : ℝ) / β - 2)
  have hkβ : 0 ≤ (k : ℝ) / β := div_nonneg (Nat.cast_nonneg k) hβ.le
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hs := Real.abs_sin_le_one (k * θ)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [coneHarmonicCos, abs_mul, abs_of_pos hpow0]
    exact mul_le_of_le_one_right hpow0.le hc
  · rw [deriv_coneHarmonicCos_rho hρ, abs_mul, abs_mul, abs_of_nonneg hkβ, abs_of_pos hpow1]
    exact mul_le_of_le_one_right (by positivity) hc
  · rw [deriv_coneHarmonicCos_theta]
    have e : ρ⁻¹ * ρ ^ ((k : ℝ) / β) = ρ ^ ((k : ℝ) / β - 1) := by
      rw [Real.rpow_sub_one hρ.ne']
      field_simp
    rw [show ρ⁻¹ * -(ρ ^ ((k : ℝ) / β) * k * Real.sin (k * θ)) =
        -(k * (ρ⁻¹ * ρ ^ ((k : ℝ) / β)) * Real.sin (k * θ)) by ring, e, abs_neg, abs_mul,
      abs_mul, abs_of_nonneg hk, abs_of_pos hpow1]
    exact mul_le_of_le_one_right (by positivity) hs
  · rw [deriv_deriv_coneHarmonicCos_rho hρ, abs_mul, abs_mul, abs_mul, abs_of_nonneg hkβ,
      abs_of_pos hpow2]
    exact mul_le_of_le_one_right (by positivity) hc
  · rw [deriv_deriv_coneHarmonicCos_theta, ← rpow_mul_inv_sq ((k : ℝ) / β) hρ]
    rw [show ρ⁻¹ ^ 2 * -(ρ ^ ((k : ℝ) / β) * (k : ℝ) ^ 2 * Real.cos (k * θ)) =
      -((k : ℝ) ^ 2 * (ρ ^ ((k : ℝ) / β) * ρ⁻¹ ^ 2) * Real.cos (k * θ)) by ring]
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (by positivity : 0 ≤ ρ ^ ((k : ℝ) / β) * ρ⁻¹ ^ 2)]
    exact mul_le_of_le_one_right (by positivity) hc

/-- **Scale-invariant bounds for `v_k`** (`ρ > 0`): `|u| ≤ ρ^{k/β}`,
`|∂_ρ u| ≤ (k/β) ρ^{k/β-1}`, `|ρ⁻¹ ∂_θ u| ≤ k ρ^{k/β-1}`,
`|∂²_ρ u| ≤ (k/β)|k/β - 1| ρ^{k/β-2}`, `|ρ⁻² ∂²_θ u| ≤ k² ρ^{k/β-2}`. -/
theorem coneHarmonicSin_bounds (hβ : 0 < β) (hρ : 0 < ρ) :
    |coneHarmonicSin β k ρ θ| ≤ ρ ^ ((k : ℝ) / β) ∧
      |deriv (fun s => coneHarmonicSin β k s θ) ρ| ≤ (k / β) * ρ ^ ((k : ℝ) / β - 1) ∧
      |ρ⁻¹ * deriv (fun t => coneHarmonicSin β k ρ t) θ| ≤ k * ρ ^ ((k : ℝ) / β - 1) ∧
      |deriv (deriv fun s => coneHarmonicSin β k s θ) ρ| ≤
        (k / β) * |(k / β) - 1| * ρ ^ ((k : ℝ) / β - 2) ∧
      |ρ⁻¹ ^ 2 * deriv (deriv fun t => coneHarmonicSin β k ρ t) θ| ≤
        (k : ℝ) ^ 2 * ρ ^ ((k : ℝ) / β - 2) := by
  have hc := Real.abs_cos_le_one (k * θ)
  have hpow0 := Real.rpow_pos_of_pos hρ ((k : ℝ) / β)
  have hpow1 := Real.rpow_pos_of_pos hρ ((k : ℝ) / β - 1)
  have hpow2 := Real.rpow_pos_of_pos hρ ((k : ℝ) / β - 2)
  have hkβ : 0 ≤ (k : ℝ) / β := div_nonneg (Nat.cast_nonneg k) hβ.le
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hs := Real.abs_sin_le_one (k * θ)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [coneHarmonicSin, abs_mul, abs_of_pos hpow0]
    exact mul_le_of_le_one_right hpow0.le hs
  · rw [deriv_coneHarmonicSin_rho hρ, abs_mul, abs_mul, abs_of_nonneg hkβ, abs_of_pos hpow1]
    exact mul_le_of_le_one_right (by positivity) hs
  · rw [deriv_coneHarmonicSin_theta]
    have e : ρ⁻¹ * ρ ^ ((k : ℝ) / β) = ρ ^ ((k : ℝ) / β - 1) := by
      rw [Real.rpow_sub_one hρ.ne']
      field_simp
    rw [show ρ⁻¹ * (ρ ^ ((k : ℝ) / β) * k * Real.cos (k * θ)) =
        k * (ρ⁻¹ * ρ ^ ((k : ℝ) / β)) * Real.cos (k * θ) by ring, e, abs_mul,
      abs_mul, abs_of_nonneg hk, abs_of_pos hpow1]
    exact mul_le_of_le_one_right (by positivity) hc
  · rw [deriv_deriv_coneHarmonicSin_rho hρ, abs_mul, abs_mul, abs_mul, abs_of_nonneg hkβ,
      abs_of_pos hpow2]
    exact mul_le_of_le_one_right (by positivity) hs
  · rw [deriv_deriv_coneHarmonicSin_theta, ← rpow_mul_inv_sq ((k : ℝ) / β) hρ]
    rw [show ρ⁻¹ ^ 2 * -(ρ ^ ((k : ℝ) / β) * (k : ℝ) ^ 2 * Real.sin (k * θ)) =
      -((k : ℝ) ^ 2 * (ρ ^ ((k : ℝ) / β) * ρ⁻¹ ^ 2) * Real.sin (k * θ)) by ring]
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (by positivity : 0 ≤ ρ ^ ((k : ℝ) / β) * ρ⁻¹ ^ 2)]
    exact mul_le_of_le_one_right (by positivity) hs

end Estimates

end ConicalKahler
