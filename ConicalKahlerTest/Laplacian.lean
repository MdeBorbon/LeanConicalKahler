module

public import ConicalKahler

/-!
# Tests for the Laplace–Beltrami operator of the cone models
-/

namespace ConicalKahler.Test

open ConicalKahler
open scoped Manifold ContDiff Topology

/-- `β = 1`: the standard "cone" is `ℂ` with `g = 2(dx² + dy²)`, and the polar formula is the usual
one, with the factor `½` of the normalisation. -/
example {f : E 1 → ℝ} (hf : ContDiffOn ℝ ∞ f (modelDomain (singleConeWeights (n := 1) ConeAngle.one)))
    (w : E 1) {r φ : ℝ} (hr : 0 < r) :
    laplaceBeltrami (standardConeForm (n := 1) ConeAngle.one) (restrictSmooth _ hf)
        ⟨coordSlice 0 w (polarMap (r ^ ConeAngle.one.beta⁻¹, φ)),
          (by rw [mem_modelDomain_single, coordSlice_apply_self]
              exact polarMap_ne_zero (Real.rpow_pos_of_pos hr _))⟩ =
      (deriv (deriv fun s : ℝ => f (coordSlice 0 w (polarMap (s ^ ConeAngle.one.beta⁻¹, φ)))) r +
        r⁻¹ * deriv (fun s : ℝ => f (coordSlice 0 w (polarMap (s ^ ConeAngle.one.beta⁻¹, φ)))) r +
        (ConeAngle.one.beta * r)⁻¹ ^ 2 *
          deriv (deriv fun t : ℝ => f (coordSlice 0 w (polarMap (r ^ ConeAngle.one.beta⁻¹, t))))
            φ) / 2 :=
  laplaceBeltrami_standardCone_polar ConeAngle.one hf w hr

/-- `Re z^k` is harmonic on the standard two-dimensional cone of any angle. -/
example (β : ConeAngle) (k : ℕ) (x : modelDomain (singleConeWeights (n := 1) β)) :
    laplaceBeltrami (standardConeForm (n := 1) β)
      (restrictSmooth _ (contDiffOn_re_of_contDiffOn (contDiff_coord_pow (0 : Fin 1) k).contDiffOn))
      x = 0 :=
  laplaceBeltrami_re_pow_eq_zero _ 0 k x

/-- `Im z_1^k` is harmonic on the product of two cones with angles `π` and `2π/3`. -/
example (k : ℕ) (x : modelDomain (coordSNCWeights (n := 2) le_rfl
      ![⟨1 / 2, by norm_num⟩, ⟨1 / 3, by norm_num⟩])) :
    laplaceBeltrami (ModelConeForm (coordSNCWeights (n := 2) le_rfl
        ![⟨1 / 2, by norm_num⟩, ⟨1 / 3, by norm_num⟩]))
      (restrictSmooth _ (contDiffOn_im_of_contDiffOn (contDiff_coord_pow (1 : Fin 2) k).contDiffOn))
      x = 0 :=
  laplaceBeltrami_im_pow_eq_zero _ 1 k x

/-- **Cross-check of the two routes.** Through the polar formula, the Laplacian of `Re z^k` is half
the polar Laplace operator applied to `ρ^{k/β} cos(kθ)`, which vanishes. -/
example (β : ConeAngle) (k : ℕ) (w : E 1) {ρ φ : ℝ} (hρ : 0 < ρ) :
    (deriv (deriv fun s : ℝ =>
          ((coordSlice 0 w (polarMap (s ^ β.beta⁻¹, φ)) 0) ^ k).re) ρ +
        ρ⁻¹ * deriv (fun s : ℝ => ((coordSlice 0 w (polarMap (s ^ β.beta⁻¹, φ)) 0) ^ k).re) ρ +
        (β.beta * ρ)⁻¹ ^ 2 *
          deriv (deriv fun t : ℝ => ((coordSlice 0 w (polarMap (ρ ^ β.beta⁻¹, t)) 0) ^ k).re)
            φ) = 0 := by
  -- near `ρ`, the radial slice is `s ↦ u_k(s, φ)`; the angular slice is `t ↦ u_k(ρ, t)`
  have hrad : (fun s : ℝ => ((coordSlice 0 w (polarMap (s ^ β.beta⁻¹, φ)) 0) ^ k).re) =ᶠ[𝓝 ρ]
      fun s => coneHarmonicCos β.beta k s φ := by
    filter_upwards [lt_mem_nhds hρ] with s hs
    exact re_pow_coordSlice_conePolar 0 w hs φ
  have hang : (fun t : ℝ => ((coordSlice 0 w (polarMap (ρ ^ β.beta⁻¹, t)) 0) ^ k).re) =
      fun t => coneHarmonicCos β.beta k ρ t :=
    funext fun t => re_pow_coordSlice_conePolar 0 w hρ t
  rw [hrad.deriv.deriv_eq, hrad.deriv_eq, hang]
  exact coneHarmonicCos_polar_eq_zero β.pos hρ

/-- Product of a cone of angle `π` and a Euclidean factor: `Δ_g f = Δ_{z_0} f / (2 w_0) + ½ Δ_{z_1} f`. -/
example {f : E 2 → ℝ}
    (hf : ContDiffOn ℝ ∞ f (modelDomain (singleConeWeights (n := 2) ⟨1 / 2, by norm_num⟩)))
    (x : modelDomain (singleConeWeights (n := 2) ⟨1 / 2, by norm_num⟩)) :
    laplaceBeltrami (standardConeForm (n := 2) ⟨1 / 2, by norm_num⟩) (restrictSmooth _ hf) x =
      coordLaplacian 0 f x /
          (2 * modelWeight (singleConeWeights (n := 2) ⟨1 / 2, by norm_num⟩) x 0) +
        coordLaplacian 1 f x / 2 := by
  rw [show standardConeForm (n := 2) ⟨1 / 2, by norm_num⟩ =
      modelConeFormOn (singleConeWeights ⟨1 / 2, by norm_num⟩) _ subset_rfl from rfl,
    laplaceBeltrami_modelConeFormOn, Fin.sum_univ_two,
    modelWeight_of_none (singleConeWeights_angle_of_ne _ (by decide : (1 : Fin 2) ≠ 0)), mul_one]

/-- The two-cone weights with angles `π` and `2π/3`. -/
noncomputable abbrev twoConeAngles : ConeWeights 2 :=
  coordSNCWeights (n := 2) le_rfl ![⟨1 / 2, by norm_num⟩, ⟨1 / 3, by norm_num⟩]

/-- The cone dilation scales the product metric by `λ²`. -/
example (lam : ℝ) (hlam : 0 < lam) (z v : E 2) :
    modelConeQuadratic twoConeAngles (coneDilation twoConeAngles lam z)
        (coneDilation twoConeAngles lam v) =
      lam ^ 2 * modelConeQuadratic twoConeAngles z v :=
  modelConeQuadratic_coneDilation _ hlam z v

/-- Angle `π` (`β = 1/2`), `k = 1`: `u_1 = ρ² cos θ`; its gradient norm is `4ρ²`. -/
example {ρ θ : ℝ} (hρ : 0 < ρ) :
    (deriv (fun s => coneHarmonicCos (1 / 2) 1 s θ) ρ) ^ 2 +
        ((1 / 2) * ρ)⁻¹ ^ 2 * (deriv (fun t => coneHarmonicCos (1 / 2) 1 ρ t) θ) ^ 2 =
      4 * ρ ^ (2 : ℝ) := by
  rw [coneHarmonicCos_gradNormSq (by norm_num) hρ]
  norm_num

/-- Homogeneity of degree `k/β`. -/
example (β : ℝ) (k : ℕ) {lam ρ : ℝ} (hlam : 0 ≤ lam) (hρ : 0 ≤ ρ) (θ : ℝ) :
    coneHarmonicSin β k (lam * ρ) θ = lam ^ ((k : ℝ) / β) * coneHarmonicSin β k ρ θ :=
  coneHarmonicSin_homogeneous hlam hρ θ

end ConicalKahler.Test
