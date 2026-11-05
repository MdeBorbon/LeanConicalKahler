module

public import ConicalKahler.Real.D2
public import ConicalKahler.Real.Bridge
public import ConicalKahler.Laplacian.Model

/-!
# Normalisations: the project's Kähler cone and the paper's real cone

The dictionary between the two normalisations (`ROADMAP.md`) is:

| | project (Kähler) | paper (real) |
|---|---|---|
| point | `z ∈ ℂ` | `w = Φ_β(z) = |z|^{β-1} z = r e^{iθ}`, `r = |z|^β` |
| metric | `g = ω_β(·, J·) = 2 β² |z|^{2β-2} |dz|²` | `g_paper = dr² + β² r² dθ²` |
| Laplacian | `Δ_g` (`laplaceBeltrami`) | `Δ_β = ∂²_r + r⁻¹ ∂_r + (βr)⁻² ∂²_θ` |

The metric statement `g = 2 Φ_β^* g_paper` is `ConeWeights.modelConeForm_apply_I_smul_eq_two_mul`.
In real dimension `2`, the Laplacian of `g = 2 g_paper` is `Δ_g = ½ Δ_β`. Here we check this
against the upper half of the dictionary, using the Laplace–Beltrami operator of the actual Kähler
form `ω_β` (`laplaceBeltrami_eq_half_coneLaplacian`). The paper's statements about `Δ` therefore
transfer to `laplaceBeltrami` with a factor `2` (`Δ_paper = 2 Δ_g`), and conversely.
-/

@[expose] public section

open scoped Topology ContDiff
open Filter

namespace ConicalKahler

/-- **`Δ_g = ½ Δ_β`.** Let `u` be a function of the paper's real coordinate `w ∈ ℂ` whose pull-back
`f = u ∘ Φ_β ∘ z₀` to the Kähler model on `ℂ¹` is smooth on `{z₀ ≠ 0}`. At the Kähler point with
polar coordinates `(ρ^{1/β}, φ)`, i.e. the paper's point `(r, θ) = (ρ, φ)`, the Laplace–Beltrami
operator of `ω_β` applied to `f` is half the paper's cone Laplacian of `U(r, θ) = u(r e^{iθ})`. -/
theorem laplaceBeltrami_eq_half_coneLaplacian (β : ConeAngle) {u : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun z : E 1 => u (realConeChart β.beta (z 0)))
      (modelDomain (singleConeWeights (n := 1) β)))
    (w : E 1) {ρ φ : ℝ} (hρ : 0 < ρ) (c : PolarPoint (Fin 1) Empty) (hcr : c (.r 0) = ρ)
    (hcθ : c (.θ 0) = φ) :
    laplaceBeltrami (standardConeForm (n := 1) β) (restrictSmooth _ hf)
        ⟨coordSlice 0 w (polarMap (ρ ^ β.beta⁻¹, φ)),
          (by rw [mem_modelDomain_single, coordSlice_apply_self]
              exact polarMap_ne_zero (Real.rpow_pos_of_pos hρ _))⟩ =
      coneLaplacian β.beta (0 : Fin 1)
        (fun c : PolarPoint (Fin 1) Empty => u (polarMap (c (.r 0), c (.θ 0)))) c / 2 := by
  rw [laplaceBeltrami_standardCone_polar β hf w hρ]
  have hL := coneLaplacian_factor (fun x y => u (polarMap (x, y))) (0 : Fin 1) c β.beta
  rw [hL, hcr, hcθ]
  have hβ0 : β.beta ≠ 0 := β.pos.ne'
  have hev : (fun s : ℝ => u (realConeChart β.beta
      (coordSlice 0 w (polarMap (s ^ β.beta⁻¹, φ)) 0))) =ᶠ[𝓝 ρ]
        fun s => u (polarMap (s, φ)) := by
    filter_upwards [lt_mem_nhds hρ] with s hs
    rw [coordSlice_apply_self, realConeChart_polarMap hβ0 hs]
  have hθ : (fun t : ℝ => u (realConeChart β.beta
      (coordSlice 0 w (polarMap (ρ ^ β.beta⁻¹, t)) 0))) = fun t => u (polarMap (ρ, t)) := by
    funext t
    rw [coordSlice_apply_self, realConeChart_polarMap hβ0 hρ]
  rw [hev.deriv.deriv_eq, hev.deriv_eq, hθ]

end ConicalKahler
