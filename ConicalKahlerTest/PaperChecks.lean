module

public import ConicalKahler

/-!
# Lean checks of items in `PAPER_REVIEW.md`

Each section refers to an item of `PAPER_REVIEW.md` (de Borbon–Edwards, *Schauder estimates on
products of cones*). These are computations that support the items listed there as **verified**.
They do not change any definition of the project.
-/

namespace ConicalKahler.Test

open ConicalKahler
open scoped Real

/-! ### V1. Appendix A.2: the eigenvalues of `β⁻² ∂²_θ` are `k²/β²`, not `k²β²` -/

/-- `β⁻² ∂²_θ cos(kθ) = -(k²/β²) cos(kθ)`. -/
example (β k θ : ℝ) :
    β⁻¹ ^ 2 * deriv (deriv fun t => 1 * Real.cos (k * t)) θ = -(k ^ 2 / β ^ 2 * Real.cos (k * θ)) := by
  rw [deriv_deriv_const_mul_cos]
  field_simp

/-- The exponent `kβ` that the eigenvalue `k²β²` would give does not produce a harmonic function:
for `β = 1/2`, `k = 1`, the polar Laplacian of `r^{1/2} cos θ` at `(r, θ) = (1, 0)` is `-15/4`.
(`coneHarmonicCos 2 1` is `r^{1/2} cos θ`.) The correct exponent `k/β` gives `0`
(`coneHarmonicCos_polar_eq_zero`). -/
example :
    deriv (deriv fun s => coneHarmonicCos 2 1 s 0) 1 +
        (1 : ℝ)⁻¹ * deriv (fun s => coneHarmonicCos 2 1 s 0) 1 +
        (1 / 2 * 1 : ℝ)⁻¹ ^ 2 * deriv (deriv fun t => coneHarmonicCos 2 1 1 t) 0 = -15 / 4 := by
  rw [deriv_deriv_coneHarmonicCos_rho one_pos, deriv_coneHarmonicCos_rho one_pos,
    deriv_deriv_coneHarmonicCos_theta]
  norm_num

/-! ### V2. §5.1 and Appendix A.2: the complex coordinate -/

/-- Rescaling the complex coordinate `z = c ζ`: the metric `β² |ζ|^{2β-2} |dζ|²` becomes
`β² c^{-2β} |z|^{2β-2} |dz|²`. -/
theorem transverseConeMetric_rescale (β : ConeAngle) {c : ℝ} (hc : 0 < c) (ζ v : ℂ) :
    transverseConeMetric β ζ v =
      β.beta ^ 2 * c ^ (-2 * β.beta) *
        (‖(c : ℂ) * ζ‖ ^ (2 * β.beta - 2) * Complex.normSq ((c : ℂ) * v)) := by
  rw [transverseConeMetric, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
    Real.mul_rpow hc.le (norm_nonneg ζ), Complex.normSq_mul, Complex.normSq_ofReal]
  have h : c ^ (-2 * β.beta) * (c ^ (2 * β.beta - 2) * (c * c)) = 1 := by
    rw [show c * c = c ^ (2 : ℝ) by rw [Real.rpow_two]; ring, ← Real.rpow_add hc,
      ← Real.rpow_add hc, show -2 * β.beta + (2 * β.beta - 2 + 2) = 0 by ring, Real.rpow_zero]
  calc β.beta ^ 2 * ‖ζ‖ ^ (2 * β.beta - 2) * Complex.normSq v
      = β.beta ^ 2 * ‖ζ‖ ^ (2 * β.beta - 2) * Complex.normSq v *
          (c ^ (-2 * β.beta) * (c ^ (2 * β.beta - 2) * (c * c))) := by rw [h, mul_one]
    _ = _ := by ring

/-- **The corrected coordinate `z = (βr)^{1/β} e^{iθ}`**, i.e. `c = β^{1/β}` (since `r = |ζ|^β`),
gives exactly `dr² + β² r² dθ² = |z|^{2β-2} |dz|²`: the coefficient `β² c^{-2β}` is `1`. -/
example (β : ConeAngle) : β.beta ^ 2 * (β.beta ^ β.beta⁻¹) ^ (-2 * β.beta) = 1 := by
  have hb := β.pos
  rw [← Real.rpow_mul hb.le, show β.beta⁻¹ * (-2 * β.beta) = -2 by field_simp, Real.rpow_neg hb.le,
    Real.rpow_two]
  field_simp

/-- **The paper's coordinate `z = (1/β) r^{1/β} e^{iθ}`**, i.e. `c = 1/β`, gives the coefficient
`β² β^{2β} = β^{2+2β}`. For `β = 1/2` it is `1/8 ≠ 1`, so the stated identity
`dr² + β² r² dθ² = |z|^{2β-2} |dz|²` fails. -/
example : (1 / 2 : ℝ) ^ 2 * (1 / (1 / 2) : ℝ) ^ (-2 * (1 / 2 : ℝ)) = 1 / 8 := by
  norm_num [Real.rpow_neg_one]

/-- The Laplacian: in the corrected coordinate the conformal factor of `Δ_β` is
`β⁻² c^{2β} |z|^{2-2β} = |z|^{2-2β}` (from `coordLaplacian_conePolar`), so
`Δ_β = |z|^{2-2β} (∂²_x + ∂²_y) = 4 |z|^{2-2β} ∂_z ∂_{z̄}`. The constant check: -/
example (β : ConeAngle) : β.beta⁻¹ ^ 2 * (β.beta ^ β.beta⁻¹) ^ (2 * β.beta) = 1 := by
  have hb := β.pos
  rw [← Real.rpow_mul hb.le, show β.beta⁻¹ * (2 * β.beta) = 2 by field_simp, Real.rpow_two]
  field_simp

/-! ### V3. §3.4: the sign of the eigenvalue of `L_{0,0}` -/

/-- `L_{0,0} f = -4x(1-x) f'' + 2((2 + n₁ + n₂)x - 1 - n₁) f'` (eq. (3.2) with
`λ₁ = λ₂ = 0`) applied to `f(x) = (1/(n₁+1) + 1/(n₂+1)) x - 1/(n₂+1)` gives `+λ f` with
`λ = 2(n₁ + n₂ + 2)`. The paper writes `L_{0,0} f = -λ f`. -/
example (n₁ n₂ x : ℝ) (h₁ : n₁ + 1 ≠ 0) (h₂ : n₂ + 1 ≠ 0) :
    -4 * x * (1 - x) *
        deriv (deriv fun y => (1 / (n₁ + 1) + 1 / (n₂ + 1)) * y - 1 / (n₂ + 1)) x +
      2 * ((2 + n₁ + n₂) * x - 1 - n₁) *
        deriv (fun y => (1 / (n₁ + 1) + 1 / (n₂ + 1)) * y - 1 / (n₂ + 1)) x =
      2 * (n₁ + n₂ + 2) * ((1 / (n₁ + 1) + 1 / (n₂ + 1)) * x - 1 / (n₂ + 1)) := by
  set A := 1 / (n₁ + 1) + 1 / (n₂ + 1)
  set B := 1 / (n₂ + 1)
  have hd : deriv (fun y => A * y - B) = fun _ => A := funext fun y => by
    rw [(((hasDerivAt_id' y).const_mul A).sub_const B).deriv, mul_one]
  rw [hd, deriv_const, mul_zero, zero_add]
  simp only [A, B]
  field_simp
  ring

/-! ### V4. Proof of Prop. 3.4: `(1/2) r² - (m-2)⁻¹ |s|²`, not `(m-3)⁻¹` -/

theorem deriv_deriv_sq : deriv (deriv fun x : ℝ => x ^ 2) = fun _ => 2 := by
  have h : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := funext fun x => by simp
  rw [h]
  funext x
  simp

/-- In the paper's normalisation `Δ_β r² = 4`. -/
example (b : ℝ) (c : PolarPoint (Fin 1) (Fin 2)) (hr : 0 < c (.r 0)) :
    coneLaplacian b 0 (fun c : PolarPoint (Fin 1) (Fin 2) => c (.r 0) ^ 2) c = 4 := by
  simp [coneLaplacian, pd]
  field_simp
  ring

/-- `m = 4` (one cone factor and `ℝ²`): `(1/2) r² - (m-2)⁻¹ |s|²` is harmonic. -/
example (β : ConeAngle) (c : PolarPoint (Fin 1) (Fin 2)) (hr : 0 < c (.r 0)) :
    paperLaplacian (fun _ : Fin 1 => β)
      (fun c => c (.r 0) ^ 2 / 2 - (4 - 2 : ℝ)⁻¹ * (c (.s 0) ^ 2 + c (.s 1) ^ 2)) c = 0 := by
  simp [paperLaplacian, coneLaplacian, pd, Fin.sum_univ_two, deriv_deriv_sq]
  field_simp
  ring

/-- `m = 4`: with the paper's coefficient `(m-3)⁻¹ = 1` the function is not harmonic. -/
example (β : ConeAngle) (c : PolarPoint (Fin 1) (Fin 2)) (hr : 0 < c (.r 0)) :
    paperLaplacian (fun _ : Fin 1 => β)
      (fun c => c (.r 0) ^ 2 / 2 - (4 - 3 : ℝ)⁻¹ * (c (.s 0) ^ 2 + c (.s 1) ^ 2)) c = -2 := by
  simp [paperLaplacian, coneLaplacian, pd, Fin.sum_univ_two, deriv_deriv_sq]
  field_simp
  ring

/-! ### V5. The restriction `β_a < 1/2` in `𝒟₂` must exclude `β_a = 1/2` -/

/-- At `β = 1/2` the excluded operator `∂²_r` maps the harmonic function `r² cos θ` to `2 cos θ`,
which is not Hölder near the vertex for any exponent. The paper's introduction (item 1) writes
"`β_a > 1/2`", the definition of `𝒟₂` writes "`β ≥ 1/2`". The definition is the correct one. -/
example (a : Fin 1) {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    ¬ HolderNearVertex ⟨1 / 2, by norm_num⟩ α ε
      (radialCosFn ((1 / 2 : ℝ)⁻¹ * ((1 / 2 : ℝ)⁻¹ - 1)) ((1 / 2 : ℝ)⁻¹ - 2)) :=
  (not_holderNearVertex_pure_of_half_le (ι := Empty) (β := ⟨1 / 2, by norm_num⟩) (by norm_num)
    (by norm_num) a hα hε).2

/-! ### V6. Appendix A.1: the constant `c_β` -/

/-- For `0 < β ≤ 1`, the cone distance from `(d, 0)` to a point `(s, π)` of the opposite ray is at
least `d sin(πβ)`, with equality at `s = d cos(πβ)`. So the unit ball about `(d, 0)` meets the cut
`{θ = π}` unless `d sin(πβ) ≥ 1`. For `β ≤ 1/2` it is Euclidean iff `d ≥ 1/sin(πβ)`, not `sin(πβ)`
as written. -/
theorem coneDist_opposite_ray {β d s : ℝ} (hβ1 : β ≤ 1) (hd : 0 < d) (hs : 0 < s) :
    coneDist β (polarMap (d, 0)) (polarMap (s, π)) = hingeDist d s (β * π) := by
  rw [coneDist, coneVertexAngle, angle_polarMap hd hs (by rw [zero_sub, abs_neg,
      abs_of_pos Real.pi_pos]),
    zero_sub, abs_neg, abs_of_pos Real.pi_pos, norm_polarMap_of_nonneg hd.le,
    norm_polarMap_of_nonneg hs.le, min_eq_left (mul_le_of_le_one_left Real.pi_pos.le hβ1)]

theorem mul_sin_le_hingeDist (d s φ : ℝ) : d * Real.sin φ ≤ hingeDist d s φ := by
  rw [hingeDist]
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (s - d * Real.cos φ), Real.sin_sq_add_cos_sq φ]

theorem hingeDist_cos {d φ : ℝ} (hd : 0 ≤ d) (hφ0 : 0 ≤ φ) (hφπ : φ ≤ π) :
    hingeDist d (d * Real.cos φ) φ = d * Real.sin φ := by
  rw [hingeDist, ← Real.sqrt_sq (mul_nonneg hd (Real.sin_nonneg_of_nonneg_of_le_pi hφ0 hφπ))]
  congr 1
  nlinarith [Real.sin_sq_add_cos_sq φ]

end ConicalKahler.Test
