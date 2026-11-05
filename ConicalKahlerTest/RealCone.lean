module

public import ConicalKahler
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Tests for the real cone models (Milestone 8)
-/

namespace ConicalKahler.Test

open ConicalKahler InnerProductGeometry MeasureTheory Module
open scoped Real

/-! ### One cone factor -/

/-- The cone of angle `π`. -/
noncomputable def halfAngle : ConeAngle := ⟨1 / 2, by norm_num⟩

/-- `β = 1` is the Euclidean plane. -/
example (p q : ℂ) : coneDist 1 p q = ‖p - q‖ := coneDist_one p q

/-- Opposite points at radius `1` on the cone of angle `π`: the vertex angle is `π/2`, so the
cone distance is `√2`. The Euclidean distance in the real coordinates is `2`. -/
example : dist (ConeTwo.mk 1 : ConeTwo halfAngle) (ConeTwo.mk (-1)) = √2 := by
  rw [ConeTwo.dist_mk, coneDist, coneVertexAngle, angle_self_neg_of_nonzero one_ne_zero,
    show halfAngle.beta * π = π / 2 by simp [halfAngle]; ring,
    min_eq_left (by linarith [Real.pi_pos]), hingeDist, Real.cos_pi_div_two]
  norm_num

/-- For `β = 3` (total angle `6π`), opposite points are joined through the vertex. -/
example : coneDist 3 1 (-1) = 2 := by
  rw [coneDist, coneVertexAngle, angle_self_neg_of_nonzero one_ne_zero,
    min_eq_right (by nlinarith [Real.pi_pos]), norm_neg, norm_one, hingeDist_pi zero_le_one zero_le_one]
  norm_num

/-- The distance to the vertex is the radius. -/
example (w : ℂ) : dist (ConeTwo.mk w : ConeTwo halfAngle) ConeTwo.vertex = ‖w‖ :=
  ConeTwo.dist_vertex _

/-- Uniform equivalence with the Euclidean distance for the cone of angle `π`. -/
example (w z : ℂ) :
    1 / 2 * ‖w - z‖ ≤ dist (ConeTwo.mk w : ConeTwo halfAngle) (ConeTwo.mk z) ∧
      dist (ConeTwo.mk w : ConeTwo halfAngle) (ConeTwo.mk z) ≤ ‖w - z‖ :=
  ConeTwo.dist_bounds_of_le_one (β := halfAngle) (by norm_num [halfAngle]) w z

/-- The paper's metric is uniformly equivalent to the Euclidean metric. -/
example {w : ℂ} (hw : w ≠ 0) (v : ℂ) :
    (1 / 2) ^ 2 * Complex.normSq v ≤ paperConeMetric (1 / 2) w v ∧
      paperConeMetric (1 / 2) w v ≤ Complex.normSq v :=
  ⟨le_paperConeMetric_of_le_one (by norm_num) hw v,
    paperConeMetric_le_of_le_one (by norm_num) hw v⟩

/-- On a sector, the cone distance is flat in the developing coordinates. -/
example : coneDist (1 / 2) (polarMap (1, 0)) (polarMap (1, 1)) =
    ‖polarMap (1, 1 / 2 * 0) - polarMap (1, 1 / 2 * 1)‖ :=
  coneDist_polarMap_eq_developing one_pos one_pos (by norm_num; linarith [Real.two_le_pi])
    (by norm_num; linarith [Real.two_le_pi])

/-- The developing coordinates are not single-valued for `β = 1/2`. -/
example (θ : ℝ) : polarMap (1, 1 / 2 * (θ + 2 * π)) ≠ polarMap (1, 1 / 2 * θ) := by
  refine developing_add_two_pi_ne ?_ one_pos θ
  rintro ⟨m, hm⟩
  have h1 : (0 : ℝ) < m := by rw [← hm]; norm_num
  have h2 : (m : ℝ) < 1 := by rw [← hm]; norm_num
  have h1' : (0 : ℤ) < m := by exact_mod_cast h1
  have h2' : m < (1 : ℤ) := by exact_mod_cast h2
  omega

/-- The bridge: the Kähler point `ρ^{1/β} e^{iθ}` has the paper's coordinates `ρ e^{iθ}`. -/
example {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    realConeChart (1 / 2) (polarMap (ρ ^ (1 / 2 : ℝ)⁻¹, θ)) = polarMap (ρ, θ) :=
  realConeChart_polarMap (by norm_num) hρ θ

/-- `β = 1`: the paper's coordinate is the Kähler coordinate. -/
example (z : ℂ) : realConeChart 1 z = z := realConeChart_one z

/-- The volume density of one factor is `β`. -/
example {w : ℂ} (hw : w ≠ 0) : Real.sqrt (paperConeGram (1 / 2) w).det = 1 / 2 :=
  sqrt_det_paperConeGram (by norm_num) hw

/-! ### Products, including odd dimensions -/

/-- Two cones of angles `π` and `2π/3` and one Euclidean line. -/
noncomputable def twoCones : Fin 2 → ConeAngle := ![⟨1 / 2, by norm_num⟩, ⟨1 / 3, by norm_num⟩]

/-- The real model `C(S¹_π) × C(S¹_{2π/3}) × ℝ` has odd dimension `5`. -/
example : finrank ℝ (RealConeModel (Fin 2) (Fin 1)) = 5 := by
  simp [finrank_euclideanSpace]

/-- The Riemannian volume is `β₁β₂ = 1/6` times Lebesgue measure. -/
example : productConeVolume (ι := Fin 1) twoCones = ENNReal.ofReal (1 / 6) • volume := by
  rw [productConeVolume_eq]
  congr 2
  simp [Fin.prod_univ_two, twoCones]
  norm_num

/-- **Area of a cone disk.** The metric disk of radius `ρ` around the vertex of the cone of total
angle `2πβ` has area `πβρ²`, the area of a circular sector of angle `2πβ`. This checks the
distance and the volume normalisations against each other. -/
example (β : ConeAngle) (ρ : ℝ) :
    productConeVolume (ι := Empty) (fun _ : Fin 1 => β)
        (ConeProduct.mk ⁻¹' Metric.ball (ConeProduct.mk 0 : ConeProduct (fun _ : Fin 1 => β) Empty) ρ) =
      ENNReal.ofReal β.beta * (ENNReal.ofReal ρ ^ 2 * ENNReal.ofReal π) := by
  have hk : finrank ℝ (RealConeModel (Fin 1) Empty) = 2 * 1 := by simp [finrank_euclideanSpace]
  rw [ConeProduct.ball_of_cone_eq_zero (fun a => RealConeModel.cone_zero a),
    productConeVolume_eq, Measure.smul_apply, InnerProductSpace.volume_ball_of_dim_even hk, hk]
  simp

/-- Uniform equivalence of the product distance (`β_a ≤ 1`). -/
example (p q : RealConeModel (Fin 2) (Fin 1)) :
    1 / 3 * ‖p - q‖ ≤ dist (ConeProduct.mk p : ConeProduct twoCones (Fin 1)) (ConeProduct.mk q) ∧
      dist (ConeProduct.mk p : ConeProduct twoCones (Fin 1)) (ConeProduct.mk q) ≤ ‖p - q‖ :=
  ConeProduct.dist_bounds_of_le_one
    (fun a => by fin_cases a <;> norm_num [twoCones]) (by norm_num) (by norm_num)
    (fun a => by fin_cases a <;> norm_num [twoCones]) p q

/-- Balls centred on the vertex stratum `{r₁ = r₂ = 0}` are Euclidean balls. -/
example (s ρ : ℝ) :
    ConeProduct.mk ⁻¹' Metric.ball
        (ConeProduct.mk (RealConeModel.ofCones 0 fun _ => s) : ConeProduct twoCones (Fin 1)) ρ =
      Metric.ball (RealConeModel.ofCones 0 fun _ => s) ρ :=
  ConeProduct.ball_of_cone_eq_zero (fun a => by simp) ρ

/-! ### The operators `𝒟₂` -/

/-- A cone of angle `2π/3`. -/
noncomputable def thirdAngles : Fin 1 → ConeAngle := fun _ => ⟨1 / 3, by norm_num⟩

/-- For `β = 1/3 < 1/2` the pure conical operator `∂²/∂r²` belongs to `𝒟₂`. -/
example : D2Op thirdAngles Empty := .rrPure 0 (by norm_num [thirdAngles])

/-- For `β = 2/3 ≥ 1/2` it does not: the constructor's hypothesis is false. -/
example : ¬ ((⟨2 / 3, by norm_num⟩ : ConeAngle).beta < 1 / 2) := by norm_num

/-- The exponent bounds of the paper's `μ`. -/
example : holderExponentBound (2 / 3) = 1 / 2 := by norm_num [holderExponentBound]
example : holderExponentBound (2 / 5) = 1 / 2 := by norm_num [holderExponentBound]
example : holderExponentBound (1 / 2) = 1 := by norm_num [holderExponentBound]

/-- `β = 1/2`: `∂²_r (r² cos θ) = 2 cos θ`, which has no limit at the vertex. -/
example (c : PolarPoint (Fin 1) Empty) (hr : 0 < c (.r 0)) :
    pd (.r 0) (pd (.r 0) (harmonicCos (1 / 2) 1 0)) c = 2 * Real.cos (c (.θ 0)) := by
  rw [pd_r_pd_r_harmonicCos_one _ _ hr]
  norm_num

/-- A cone of angle `4π/3`. -/
noncomputable def twoThirds : ConeAngle := ⟨2 / 3, by norm_num⟩

/-- For `β = 2/3`, every operator of `𝒟₂` annihilates `r^{3/2} cos θ`. -/
example (D : D2Op (fun _ : Fin 1 => twoThirds) (Fin 1)) (c : PolarPoint (Fin 1) (Fin 1))
    (hr : 0 < c (.r 0)) :
    D.apply (fun c => coneHarmonicCos twoThirds.beta 1 (c (.r 0)) (c (.θ 0))) c = 0 := by
  apply D2Op.apply_factor_eq_zero (fun x y => coneHarmonicCos twoThirds.beta 1 x y) 0 c
    (by norm_num [twoThirds])
  exact coneLaplacian_harmonicCos twoThirds.pos 1 0 hr

/-- Sharpness for `β = 2/3`: with `α = 3/5 > 1/2 = 1/β - 1` there is `D ∈ 𝒟₂` and a harmonic
function whose image is not `α`-Hölder near the vertex. -/
example : ∃ (D : D2Op (fun _ : Fin 1 => twoThirds) (Fin 1))
    (U : PolarPoint (Fin 1) (Fin 1) → ℝ) (C : ℝ), C ≠ 0 ∧
      (∀ c : PolarPoint (Fin 1) (Fin 1), 0 < c (.r 0) →
        paperLaplacian (fun _ : Fin 1 => twoThirds) U c = 0) ∧
      (∀ c : PolarPoint (Fin 1) (Fin 1), 0 < c (.r 0) →
        D.apply U c = radialCosFn C (holderExponentBound twoThirds.beta)
          (polarMap (c (.r 0), c (.θ 0)))) ∧
      ∀ ε > 0, ¬ HolderNearVertex twoThirds (3 / 5) ε
        (radialCosFn C (holderExponentBound twoThirds.beta)) :=
  sharp_holderExponent (fun _ : Fin 1 => twoThirds) 0 0 (by norm_num)
    (by norm_num [holderExponentBound, twoThirds])

end ConicalKahler.Test
