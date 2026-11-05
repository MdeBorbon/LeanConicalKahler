module

public import ConicalKahler.Real.ConeFactor
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Analysis.Complex.Angle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The intrinsic distance of a two-dimensional cone

The cone `C(S¹_{2πβ})` is the Euclidean cone over a circle of length `2πβ`. Two points at radii
`r, s` whose angles differ by `δ ∈ [0, π]` (the distance in `ℝ/2πℤ`) are at distance

  `d² = r² + s² - 2 r s cos(min(β δ, π))`.

This is the standard formula for the Euclidean cone over a metric space (Bridson–Haefliger, I.5.6).
Here it is the **definition** of `coneDist`.

## Main results

* `hingeDist_triangle`: the comparison lemma for planar hinges that gives the triangle inequality.
* `ConeTwo β`: the paper's real coordinates `w ∈ ℂ ≅ ℝ²` with the metric `coneDist`, as a
  `MetricSpace`.
* `coneDist_polarMap`: the formula in the paper's polar coordinates, with `θ ∈ ℝ/2πℤ`.
* `coneDist_polarMap_eq_developing`: on a sector of opening `≤ min(π, π/β)` the cone distance is the
  Euclidean distance in the flat developing coordinates `r e^{iβθ}`, where the paper's metric is
  `|dw|²` (`FlatCone`).
* `coneDist_vertex`, `coneDist_radial`: distances to the vertex and along rays.
* `coneDist_mul_left`: dilations scale the distance and rotations preserve it.
* Comparison with the Euclidean distance `|p - q|` in the real coordinates:
  `β |p - q| ≤ d(p, q) ≤ |p - q|` for `β ≤ 1`, and
  `|p - q| ≤ d(p, q) ≤ (πβ/2) |p - q|` for `β ≥ 1`. Corresponding ball inclusions.
  `ConeTwo.homeomorph`: the cone distance induces the usual topology of `ℝ²`.

## Not proved here

We do **not** prove that `coneDist` is the length distance of the Riemannian metric
`dr² + β² r² dθ²` (the infimum of lengths of curves). That identification is the content of the
standard theory of Euclidean cones. The results above are consistent with it: the distance to the
vertex is `r`, rays are realised with length `|r - s|`, and locally the distance is flat in
developing coordinates. Until it is proved, statements that use `coneDist` are about this formally
defined distance.
-/

@[expose] public section

open scoped Real
open InnerProductGeometry

namespace ConicalKahler

/-! ### Planar hinges -/

/-- The third side of a planar triangle with sides `a`, `b` enclosing the angle `φ`. -/
noncomputable def hingeDist (a b φ : ℝ) : ℝ :=
  √(a ^ 2 + b ^ 2 - 2 * a * b * Real.cos φ)

theorem cos_eq_one_sub_two_mul_sin_half_sq (φ : ℝ) :
    Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ 2 := by
  have h1 := Real.cos_two_mul (φ / 2)
  have h2 := Real.sin_sq_add_cos_sq (φ / 2)
  rw [show 2 * (φ / 2) = φ by ring] at h1
  linear_combination h1 + 2 * h2

theorem hinge_expr_eq (a b φ : ℝ) :
    a ^ 2 + b ^ 2 - 2 * a * b * Real.cos φ = (a - b) ^ 2 + 4 * a * b * Real.sin (φ / 2) ^ 2 := by
  rw [cos_eq_one_sub_two_mul_sin_half_sq]
  ring

theorem hinge_expr_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (φ : ℝ) :
    0 ≤ a ^ 2 + b ^ 2 - 2 * a * b * Real.cos φ := by
  rw [hinge_expr_eq]
  positivity

theorem hingeDist_nonneg (a b φ : ℝ) : 0 ≤ hingeDist a b φ :=
  Real.sqrt_nonneg _

theorem hingeDist_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (φ : ℝ) :
    hingeDist a b φ ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * Real.cos φ :=
  Real.sq_sqrt (hinge_expr_nonneg ha hb φ)

theorem hingeDist_comm (a b φ : ℝ) : hingeDist a b φ = hingeDist b a φ := by
  unfold hingeDist
  ring_nf

theorem hingeDist_neg (a b φ : ℝ) : hingeDist a b (-φ) = hingeDist a b φ := by
  simp [hingeDist, Real.cos_neg]

theorem hingeDist_zero_right {a : ℝ} (ha : 0 ≤ a) (φ : ℝ) : hingeDist a 0 φ = a := by
  simp [hingeDist, Real.sqrt_sq ha]

theorem hingeDist_zero_left {b : ℝ} (hb : 0 ≤ b) (φ : ℝ) : hingeDist 0 b φ = b := by
  rw [hingeDist_comm, hingeDist_zero_right hb]

theorem hingeDist_angle_zero (a b : ℝ) : hingeDist a b 0 = |a - b| := by
  rw [hingeDist, Real.cos_zero, ← Real.sqrt_sq_eq_abs]
  congr 1
  ring

theorem hingeDist_pi {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : hingeDist a b π = a + b := by
  rw [hingeDist, Real.cos_pi, show a ^ 2 + b ^ 2 - 2 * a * b * -1 = (a + b) ^ 2 by ring,
    Real.sqrt_sq (add_nonneg ha hb)]

/-- Scaling both sides of a hinge. -/
theorem hingeDist_mul {k : ℝ} (hk : 0 ≤ k) (a b φ : ℝ) :
    hingeDist (k * a) (k * b) φ = k * hingeDist a b φ := by
  rw [hingeDist, hingeDist, show (k * a) ^ 2 + (k * b) ^ 2 - 2 * (k * a) * (k * b) * Real.cos φ =
    k ^ 2 * (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos φ) by ring, Real.sqrt_mul (sq_nonneg k),
    Real.sqrt_sq hk]

/-- The hinge grows with the angle on `[0, π]`. -/
theorem hingeDist_mono {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {φ ψ : ℝ} (h0 : 0 ≤ φ) (hle : φ ≤ ψ)
    (hπ : ψ ≤ π) : hingeDist a b φ ≤ hingeDist a b ψ := by
  apply Real.sqrt_le_sqrt
  have := Real.cos_le_cos_of_nonneg_of_le_pi h0 hπ hle
  nlinarith [mul_nonneg ha hb]

theorem hingeDist_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (φ : ℝ) : hingeDist a b φ ≤ a + b := by
  calc hingeDist a b φ ≤ √((a + b) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [Real.neg_one_le_cos φ, mul_nonneg ha hb])
    _ = a + b := Real.sqrt_sq (add_nonneg ha hb)

/-- **The hinge is a planar distance:** `|r e^{ix} - s e^{iy}| = hingeDist r s (x - y)`. -/
theorem hingeDist_eq_norm_sub (a b x y : ℝ) :
    hingeDist a b (x - y) = ‖polarMap (a, x) - polarMap (b, y)‖ := by
  rw [hingeDist, Complex.norm_def]
  congr 1
  simp only [polarMap, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero]
  rw [Real.cos_sub]
  linear_combination (-a ^ 2) * Real.sin_sq_add_cos_sq x + (-b ^ 2) * Real.sin_sq_add_cos_sq y

/-- **Hinge comparison.** If `ψ ≤ φ₁ + φ₂` (all angles in `[0, π]`), then the hinge `(r₁, r₃, ψ)` is
at most the sum of the hinges `(r₁, r₂, φ₁)` and `(r₂, r₃, φ₂)`. This is the triangle inequality
of the Euclidean cone. If `φ₁ + φ₂ ≤ π`, place the three points in the plane at angles `φ₁, 0, -φ₂`.
Otherwise the path through `r₂` goes around the vertex and is at least `r₁ + r₃`. -/
theorem hingeDist_triangle {r₁ r₂ r₃ φ₁ φ₂ ψ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) (h₃ : 0 ≤ r₃)
    (hφ₁' : φ₁ ≤ π) (hφ₂' : φ₂ ≤ π) (hψ : 0 ≤ ψ) (hle : ψ ≤ φ₁ + φ₂) :
    hingeDist r₁ r₃ ψ ≤ hingeDist r₁ r₂ φ₁ + hingeDist r₂ r₃ φ₂ := by
  rcases le_or_gt (φ₁ + φ₂) π with hsum | hsum
  · calc hingeDist r₁ r₃ ψ ≤ hingeDist r₁ r₃ (φ₁ - -φ₂) := by
          rw [sub_neg_eq_add]
          exact hingeDist_mono h₁ h₃ hψ hle hsum
      _ = ‖polarMap (r₁, φ₁) - polarMap (r₃, -φ₂)‖ := hingeDist_eq_norm_sub _ _ _ _
      _ ≤ ‖polarMap (r₁, φ₁) - polarMap (r₂, 0)‖ + ‖polarMap (r₂, 0) - polarMap (r₃, -φ₂)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = hingeDist r₁ r₂ φ₁ + hingeDist r₂ r₃ φ₂ := by
          rw [← hingeDist_eq_norm_sub, ← hingeDist_eq_norm_sub, sub_zero, zero_sub, neg_neg]
  · have hB : hingeDist r₂ r₃ (π - φ₁) ≤ hingeDist r₂ r₃ φ₂ :=
      hingeDist_mono h₂ h₃ (by linarith) (by linarith) hφ₂'
    calc hingeDist r₁ r₃ ψ ≤ r₁ + r₃ := hingeDist_le_add h₁ h₃ ψ
      _ = hingeDist r₁ r₃ (φ₁ - (φ₁ - π)) := by rw [sub_sub_cancel, hingeDist_pi h₁ h₃]
      _ = ‖polarMap (r₁, φ₁) - polarMap (r₃, φ₁ - π)‖ := hingeDist_eq_norm_sub _ _ _ _
      _ ≤ ‖polarMap (r₁, φ₁) - polarMap (r₂, 0)‖ + ‖polarMap (r₂, 0) - polarMap (r₃, φ₁ - π)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = hingeDist r₁ r₂ φ₁ + hingeDist r₂ r₃ (π - φ₁) := by
          rw [← hingeDist_eq_norm_sub, ← hingeDist_eq_norm_sub, sub_zero, zero_sub, neg_sub]
      _ ≤ hingeDist r₁ r₂ φ₁ + hingeDist r₂ r₃ φ₂ := by linarith

/-! ### The cone distance -/

/-- The angle at the vertex between the rays through `p` and `q` in the cone of total angle `2πβ`,
capped at `π`: `min(β ∠(p, q), π)`. Here `∠(p, q) ∈ [0, π]` is the Euclidean angle in the real
coordinates, i.e. the distance of the paper's angles `θ_p, θ_q` in `ℝ/2πℤ`
(`angle_polarMap_eq_abs_toReal`). -/
noncomputable def coneVertexAngle (β : ℝ) (p q : ℂ) : ℝ :=
  min (β * angle p q) π

/-- **The cone distance** of `C(S¹_{2πβ})` in the paper's real coordinates. -/
noncomputable def coneDist (β : ℝ) (p q : ℂ) : ℝ :=
  hingeDist ‖p‖ ‖q‖ (coneVertexAngle β p q)

theorem coneVertexAngle_nonneg {β : ℝ} (hβ : 0 ≤ β) (p q : ℂ) : 0 ≤ coneVertexAngle β p q :=
  le_min (mul_nonneg hβ (angle_nonneg p q)) Real.pi_pos.le

theorem coneVertexAngle_le_pi (β : ℝ) (p q : ℂ) : coneVertexAngle β p q ≤ π :=
  min_le_right _ _

theorem coneVertexAngle_comm (β : ℝ) (p q : ℂ) : coneVertexAngle β p q = coneVertexAngle β q p := by
  rw [coneVertexAngle, coneVertexAngle, angle_comm]

theorem min_pi_le_add {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : z ≤ x + y) :
    min z π ≤ min x π + min y π := by
  have hπ := Real.pi_pos
  have hz := min_le_right z π
  rcases le_total x π with h1 | h1 <;> rcases le_total y π with h2 | h2
  · rw [min_eq_left h1, min_eq_left h2]
    exact (min_le_left _ _).trans h
  · rw [min_eq_right h2]
    linarith [le_min hx hπ.le]
  · rw [min_eq_right h1]
    linarith [le_min hy hπ.le]
  · rw [min_eq_right h1, min_eq_right h2]
    linarith

theorem coneVertexAngle_triangle {β : ℝ} (hβ : 0 ≤ β) (p q r : ℂ) :
    coneVertexAngle β p r ≤ coneVertexAngle β p q + coneVertexAngle β q r :=
  min_pi_le_add (mul_nonneg hβ (angle_nonneg p q)) (mul_nonneg hβ (angle_nonneg q r))
    (by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (angle_le_angle_add_angle p q r) hβ)

theorem coneDist_nonneg (β : ℝ) (p q : ℂ) : 0 ≤ coneDist β p q :=
  hingeDist_nonneg _ _ _

theorem coneDist_comm (β : ℝ) (p q : ℂ) : coneDist β p q = coneDist β q p := by
  rw [coneDist, coneDist, hingeDist_comm, coneVertexAngle_comm]

theorem coneDist_self (β : ℝ) (p : ℂ) : coneDist β p p = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [coneDist, hingeDist]
  · rw [coneDist, coneVertexAngle, angle_self hp, mul_zero, min_eq_left Real.pi_pos.le,
      hingeDist_angle_zero, sub_self, abs_zero]

theorem coneDist_triangle {β : ℝ} (hβ : 0 ≤ β) (p q r : ℂ) :
    coneDist β p r ≤ coneDist β p q + coneDist β q r :=
  hingeDist_triangle (norm_nonneg p) (norm_nonneg q) (norm_nonneg r)
    (coneVertexAngle_le_pi β p q) (coneVertexAngle_le_pi β q r) (coneVertexAngle_nonneg hβ p r)
    (coneVertexAngle_triangle hβ p q r)

theorem eq_of_coneDist_eq_zero {β : ℝ} (hβ : 0 < β) {p q : ℂ} (h : coneDist β p q = 0) :
    p = q := by
  rw [coneDist, hingeDist, Real.sqrt_eq_zero' , hinge_expr_eq] at h
  set φ := coneVertexAngle β p q with hφ
  have hab : 0 ≤ 4 * ‖p‖ * ‖q‖ * Real.sin (φ / 2) ^ 2 := by positivity
  have h1 : (‖p‖ - ‖q‖) ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (‖p‖ - ‖q‖)]) (sq_nonneg _)
  have h2 : ‖p‖ * ‖q‖ * Real.sin (φ / 2) ^ 2 = 0 := by nlinarith [sq_nonneg (‖p‖ - ‖q‖)]
  have hnorm : ‖p‖ = ‖q‖ := by nlinarith [sq_eq_zero_iff.mp h1]
  rcases eq_or_ne p 0 with rfl | hp
  · rw [norm_zero, eq_comm, norm_eq_zero] at hnorm
    exact hnorm.symm
  have hq : q ≠ 0 := by
    rw [← norm_ne_zero_iff, ← hnorm]
    exact norm_ne_zero_iff.mpr hp
  have hs : Real.sin (φ / 2) = 0 := by
    have hpq : ‖p‖ * ‖q‖ ≠ 0 := mul_ne_zero (norm_ne_zero_iff.mpr hp) (norm_ne_zero_iff.mpr hq)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp h2).resolve_left hpq)
  have hφ0 : φ = 0 := by
    by_contra hne
    have hpos : 0 < φ / 2 := by
      have := coneVertexAngle_nonneg hβ.le p q
      rw [← hφ] at this
      positivity
    have hlt : φ / 2 < π := by
      have := coneVertexAngle_le_pi β p q
      rw [← hφ] at this
      linarith [Real.pi_pos]
    exact (Real.sin_pos_of_pos_of_lt_pi hpos hlt).ne' hs
  have hangle : angle p q = 0 := by
    rw [hφ, coneVertexAngle] at hφ0
    rcases min_choice (β * angle p q) π with hm | hm
    · rw [hm] at hφ0
      exact (mul_eq_zero.mp hφ0).resolve_left hβ.ne'
    · rw [hm] at hφ0
      exact absurd hφ0 Real.pi_ne_zero
  obtain ⟨-, t, ht, rfl⟩ := angle_eq_zero_iff.mp hangle
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hnorm
  have ht1 : t = 1 := by
    have hpn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
    field_simp at hnorm
    linarith
  rw [ht1, one_smul]

/-! ### The paper's polar coordinates and the developing coordinates -/

theorem cos_angle_polarMap {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (θ φ : ℝ) :
    Real.cos (angle (polarMap (r, θ)) (polarMap (s, φ))) = Real.cos (θ - φ) := by
  rw [cos_angle, Complex.inner, norm_polarMap_of_nonneg hr.le, norm_polarMap_of_nonneg hs.le]
  simp only [polarMap, map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [Real.cos_sub]
  field_simp
  ring

/-- **The vertex angle in the paper's coordinates:** the angle between the rays at `θ` and `φ` is
the distance `|θ - φ|` in `ℝ/2πℤ`. -/
theorem angle_polarMap_eq_abs_toReal {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (θ φ : ℝ) :
    angle (polarMap (r, θ)) (polarMap (s, φ)) = |((θ - φ : ℝ) : Real.Angle).toReal| := by
  apply Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩
    ⟨abs_nonneg _, Real.Angle.abs_toReal_le_pi _⟩
  rw [Real.cos_abs, Real.Angle.cos_toReal, Real.Angle.cos_coe, cos_angle_polarMap hr hs]

theorem angle_polarMap {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {θ φ : ℝ} (h : |θ - φ| ≤ π) :
    angle (polarMap (r, θ)) (polarMap (s, φ)) = |θ - φ| := by
  apply Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨abs_nonneg _, h⟩
  rw [Real.cos_abs, cos_angle_polarMap hr hs]

/-- **The cone distance in the paper's polar coordinates** `(r, θ)`, `θ ∈ ℝ/2πℤ`:
`d² = r² + s² - 2 r s cos(min(β |θ - φ|_{ℝ/2πℤ}, π))`. -/
theorem coneDist_polarMap (β : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (θ φ : ℝ) :
    coneDist β (polarMap (r, θ)) (polarMap (s, φ)) =
      hingeDist r s (min (β * |((θ - φ : ℝ) : Real.Angle).toReal|) π) := by
  rw [coneDist, coneVertexAngle, angle_polarMap_eq_abs_toReal hr hs, norm_polarMap_of_nonneg hr.le,
    norm_polarMap_of_nonneg hs.le]

/-- **Locally, the cone distance is flat in the developing coordinates.** If `|θ - φ| ≤ π` and
`β |θ - φ| ≤ π`, the cone distance between `(r, θ)` and `(s, φ)` is the Euclidean distance between
`r e^{iβθ}` and `s e^{iβφ}`. In these coordinates the paper's metric is `|dw|²`. The developing
coordinates depend on the lifts `θ, φ ∈ ℝ` and are not single-valued on the cone
(`developing_add_two_pi_ne`). -/
theorem coneDist_polarMap_eq_developing {β : ℝ} {r s θ φ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h : |θ - φ| ≤ π) (hβπ : β * |θ - φ| ≤ π) :
    coneDist β (polarMap (r, θ)) (polarMap (s, φ)) =
      ‖polarMap (r, β * θ) - polarMap (s, β * φ)‖ := by
  rw [coneDist, coneVertexAngle, angle_polarMap hr hs h, min_eq_left hβπ,
    norm_polarMap_of_nonneg hr.le, norm_polarMap_of_nonneg hs.le, ← hingeDist_eq_norm_sub,
    ← mul_sub]
  rcases abs_choice (θ - φ) with h' | h'
  · rw [h']
  · rw [h', mul_neg, hingeDist_neg]

/-! ### Vertex, rays, dilations and rotations -/

/-- **The distance to the vertex is the radius** `r = |p|`. -/
theorem coneDist_vertex (β : ℝ) (p : ℂ) : coneDist β p 0 = ‖p‖ := by
  rw [coneDist, norm_zero, hingeDist_zero_right (norm_nonneg p)]

theorem coneDist_vertex_left (β : ℝ) (q : ℂ) : coneDist β 0 q = ‖q‖ := by
  rw [coneDist_comm, coneDist_vertex]

/-- **Along a ray the distance is the difference of the radii.** -/
theorem coneDist_radial (β : ℝ) (p : ℂ) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    coneDist β ((t : ℂ) * p) ((s : ℂ) * p) = |t - s| * ‖p‖ := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [coneDist_self]
  rcases ht.eq_or_lt with rfl | ht'
  · simp [coneDist_vertex_left, abs_of_nonneg hs]
  rcases hs.eq_or_lt with rfl | hs'
  · simp [coneDist_vertex, abs_of_nonneg ht]
  have hang : angle ((t : ℂ) * p) ((s : ℂ) * p) = 0 := by
    rw [← Complex.real_smul, ← Complex.real_smul, angle_smul_left_of_pos _ _ ht',
      angle_smul_right_of_pos _ _ hs', angle_self hp]
  rw [coneDist, coneVertexAngle, hang, mul_zero, min_eq_left Real.pi_pos.le, hingeDist_angle_zero,
    norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ht, abs_of_nonneg hs, ← sub_mul, abs_mul, abs_of_nonneg (norm_nonneg p)]

/-- **Dilations and rotations.** Multiplication by `a ≠ 0` scales the cone distance by `|a|`:
`r ↦ |a| r`, `θ ↦ θ + arg a`. -/
theorem coneDist_mul_left (β : ℝ) {a : ℂ} (ha : a ≠ 0) (p q : ℂ) :
    coneDist β (a * p) (a * q) = ‖a‖ * coneDist β p q := by
  rw [coneDist, coneDist, coneVertexAngle, coneVertexAngle, Complex.angle_mul_left ha, norm_mul,
    norm_mul, hingeDist_mul (norm_nonneg a)]

/-! ### Comparison with the Euclidean distance in the real coordinates -/

/-- The law of cosines: the Euclidean distance is the hinge with the Euclidean angle. -/
theorem norm_sub_eq_hingeDist (p q : ℂ) : ‖p - q‖ = hingeDist ‖p‖ ‖q‖ (angle p q) := by
  rw [hingeDist, ← Real.sqrt_sq (norm_nonneg (p - q)), sq,
    norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle]
  ring_nf

/-- `β = 1`: the cone of total angle `2π` is the Euclidean plane. -/
theorem coneDist_one (p q : ℂ) : coneDist 1 p q = ‖p - q‖ := by
  rw [norm_sub_eq_hingeDist, coneDist, coneVertexAngle, one_mul, min_eq_left (angle_le_pi p q)]

/-- Concavity of `sin` on `[0, π]`: `β sin x ≤ sin (β x)` for `0 ≤ β ≤ 1`. -/
theorem mul_sin_le_sin_mul {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hx0 : 0 ≤ x) (hxπ : x ≤ π) :
    β * Real.sin x ≤ Real.sin (β * x) := by
  have h := strictConcaveOn_sin_Icc.concaveOn.2 (x := x) (y := 0) ⟨hx0, hxπ⟩
    ⟨le_rfl, Real.pi_pos.le⟩ hβ0 (sub_nonneg.mpr hβ1) (by ring)
  simpa using h

theorem coneVertexAngle_of_le_one {β : ℝ} (hβ1 : β ≤ 1) (p q : ℂ) :
    coneVertexAngle β p q = β * angle p q :=
  min_eq_left ((mul_le_of_le_one_left (angle_nonneg p q) hβ1).trans (angle_le_pi p q))

/-- **Upper bound, `β ≤ 1`:** `d(p, q) ≤ |p - q|`. -/
theorem coneDist_le_norm_sub {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (p q : ℂ) :
    coneDist β p q ≤ ‖p - q‖ := by
  rw [norm_sub_eq_hingeDist, coneDist, coneVertexAngle_of_le_one hβ1]
  exact hingeDist_mono (norm_nonneg _) (norm_nonneg _) (mul_nonneg hβ0 (angle_nonneg p q))
    (mul_le_of_le_one_left (angle_nonneg p q) hβ1) (angle_le_pi p q)

/-- **Lower bound, `β ≤ 1`:** `β |p - q| ≤ d(p, q)`. -/
theorem mul_norm_sub_le_coneDist {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (p q : ℂ) :
    β * ‖p - q‖ ≤ coneDist β p q := by
  rw [norm_sub_eq_hingeDist, coneDist, coneVertexAngle_of_le_one hβ1]
  set a := ‖p‖
  set b := ‖q‖
  set θ := angle p q
  have hθ0 : 0 ≤ θ / 2 := by have := angle_nonneg p q; positivity
  have hθπ : θ / 2 ≤ π := by linarith [angle_le_pi p q, Real.pi_pos]
  have hs := mul_sin_le_sin_mul hβ0 hβ1 hθ0 hθπ
  rw [show β * (θ / 2) = β * θ / 2 by ring] at hs
  have hs0 : 0 ≤ β * Real.sin (θ / 2) :=
    mul_nonneg hβ0 (Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθπ)
  have hsq : (β * Real.sin (θ / 2)) ^ 2 ≤ Real.sin (β * θ / 2) ^ 2 := pow_le_pow_left₀ hs0 hs 2
  have hab : 0 ≤ 4 * a * b := by positivity
  have hβ2 : β ^ 2 ≤ 1 := by nlinarith
  calc β * hingeDist a b θ = √(β ^ 2 * (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos θ)) := by
        rw [hingeDist, Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ0]
    _ ≤ hingeDist a b (β * θ) := by
        apply Real.sqrt_le_sqrt
        rw [hinge_expr_eq, hinge_expr_eq]
        nlinarith [mul_le_mul_of_nonneg_left hsq hab,
          mul_le_mul_of_nonneg_right hβ2 (sq_nonneg (a - b))]

/-- **Lower bound, `β ≥ 1`:** `|p - q| ≤ d(p, q)`. -/
theorem norm_sub_le_coneDist {β : ℝ} (hβ1 : 1 ≤ β) (p q : ℂ) : ‖p - q‖ ≤ coneDist β p q := by
  rw [norm_sub_eq_hingeDist, coneDist]
  exact hingeDist_mono (norm_nonneg _) (norm_nonneg _) (angle_nonneg p q)
    (le_min (le_mul_of_one_le_left (angle_nonneg p q) hβ1) (angle_le_pi p q))
    (coneVertexAngle_le_pi β p q)

/-- **Upper bound, `β ≥ 1`:** `d(p, q) ≤ (πβ/2) |p - q|`. -/
theorem coneDist_le_mul_norm_sub {β : ℝ} (hβ1 : 1 ≤ β) (p q : ℂ) :
    coneDist β p q ≤ π * β / 2 * ‖p - q‖ := by
  rw [norm_sub_eq_hingeDist, coneDist]
  set a := ‖p‖
  set b := ‖q‖
  set θ := angle p q
  set φ := coneVertexAngle β p q
  have hK : 1 ≤ π * β / 2 := by nlinarith [Real.two_le_pi]
  have hK0 : 0 ≤ π * β / 2 := by linarith
  have hφ0 : 0 ≤ φ / 2 := by
    have := coneVertexAngle_nonneg (β := β) (by linarith) p q; positivity
  have hθ0 : 0 ≤ θ / 2 := by have := angle_nonneg p q; positivity
  have hθπ : θ / 2 ≤ π / 2 := by linarith [angle_le_pi p q]
  -- `sin(φ/2) ≤ φ/2 ≤ βθ/2 ≤ (πβ/2) sin(θ/2)` (Jordan's inequality)
  have h1 : Real.sin (φ / 2) ≤ φ / 2 := Real.sin_le hφ0
  have h2 : φ / 2 ≤ β * θ / 2 := by
    have : φ ≤ β * θ := show min (β * θ) π ≤ β * θ from min_le_left _ _
    linarith
  have h3 : 2 / π * (θ / 2) ≤ Real.sin (θ / 2) := Real.mul_le_sin hθ0 hθπ
  have h4 : β * θ / 2 ≤ π * β / 2 * Real.sin (θ / 2) := by
    have hπ := Real.pi_pos
    have : θ / 2 ≤ π / 2 * Real.sin (θ / 2) := by
      have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ π / 2)
      rwa [← mul_assoc, show π / 2 * (2 / π) = 1 by field_simp, one_mul] at this
    nlinarith
  have hsφ0 : 0 ≤ Real.sin (φ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith [coneVertexAngle_le_pi β p q])
  have hsq : Real.sin (φ / 2) ^ 2 ≤ (π * β / 2 * Real.sin (θ / 2)) ^ 2 :=
    pow_le_pow_left₀ hsφ0 (h1.trans (h2.trans h4)) 2
  have hab : 0 ≤ 4 * a * b := by positivity
  have hK2 : 1 ≤ (π * β / 2) ^ 2 := by nlinarith
  calc hingeDist a b φ ≤ √((π * β / 2) ^ 2 * (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos θ)) := by
        apply Real.sqrt_le_sqrt
        rw [hinge_expr_eq, hinge_expr_eq]
        nlinarith [mul_le_mul_of_nonneg_left hsq hab,
          mul_le_mul_of_nonneg_right hK2 (sq_nonneg (a - b))]
    _ = π * β / 2 * hingeDist a b θ := by
        rw [hingeDist, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK0]

/-- **Uniform equivalence with the Euclidean distance, any `β > 0`:**
`min(1, β) |p - q| ≤ d(p, q) ≤ max(1, πβ/2) |p - q|`. -/
theorem coneDist_bounds {β : ℝ} (hβ : 0 < β) (p q : ℂ) :
    min 1 β * ‖p - q‖ ≤ coneDist β p q ∧ coneDist β p q ≤ max 1 (π * β / 2) * ‖p - q‖ := by
  have hn := norm_nonneg (p - q)
  rcases le_total β 1 with h | h
  · refine ⟨?_, ?_⟩
    · rw [min_eq_right h]
      exact mul_norm_sub_le_coneDist hβ.le h p q
    · exact (coneDist_le_norm_sub hβ.le h p q).trans
        (le_mul_of_one_le_left hn (le_max_left _ _))
  · refine ⟨?_, ?_⟩
    · rw [min_eq_left h, one_mul]
      exact norm_sub_le_coneDist h p q
    · exact (coneDist_le_mul_norm_sub h p q).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hn)

/-! ### The metric space -/

/-- **The two-dimensional cone `C(S¹_{2πβ})`** in the paper's real coordinates. A point is
`w = r e^{iθ} ∈ ℂ ≅ ℝ²`, and the distance is `coneDist β`. A type synonym of `ℂ`, so that `ℂ`
keeps its Euclidean metric. -/
def ConeTwo (_β : ConeAngle) : Type := ℂ

namespace ConeTwo

variable {β : ConeAngle}

/-- The point of the cone with real coordinate `w`. -/
def mk (w : ℂ) : ConeTwo β := w

/-- The paper's real coordinate of a point of the cone. -/
def coord (p : ConeTwo β) : ℂ := p

@[simp] theorem coord_mk (w : ℂ) : coord (mk w : ConeTwo β) = w := rfl

@[simp] theorem mk_coord (p : ConeTwo β) : mk (coord p) = p := rfl

theorem coord_injective : Function.Injective (coord : ConeTwo β → ℂ) := fun _ _ h => h

noncomputable instance (β : ConeAngle) : MetricSpace (ConeTwo β) where
  dist p q := coneDist β.beta (coord p) (coord q)
  dist_self p := coneDist_self _ _
  dist_comm p q := coneDist_comm _ _ _
  dist_triangle p q r := coneDist_triangle β.pos.le _ _ _
  eq_of_dist_eq_zero h := coord_injective (eq_of_coneDist_eq_zero β.pos h)

theorem dist_eq (p q : ConeTwo β) : dist p q = coneDist β.beta (coord p) (coord q) := rfl

@[simp] theorem dist_mk (w z : ℂ) : dist (mk w : ConeTwo β) (mk z) = coneDist β.beta w z := rfl

/-- The vertex. -/
def vertex : ConeTwo β := mk 0

theorem dist_vertex (p : ConeTwo β) : dist p vertex = ‖coord p‖ :=
  coneDist_vertex _ _

/-- **Euclidean comparison, `β ≤ 1`.** -/
theorem dist_bounds_of_le_one (hβ1 : β.beta ≤ 1) (w z : ℂ) :
    β.beta * ‖w - z‖ ≤ dist (mk w : ConeTwo β) (mk z) ∧ dist (mk w : ConeTwo β) (mk z) ≤ ‖w - z‖ :=
  ⟨mul_norm_sub_le_coneDist β.pos.le hβ1 w z, coneDist_le_norm_sub β.pos.le hβ1 w z⟩

/-- **Ball inclusions, `β ≤ 1`:** `B_E(w, ρ) ⊆ B_d(w, ρ) ⊆ B_E(w, ρ/β)`. -/
theorem ball_subset_of_le_one (hβ1 : β.beta ≤ 1) (w : ℂ) (ρ : ℝ) :
    Metric.ball w ρ ⊆ mk ⁻¹' Metric.ball (mk w : ConeTwo β) ρ ∧
      mk ⁻¹' Metric.ball (mk w : ConeTwo β) ρ ⊆ Metric.ball w (ρ / β.beta) := by
  constructor
  · intro z hz
    rw [Set.mem_preimage, Metric.mem_ball, dist_mk]
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact (coneDist_le_norm_sub β.pos.le hβ1 z w).trans_lt hz
  · intro z hz
    rw [Set.mem_preimage, Metric.mem_ball, dist_mk] at hz
    rw [Metric.mem_ball, dist_eq_norm, lt_div_iff₀ β.pos, mul_comm]
    exact (mul_norm_sub_le_coneDist β.pos.le hβ1 z w).trans_lt hz

/-- Balls centred at the vertex are Euclidean balls. -/
theorem ball_vertex (ρ : ℝ) : mk ⁻¹' Metric.ball (vertex : ConeTwo β) ρ = Metric.ball 0 ρ := by
  ext z
  simp [vertex, dist_mk, coneDist_vertex]

theorem lipschitzWith_mk :
    LipschitzWith (Real.toNNReal (max 1 (π * β.beta / 2))) (mk : ℂ → ConeTwo β) := by
  refine LipschitzWith.of_dist_le_mul fun w z => ?_
  rw [Real.coe_toNNReal _ ((zero_le_one).trans (le_max_left _ _)), dist_mk, dist_eq_norm]
  exact (coneDist_bounds β.pos w z).2

theorem lipschitzWith_coord :
    LipschitzWith (Real.toNNReal (min 1 β.beta)⁻¹) (coord : ConeTwo β → ℂ) := by
  have hm : 0 < min 1 β.beta := lt_min one_pos β.pos
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr hm.le), dist_eq_norm, dist_eq, inv_mul_eq_div,
    le_div_iff₀ hm, mul_comm]
  exact (coneDist_bounds β.pos _ _).1

/-- **The cone distance induces the usual topology of `ℝ²`.** -/
noncomputable def homeomorph (β : ConeAngle) : ℂ ≃ₜ ConeTwo β where
  toFun := mk
  invFun := coord
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := lipschitzWith_mk.continuous
  continuous_invFun := lipschitzWith_coord.continuous

end ConeTwo

end ConicalKahler
