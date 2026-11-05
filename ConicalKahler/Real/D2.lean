module

public import ConicalKahler.Real.Product
public import ConicalKahler.Laplacian.ConeHarmonic

/-!
# The second-order operators `𝒟₂` of de Borbon–Edwards

The paper (p. 2) works in polar coordinates `(r_a, θ_a)` on each cone factor and Cartesian
coordinates `s_i` on the Euclidean factor. It defines `𝒟₂` as the following **coordinate**
differential operators (not components of the covariant Hessian):

* pure Euclidean: `∂²/∂s_i∂s_j`;
* mixed conical-Euclidean: `∂²/∂r_a∂s_i`, `r_a⁻¹ ∂²/∂θ_a∂s_i`;
* mixed conical, `a ≠ b`: `∂²/∂r_a∂r_b`, `(r_a r_b)⁻¹ ∂²/∂θ_a∂θ_b`, `r_b⁻¹ ∂²/∂r_a∂θ_b`;
* conical Laplacians: `Δ_{β_a} = ∂²/∂r_a² + r_a⁻¹ ∂/∂r_a + (β_a r_a)⁻² ∂²/∂θ_a²`;
* pure conical, **only for `β_a < 1/2`**: `∂²/∂r_a²`, `r_a⁻² ∂²/∂θ_a²`, `r_a⁻¹ ∂²/∂r_a∂θ_a`.

`D2Op β ι` lists these operators. The pure conical constructors carry a proof of `β_a < 1/2`.
`D2Op.apply` applies them to a function of the polar coordinates. Here `PolarPoint κ ι` is the
space of coordinate values, with `θ_a ∈ ℝ` a lift of the angle in `ℝ/2πℤ`. `pd k U` is the
coordinate partial derivative `∂U/∂x_k`, and `∂²/∂x∂y` means `∂_x (∂_y U)`.

`PolarPoint.toModel` maps polar coordinates to the paper's real coordinates
(`x_a + i y_a = r_a e^{iθ_a}`). A function `u` on the real model has the polar expression
`u ∘ toModel`, which is `2π`-periodic in each `θ_a` (`toModel_update_theta_add_two_pi`).

## Results

* `coneLaplacian_harmonicCos`, `paperLaplacian_harmonicCos`, `paperLaplacian_mixedExample`:
  `r_a^{k/β} cos(kθ_a)` and `r_a^{1/β} s_i cos θ_a` are harmonic for
  `Δ = ∑_a Δ_{β_a} + Δ_{ℝ^ι}`.
* `D2Op.apply_factor_eq_zero`: if `β_a ≥ 1/2`, every operator of `𝒟₂` annihilates every
  `Δ_{β_a}`-harmonic function of `(r_a, θ_a)` alone, for example `r_a^{1/β} cos θ_a`.
* `pd_r_pd_r_harmonicCos_one`: `∂²_r (r^{1/β} cos θ) = β⁻¹(β⁻¹ - 1) r^{1/β - 2} cos θ`.
  `rs_apply_mixedExample`: `∂²/∂r∂s (r^{1/β} s cos θ) = β⁻¹ r^{1/β - 1} cos θ`.
* `not_holderNearVertex_radialCosFn`: on `C(S¹_{2πβ})` with its cone distance, `C r^γ cos θ`
  (`C ≠ 0`) is not `α`-Hölder near the vertex for any `α > γ`, `α > 0`.
* **Sharpness of the Hölder exponent** (`sharp_holderExponent`): for each `a` and each
  `α > holderExponentBound β_a` there is an operator `D ∈ 𝒟₂` and a harmonic `u` (the paper's
  examples on p. 3) such that `D u = C r_a^γ cos θ_a` with `γ = holderExponentBound β_a` and
  `C ≠ 0`, which is not `α`-Hölder near the vertex. Here `holderExponentBound β` is `1/β - 1` for
  `β ≥ 1/2` and `1/β - 2` for `β < 1/2`, the quantities in the paper's `μ` (eq. (1.1)).
* `not_holderNearVertex_pure_of_half_le`: for `1/2 ≤ β < 1` the excluded operator `∂²/∂r²`
  maps the harmonic function `r^{1/β} cos θ` to a function that is not `α`-Hölder near the vertex
  for any `α > 0`. It is unbounded for `β > 1/2`, and at `β = 1/2` it equals `2 cos θ`, which has
  no limit at the vertex. So the restriction `β_a < 1/2` in the definition of `𝒟₂` is needed,
  including at `β_a = 1/2`.
-/

@[expose] public section

open scoped Real

namespace ConicalKahler

/-- The paper's polar coordinate variables `r_a`, `θ_a` (`a : κ`) and `s_i` (`i : ι`). -/
inductive ConeVar (κ ι : Type) where
  | r (a : κ)
  | θ (a : κ)
  | s (i : ι)
  deriving DecidableEq

/-- Values of the polar coordinates. `θ_a ∈ ℝ` is a lift of the angle in `ℝ/2πℤ`. -/
abbrev PolarPoint (κ ι : Type) : Type := ConeVar κ ι → ℝ

variable {κ ι : Type}

/-- The point of the real model with polar coordinates `c`: `x_a + i y_a = r_a e^{iθ_a}`. -/
noncomputable def PolarPoint.toModel (c : PolarPoint κ ι) : RealConeModel κ ι :=
  RealConeModel.ofCones (fun a => polarMap (c (.r a), c (.θ a))) fun i => c (.s i)

@[simp] theorem PolarPoint.cone_toModel (c : PolarPoint κ ι) (a : κ) :
    c.toModel.cone a = polarMap (c (.r a), c (.θ a)) := by
  simp [toModel]

@[simp] theorem PolarPoint.eucl_toModel (c : PolarPoint κ ι) (i : ι) :
    c.toModel.eucl i = c (.s i) := by
  simp [toModel]

variable [DecidableEq κ] [DecidableEq ι]

/-- The paper's angles live in `ℝ/2πℤ`: the real coordinates do not see `θ_a ↦ θ_a + 2π`. -/
theorem PolarPoint.toModel_update_theta_add_two_pi (c : PolarPoint κ ι) (a : κ) :
    PolarPoint.toModel (Function.update c (.θ a) (c (.θ a) + 2 * π)) = c.toModel := by
  refine RealConeModel.ext_cone_eucl (fun b => ?_) fun i => by simp
  by_cases h : b = a
  · subst h
    simp [polarMap_add_two_pi]
  · simp [h]

/-! ### Coordinate partial derivatives -/

/-- **The coordinate partial derivative** `∂U/∂x_k` at `c`. -/
noncomputable def pd (k : ConeVar κ ι) (U : PolarPoint κ ι → ℝ) (c : PolarPoint κ ι) : ℝ :=
  deriv (fun t => U (Function.update c k t)) (c k)

/-- The cone Laplacian `Δ_β = ∂²_{r_a} + r_a⁻¹ ∂_{r_a} + (β r_a)⁻² ∂²_{θ_a}` of the factor `a`. -/
noncomputable def coneLaplacian (b : ℝ) (a : κ) (U : PolarPoint κ ι → ℝ) (c : PolarPoint κ ι) :
    ℝ :=
  pd (.r a) (pd (.r a) U) c + (c (.r a))⁻¹ * pd (.r a) U c +
    (b * c (.r a))⁻¹ ^ 2 * pd (.θ a) (pd (.θ a) U) c

/-- **The paper's Laplacian** `Δ = Δ_{β_1} + ⋯ + Δ_{β_n} + Δ_{ℝ^ι}`. -/
noncomputable def paperLaplacian [Fintype κ] [Fintype ι] (β : κ → ConeAngle)
    (U : PolarPoint κ ι → ℝ) (c : PolarPoint κ ι) : ℝ :=
  ∑ a, coneLaplacian (β a).beta a U c + ∑ i, pd (.s i) (pd (.s i) U) c

/-! ### The operators `𝒟₂` -/

/-- **The operators of `𝒟₂`**, exactly as listed on p. 2 of the paper. -/
inductive D2Op (β : κ → ConeAngle) (ι : Type) where
  /-- `∂²/∂s_i∂s_j` -/
  | ss (i j : ι)
  /-- `∂²/∂r_a∂s_i` -/
  | rs (a : κ) (i : ι)
  /-- `r_a⁻¹ ∂²/∂θ_a∂s_i` -/
  | θs (a : κ) (i : ι)
  /-- `∂²/∂r_a∂r_b`, `a ≠ b` -/
  | rr (a b : κ) (hab : a ≠ b)
  /-- `(r_a r_b)⁻¹ ∂²/∂θ_a∂θ_b`, `a ≠ b` -/
  | θθ (a b : κ) (hab : a ≠ b)
  /-- `r_b⁻¹ ∂²/∂r_a∂θ_b`, `a ≠ b` -/
  | rθ (a b : κ) (hab : a ≠ b)
  /-- `Δ_{β_a}` -/
  | lap (a : κ)
  /-- `∂²/∂r_a²`, only for `β_a < 1/2` -/
  | rrPure (a : κ) (h : (β a).beta < 1 / 2)
  /-- `r_a⁻² ∂²/∂θ_a²`, only for `β_a < 1/2` -/
  | θθPure (a : κ) (h : (β a).beta < 1 / 2)
  /-- `r_a⁻¹ ∂²/∂r_a∂θ_a`, only for `β_a < 1/2` -/
  | rθPure (a : κ) (h : (β a).beta < 1 / 2)

/-- The action of an operator of `𝒟₂` on a function of the polar coordinates. -/
noncomputable def D2Op.apply {β : κ → ConeAngle} :
    D2Op β ι → (PolarPoint κ ι → ℝ) → PolarPoint κ ι → ℝ
  | .ss i j, U, c => pd (.s i) (pd (.s j) U) c
  | .rs a i, U, c => pd (.r a) (pd (.s i) U) c
  | .θs a i, U, c => (c (.r a))⁻¹ * pd (.θ a) (pd (.s i) U) c
  | .rr a b _, U, c => pd (.r a) (pd (.r b) U) c
  | .θθ a b _, U, c => (c (.r a) * c (.r b))⁻¹ * pd (.θ a) (pd (.θ b) U) c
  | .rθ a b _, U, c => (c (.r b))⁻¹ * pd (.r a) (pd (.θ b) U) c
  | .lap a, U, c => coneLaplacian (β a).beta a U c
  | .rrPure a _, U, c => pd (.r a) (pd (.r a) U) c
  | .θθPure a _, U, c => (c (.r a))⁻¹ ^ 2 * pd (.θ a) (pd (.θ a) U) c
  | .rθPure a _, U, c => (c (.r a))⁻¹ * pd (.r a) (pd (.θ a) U) c

/-! ### Functions of one cone factor -/

section Factor

variable (F : ℝ → ℝ → ℝ) (a : κ) (c : PolarPoint κ ι)

theorem pd_r_factor :
    pd (.r a) (fun c : PolarPoint κ ι => F (c (.r a)) (c (.θ a))) c =
      deriv (fun t => F t (c (.θ a))) (c (.r a)) := by
  simp [pd]

theorem pd_theta_factor :
    pd (.θ a) (fun c : PolarPoint κ ι => F (c (.r a)) (c (.θ a))) c =
      deriv (fun t => F (c (.r a)) t) (c (.θ a)) := by
  simp [pd]

theorem pd_r_pd_r_factor :
    pd (.r a) (pd (.r a) fun c : PolarPoint κ ι => F (c (.r a)) (c (.θ a))) c =
      deriv (deriv fun t => F t (c (.θ a))) (c (.r a)) := by
  simp [pd]

theorem pd_theta_pd_theta_factor :
    pd (.θ a) (pd (.θ a) fun c : PolarPoint κ ι => F (c (.r a)) (c (.θ a))) c =
      deriv (deriv fun t => F (c (.r a)) t) (c (.θ a)) := by
  simp [pd]

/-- The cone Laplacian of a function of `(r_a, θ_a)` is the polar expression of `Δ_β`. -/
theorem coneLaplacian_factor (b : ℝ) :
    coneLaplacian b a (fun c : PolarPoint κ ι => F (c (.r a)) (c (.θ a))) c =
      deriv (deriv fun t => F t (c (.θ a))) (c (.r a)) +
        (c (.r a))⁻¹ * deriv (fun t => F t (c (.θ a))) (c (.r a)) +
        (b * c (.r a))⁻¹ ^ 2 * deriv (deriv fun t => F (c (.r a)) t) (c (.θ a)) := by
  rw [coneLaplacian, pd_r_pd_r_factor, pd_r_factor, pd_theta_pd_theta_factor]

/-- A function of `(r_a, θ_a)` does not see the cone factors `b ≠ a`. -/
theorem coneLaplacian_factor_of_ne (b : ℝ) {a' : κ} (h : a' ≠ a) :
    coneLaplacian b a' (fun c : PolarPoint κ ι => F (c (.r a)) (c (.θ a))) c = 0 := by
  simp [coneLaplacian, pd, Ne.symm h]

/-- **`𝒟₂` annihilates the harmonic functions of one cone factor with `β_a ≥ 1/2`.** If
`Δ_{β_a} U = 0` at `c` and `U` depends only on `(r_a, θ_a)`, then `D U = 0` at `c` for every
`D ∈ 𝒟₂`. The pure conical operators of the factor `a` are absent from `𝒟₂` because
`β_a ≥ 1/2`. -/
theorem D2Op.apply_factor_eq_zero {β : κ → ConeAngle} (hβ : 1 / 2 ≤ (β a).beta)
    (hΔ : coneLaplacian (β a).beta a (fun c : PolarPoint κ ι => F (c (.r a)) (c (.θ a))) c = 0)
    (D : D2Op β ι) : D.apply (fun c : PolarPoint κ ι => F (c (.r a)) (c (.θ a))) c = 0 := by
  cases D with
  | ss i j => simp [D2Op.apply, pd]
  | rs b i => simp [D2Op.apply, pd]
  | θs b i => simp [D2Op.apply, pd]
  | rr b b' hbb =>
    by_cases h1 : b' = a
    · subst h1
      simp [D2Op.apply, pd, Ne.symm hbb]
    · simp [D2Op.apply, pd, Ne.symm h1]
  | θθ b b' hbb =>
    by_cases h1 : b' = a
    · subst h1
      simp [D2Op.apply, pd, Ne.symm hbb]
    · simp [D2Op.apply, pd, Ne.symm h1]
  | rθ b b' hbb =>
    by_cases h1 : b' = a
    · subst h1
      simp [D2Op.apply, pd, Ne.symm hbb]
    · simp [D2Op.apply, pd, Ne.symm h1]
  | lap b =>
    by_cases h : b = a
    · subst h
      exact hΔ
    · exact coneLaplacian_factor_of_ne F a c _ h
  | rrPure b hb =>
    by_cases h : b = a
    · subst h
      exact absurd hb (not_lt.mpr hβ)
    · simp [D2Op.apply, pd, Ne.symm h]
  | θθPure b hb =>
    by_cases h : b = a
    · subst h
      exact absurd hb (not_lt.mpr hβ)
    · simp [D2Op.apply, pd, Ne.symm h]
  | rθPure b hb =>
    by_cases h : b = a
    · subst h
      exact absurd hb (not_lt.mpr hβ)
    · simp [D2Op.apply, pd, Ne.symm h]

end Factor

/-! ### The explicit harmonic functions -/

/-- `r_a^{k/b} cos(kθ_a)`, the function `coneHarmonicCos` of the factor `a`. -/
noncomputable def harmonicCos (b : ℝ) (k : ℕ) (a : κ) (c : PolarPoint κ ι) : ℝ :=
  coneHarmonicCos b k (c (.r a)) (c (.θ a))

/-- `r_a^{k/b} sin(kθ_a)`. -/
noncomputable def harmonicSin (b : ℝ) (k : ℕ) (a : κ) (c : PolarPoint κ ι) : ℝ :=
  coneHarmonicSin b k (c (.r a)) (c (.θ a))

/-- The paper's example `r_a^{1/b} s_i cos θ_a` (p. 3). -/
noncomputable def mixedExample (b : ℝ) (a : κ) (i : ι) (c : PolarPoint κ ι) : ℝ :=
  coneHarmonicCos b 1 (c (.r a)) (c (.θ a)) * c (.s i)

theorem coneLaplacian_harmonicCos {b : ℝ} (hb : 0 < b) (k : ℕ) (a : κ) {c : PolarPoint κ ι}
    (hr : 0 < c (.r a)) : coneLaplacian b a (harmonicCos b k a) c = 0 := by
  rw [show harmonicCos b k a = fun c : PolarPoint κ ι => coneHarmonicCos b k (c (.r a)) (c (.θ a))
    from rfl, coneLaplacian_factor]
  exact coneHarmonicCos_polar_eq_zero hb hr

theorem coneLaplacian_harmonicSin {b : ℝ} (hb : 0 < b) (k : ℕ) (a : κ) {c : PolarPoint κ ι}
    (hr : 0 < c (.r a)) : coneLaplacian b a (harmonicSin b k a) c = 0 := by
  rw [show harmonicSin b k a = fun c : PolarPoint κ ι => coneHarmonicSin b k (c (.r a)) (c (.θ a))
    from rfl, coneLaplacian_factor]
  exact coneHarmonicSin_polar_eq_zero hb hr

/-- Multiplying by a Euclidean coordinate `s_i` commutes with `∂/∂x_k` for `x_k ≠ s_i`. -/
theorem pd_mul_s {k : ConeVar κ ι} {i : ι} (hk : k ≠ .s i) (V : PolarPoint κ ι → ℝ) :
    pd k (fun c => V c * c (.s i)) = fun c => pd k V c * c (.s i) := by
  funext c
  simp only [pd]
  rw [show (fun t => V (Function.update c k t) * Function.update c k t (.s i)) =
      fun t => V (Function.update c k t) * c (.s i) from
    funext fun t => by rw [Function.update_of_ne (Ne.symm hk)]]
  exact deriv_mul_const_field _

theorem coneLaplacian_mul_s (b : ℝ) (a : κ) (i : ι) (V : PolarPoint κ ι → ℝ)
    (c : PolarPoint κ ι) :
    coneLaplacian b a (fun c => V c * c (.s i)) c = coneLaplacian b a V c * c (.s i) := by
  simp only [coneLaplacian]
  rw [pd_mul_s (k := .r a) (by simp), pd_mul_s (k := .r a) (by simp),
    pd_mul_s (k := .θ a) (by simp), pd_mul_s (k := .θ a) (by simp)]
  ring

variable [Fintype κ] [Fintype ι]

/-- **`r_a^{k/β_a} cos(kθ_a)` is harmonic** for the paper's Laplacian on the regular part. -/
theorem paperLaplacian_harmonicCos (β : κ → ConeAngle) (k : ℕ) (a : κ) {c : PolarPoint κ ι}
    (hr : 0 < c (.r a)) : paperLaplacian β (harmonicCos (β a).beta k a) c = 0 := by
  have hs : ∑ i, pd (.s i) (pd (.s i) (harmonicCos (β a).beta k a)) c = 0 :=
    Finset.sum_eq_zero fun i _ => by simp [pd, harmonicCos]
  rw [paperLaplacian, hs, add_zero, Finset.sum_eq_single a]
  · exact coneLaplacian_harmonicCos (β a).pos k a hr
  · exact fun b _ hb =>
      coneLaplacian_factor_of_ne (fun x y => coneHarmonicCos (β a).beta k x y) a c _ hb
  · simp

/-- **The paper's example `r_a^{1/β_a} s_i cos θ_a` is harmonic** on the regular part. -/
theorem paperLaplacian_mixedExample (β : κ → ConeAngle) (a : κ) (i : ι) {c : PolarPoint κ ι}
    (hr : 0 < c (.r a)) : paperLaplacian β (mixedExample (β a).beta a i) c = 0 := by
  have hs : ∑ j, pd (.s j) (pd (.s j) (mixedExample (β a).beta a i)) c = 0 :=
    Finset.sum_eq_zero fun j _ => by
      by_cases h : j = i
      · subst h
        simp [pd, mixedExample]
      · simp [pd, mixedExample, Ne.symm h]
  have hcone : ∀ b, coneLaplacian (β b).beta b (mixedExample (β a).beta a i) c = 0 := by
    intro b
    rw [show mixedExample (β a).beta a i =
        fun c : PolarPoint κ ι => harmonicCos (β a).beta 1 a c * c (.s i) from rfl,
      coneLaplacian_mul_s]
    by_cases h : b = a
    · subst h
      rw [coneLaplacian_harmonicCos (β b).pos 1 b hr, zero_mul]
    · rw [show harmonicCos (β a).beta 1 a =
          fun c : PolarPoint κ ι => coneHarmonicCos (β a).beta 1 (c (.r a)) (c (.θ a)) from rfl,
        coneLaplacian_factor_of_ne _ a c _ h, zero_mul]
  rw [paperLaplacian, hs, add_zero]
  exact Finset.sum_eq_zero fun b _ => hcone b

omit [Fintype κ] [Fintype ι] in
/-- `∂²_r (r^{1/b} cos θ) = b⁻¹ (b⁻¹ - 1) r^{1/b - 2} cos θ`. -/
theorem pd_r_pd_r_harmonicCos_one (b : ℝ) (a : κ) {c : PolarPoint κ ι} (hr : 0 < c (.r a)) :
    pd (.r a) (pd (.r a) (harmonicCos b 1 a)) c =
      b⁻¹ * (b⁻¹ - 1) * c (.r a) ^ (b⁻¹ - 2) * Real.cos (c (.θ a)) := by
  rw [show harmonicCos b 1 a = fun c : PolarPoint κ ι => coneHarmonicCos b 1 (c (.r a)) (c (.θ a))
    from rfl, pd_r_pd_r_factor, deriv_deriv_coneHarmonicCos_rho hr]
  simp

omit [Fintype κ] [Fintype ι] in
/-- `∂²/∂r∂s (r^{1/b} s cos θ) = b⁻¹ r^{1/b - 1} cos θ`. -/
theorem rs_apply_mixedExample {β : κ → ConeAngle} (a : κ) (i : ι) {c : PolarPoint κ ι}
    (hr : 0 < c (.r a)) :
    (D2Op.rs (β := β) a i).apply (mixedExample (β a).beta a i) c =
      (β a).beta⁻¹ * c (.r a) ^ ((β a).beta⁻¹ - 1) * Real.cos (c (.θ a)) := by
  simp [D2Op.apply, pd, mixedExample]
  rw [deriv_coneHarmonicCos_rho hr]
  simp

/-! ### Hölder continuity at the vertex -/

/-- `C r^γ cos θ` in the paper's real coordinates `w = r e^{iθ}`: `C |w|^{γ-1} Re w`. -/
noncomputable def radialCosFn (C γ : ℝ) (w : ℂ) : ℝ :=
  C * ‖w‖ ^ (γ - 1) * w.re

theorem radialCosFn_polarMap (C γ : ℝ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    radialCosFn C γ (polarMap (r, θ)) = C * r ^ γ * Real.cos θ := by
  rw [radialCosFn, norm_polarMap_of_nonneg hr.le, Real.rpow_sub_one hr.ne']
  simp only [polarMap, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]
  field_simp

/-- `f` is `α`-Hölder for the cone distance on the punctured ball of radius `ε` about the vertex. -/
def HolderNearVertex (β : ConeAngle) (α ε : ℝ) (f : ℂ → ℝ) : Prop :=
  ∃ K : ℝ, ∀ p q : ConeTwo β, p ≠ ConeTwo.vertex → q ≠ ConeTwo.vertex →
    dist p ConeTwo.vertex < ε → dist q ConeTwo.vertex < ε →
      |f p.coord - f q.coord| ≤ K * dist p q ^ α

/-- The Hölder estimate at the vertex, with value `0` there: `|C r^γ cos θ| ≤ |C| d(p, o)^γ`. -/
theorem abs_radialCosFn_le {β : ConeAngle} (C γ : ℝ) (w : ℂ) (hw : w ≠ 0) :
    |radialCosFn C γ w| ≤ |C| * dist (ConeTwo.mk w : ConeTwo β) ConeTwo.vertex ^ γ := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [ConeTwo.dist_vertex, ConeTwo.coord_mk, radialCosFn, abs_mul, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hn _), Real.rpow_sub_one hn.ne']
  have hre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  calc |C| * (‖w‖ ^ γ / ‖w‖) * |w.re| ≤ |C| * (‖w‖ ^ γ / ‖w‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_left hre (by positivity)
    _ = |C| * ‖w‖ ^ γ := by field_simp

theorem exists_small_rpow_gt {e : ℝ} (he : e < 0) {ε : ℝ} (hε : 0 < ε) (M : ℝ) :
    ∃ r, 0 < r ∧ r < ε ∧ M < r ^ e := by
  set X := |M| + 1
  have hX : 0 < X := by positivity
  have hpos : 0 < min (ε / 2) (X ^ e⁻¹) := lt_min (by linarith) (Real.rpow_pos_of_pos hX _)
  refine ⟨min (ε / 2) (X ^ e⁻¹), hpos, (min_le_left _ _).trans_lt (by linarith), ?_⟩
  have h1 : X ≤ (min (ε / 2) (X ^ e⁻¹)) ^ e :=
    calc X = (X ^ e⁻¹) ^ e := (Real.rpow_inv_rpow hX.le he.ne).symm
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos hpos (min_le_right _ _) he.le
  linarith [le_abs_self M]

/-- **`C r^γ cos θ` is not `α`-Hölder near the vertex for `α > γ`.** Compare the opposite points
`r` and `-r`: the values differ by `2 C r^γ`, the cone distance is at most `2r`, and
`r^{γ - α} → ∞` as `r → 0`. -/
theorem not_holderNearVertex_radialCosFn {β : ConeAngle} {C γ α ε : ℝ} (hC : C ≠ 0)
    (hα : 0 < α) (hγα : γ < α) (hε : 0 < ε) : ¬ HolderNearVertex β α ε (radialCosFn C γ) := by
  rintro ⟨K, hK⟩
  have hC' : 0 < |C| := abs_pos.mpr hC
  obtain ⟨r, hr0, hrε, hrM⟩ :=
    exists_small_rpow_gt (sub_neg.mpr hγα) hε (|K| * 2 ^ α / (2 * |C|))
  set p : ConeTwo β := ConeTwo.mk (r : ℂ)
  set q : ConeTwo β := ConeTwo.mk (-(r : ℂ))
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  have hp : p ≠ ConeTwo.vertex := fun h => hrC (congrArg ConeTwo.coord h)
  have hq : q ≠ ConeTwo.vertex := fun h => (neg_ne_zero.mpr hrC) (congrArg ConeTwo.coord h)
  have hdp : dist p ConeTwo.vertex = r := by
    rw [ConeTwo.dist_vertex, ConeTwo.coord_mk, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0]
  have hdq : dist q ConeTwo.vertex = r := by
    rw [ConeTwo.dist_vertex, ConeTwo.coord_mk, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0]
  have h := hK p q hp hq (hdp ▸ hrε) (hdq ▸ hrε)
  have hf : radialCosFn C γ p.coord - radialCosFn C γ q.coord = 2 * C * r ^ γ := by
    simp only [p, q, ConeTwo.coord_mk, radialCosFn, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr0, Complex.neg_re, Complex.ofReal_re,
      Real.rpow_sub_one hr0.ne']
    field_simp
    ring
  have hd : dist p q ≤ 2 * r := by
    have := dist_triangle p ConeTwo.vertex q
    rw [hdp, dist_comm ConeTwo.vertex q, hdq] at this
    linarith
  have hd' : dist p q ^ α ≤ (2 * r) ^ α := Real.rpow_le_rpow dist_nonneg hd hα.le
  have hrγ : 0 < r ^ γ := Real.rpow_pos_of_pos hr0 _
  have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr0 _
  have h1 : 2 * |C| * r ^ γ ≤ |K| * 2 ^ α * r ^ α :=
    calc 2 * |C| * r ^ γ = |radialCosFn C γ p.coord - radialCosFn C γ q.coord| := by
          rw [hf, abs_mul, abs_mul, abs_of_pos hrγ, abs_two]
      _ ≤ K * dist p q ^ α := h
      _ ≤ |K| * dist p q ^ α :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg dist_nonneg _)
      _ ≤ |K| * (2 * r) ^ α := mul_le_mul_of_nonneg_left hd' (abs_nonneg K)
      _ = |K| * 2 ^ α * r ^ α := by rw [Real.mul_rpow (by norm_num) hr0.le]; ring
  have h2 : r ^ (γ - α) ≤ |K| * 2 ^ α / (2 * |C|) := by
    rw [Real.rpow_sub hr0, div_le_div_iff₀ hrα (by positivity)]
    nlinarith
  linarith

/-! ### Sharpness of the Hölder exponent -/

/-- The bound on the Hölder exponent coming from the factor of angle `2πβ` in the paper's `μ`
(eq. (1.1)): `1/β - 1` for `β ≥ 1/2` and `1/β - 2` for `β < 1/2`. The paper's condition
`α < μ` is `α < 1` and `α < holderExponentBound β_a` for all `a`. -/
noncomputable def holderExponentBound (β : ℝ) : ℝ :=
  if β < 1 / 2 then β⁻¹ - 2 else β⁻¹ - 1

omit [Fintype κ] [Fintype ι] in
/-- **The examples on p. 3 of the paper are sharp.** For every cone factor `a`, every Euclidean
direction `i` and every `α > holderExponentBound β_a` (with `α > 0`), there are an operator
`D ∈ 𝒟₂` and a function `U`, harmonic on `{r_a > 0}`, such that `D U = C r_a^γ cos θ_a` with
`C ≠ 0` and `γ = holderExponentBound β_a`. That function is not `α`-Hölder near the vertex.
* `β_a < 1/2`: `D = ∂²/∂r_a²`, `U = r_a^{1/β_a} cos θ_a`.
* `β_a ≥ 1/2`: `D = ∂²/∂r_a∂s_i`, `U = r_a^{1/β_a} s_i cos θ_a`. -/
theorem sharp_holderExponent [Fintype κ] [Fintype ι] (β : κ → ConeAngle) (a : κ) (i : ι) {α : ℝ}
    (hα : 0 < α) (hαβ : holderExponentBound (β a).beta < α) :
    ∃ (D : D2Op β ι) (U : PolarPoint κ ι → ℝ) (C : ℝ), C ≠ 0 ∧
      (∀ c : PolarPoint κ ι, 0 < c (.r a) → paperLaplacian β U c = 0) ∧
      (∀ c : PolarPoint κ ι, 0 < c (.r a) →
        D.apply U c = radialCosFn C (holderExponentBound (β a).beta)
          (polarMap (c (.r a), c (.θ a)))) ∧
      ∀ ε > 0, ¬ HolderNearVertex (β a) α ε
        (radialCosFn C (holderExponentBound (β a).beta)) := by
  have hb := (β a).pos
  by_cases h : (β a).beta < 1 / 2
  · have hγ : holderExponentBound (β a).beta = (β a).beta⁻¹ - 2 := ite_eq_left h
    have hinv : 2 < (β a).beta⁻¹ := by
      rw [lt_inv_comm₀ two_pos hb]
      linarith
    refine ⟨.rrPure a h, harmonicCos (β a).beta 1 a, (β a).beta⁻¹ * ((β a).beta⁻¹ - 1),
      mul_ne_zero (inv_ne_zero hb.ne') (by linarith), fun c hr => paperLaplacian_harmonicCos β 1 a hr,
      fun c hr => ?_, fun ε hε => not_holderNearVertex_radialCosFn
        (mul_ne_zero (inv_ne_zero hb.ne') (by linarith)) hα hαβ hε⟩
    rw [hγ, radialCosFn_polarMap _ _ hr]
    exact pd_r_pd_r_harmonicCos_one _ a hr
  · have hγ : holderExponentBound (β a).beta = (β a).beta⁻¹ - 1 := ite_eq_right h
    refine ⟨.rs a i, mixedExample (β a).beta a i, (β a).beta⁻¹, inv_ne_zero hb.ne',
      fun c hr => paperLaplacian_mixedExample β a i hr, fun c hr => ?_,
      fun ε hε => not_holderNearVertex_radialCosFn (inv_ne_zero hb.ne') hα hαβ hε⟩
    rw [hγ, radialCosFn_polarMap _ _ hr]
    exact rs_apply_mixedExample a i hr

omit [Fintype κ] [Fintype ι] in
/-- **The pure conical operators must be excluded for `β ≥ 1/2`, including `β = 1/2`.** For
`1/2 ≤ β < 1`, `∂²_r (r^{1/β} cos θ) = C r^γ cos θ` with `C = β⁻¹(β⁻¹ - 1) ≠ 0` and
`γ = 1/β - 2 ≤ 0`. This is not `α`-Hölder near the vertex for any `α > 0`. For `β > 1/2` it is
unbounded; for `β = 1/2` it is `2 cos θ`, which has no limit at the vertex. -/
theorem not_holderNearVertex_pure_of_half_le {β : ConeAngle} (hβ : 1 / 2 ≤ β.beta)
    (hβ1 : β.beta < 1) (a : κ) {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    (∀ c : PolarPoint κ ι, 0 < c (.r a) →
      pd (.r a) (pd (.r a) (harmonicCos β.beta 1 a)) c =
        radialCosFn (β.beta⁻¹ * (β.beta⁻¹ - 1)) (β.beta⁻¹ - 2) (polarMap (c (.r a), c (.θ a)))) ∧
      ¬ HolderNearVertex β α ε (radialCosFn (β.beta⁻¹ * (β.beta⁻¹ - 1)) (β.beta⁻¹ - 2)) := by
  have hb := β.pos
  have hinv1 : 1 < β.beta⁻¹ := by rw [lt_inv_comm₀ one_pos hb, inv_one]; exact hβ1
  have hinv2 : β.beta⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hb two_pos]
    linarith
  refine ⟨fun c hr => ?_, not_holderNearVertex_radialCosFn
    (mul_ne_zero (inv_ne_zero hb.ne') (by linarith)) hα (by linarith) hε⟩
  rw [radialCosFn_polarMap _ _ hr]
  exact pd_r_pd_r_harmonicCos_one _ a hr

end ConicalKahler
