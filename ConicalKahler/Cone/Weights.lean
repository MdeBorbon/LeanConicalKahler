module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Sets.Opens

/-!
# Cone angles, cone weights and the diagonal model metric (numerical part)

The local model of a Kähler metric with cone angle `2πβ` along `{z_0 = 0}` is

  `ω_β = i β² |z_0|^(2β-2) dz_0 ∧ dz̄_0 + i ∑_{j ≥ 1} dz_j ∧ dz̄_j`.

More generally (simple normal crossings), each coordinate `z_j` either carries a cone angle
`2πβ_j` or is a smooth direction. This is recorded by `θ : ConeWeights n`, a map
`Fin n → Option ConeAngle` with `none` for smooth directions.

## Conventions

* Coordinates are indexed by `Fin n`, so the singular coordinate of the single-divisor model is
  `z_0` (written `z_1` in 1-indexed mathematical notation).
* Upstream `KahlerForm` uses `ω = i ∑ g_{jk̄} dz_j ∧ dz̄_k` and the Riemannian metric
  `g(v, v) = ω(v, Jv) = 2 ∑ g_{jk̄} v_j v̄_k`. The model coefficient matrix is
  `modelConeMatrix θ z = diag(w_j(z))` and `modelConeQuadratic θ z v = ∑ w_j(z) |v_j|²` is the
  **Hermitian** (half-Riemannian) quadratic form: the Riemannian length is
  `2 * modelConeQuadratic`.

## Main declarations

* `ConeAngle`, `ConeWeights`, `singleConeWeights`, `ConeWeights.smooth`.
* `modelDomain θ : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))`: the complement of the
  singular coordinate hyperplanes. `isOpen` is part of the `Opens` structure.
* `modelWeight θ z j`: `1` for a smooth direction and `β² |z_j|^(2β-2)` for a cone direction.
* `modelConeQuadratic`, `modelConeMatrix`, with positivity on `modelDomain θ`.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace ConicalKahler

/-- The model space `ℂⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- A cone angle `2πβ`, recorded by the positive real number `β`. The standard range for
Kähler–Einstein theory is `0 < β ≤ 1`; angles `β > 1` are allowed as models. -/
@[ext]
structure ConeAngle where
  /-- The cone angle divided by `2π`. -/
  beta : ℝ
  pos : 0 < beta

/-- Cone weights on `ℂⁿ`: coordinate `j` carries the cone angle `θ.angle j = some β`, or is a
smooth direction when `θ.angle j = none`. -/
@[ext]
structure ConeWeights (n : ℕ) where
  /-- The cone angle of each coordinate (`none` = smooth direction). -/
  angle : Fin n → Option ConeAngle

variable {n : ℕ}

/-- The trivial weights: every direction is smooth. -/
def ConeWeights.smooth (n : ℕ) : ConeWeights n :=
  ⟨fun _ => none⟩

/-- The single-divisor weights: cone angle `2πβ` along `z_0 = 0`, smooth in `z_1, …, z_{n-1}`. -/
def singleConeWeights [NeZero n] (β : ConeAngle) : ConeWeights n :=
  ⟨fun j => if j = 0 then some β else none⟩

@[simp]
theorem singleConeWeights_angle_zero [NeZero n] (β : ConeAngle) :
    (singleConeWeights (n := n) β).angle 0 = some β := by
  simp [singleConeWeights]

@[simp]
theorem singleConeWeights_angle_of_ne [NeZero n] (β : ConeAngle) {j : Fin n} (hj : j ≠ 0) :
    (singleConeWeights (n := n) β).angle j = none := by
  simp [singleConeWeights, hj]

/-! ### The model domain -/

/-- The set of `z` with `z_j ≠ 0` for every singular coordinate `j`. -/
def modelDomainSet (θ : ConeWeights n) : Set (E n) :=
  {z | ∀ j β, θ.angle j = some β → z j ≠ 0}

theorem isOpen_modelDomainSet (θ : ConeWeights n) : IsOpen (modelDomainSet θ) := by
  have hrw : modelDomainSet θ = ⋂ j, {z : E n | ∀ β, θ.angle j = some β → z j ≠ 0} := by
    ext z
    simp [modelDomainSet]
  rw [hrw]
  refine isOpen_iInter_of_finite fun j => ?_
  cases hθ : θ.angle j with
  | none => simp
  | some β =>
    simp only [Option.some.injEq, forall_eq']
    exact isOpen_ne_fun (EuclideanSpace.proj j : E n →L[ℂ] ℂ).continuous continuous_const

/-- The model domain `{z | z_j ≠ 0 for all singular j}`, an open subset of `ℂⁿ`. -/
def modelDomain (θ : ConeWeights n) : TopologicalSpace.Opens (E n) :=
  ⟨modelDomainSet θ, isOpen_modelDomainSet θ⟩

theorem mem_modelDomain {θ : ConeWeights n} {z : E n} :
    z ∈ modelDomain θ ↔ ∀ j β, θ.angle j = some β → z j ≠ 0 :=
  Iff.rfl

/-- For the single-divisor weights, the model domain is `{z_0 ≠ 0}`. -/
theorem mem_modelDomain_single [NeZero n] {β : ConeAngle} {z : E n} :
    z ∈ modelDomain (singleConeWeights β) ↔ z 0 ≠ 0 := by
  rw [mem_modelDomain]
  constructor
  · intro h
    exact h 0 β (singleConeWeights_angle_zero β)
  · intro h j γ hj
    by_cases hj0 : j = 0
    · subst hj0
      exact h
    · rw [singleConeWeights_angle_of_ne β hj0] at hj
      cases hj

/-- Every point is in the domain of the smooth weights. -/
@[simp]
theorem mem_modelDomain_smooth (z : E n) : z ∈ modelDomain (ConeWeights.smooth n) := by
  intro j β h
  cases h

/-! ### Weights, quadratic form and coefficient matrix -/

/-- The diagonal coefficient `w_j(z)`: `1` for a smooth direction and `β² |z_j|^(2β-2)` for a
cone direction of angle `2πβ`. -/
noncomputable def modelWeight (θ : ConeWeights n) (z : E n) (j : Fin n) : ℝ :=
  match θ.angle j with
  | none => 1
  | some β => β.beta ^ 2 * ‖z j‖ ^ (2 * β.beta - 2)

theorem modelWeight_of_none {θ : ConeWeights n} {j : Fin n} (h : θ.angle j = none) (z : E n) :
    modelWeight θ z j = 1 := by
  simp [modelWeight, h]

theorem modelWeight_of_some {θ : ConeWeights n} {j : Fin n} {β : ConeAngle}
    (h : θ.angle j = some β) (z : E n) :
    modelWeight θ z j = β.beta ^ 2 * ‖z j‖ ^ (2 * β.beta - 2) := by
  simp [modelWeight, h]

theorem modelWeight_nonneg (θ : ConeWeights n) (z : E n) (j : Fin n) :
    0 ≤ modelWeight θ z j := by
  unfold modelWeight
  split
  · exact zero_le_one
  · positivity

/-- All weights are strictly positive off the singular coordinate hyperplanes. -/
theorem modelWeight_pos {θ : ConeWeights n} {z : E n} (hz : z ∈ modelDomain θ) (j : Fin n) :
    0 < modelWeight θ z j := by
  cases hθ : θ.angle j with
  | none => simp [modelWeight_of_none hθ]
  | some β =>
    rw [modelWeight_of_some hθ]
    have hzj : 0 < ‖z j‖ := norm_pos_iff.mpr (hz j β hθ)
    have := β.pos
    positivity

/-- The Hermitian quadratic form `q_model(v) = ∑ w_j(z) |v_j|²` (half the Riemannian
quadratic form). -/
noncomputable def modelConeQuadratic (θ : ConeWeights n) (z v : E n) : ℝ :=
  ∑ j : Fin n, modelWeight θ z j * Complex.normSq (v j)

/-- The Hermitian coefficient matrix `diag(w_j(z))` of the model. -/
noncomputable def modelConeMatrix (θ : ConeWeights n) (z : E n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun j => (modelWeight θ z j : ℂ)

theorem modelConeQuadratic_nonneg (θ : ConeWeights n) (z v : E n) :
    0 ≤ modelConeQuadratic θ z v :=
  Finset.sum_nonneg fun j _ =>
    mul_nonneg (modelWeight_nonneg θ z j) (Complex.normSq_nonneg _)

theorem modelConeQuadratic_pos {θ : ConeWeights n} {z : E n} (hz : z ∈ modelDomain θ)
    {v : E n} (hv : v ≠ 0) : 0 < modelConeQuadratic θ z v := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv (PiLp.ext h)
  refine Finset.sum_pos' (fun k _ =>
    mul_nonneg (modelWeight_nonneg θ z k) (Complex.normSq_nonneg _)) ⟨j, Finset.mem_univ _, ?_⟩
  exact mul_pos (modelWeight_pos hz j) (Complex.normSq_pos.mpr hj)

/-- The quadratic form is the Hermitian form of the coefficient matrix, in the upstream index
convention `∑ⱼₖ a_{jk̄} vⱼ v̄ₖ` (`ContinuousAlternatingMap.IsOneOne.apply_I_smul`). -/
theorem modelConeQuadratic_eq_sum (θ : ConeWeights n) (z v : E n) :
    (modelConeQuadratic θ z v : ℂ) =
      ∑ j, ∑ k, modelConeMatrix θ z j k * v j * star (v k) := by
  simp only [modelConeQuadratic, modelConeMatrix, Matrix.diagonal_apply, Complex.ofReal_sum,
    Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
  simp only [ite_true]
  rw [Complex.normSq_eq_conj_mul_self, mul_assoc, mul_comm (starRingEnd ℂ (v j))]
  rfl

theorem modelConeMatrix_isHermitian (θ : ConeWeights n) (z : E n) :
    (modelConeMatrix θ z).IsHermitian :=
  isHermitian_diagonal_of_self_adjoint _ <| funext fun j => by
    simp [Complex.conj_ofReal]

theorem modelConeMatrix_posDef {θ : ConeWeights n} {z : E n} (hz : z ∈ modelDomain θ) :
    (modelConeMatrix θ z).PosDef :=
  Matrix.PosDef.diagonal fun j => by
    simpa using modelWeight_pos hz j

theorem det_modelConeMatrix (θ : ConeWeights n) (z : E n) :
    (modelConeMatrix θ z).det = ((∏ j, modelWeight θ z j : ℝ) : ℂ) := by
  simp [modelConeMatrix, Matrix.det_diagonal]

/-! ### The smooth case `β = 1` -/

/-- The cone angle `2π`, i.e. no cone singularity. -/
def ConeAngle.one : ConeAngle :=
  ⟨1, one_pos⟩

/-- A cone direction with angle `2π` has the Euclidean weight `1`. -/
theorem modelWeight_of_some_one {θ : ConeWeights n} {j : Fin n}
    (h : θ.angle j = some ConeAngle.one) (z : E n) : modelWeight θ z j = 1 := by
  rw [modelWeight_of_some h]
  simp [ConeAngle.one]

end ConicalKahler
