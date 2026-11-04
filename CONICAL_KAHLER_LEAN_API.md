# Conical Kähler geometry in Lean 4 — API design (v0.1)

**Status:** mathematical/interface design, inspected against `wxkj99/calabi-yau` on 3 November 2026. **Not yet implemented or compiler-checked.** The declarations below are proposed public signatures. They must not be presented as existing Lean theorems or compiled code. No `axiom`, `sorry`, or `opaque` proof substitutes are acceptable for a completed milestone.

## 1. Existing library: confirmed interfaces

The proposed dependency is `wxkj99/calabi-yau` at a pinned commit. The relevant actual source files and public declarations are:

- [`CalabiYau/Geometry/Kahler/Basic.lean`](https://github.com/wxkj99/calabi-yau/blob/main/CalabiYau/Geometry/Kahler/Basic.lean): `KahlerForm n M`, with `toFormField`, `isSmooth'`, `isPositive'`, `isClosed'`, `metricInChart`, `innerAt`, `IsPotential`, `perturb`.
- [`CalabiYau/Geometry/Complex/Forms/Basic.lean`](https://github.com/wxkj99/calabi-yau/blob/main/CalabiYau/Geometry/Complex/Forms/Basic.lean): `FormField E M k`, `FormField.chartRep`, `.IsSmooth`, `.IsClosed`, `.extDeriv`, `.IsExact`.
- [`CalabiYau/Geometry/Complex/Forms/OneOne.lean`](https://github.com/wxkj99/calabi-yau/blob/main/CalabiYau/Geometry/Complex/Forms/OneOne.lean): `ContinuousAlternatingMap.IsOneOne`, `.IsPositive`, `.IsNonneg`, `.coeffMatrix`, `.relDet`, `.relTrace`; normalization: `α(v,Iv)=2∑ a_{j k̄}v_j conj(v_k)`.
- [`CalabiYau/Geometry/Complex/Forms/ComplexHessian.lean`](https://github.com/wxkj99/calabi-yau/blob/main/CalabiYau/Geometry/Complex/Forms/ComplexHessian.lean): `ddbar`, `mddbar`, `complexHessian`, and `complexHessian_normSq`.
- [`CalabiYau/Geometry/Kahler/Ricci.lean`](https://github.com/wxkj99/calabi-yau/blob/main/CalabiYau/Geometry/Kahler/Ricci.lean): `KahlerForm.ricciForm`.
- [`CalabiYau/MongeAmpere/Operator.lean`](https://github.com/wxkj99/calabi-yau/blob/main/CalabiYau/MongeAmpere/Operator.lean): `KahlerForm.mongeAmpere`, `KahlerForm.SolvesMongeAmpere`.
- [`CalabiYau/Geometry/Complex/DDBar/ScalarPotential/Componentwise.lean`](https://github.com/wxkj99/calabi-yau/blob/main/CalabiYau/Geometry/Complex/DDBar/ScalarPotential/Componentwise.lean): induced atlas on `TopologicalSpace.Opens M`, with a proof of compatibility of `mddbar` under restriction to an open submanifold (private there; useful as a pattern).
- [`Comparator/Challenge.lean`](https://github.com/wxkj99/calabi-yau/blob/main/Comparator/Challenge.lean): smooth compact Monge–Ampère and Ricci-flat theorems.

The *actual* repository `lean-toolchain` and `lakefile.toml` pin **Lean 4.34.1** and Mathlib 4.34.1 (as inspected); the README mentioned 4.33.1, so use the files, not the README, for dependency resolution. The Tau Ceti repository was on a different 4.36.0 release candidate: **do not depend on both projects in the first milestone**.

## 2. Design decisions

1. A conical Kähler form is an **ordinary `KahlerForm` on the open complex manifold `X \ D`** with a separate condition near the divisor. Do not modify `KahlerForm`.
2. Define a smooth divisor analytically by **local adapted biholomorphic charts** cutting it out by `z₀ = 0`. Do not require line bundles, sheaf theory, currents, or Cartier-divisor infrastructure initially.
3. The conical comparison will use **quadratic form inequalities** rather than introduce an additional tensor carrier: `C⁻¹ q_model ≤ q_ω ≤ C q_model` for *all* tangent vectors in an adapted chart. This is equivalent to Hermitian Loewner inequalities and compatible with the existing `.IsNonneg`/`.coeffMatrix` machinery.
4. Distinguish **quasi-isometric cone control** from a **strong asymptotic cone condition**. The former does not by itself assert a unique metric tangent cone, polyhomogeneity, or weighted Hölder regularity.
5. General model weights are represented by `Fin n → Option ConeAngle`, where `none` means a nonsingular coordinate. This generalizes the smooth-divisor model to SNC models without changing `ModelConeForm`.
6. The local diagonal model exists for every `β > 0`, including angles above `2π`. **However**, chart invariance of its naive quasi-isometric condition under arbitrary adapted biholomorphisms holds only in the standard `0 < β ≤ 1` range. For `β > 1`, choose a compatible atlas or formulate stronger/intrinsic geometric data. Do not claim unrestricted invariance.
7. Don't require compactness. The complement and the local model are noncompact. Compactness enters only when applying Yau's theorem to smooth approximations on the original compact `X`.

## 3. Foundational objects and expected public signatures

The following are **Lean-oriented target signatures**; some helper declarations and coercion notation will require adjustment to the pinned Mathlib revision at implementation time. In particular, `metricInAdaptedChart`, a restriction/pullback adapter, is a NEW construction and is not claimed to exist upstream.

```lean
module

public import CalabiYau.Geometry.Kahler.Basic
public import CalabiYau.Geometry.Kahler.Ricci
public import CalabiYau.Geometry.Complex.Forms.OneOne

open scoped Manifold ContDiff
open Set

namespace ConicalKahler

abbrev E (n : ℕ) := EuclideanSpace ℂ (Fin n)

structure ConeAngle where
  beta : ℝ
  pos : 0 < beta

structure ConeWeights (n : ℕ) where
  angle : Fin n → Option ConeAngle
```

### 3.1 Adapted chart for a hypersurface

The chart must be a **biholomorphic** local coordinate map, not merely a homeomorphism. Since the selected `chartAt` of an arbitrary manifold is not automatically adapted to `D`, an arbitrary adapted chart and its inverse have to be carried explicitly. Mathlib uses `OpenPartialHomeomorph` for its manifold charts.

```lean
-- Proposed; all instances and `ContMDiffOn` spellings to be checked on the pin.
structure DivisorChart (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (E n) X]
    [IsManifold 𝓘(ℂ, E n) ω X] [NeZero n]
    (D : Set X) (p : X) where
  coord : OpenPartialHomeomorph X (E n)
  center_mem : p ∈ coord.source
  holomorphic :
    ContMDiffOn 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ coord coord.source
  inverse_holomorphic :
    ContMDiffOn 𝓘(ℂ, E n) 𝓘(ℂ, E n) ∞ coord.symm coord.target
  cutsOut : ∀ x ∈ coord.source, x ∈ D ↔ coord x 0 = 0

structure SmoothDivisor (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (E n) X]
    [IsManifold 𝓘(ℂ, E n) ω X] [NeZero n] where
  carrier : Set X
  isClosed : IsClosed carrier
  exists_chart : ∀ p ∈ carrier, Nonempty (DivisorChart n X carrier p)

-- Actual intended implementation, with type class parameters in scope:
def SmoothDivisor.complement (D : SmoothDivisor n X) :
    TopologicalSpace.Opens X :=
  ⟨D.carrierᶜ, D.isClosed.isOpen_compl⟩
```

**Important:** `D.carrier` is a *set*, not a `SmoothDivisor` constructor argument to `KahlerForm`. The type `D.complement` is the open subtype. A `KahlerForm n D.complement` has the correct manifold structure once Mathlib's induced open-atlas instances are instantiated. The `Componentwise.lean` module demonstrates this exact open-submanifold strategy.

A future bridge `smoothDivisor_of_regularHolomorphicSection` should construct these adapted charts from a holomorphic section of a line bundle transverse to the zero section, using the holomorphic implicit-function theorem. That theorem is *not* needed for the initial analytic divisor API.

### 3.2 Universal diagonal model (smooth and SNC)

For `θ : ConeWeights n`, the coordinate domain is

`{ z : ℂⁿ | ∀ j, θ.angle j = some β → z j ≠ 0 }`.

The real diagonal coefficients are

`w_j(z) = 1` if `θ.angle j = none`, and

`w_j(z) = β² |z_j|^(2β-2)` if `θ.angle j = some β`.

Use the existing convention `ω = i Σ g_{j k̄} dz_j ∧ dbar(z_k)`. In particular `g(v,v) = ω(v,Jv) = 2 Σ w_j(z) |v_j|²` in the model; define the model *half-metric quadratic form* `q_model = Σ w_j |v_j|²` to avoid a factor-of-two error.

```lean
-- Target helper definitions (with explicit types and proof obligations).
def modelDomain (θ : ConeWeights n) : TopologicalSpace.Opens (E n)

noncomputable def modelWeight (θ : ConeWeights n)
    (z : E n) (j : Fin n) : ℝ

noncomputable def modelConeQuadratic (θ : ConeWeights n)
    (z v : E n) : ℝ :=
  ∑ j : Fin n, modelWeight θ z j * Complex.normSq (v j)

noncomputable def modelConeMatrix (θ : ConeWeights n)
    (z : E n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun j => (modelWeight θ z j : ℂ))

-- MODEL FORM: a real Kähler form on the coordinate complement.
noncomputable def ModelConeForm (θ : ConeWeights n) :
    KahlerForm n (modelDomain θ)

-- Main correctness checks; precise pointwise statement:
theorem modelConeMatrix_eq_coeffMatrix (θ : ConeWeights n)
    (z : modelDomain θ) :
    ((ModelConeForm θ) z).coeffMatrix = modelConeMatrix θ z

theorem modelConeForm_ricciFlat (θ : ConeWeights n) :
    (ModelConeForm θ).IsRicciFlat
```

Implementation method: construct the model from the potential `Σ_j |z_j|^(2β_j)` for singular coordinates and `Σ_j |z_j|²` for nonsingular coordinates, *restricted to the complement*. First prove the one-variable Hessian identities away from zero, and then use `ddbar`/`complexHessian` and `KahlerForm` to show smoothness, closedness and positivity. The exponent `2β` on the potential yields the crucial coefficient `β² |z|^(2β−2)`.

The theorem `.IsRicciFlat` on the open complement is valid: `log det g` is a sum of multiples of `log |z_j|`, pluriharmonic away from the coordinate hyperplanes. It does **not** assert the Ricci current vanishes on the ambient space.

### 3.3 Pullback of a metric into an *arbitrary* adapted chart

This is the first missing bridge. `KahlerForm.metricInChart` is computed using the ambient **selected** `chartAt`; an arbitrary `DivisorChart` need not equal that chart. One **must not** write `ω.metricInChart χ ...` as if `χ` had the selected-chart type.

```lean
-- New geometric adapter, to be implemented using `FormField.chartRep`,
-- the complex Jacobian of the change of coordinates, and the induced
-- open-submanifold chart on `D.complement`.
noncomputable def metricInAdaptedChart
    (D : SmoothDivisor n X)
    (ω : KahlerForm n D.complement)
    {p : X} (χ : DivisorChart n X D.carrier p)
    (z : E n) (hz : z ∈ χ.coord.target)
    (haway : z 0 ≠ 0) : Matrix (Fin n) (Fin n) ℂ

noncomputable def metricQuadraticInAdaptedChart
    (D : SmoothDivisor n X)
    (ω : KahlerForm n D.complement)
    {p : X} (χ : DivisorChart n X D.carrier p)
    (z : E n) (hz : z ∈ χ.coord.target)
    (haway : z 0 ≠ 0) (v : E n) : ℝ
```

Define `metricQuadraticInAdaptedChart` from the pullback Hermitian matrix so that it is `g_χ(v,v)/2` in the normalisation of the source repository. Prove: positivity, coordinate change under a biholomorphism, and agreement with the original metric when the adapted chart equals the selected chart. The transformation law for Hermitian coefficient matrices already appears in `KahlerForm.metricInChart_transition_eq` (private) and `KahlerForm.chartChristoffel_transition` (public); follow their **actual matrix-index convention** instead of assuming a textbook `A*GA` orientation.

### 3.4 `IsConeAlong` and `ConeKahlerForm`

For a smooth divisor use the weight vector with `some β` in coordinate `0` and `none` elsewhere. Let `singleConeWeights β` denote this vector; its construction needs `[NeZero n]`.

```lean
-- The local comparison must use ONE C for all z and v on a suitably
-- small adapted chart. C may depend on the basepoint p.
noncomputable def singleConeWeights [NeZero n]
    (β : ConeAngle) : ConeWeights n

-- Main conical *quasi-isometry* condition, NOT a full asymptotic expansion.
def IsQuasiIsometricCone
    (D : SmoothDivisor n X) (β : ConeAngle)
    (ω : KahlerForm n D.complement) : Prop :=
  ∀ p : X, p ∈ D.carrier →
    ∃ (χ : DivisorChart n X D.carrier p) (C : ℝ),
      1 ≤ C ∧
      ∀ (z : E n) (hz : z ∈ χ.coord.target)
        (haway : z 0 ≠ 0) (v : E n),
        C⁻¹ * modelConeQuadratic (singleConeWeights β) z v ≤
          metricQuadraticInAdaptedChart D ω χ z hz haway v ∧
        metricQuadraticInAdaptedChart D ω χ z hz haway v ≤
          C * modelConeQuadratic (singleConeWeights β) z v

-- An alias is fine if the documentation is *explicit* about its meaning.
abbrev IsConeAlong (D : SmoothDivisor n X) (β : ConeAngle)
    (ω : KahlerForm n D.complement) : Prop :=
  IsQuasiIsometricCone D β ω

structure ConeKahlerForm (D : SmoothDivisor n X)
    (β : ConeAngle) where
  form : KahlerForm n D.complement
  cone_condition : IsConeAlong D β form

-- Optional, but natural: KE is an equation only on the smooth complement.
def ConeKahlerForm.IsKahlerEinstein
    (g : ConeKahlerForm D β) (lambda : ℝ) : Prop :=
  g.form.ricciForm = lambda • g.form.toFormField
```

**Important split by angle.** For `0 < β ≤ 1`, prove that if a metric satisfies this comparison in one adapted chart at `p`, then after restriction to a sufficiently small neighbourhood it satisfies an equivalent comparison in any other adapted chart at `p`. A divisor-preserving coordinate change has `w₀ = u(z) z₀` with `u(0,z') ≠ 0` and `w' = F(z)`. For `β > 1`, that unrestricted chart-change theorem is **false**, as explained below. Treat `IsConeAlong` at arbitrary positive angle as an **existence-of-compatible-chart** condition; if stronger global chart-invariance is desired, add a designated cone-admissible atlas and prove the bounds only for its compatible changes.

### 3.5 Stronger regularity is separate

Do not define `IsAsymptoticCone` as a synonym for `IsConeAlong`. A possible first stronger condition says in an adapted chart and appropriate weighted frame,

`‖G_model(z)⁻¹/² G_ω(z) G_model(z)⁻¹/² − I‖ → 0`

as `z` approaches the chart centre on `D`. This is a **strong** leading-model hypothesis (one will need a properly normalized chart and often a version varying smoothly along `D`). It is not the general definition of Donaldson's `C^{2,α,β}` regularity. Record separate future interfaces for `WeightedHolder`, `Conormal`, and `Polyhomogeneous` regularity instead of smuggling any of them into quasi-isometry.

## 4. SNC scalability: don't rewrite the model

Eventually take a finite index type `ι` of labelled irreducible components, each a `SmoothDivisor n X`, together with `angle : ι → ConeAngle`.

```lean
-- Proposed shape; may be introduced after the smooth-divisor milestone.
structure SNCChart (n : ℕ) (X : Type*) (ι : Type*)
    (components : ι → Set X) (p : X) where
  k : ℕ
  le_dim : k ≤ n
  active : Fin k ↪ ι
  coord : OpenPartialHomeomorph X (E n)
  center_mem : p ∈ coord.source
  holomorphic : ContMDiffOn 𝓘(ℂ,E n) 𝓘(ℂ,E n) ∞ coord coord.source
  inverse_holomorphic :
    ContMDiffOn 𝓘(ℂ,E n) 𝓘(ℂ,E n) ∞ coord.symm coord.target
  coordinate_zero_iff : ∀ x ∈ coord.source, ∀ j : Fin k,
    x ∈ components (active j) ↔
      coord x (Fin.castLE le_dim j) = 0
  other_components_absent : ∀ x ∈ coord.source, ∀ i : ι,
    i ∉ Set.range active → x ∉ components i
```

The omitted typeclass context matches `DivisorChart`, with `[Fintype ι]` useful for the first implementation. The local weight vector is `some (angle (active j))` for `j < k` and `none` otherwise. Then the *same* `ModelConeForm` gives the SNC local model. At angles above `2π`, use charts satisfying the necessary compatibility conditions (rather than asserting invariance under every adapted SNC chart):

`i Σ_{j<k} β_j² |z_j|^(2β_j−2) dz_j ∧ dbar(z_j) + i Σ_{j≥k} dz_j ∧ dbar(z_j)`.

This generalizes to e.g. labelled line arrangements **only where the divisor has SNC**; singular multiple intersections must wait for a further singular-divisor package (typically a log resolution) rather than being silently accepted as SNC.

## 4.1 Why `β > 1` needs a separate chart notion

Consider the product model in complex dimension two,

`g_β = β² |z|^(2β−2) |dz|² + |dw|²`.

The biholomorphic change `z' = z`, `w' = w + z` preserves `D = {z = 0}`. In the new coordinates, the vector satisfying `dz' ≠ 0`, `dw' = 0` has `dw = −dz'`, hence `g_β(v,v) ≈ |dz'|²` as `z' → 0`. But the *diagonal* model in the new coordinates assigns this vector the squared length `β² |z'|^(2β−2) |dz'|² → 0` when `β > 1`. Their ratio is unbounded. Thus the model is perfectly meaningful for any `β > 0`, but **arbitrary adapted-chart invariance is not true** when `β > 1`.

A later `ConeAdmissibleChartChange` should require locally bounded weighted Jacobian and inverse weighted Jacobian; a compatible atlas can then be part of the conical structure. The first version should not attempt to guess a general automatic atlas theorem beyond the positive-curvature angle range.

## 5. Proof obligations and minimal test suite

| Order | Module / theorem | Acceptance criterion |
|---|---|---|
| 1 | `Divisors/AdaptedChart` | chart definition, complement as `TopologicalSpace.Opens`, open-atlas instances working |
| 2 | `Cone/Weights` | model domain open, all weights strictly positive off the coordinate divisor |
| 3 | `Cone/Model` | form constructed with `KahlerForm`, computed Hermitian diagonal, closedness |
| 4 | `Cone/ModelRicci` | Ricci form vanishes on the punctured coordinate domain |
| 5 | `Cone/ChartMetric` | adapted-chart metric is genuinely pulled back from existing `KahlerForm`; positivity and chart-change formula |
| 6 | `Cone/Comparison` | `IsConeAlong` implemented; shrinking and chart invariance for `0 < β ≤ 1`; explicit counterexample for `β > 1` |
| 7 | `Cone/Kahler` | `ConeKahlerForm`, KE equation, transport/restriction lemmas |
| 8 | `Divisors/SNC` | smooth one-component case is a specialization of the general SNC model |

**Mathematical tests:**

- `n = 1`: model has `g_{z z̄} = β² |z|^(2β−2)` and is flat on `ℂ*`.
- `β = 1`: model reduces exactly to the Euclidean Kähler form.
- `n = 2`: verify `diag(β² |z₀|^(2β−2),1)` and the expected volume factor.
- `n = 2, k = 2`: verify `diag(β₀² |z₀|^(2β₀−2), β₁² |z₁|^(2β₁−2))`.
- For `0 < β ≤ 1`, a holomorphic adapted coordinate change `w₀=u(z) z₀`, `u(p)≠0`, preserves the quasi-isometric cone bounds after shrinking the chart.
- For `β > 1`, test the **failure** of unrestricted chart invariance under `(z,w) ↦ (z,w+z)`; the diagonal cone model degenerates normally while the changed tangential metric contributes a nondecaying `|dz|²` term.
- A proposed *cone-admissible* coordinate change for `β > 1` must pass a bounded weighted-Jacobian comparison test; this is a separate interface, not a theorem about all adapted charts.
- `z₀↦z₀^m` for `m>1` is **not** an adapted biholomorphic coordinate change at `z₀=0`; tests must not treat it as one.

## 6. Boundary of scope; what is not automatic

**Do not claim** the formalized smooth Yau theorem immediately proves a conical Monge–Ampère theorem. To pass from smooth `ω_ε` to `ω_β`, new estimates uniform in `ε` are required, as well as compactness and identification of the limit. The result may need Kołodziej-type estimates, conical Schauder theory and/or comparison arguments depending on the setup. Similarly, the **current identity**

`Ric(ω) = λ ω + 2π(1−β)[D]`

requires defining the relevant extensions/currents and proving a Poincaré–Lelong-type statement; it is not literally the same as the complement equation, and one must specify normalisations, regularity and equality of currents. Noncompact results require additional weighted estimates at infinity.

The first deliverable is intentionally a **geometric library**, not a claim of formalizing an existence theorem for conical KE metrics.

## 7. Agent implementation contract (first PR)

1. Pin a working upstream commit of `wxkj99/calabi-yau` and its toolchain. Start with **that dependency alone**; do not import Tau Ceti, migrate form carriers, or change upstream code unless a demonstrable blocker requires it.
2. Implement `DivisorChart`, `SmoothDivisor`, `SmoothDivisor.complement`, `ConeAngle`, `ConeWeights`, `modelDomain` and the numerical `modelWeight`, `modelConeQuadratic`, `modelConeMatrix`.
3. Prove `modelDomain` open and modelWeight positivity off the normal crossing set. Start the `ModelConeForm` construction; do not add it as an opaque constant or axiom to fake progress.
4. Compile each module with `lake build`; add GitHub Actions to run the build and audit proofs for `sorry` and nonstandard axioms.
5. Supply a README explaining the `ω=i Σ g dz∧dbar(z)` normalization and why the Riemannian quadratic is **twice** the Hermitian coefficient quadratic.
6. Make subsequent PRs separately for `ModelConeForm`, adapted-chart pullback, and `IsConeAlong`. Never make a statement about arbitrary adapted charts using `metricInChart` before proving the necessary pullback bridge.
7. Record any missing Mathlib or Calabi–Yau lemmas as explicit blockers with a minimal Lean reproducer; do not quietly weaken definitions to get a build to pass.

**Definition of done for v0.1:** The model cone form and smooth-divisor conical quasi-isometry are formally defined, proofs of the model identities and **chart independence for `0 < β ≤ 1`** compile without `sorry` or extra axioms, and the SNC generalization does not require changing the underlying model construction. Angles `β > 1` remain supported as *models* and as existential compatible-chart conditions, without a false unrestricted chart-independence theorem.
