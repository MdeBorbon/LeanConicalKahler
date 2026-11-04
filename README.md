# ConicalKahlerLean

A Lean 4 formalisation of Kähler metrics with cone singularities along complex divisors,
built on top of the formal proof of the Calabi conjecture
[`wxkj99/calabi-yau`](https://github.com/wxkj99/calabi-yau).

The design document is [`CONICAL_KAHLER_LEAN_API.md`](CONICAL_KAHLER_LEAN_API.md); progress,
open proof obligations and blockers are tracked in [`STATUS.md`](STATUS.md).

## Main result so far

For every `β > 0`, the standard cone metric with cone angle `2πβ` along `{z₀ = 0}`

```
ω_β = i β² |z₀|^(2β-2) dz₀ ∧ dz̄₀ + i ∑_{j ≥ 1} dz_j ∧ dz̄_j
```

is an (upstream) `KahlerForm` on the open complex manifold `{z₀ ≠ 0} ⊆ ℂⁿ`, and it is Ricci-flat
there:

```lean
ConicalKahler.standardConeForm (β : ConeAngle) :
  KahlerForm n (modelDomain (singleConeWeights β))
ConicalKahler.standardConeForm_coeffMatrix   -- g_{jk̄} = diag(β² |z₀|^(2β-2), 1, …, 1)
ConicalKahler.standardConeForm_ricciFlat     -- (standardConeForm β).IsRicciFlat
```

More generally `ModelConeForm θ` is the normal-crossings model with an independent cone angle
(or none) in each coordinate direction. Coordinates are 0-indexed (`Fin n`), so the singular
coordinate written `z₁` in the usual notation is `z 0` in Lean.

Along an arbitrary smooth divisor `D ⊆ X` (`SmoothDivisor`, given by adapted holomorphic charts),
a Kähler form on `X \ D` has *quasi-isometric* cone angle `2πβ` (`IsConeAlong D β ω₀`) if, in
some adapted chart near each point of `D`, its Hermitian quadratic form is uniformly equivalent to
that of `ω_β`. The form is pulled back to an arbitrary adapted chart by `metricInAdaptedChart`.

* For `0 < β ≤ 1` the condition does not depend on the adapted chart
  (`IsQuasiIsometricCone.forall_chart_of_le_one`).
* For `β > 1` it does: under the shear `(z₀, z₁) ↦ (z₀, z₁ + z₀)` the standard cone metric fails
  the comparison on every neighbourhood (`not_coneComparableIn_shear`). For `β > 1`,
  `IsConeAlong` is therefore an existence-of-compatible-chart condition.
* `IsConeAlong` asserts quasi-isometry only: no tangent-cone uniqueness, asymptotic expansion
  or weighted regularity.

## Normalisation conventions

We use the upstream conventions without change.

* A real `(1,1)`-form is written `ω = i ∑_{j,k} g_{jk̄} dz_j ∧ dz̄_k`, and
  `ContinuousAlternatingMap.coeffMatrix` returns the Hermitian matrix `(g_{jk̄})`.
  For example the Euclidean form `i ∑ dz_j ∧ dz̄_j = 2 ∑ dx_j ∧ dy_j` has coefficient matrix `1`
  (`complexHessian_normSq`).
* The Riemannian metric is `g(u, v) = ω(u, Jv)` with `J v = i v`. Hence
  (`IsOneOne.apply_I_smul`)

  ```
  g(v, v) = ω(v, Jv) = 2 ∑_{j,k} g_{jk̄} v_j v̄_k .
  ```

  The **Riemannian quadratic form is twice the Hermitian coefficient quadratic form.** The model
  quantity `modelConeQuadratic θ z v = ∑_j w_j(z) |v_j|²` is the *Hermitian* one, and
  `modelConeForm_apply_I_smul` states `ω_θ(v, Jv) = 2 · modelConeQuadratic θ z v`. All cone
  comparison conditions are formulated with the Hermitian quadratic forms on both sides, so the
  factor `2` cancels; mixing a Hermitian and a Riemannian quantity would be a factor-two error.
* `i∂∂̄|z|^(2β) = β² |z|^(2β-2) i dz ∧ dz̄` on `ℂ*` (`radialCoeff_rpow`). This is why the potential
  `|z₀|^(2β) + ∑_{j≥1} |z_j|²` produces exactly `ω_β`.

## Layout

| File | Content |
|---|---|
| `ConicalKahler/Analysis/DDBarLocal.lean` | germ locality and additivity of `ddbar` |
| `ConicalKahler/Analysis/RadialHessian.lean` | complex Hessian of `∑_j g_j(|z_j|²)` |
| `ConicalKahler/Manifold/OpenSubset.lean` | charts and `i∂∂̄` on open subsets of `ℂⁿ` |
| `ConicalKahler/Cone/Weights.lean` | `ConeAngle`, `ConeWeights`, model domain, weights, quadratic form, matrix |
| `ConicalKahler/Cone/Model.lean` | `ModelConeForm` and its coefficient matrix |
| `ConicalKahler/Cone/ModelRicci.lean` | Ricci-flatness of the model |
| `ConicalKahler/Cone/Standard.lean` | the standard cone metric `ω_β` along `{z₀ = 0}` |
| `ConicalKahler/Divisors/AdaptedChart.lean` | `DivisorChart`, `SmoothDivisor`, complement, coordinate hyperplane |
| `ConicalKahler/Cone/ChartMetric.lean` | metric in an arbitrary adapted chart; positivity; chart-change law |
| `ConicalKahler/Cone/Comparison.lean` | `IsQuasiIsometricCone` / `IsConeAlong`; shrinking; the model is conical |
| `ConicalKahler/Analysis/HyperplaneMaps.lean` | estimates for holomorphic maps preserving `{z₀ = 0}` |
| `ConicalKahler/Cone/ChartInvariance.lean` | chart invariance for `0 < β ≤ 1` |
| `ConicalKahler/Cone/AngleRestriction.lean` | the shear test: failure for `β > 1`, success for `β ≤ 1` |
| `ConicalKahler/Cone/Kahler.lean` | `ConeKahlerForm`, Kähler–Einstein equation on `X \ D` |
| `ConicalKahlerTest/Model.lean` | the specification's concrete tests (`n = 1`, `β = 1`, `n = 2`, SNC) |
| `ConicalKahlerTest/Divisor.lean` | divisor and cone-condition tests; `z₀ ↦ z₀²` is not an adapted chart |
| `scripts/AxiomAudit.lean` | fails unless every declaration uses only the standard axioms |

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain (Lean `v4.34.1`), Mathlib
(`v4.34.1`) and the upstream commit
(`91b1ddf000c7028bc42ae6102eba0e2042eb37ff`) are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`. These are the same Lean and Mathlib versions as the upstream project.

```sh
lake exe cache get        # Mathlib build cache
lake build                # library and tests
lake env lean scripts/AxiomAudit.lean
```

CI (`.github/workflows/ci.yml`) runs all three steps on every push and also rejects `sorry`,
`admit`, `axiom` and `opaque` in the sources.
