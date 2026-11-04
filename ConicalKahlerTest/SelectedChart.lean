module

public import ConicalKahler

/-!
# Tests for the compatibility of adapted-chart metrics with `KahlerForm.metricInChart`
-/

namespace ConicalKahler.Test

open ConicalKahler
open scoped Manifold

/-- For the coordinate hyperplane, the adapted-chart metric of the model is the upstream local
metric, which is the model matrix. -/
example (β : ConeAngle) (p : E 2) (x : (coordHyperplane 2).complement) {z : E 2}
    (hz : z ∈ (coordHyperplaneChart 2 p).coord.target) (haway : z 0 ≠ 0)
    (hzx : z ∈ (extChartAt 𝓘(ℝ, E 2) x).target) :
    metricInAdaptedChart (coordHyperplane 2) (modelOnHyperplane β) (coordHyperplaneChart 2 p) z
        hz haway = modelConeMatrix (singleConeWeights β) z := by
  rw [metricInAdaptedChart_coordHyperplane_eq_metricInChart _ p x hz haway, modelOnHyperplane,
    modelConeFormOn_metricInChart _ _ _ x hzx]

/-- In the shear chart, the upstream metric is related to the shear-chart metric by the
transformation law with `A = D(shear)`. -/
example (β : ConeAngle) (p : E 2) (x : (coordHyperplane 2).complement) {z : E 2}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E 2) x).target) :
    (modelOnHyperplane β).metricInChart x z =
      (EuclideanSpace.clmMatrix (fderiv ℂ ((shearChart p).coord ∘
          (chartAt (E 2) (x : E 2)).symm) z)).transpose *
        metricInAdaptedChart (coordHyperplane 2) (modelOnHyperplane β) (shearChart p)
          ((shearChart p).coord ((chartAt (E 2) (x : E 2)).symm z))
          ((shearChart p).coord.map_source (Set.mem_univ _))
          ((shearChart p).coord_chartAt_symm_ne_zero x hz (Set.mem_univ _)) *
        (EuclideanSpace.clmMatrix (fderiv ℂ ((shearChart p).coord ∘
          (chartAt (E 2) (x : E 2)).symm) z)).map star :=
  metricInChart_eq_metricInAdaptedChart_change _ _ x hz (Set.mem_univ _)

end ConicalKahler.Test
