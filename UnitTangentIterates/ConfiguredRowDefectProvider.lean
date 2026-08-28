import UnitTangentIterates.ConfiguredApproximateDefectPathRowwiseCost
import UnitTangentIterates.TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-!
# Configured recursive row-defect provider

This is the scalar half of the configured variable-terminal recursion.  The
error at row `n`, depth `k` is the honest transported interpolation cost
`K^k * rowDefect (n+k)`.  Its rowwise summability follows from the explicit
configured cost comparison; no endpoint-identification residual is involved.
-/

noncomputable section

open PathMetric

namespace ConfiguredRowDefectProvider

open ConfiguredApproximateDefectPathRowwise
  ConfiguredApproximateDefectPathRowwiseCost
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- Honest two-index configured interpolation error. -/
def error (D : ConstructedConfiguredSequenceWeighted.Data) (K : ℝ)
    (n k : ℕ) : ℝ :=
  WeightedRecursiveDefect.pullbackError K (rowDefect D) n k

theorem rowDefect_nonneg
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    0 ≤ rowDefect D n := by
  unfold rowDefect rowDsup
  exact InterpolationPathDist.interpPathCost_nonneg D.kstar_nonneg D.kd_nonneg
    (CurvatureStabilityL1.l1Modulus_nonneg _ _ _)
    (D.model.separation_pos n).le (edgeEps_nonneg D n)

/-- The actual configured interpolation costs form a recursive row-defect
provider whenever the transport factor satisfies the honest exponential
threshold. -/
def provider
    (D : ConstructedConfiguredSequenceWeighted.Data) {K : ℝ}
    (hK : 1 ≤ K)
    (hthreshold : K * Real.exp (-((D.model.beta / 4) * D.deltaStep)) < 1) :
    RowDefectProvider (error D K) where
  nonnegative := fun n k =>
    WeightedRecursiveDefect.pullbackError_nonneg
      (zero_le_one.trans hK) (rowDefect_nonneg D) n k
  summable := WeightedRecursiveDefect.summable_pullbackError_of_summable_weighted
    hK (rowDefect_nonneg D)
      (summable_weighted_rowDefect D (zero_le_one.trans hK) hthreshold)

end ConfiguredRowDefectProvider
