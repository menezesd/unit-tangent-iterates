import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackStages

/-!
# Raw chosen-path metric leg

Displayed convergence uses the theorem-produced raw chosen path.  Canonical
recosting is reserved for the recursive source carrier and is not required to
satisfy the raw variable-speed geometry bounds.
-/

noncomputable section

open Function Set MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed

namespace FiniteSmoothRearFamilyMarkingAwareActualPullbackRawMetric

open FiniteSmoothRearFamilyMarkingAwareActualPullbackStages

variable {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
  {S : Stage P0 kh khat Qmax j} (G : GeometricInput S)

structure RawMetricInput where
  pathP0 : ℝ
  pathP1 : ℝ
  pathKhat : ℝ
  pathG1 : ℝ
  pathCg : ℝ
  start_curve_deriv : ∀ u, HasDerivAt S.displayed.1 (S.displayed.2.1 u) u
  start_vel_deriv : ∀ u, HasDerivAt S.displayed.2.1 (S.displayed.2.2 u) u
  geometry : IsVariableSpeedNormalPath
    pathP0 pathP1 pathKhat pathG1 pathCg G.rawPath
  costBound : ℝ
  cost_le : G.rawPath.cost ≤ costBound

namespace RawMetricInput

def pathFactor (M : RawMetricInput G) : ℝ :=
  c2ConstVar M.pathP0 M.pathP1 M.pathKhat M.pathG1 M.pathCg

def edgeBudget (M : RawMetricInput G) : ℝ :=
  M.pathFactor * M.costBound + G.endpointCap

theorem dist_start_rear_le
    (M : RawMetricInput G) :
    dist S.displayed G.output.jets.rear ≤
      M.pathFactor * G.rawPath.cost := by
  exact dist_le_cost_variableSpeed G.rawPath M.start_curve_deriv
    G.output.stage.rear_curve_deriv M.start_vel_deriv
    G.output.stage.rear_vel_deriv M.geometry

theorem dist_displayed_base_le_edgeBudget
    (M : RawMetricInput G) :
    dist S.displayed G.base ≤ M.edgeBudget := by
  have hK : 0 ≤ M.pathFactor := c2ConstVar_nonneg _ _ _ _ _
  calc
    dist S.displayed G.base ≤
        dist S.displayed G.output.jets.rear +
          dist G.output.jets.rear G.base := dist_triangle _ _ _
    _ ≤ M.pathFactor * G.rawPath.cost + G.endpointCap :=
      add_le_add M.dist_start_rear_le G.rear_dist_base_le_endpointCap
    _ ≤ M.pathFactor * M.costBound + G.endpointCap :=
      add_le_add (mul_le_mul_of_nonneg_left M.cost_le hK) le_rfl
    _ = M.edgeBudget := rfl

theorem edgeBudget_nonnegative
    (M : RawMetricInput G) (hcost : 0 ≤ M.costBound) :
    0 ≤ M.edgeBudget :=
  add_nonneg (mul_nonneg (c2ConstVar_nonneg _ _ _ _ _) hcost)
    G.endpointCap_nonnegative

end RawMetricInput

end FiniteSmoothRearFamilyMarkingAwareActualPullbackRawMetric

