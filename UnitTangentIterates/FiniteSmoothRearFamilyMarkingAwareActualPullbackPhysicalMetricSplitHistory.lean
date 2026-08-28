import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
import UnitTangentIterates.ConfiguredRecursiveEdgeActualPhysicalSplitHistory

/-!
# Physical metric input from a split finite history

This adapter keeps the stage-specific geometric and regularity witnesses
explicit and discharges precisely the stable-component field from the actual
finite split history.
-/

noncomputable section

open MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareActualPullbackStages

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  ConfiguredRecursiveEdgeActualPhysicalSplitHistory
  NormalPathC2IncrementVariableSpeed

namespace PhysicalMetricInput

/-- Assemble the metric package for an actual chosen path from its retained
geometry and its finite fully-physical ancestry. -/
def ofSplitHistory
    {P0 kh khat Qmax : ℕ -> ℝ} {j : ℕ}
    {S : Stage P0 kh khat Qmax j} {G : GeometricInput S}
    {E C0 C1 C2 d : ℝ}
    {V : ℕ -> AnchoredJacobiStableTransition.Components}
    {major : ℕ -> ℝ} {depth : ℕ}
    (pathP0 pathP1 pathKhat pathG1 pathCg : ℝ)
    (c2 : C2NormalPathData G.rawPath)
    (eta_continuous : Continuous (Function.uncurry G.rawPath.eta))
    (eta1_continuous : Continuous (Function.uncurry c2.eta1))
    (eta2_continuous : Continuous (Function.uncurry c2.eta2))
    (start_curve_deriv : ∀ u,
      HasDerivAt (⇑S.displayed.1) (S.displayed.2.1 u) u)
    (start_vel_deriv : ∀ u,
      HasDerivAt (⇑S.displayed.2.1) (S.displayed.2.2 u) u)
    (geometry : IsVariableSpeedNormalPath pathP0 pathP1 pathKhat pathG1 pathCg
      (G.recost c2 eta_continuous eta1_continuous eta2_continuous))
    (time_one : G.rawPath.T = 1)
    (H : SplitHistory G.rawPath V major depth E C0 C1 C2 d) :
    PhysicalMetricInput G E C0 C1 C2 d where
  pathP0 := pathP0
  pathP1 := pathP1
  pathKhat := pathKhat
  pathG1 := pathG1
  pathCg := pathCg
  c2 := c2
  eta_continuous := eta_continuous
  eta1_continuous := eta1_continuous
  eta2_continuous := eta2_continuous
  start_curve_deriv := start_curve_deriv
  start_vel_deriv := start_vel_deriv
  geometry := geometry
  time_one := time_one
  d_nonnegative := H.d_nonnegative
  stable := H.toStable time_one c2 eta_continuous eta1_continuous
    eta2_continuous

end PhysicalMetricInput

end FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
