import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell
import UnitTangentIterates.RichFamilyPhysicalMarkingIntegration

/-!
# Physical curvature bounds for a chosen prepared chain

The physical front of cell `(n,k)` is a phase shift of the analytic front,
and the analytic front is a phase shift of the positive-depth physical rear
at the exact successor index `(n + 1, k + 1)`.  Consequently the retained
physical row bounds give the rowwise front-curvature ceiling required by the
automatic coherent-grid closure.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalBounds

open ConfiguredRecursiveEdgeRecostFinitePreparedChosenChain
  ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
  RichFamilyPhysicalMarkingIntegration

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  {H : Output R}

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg Crow : ℕ → ℝ} {c dlt cb db : ℝ}
  {B0 : ℕ → Data}

/-- The physical-front curvature ceiling for row `n` is the retained
acceleration ceiling of the exact successor row, divided by the common speed
floor squared. -/
def curvatureBound
    {B P : ℕ → ℕ → Data} {cb db : ℝ}
    (bounds : PhysicalRowBounds B P cb db) (n : ℕ) : ℝ :=
  bounds.Ab (n + 1) / cb ^ 2

/-- The successor-row curvature ceiling is nonnegative. -/
theorem curvatureBound_nonneg
    {B P : ℕ → ℕ → Data} {cb db : ℝ}
    (bounds : PhysicalRowBounds B P cb db) (n : ℕ) :
    0 ≤ curvatureBound bounds n :=
  div_nonneg (bounds.Ab_nonneg (n + 1)) (sq_nonneg cb)

/-- The analytic front of cell `(n,k)` inherits the physical row bound at
the exact positive-depth successor index `(n + 1, k + 1)`. -/
theorem analyticFront_curvature
    (C : ChosenChain H)
    (A : Array Q (ChosenChain.system H C).P e P0 P1 khat G1 Cg Crow c dlt)
    (bounds : PhysicalRowBounds (A.physicalRear B0)
      (ChosenChain.system H C).P cb db)
    (hcb : 0 < cb) (n k : ℕ) (u : ℝ) :
    |CurvatureFromMarkedDistance.dataCurv
      (analyticGeometry C n k).frontData u| ≤
      curvatureBound bounds n := by
  rw [analyticFront_eq_normalized_shift_P C n k]
  simpa only [MarkedShift.dataCurv_shiftData, Array.physicalRear_succ,
    curvatureBound] using
    (PhysicalRowBounds.abs_dataCurv_le bounds hcb
      (n + 1) (k + 1)
      (u + (normalizedTerminalPhase C n k : ℝ)))

/-- The actual chosen physical front has the same rowwise curvature ceiling;
its kinematically forced phase only translates the parameter. -/
theorem chosenPhysicalFront_curvature
    (C : ChosenChain H)
    (A : Array Q (ChosenChain.system H C).P e P0 P1 khat G1 Cg Crow c dlt)
    (bounds : PhysicalRowBounds (A.physicalRear B0)
      (ChosenChain.system H C).P cb db)
    (hcb : 0 < cb) (n k : ℕ) (u : ℝ) :
    |CurvatureFromMarkedDistance.dataCurv (physicalFront C n k) u| ≤
      curvatureBound bounds n := by
  change |CurvatureFromMarkedDistance.dataCurv
    (MarkedShift.shiftData (physicalFrontPhase C n k)
      (analyticGeometry C n k).frontData) u| ≤ curvatureBound bounds n
  rw [MarkedShift.dataCurv_shiftData]
  exact analyticFront_curvature C A bounds hcb n k
    (u + physicalFrontPhase C n k)

/-- Exact normalized-front form consumed by
`CoherentPhaseReachableMetricRangeAutomaticClosure.Input` when its terminal
phase is the chosen chain's `normalizedPhysicalFrontPhase`. -/
theorem physicalFront_curvature
    (C : ChosenChain H)
    (A : Array Q (ChosenChain.system H C).P e P0 P1 khat G1 Cg Crow c dlt)
    (bounds : PhysicalRowBounds (A.physicalRear B0)
      (ChosenChain.system H C).P cb db)
    (hcb : 0 < cb) (n k : ℕ) (u : ℝ) :
    |CurvatureFromMarkedDistance.dataCurv
      (MarkedShift.shiftData (normalizedPhysicalFrontPhase C n k : ℝ)
        ((ChosenChain.system H C).P (n + 1) (k + 1))) u| ≤
      curvatureBound bounds n := by
  rw [← physicalFront_eq_normalized_shift_P C n k]
  exact chosenPhysicalFront_curvature C A bounds hcb n k u

end ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalBounds
