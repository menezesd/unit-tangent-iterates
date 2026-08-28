import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedAnalyticCarrier
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource

/-!
# Recursive recost carrier without a recost geometry hypothesis

The split history controls canonical recost cost.  Displayed metric estimates
belong to the separate raw chosen-path metric leg.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedCarrierRow

open ConfiguredRecursiveEdgeActualPhysicalSplitHistory
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages

variable {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
  {S : Stage P0 kh khat Qmax j}

structure CarrierRow (S : Stage P0 kh khat Qmax j)
    (E C0 C1 C2 d : ℝ) where
  geometric : GeometricInput S
  eta_continuous : Continuous (uncurry geometric.output.chosen.Delta.eta)
  eta1_continuous : Continuous (uncurry geometric.output.chosen.c2.eta1)
  eta2_continuous : Continuous (uncurry geometric.output.chosen.c2.eta2)
  time_one : geometric.output.chosen.Delta.T = 1
  V : ℕ → AnchoredJacobiStableTransition.Components
  major : ℕ → ℝ
  depth : ℕ
  splitHistory : SplitHistory geometric.rawPath V major depth E C0 C1 C2 d

namespace CarrierRow

variable {E C0 C1 C2 d : ℝ} (R : CarrierRow S E C0 C1 C2 d)

def path : NormalPath S.displayed R.geometric.output.jets.rear :=
  CanonicalNormalPathRecost.recost R.geometric.output.chosen.Delta
    R.geometric.output.chosen.c2
    R.eta_continuous R.eta1_continuous R.eta2_continuous

def chosenSplitHistory : SplitHistory
    R.geometric.output.chosen.Delta R.V R.major R.depth E C0 C1 C2 d := by
  let h : R.geometric.rawPath = R.geometric.output.chosen.Delta :=
    R.geometric.output.stage_eq
  exact h ▸ R.splitHistory

def stable :
    FiniteColumnStablePhysicalComponentCompactness.StablePhysicalComponents
      R.path 1
      (ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
        E C0 C1 C2) d :=
  R.chosenSplitHistory.toStable R.time_one R.geometric.output.chosen.c2 R.eta_continuous
    R.eta1_continuous R.eta2_continuous

theorem cost_le :
    R.path.cost ≤
      4 * ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
        E C0 C1 C2 * d :=
  FiniteSmoothRearFamilyMarkingAwareNonaffineFiniteStability.recost_cost_le_four_configuredTarget_mul
    R.geometric.output.chosen.c2 R.eta_continuous R.eta1_continuous
      R.eta2_continuous R.stable

theorem terminal_range :
    range (R.path.X R.path.T) = range R.geometric.output.jets.rear.1 := by
  apply congrArg range
  funext u
  exact R.path.finish u

end CarrierRow

end ConfiguredRecursiveEdgeRecostedCarrierRow
