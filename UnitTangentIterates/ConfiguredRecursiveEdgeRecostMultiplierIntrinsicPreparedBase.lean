import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicPreparedReachableSystem
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness

/-! # Lightweight prepared base for the intrinsic multiplier recursion -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierIntrinsicPreparedBase

open ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
  ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicPreparedReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierRowBudget

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {K0 K1 K2 : ℝ}

/-- The exact depth-zero prepared state.  Its presented boundary and fresh
selection bounds are transported from the theorem-produced physical base. -/
noncomputable def base (R : RecostClosingOutput J O) :
    PreparedReachable R 0 where
  nodes := baseNode (K0 := K0) (K1 := K1) (K2 := K2) R
  layer := ConfiguredRecursiveEdgeRecostMultiplierBaseLayer.layer R
  presented := baseNodePresentedInput R
  selection := baseNodeSelection R

@[simp] theorem base_displayed (R : RecostClosingOutput J O) (n : ℕ) :
    ((base (K0 := K0) (K1 := K1) (K2 := K2) R).nodes n).stage.displayed =
      ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base R n := by
  exact baseNode_displayed R n

/-- Assemble a prepared provider once the theorem-produced reachable step is
available.  No base callback remains. -/
noncomputable def provider (R : RecostClosingOutput J O)
    (step : ∀ k (Z : PreparedReachable R k),
      Nonempty (PreparedStepData R Z)) : Provider R where
  base := base (K0 := K0) (K1 := K1) (K2 := K2) R
  base_displayed := base_displayed R
  step := step

end ConfiguredRecursiveEdgeRecostMultiplierIntrinsicPreparedBase
