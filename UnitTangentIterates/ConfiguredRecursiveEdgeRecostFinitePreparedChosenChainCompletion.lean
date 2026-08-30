import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedChosenChain
import UnitTangentIterates.CoherentPhaseReachableMetricRangeCompletion

open Filter Topology

namespace ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainCompletion

open CoherentPhaseReachableMetricRangeCompletion
  ConfiguredRecursiveEdgeRecostFinitePreparedChosenChain
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing

noncomputable section

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  (H : Output R)

/-- The canonical metric completion of the actual prepared chosen chain. -/
noncomputable def completion (C : ChosenChain H) :
    GridCompletion C.system :=
  CoherentPhaseReachableMetricRangeCompletion.completion
    C.system H.error_summable

/-- The canonical row limit selected by completeness. -/
noncomputable def X (C : ChosenChain H) : ℕ → MarkedSpace.Data :=
  (completion H C).X

theorem row_tendsto (C : ChosenChain H) (n : ℕ) :
    Tendsto (C.system.P n) atTop (nhds (X H C n)) :=
  (completion H C).row_tendsto n

theorem row_tail_tendsto (C : ChosenChain H) (n : ℕ) :
    Tendsto (fun k ↦ C.system.P n (k + 1)) atTop
      (nhds (X H C n)) :=
  (completion H C).row_tail_tendsto n

theorem limit_eq (C : ChosenChain H) {Y : ℕ → MarkedSpace.Data}
    (hY : ∀ n, Tendsto (C.system.P n) atTop (nhds (Y n))) (n : ℕ) :
    X H C n = Y n :=
  GridCompletion.limit_eq (completion H C) hY n

end


end ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainCompletion
