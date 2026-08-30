import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedRecursiveChain
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalPackage
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalBounds
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainCompletion
import UnitTangentIterates.CoherentPhaseReachableMetricRangeAutomaticClosure
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierCoherentAutomaticFinalStatement

/-!
# Unconditional genuine main theorem from the prepared chosen chain

The recursively prepared chosen chain supplies the coherent grid, its
canonical completion, and the complete physical package needed by the
automatic smooth adapter.
-/

noncomputable section

open Filter Topology MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainUnconditionalMain

open ConfiguredRecursiveEdgeRecostFinitePreparedChosenChain
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  {H : Output R}

/-- The chosen chain supplies every sidecar required by automatic coherent
physical-row closure. -/
noncomputable def automaticInput (C : ChosenChain H) :
    CoherentPhaseReachableMetricRangeAutomaticClosure.Input H.toClosing
      (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalPackage.physicalBaseInput C)
      C.system
      (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainCompletion.X H C) where
  grid_eq := fun _ _ => rfl
  row_tendsto :=
    ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainCompletion.row_tendsto
      H C
  terminalPhase :=
    ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell.normalizedPhysicalFrontPhase
      C
  kinematics := by
    intro n k
    simpa only [
      CoherentPhaseReachableMetricRangeAutomaticClosure.physicalFront,
      ← ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell.physicalFront_eq_normalized_shift_P
        C n k] using
      (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell.physicalKinematics
        C n k)
  curvatureBound :=
    ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalBounds.curvatureBound
      (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalPackage.sidecars C).physical
  curvatureBound_nonneg :=
    ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalBounds.curvatureBound_nonneg
      (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalPackage.sidecars C).physical
  physicalFront_curvature := by
    intro n k u
    simpa only [
      CoherentPhaseReachableMetricRangeAutomaticClosure.physicalFront] using
      (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalBounds.physicalFront_curvature
        C
        (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalPackage.physicalBaseInput
          C).core.array
        (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalPackage.sidecars C).physical
        (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalPackage.physicalBaseInput
          C).cb_pos n k u)

/-- The completed chosen rows are the canonical representative rows consumed
by the coherent automatic smooth adapter. -/
noncomputable def adapterInput (C : ChosenChain H) :
    ConfiguredRecursiveEdgeRecostMultiplierCoherentAutomaticSmoothAdapter.Input
      H.toClosing where
  baseInput :=
    ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalPackage.physicalBaseInput C
  system := C.system
  rowLimit :=
    ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainCompletion.X H C
  automatic := automaticInput C
  rowLimit_eq_representative := by
    intro n
    have hrear : ∀ m,
        ConfiguredRecursiveEdgeRecostMultiplierPaperSmoothCapstone.physicalRear
            H.toClosing
            (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalPackage.physicalBaseInput
              C) m =
          C.system.P m := by
      intro m
      funext k
      cases k with
      | zero =>
          exact
            ((ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalPackage.physicalBaseInput
              C).core.array.base m).symm
      | succ k => rfl
    change
      ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainCompletion.X H C n =
        (ConfiguredRecursiveEdgeRecostMultiplierPaperSmoothCapstone.limitOutput
          H.toClosing
          (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalPackage.physicalBaseInput
            C)).X n
    exact
      ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainCompletion.limit_eq
        H C (fun m => by
          simpa only [hrear m] using
            (ConfiguredRecursiveEdgeRecostMultiplierPaperSmoothCapstone.physical_tendsto
              H.toClosing
              (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalPackage.physicalBaseInput
                C) m)) n

/-- Every prepared chosen chain yields the genuine noncircular paper-facing
main conclusion. -/
theorem mainConclusion_of_chosenChain (C : ChosenChain H) :
    PaperMainTheoremGenuineNoncircularStatement.MainConclusion :=
  ConfiguredRecursiveEdgeRecostMultiplierCoherentAutomaticSmoothAdapter.Input.mainConclusion
    H.toClosing (adapterInput C)

/-- The theorem-produced recursive chain discharges the chosen-chain input
unconditionally. -/
theorem mainConclusion (H : Output R) {K0 K1 K2 : ℝ} :
    PaperMainTheoremGenuineNoncircularStatement.MainConclusion :=
  mainConclusion_of_chosenChain
    (ConfiguredRecursiveEdgeRecostFinitePreparedRecursiveChain.chosenChain
      (K0 := K0) (K1 := K1) (K2 := K2) H)

end ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainUnconditionalMain
