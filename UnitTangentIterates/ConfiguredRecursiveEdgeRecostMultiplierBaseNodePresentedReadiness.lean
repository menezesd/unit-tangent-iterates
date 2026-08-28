import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierBaseNodePre
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalFlowCeilings
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds

/-! # Presented and selection provenance for canonical base nodes -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness

open ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
  ConfiguredRecursiveEdgeRecostMultiplierBaseNodePre
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgePhysicalBaseFinalTailState
  ConfiguredRecursiveEdgeRecostMultiplierNativeCore
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)
  {K0 K1 K2 : ℝ}

/-- Full theorem-produced presented boundary on the canonical base node. -/
noncomputable def baseNodePresentedInput (n : ℕ) :
    PresentedInput
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage := by
  let G := baseNodeGeometricInput
    (K0 := K0) (K1 := K1) (K2 := K2) R n
  exact
    { base := G.base
      bound := G.bound
      terminal := G.terminal
      path_time_one := by
        simpa [baseNode, baseStage] using
          (raw_path_time_one (J := J) (K0 := K0) (K1 := K1) (K2 := K2)
            ((rowOutput R n).N)) }

/-- The native base core is definitionally reconstructed from retained
presented provenance. -/
noncomputable def baseNodePre (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedPreCarrier.Core
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage :=
  (baseNodePresentedInput (K0 := K0) (K1 := K1) (K2 := K2) R n).core

/-- Fresh exact successor-selection derivative bounds tied to the physical
base source itself. -/
noncomputable def baseNodeSelection (n : ℕ) :
    SelectionBounds
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source := by
  let q := (rowOutput R n).N
  let X := ConfiguredRecursiveEdgePhysicalFlowCeilings.compositionRecursiveAnalyticSuccessor
    J (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.rowC J.scalar)
      (MA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
      (NA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) q
  have hsource :
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source =
        ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.source
          J.scalar (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.rowC J.scalar)
          (MA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
          (NA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) q := by
    change
      (ConfiguredRecursiveEdgePhysicalCompositionBase.compositionBaseCorrelated
        J (K0 := K0) (K1 := K1) (K2 := K2)).source q = _
    rfl
  rw [hsource]
  simpa [X] using X.sidecars.selection

end ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness
