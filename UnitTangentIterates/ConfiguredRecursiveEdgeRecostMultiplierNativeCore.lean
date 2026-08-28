import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNativeCoreBase
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly

/-!
# Native pre-carrier cores from exact geometric inputs

This is the profile-index-independent end of native unary reconstruction.
Once a `GeometricInput` has been rebuilt directly on the target stage, its
chosen path already has joint `C²` regularity by exact-source gauge-flow
regularity.  Thus only normalization of the raw time interval remains.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierNativeCore

open ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  {k : ℕ} {N : ℕ → Node} {L : Layer R k N}

/-- Successor specialization: once its presented terminal boundary is
constructed natively, the intrinsic step receives a definitionally typed
pre-carrier with no global-stage cast. -/
noncomputable def coreOfInputDataNext
    (I : InputData R L) (n : ℕ)
    (B : PresentedInput ((I.step).next n).stage) :
    Core ((I.step).next n).stage :=
  B.core

end ConfiguredRecursiveEdgeRecostMultiplierNativeCore
