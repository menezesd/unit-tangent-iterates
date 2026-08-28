import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierCompositionInvariant
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierRegularityClosure

/-! # Truthful hybrid error table on the tail-local physical base -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase

open ConfiguredRecursiveEdgeRecostMultiplierCompositionInvariant
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierRegularityClosure
  ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase
  ConfiguredRecursiveEdgeRecostedCompositionInvariant
  ConfiguredRecursiveEdgeRecostedGeometricState
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {K0 K1 K2 : ℝ}

abbrev E0 := ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
abbrev C0 := ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
abbrev C1 := ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
abbrev C2 := ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2

def baseError (R : RecostClosingOutput J O) (n : ℕ) : ℝ :=
  ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.error R n 1

def error (R : RecostClosingOutput J O) : ℕ → ℕ → ℝ :=
  hybridErrorTable (baseError R) R.data E0 C0 C1 C2

noncomputable def column (R : RecostClosingOutput J O) :=
  relabelColumn (e' := error R)
    (ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.column
      (K0 := K0) (K1 := K1) (K2 := K2) R)

@[simp] theorem error_one (R : RecostClosingOutput J O) (n : ℕ) :
    error R n 1 =
      ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.error R n 1 := by
  simp [error, baseError]

@[simp] theorem error_add_two (R : RecostClosingOutput J O) (n k : ℕ) :
    error R n (k + 2) =
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
        R.data E0 C0 C1 C2 (n + k + 1) := by
  simp [error]

noncomputable def invariant (R : RecostClosingOutput J O) :
    GeometricCompositionInvariant
      (column (K0 := K0) (K1 := K1) (K2 := K2) R) :=
  withHybridBase (baseError R) R.data E0 C0 C1 C2
    (ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.column
      (K0 := K0) (K1 := K1) (K2 := K2) R)
    (ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.invariant
      (K0 := K0) (K1 := K1) (K2 := K2) R)
    (fun n => by
      simpa [baseError] using
        (ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.invariant
          (K0 := K0) (K1 := K1) (K2 := K2) R).source_cost_le n)

noncomputable def state (R : RecostClosingOutput J O) :
    State
      (ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.Q R)
      (error R)
      (ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.P0 R)
      (ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.P1 R)
      (ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.G1 R)
      (ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.Cg R)
      (ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.C R)
      (ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.Qmax R)
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.pathKhat J.scalar)
      (ConfiguredCanonicalPairSource.commonC
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
      (ConfiguredCanonicalPairSource.commonDlt
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh where
  current := ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.current
    (K0 := K0) (K1 := K1) (K2 := K2) R
  depth := 0
  column := column (K0 := K0) (K1 := K1) (K2 := K2) R
  invariant := invariant (K0 := K0) (K1 := K1) (K2 := K2) R

@[simp] theorem state_displayed (R : RecostClosingOutput J O) (n : ℕ) :
    ((state (K0 := K0) (K1 := K1) (K2 := K2) R).stage n).displayed =
      ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar
        (R.totalShift + n) := rfl

theorem path_time_one (R : RecostClosingOutput J O) (n : ℕ) :
    ((state (K0 := K0) (K1 := K1) (K2 := K2) R).column.path n).T = 1 := by
  simpa [state, column, relabelColumn,
    ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.column,
    ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.row,
    ConfiguredRecursiveEdgePhysicalGeometricBase.base,
    ConfiguredRecursiveEdgePhysicalCompositionBase.compositionBaseCorrelated_path]
    using
      (ConfiguredGaugeFirstPhysicalSequence.richStage_spec
        J.scalar.pair.input J.scalar.model_data 1
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.rowC J.scalar)
        (R.totalShift + n + 1)).2.1

noncomputable def regularity (R : RecostClosingOutput J O) (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedScaledGeometricStep.Regularity
      (state (K0 := K0) (K1 := K1) (K2 := K2) R) n :=
  regularity_of_path_time_one
    (state (K0 := K0) (K1 := K1) (K2 := K2) R)
    (path_time_one (K0 := K0) (K1 := K1) (K2 := K2) R) n

noncomputable def pre (R : RecostClosingOutput J O) (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedPreCarrier.Core
      ((state (K0 := K0) (K1 := K1) (K2 := K2) R).stage n) :=
  ConfiguredRecursiveEdgeRecostedScaledGeometricStep.core
    (state (K0 := K0) (K1 := K1) (K2 := K2) R) n
    (regularity (K0 := K0) (K1 := K1) (K2 := K2) R n)

end ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase
