import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalBaseFinalTailState
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalGeometricBase
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierGlobalBaseState
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedGeometricState

/-!
# Normalized state on the global physical base column

The recursive geometric construction uses the global column stage directly.
The older base-state theorem was stated on a separately rebuilt unary stage.
This module isolates that representation boundary once, opaquely, instead of
asking every successor field to reduce the full dependent source record.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePhysicalGlobalBaseNormalizedState

open ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgePhysicalBaseFinalTailState
  ConfiguredRecursiveEdgePhysicalGeometricBase
  ConfiguredRecursiveEdgePhysicalCompositionBase
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierGlobalBaseState
  ConfiguredRecursiveEdgeRecostedGeometricState
  ConfiguredRecursiveEdgeRecostedNormalizedReachableState
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveSourceP0FixedDistortion

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    choice.MA0 choice.NA0}
  {O : GaugeOutput J} {K0 K1 K2 : ℝ}

/-- The theorem-produced physical base, retained as a genuine global
geometric state rather than reindexed through a unary wrapper. -/
noncomputable def globalState :
    State (Q J.scalar) (compositionError J)
      (edgeSourceP0 (D J.scalar)) (edgeP1 (D J.scalar) choice.MA0)
      (edgeG1 (D J.scalar) choice.MA0 choice.NA0)
      (edgeCgWithKhat (D J.scalar) (pathKhat J.scalar)
        choice.MA0 choice.NA0)
      (rowC J.scalar) (Qmax J.scalar)
      (pathKhat J.scalar)
      (ConfiguredCanonicalPairSource.commonC (D J.scalar))
      (ConfiguredCanonicalPairSource.commonDlt (D J.scalar)) sourceKh where
  current := baseCurrent J (K0 := K0) (K1 := K1) (K2 := K2)
  depth := 0
  column := base J (K0 := K0) (K1 := K1) (K2 := K2)
  invariant := invariant J (K0 := K0) (K1 := K1) (K2 := K2)

/-- The global stage is the canonical unary stage before the legacy diagonal
profile repackaging. -/
theorem globalStage_eq_unaryStage (q : ℕ) :
    (globalState (J := J) (K0 := K0) (K1 := K1) (K2 := K2)).stage q =
      ConfiguredRecursiveEdgeRecostedRawDiagonalBase.unaryStage
        (K0 := K0) (K1 := K1) (K2 := K2) J q := by
  rfl

/-- The source carrier itself is unchanged by the legacy unary profile
repackaging. -/
theorem globalSource_eq_rawSource (q : ℕ) :
    ((globalState (J := J) (K0 := K0) (K1 := K1) (K2 := K2)).stage q).source =
      (ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage
        (K0 := K0) (K1 := K1) (K2 := K2) J q).asUnary.source := by
  rfl

/-- The geometric path is literally the same path in both presentations. -/
theorem globalGamma_eq_rawGamma (q : ℕ) :
    ((globalState (J := J) (K0 := K0) (K1 := K1) (K2 := K2)).stage q).Gamma =
      (ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage
        (K0 := K0) (K1 := K1) (K2 := K2) J q).asUnary.Gamma := by
  rfl

/-- Relabeling the global base source error does not change the source carrier
on a public tail row. -/
theorem globalBaseSource_eq_rawSource
    (R : RecostClosingOutput J O) (q : ℕ) :
    ((ConfiguredRecursiveEdgeRecostMultiplierGlobalBaseState.state
      (K0 := K0) (K1 := K1) (K2 := K2) R).stage
        q).source =
      (ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage
        (K0 := K0) (K1 := K1) (K2 := K2) J
        q).asUnary.source := by
  rfl

/-- Relabeling the global base source error does not change its path. -/
theorem globalBaseGamma_eq_rawGamma
    (R : RecostClosingOutput J O) (q : ℕ) :
    ((ConfiguredRecursiveEdgeRecostMultiplierGlobalBaseState.state
      (K0 := K0) (K1 := K1) (K2 := K2) R).stage
        q).Gamma =
      (ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage
        (K0 := K0) (K1 := K1) (K2 := K2) J
        q).asUnary.Gamma := by
  rfl


end ConfiguredRecursiveEdgePhysicalGlobalBaseNormalizedState
