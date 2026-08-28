import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalBaseNormalizedState
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierClosing

/-! # Final-tail normalized physical base family -/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePhysicalBaseFinalTailState

open ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgePhysicalBaseNormalizedState
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveSourceP0FixedDistortion
  ConstructedConfiguredInductiveTubeBudget.WeightedData

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    choice.MA0 choice.NA0}
  {O : GaugeOutput J} {K0 K1 K2 : ℝ}

/-- Gauge output after exactly the two additional recost closing tails. -/
def finalGaugeOutput (R : RecostClosingOutput J O) : GaugeOutput J :=
  O.shiftOutput (R.preShift + R.large.N)

def rowOutput (R : RecostClosingOutput J O) (n : ℕ) : GaugeOutput J :=
  (finalGaugeOutput R).shiftOutput n

@[simp] theorem finalGaugeOutput_N (R : RecostClosingOutput J O) :
    (finalGaugeOutput R).N = R.totalShift := by
  simp [finalGaugeOutput, totalShift, Nat.add_assoc]

/-- The final gauge data is definitionally the scalar data retained by the
recost closing output. -/
@[simp] theorem finalGaugeOutput_data (R : RecostClosingOutput J O) :
    (finalGaugeOutput R).data = R.data := by
  simp [finalGaugeOutput,
    ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data,
    RecostClosingOutput.data, RecostClosingOutput.totalShift,
    ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data, Nat.add_assoc]

@[simp] theorem rowGaugeOutput_N
    (R : RecostClosingOutput J O) (n : ℕ) :
    (rowOutput R n).N = R.totalShift + n := by
  simp [rowOutput, finalGaugeOutput, RecostClosingOutput.totalShift,
    Nat.add_assoc]

/-- Exact depth-zero synchronized stage at final row `n`. -/
def baseStage (R : RecostClosingOutput J O) (n : ℕ) :=
  ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage
    (K0 := K0) (K1 := K1) (K2 := K2) J (rowOutput R n).N

@[simp] theorem finalStage_displayed
    (R : RecostClosingOutput J O) (n : ℕ) :
    (baseStage (K0 := K0) (K1 := K1) (K2 := K2) R n).displayed =
      ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar
        (R.totalShift + n) := by
  rw [baseStage, rowGaugeOutput_N]
  exact ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage_displayed
    (K0 := K0) (K1 := K1) (K2 := K2) J _

/-- Callback-free normalized base state at every final-tail row. -/
def state (R : RecostClosingOutput J O) (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedNormalizedReachableState.State
      (rowOutput R n)
        (baseStage (K0 := K0) (K1 := K1) (K2 := K2) R n).asUnary
      (edgeP1 (D J.scalar) choice.MA0 (R.totalShift + n)) 0
      (edgePhysicalDefect (D J.scalar) (R.totalShift + n + 1)) := by
  have hDtarget : 0 ≤ configuredSourceMassTarget distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2 :=
    configuredSourceMassTarget_nonnegative distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2
  convert
    (ConfiguredRecursiveEdgePhysicalBaseNormalizedState.baseState
      (K0 := K0) (K1 := K1) (K2 := K2)
      (finalGaugeOutput R) hDtarget distortionTotal_le_eighth n) using 1 <;>
    simp [rowOutput, finalGaugeOutput, baseStage,
      RecostClosingOutput.totalShift, Nat.add_assoc]

end ConfiguredRecursiveEdgePhysicalBaseFinalTailState
