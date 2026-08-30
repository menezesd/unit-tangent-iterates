import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedCompletionScalars

/-!
# Non-circular assembly of one intrinsic multiplier layer

The pre-carrier core and scaled source are chosen first.  Normalized ancestry
then completes that pair into a carrier row.  Only afterwards is the same
scaled source viewed through the carrier, so no field depends on the record
being constructed.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierNormalizedCompletion
  ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
  ConfiguredRecursiveEdgeRecostedCompletionScalars
  ConfiguredRecursiveEdgeRecostedNormalizedReachableState
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)

abbrev globalData :=
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar

abbrev diagonal (R : RecostClosingOutput J O) (n k : ℕ) : ℕ :=
  (R.totalShift + n) + k

abbrev E0 (_n : ℕ) : ℝ :=
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
abbrev C00 (_n : ℕ) : ℝ := configuredC0
abbrev C10 (_n : ℕ) : ℝ := configuredC1
abbrev C20 (_n : ℕ) : ℝ := configuredC2
abbrev d0 (R : RecostClosingOutput J O) (n k : ℕ) : ℝ :=
  ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap (globalData (J := J))
      (diagonal R n k) ^ 2 *
    (2 * ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
      (globalData (J := J)) (diagonal R n k + 1))

structure InputData {k : ℕ} {S : ℕ → Node}
    (L : Layer R k S) where
  pre : ∀ n, ConfiguredRecursiveEdgeRecostedPreCarrier.Core (S n).stage
  analytic : ∀ n, ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input (pre (n + 1))
    (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 (globalData (J := J))
      (diagonal R n (k + 1)))
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
    (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
      (globalData (J := J)))
    (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap (globalData (J := J))
      (diagonal R n (k + 1)))
  eps_le : ∀ n, (analytic n).eps ≤
    ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
      (n + 1 + k)).major (k + 1)
  periodUpper_le : ∀ n,
    (analytic n).slice.periodUpper ≤
      ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap (globalData (J := J))
        (diagonal R n (k + 1))
  periodUpper_le_P1 : ∀ n,
    (analytic n).slice.periodUpper ≤ rowP1 R (n + (k + 1))
  rawMetric : ∀ n,
    ConfiguredRecursiveEdgeRecostedRawMetricGeometry.RawMetricGeometry.Bounded
      (pre n).geometric
  edgeBudget_le_error : ∀ n, (rawMetric n).edgeBudget ≤ R.error n k
  nextDisplayed : ℕ → Data
  terminalFrontReference : ℕ → Data
  terminalFrontPhase : ℕ → ℝ
  terminalFront_eq_phase : ∀ n,
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
      (analytic n).source = MarkedShift.shiftData
        (terminalFrontPhase n) (terminalFrontReference n)

namespace InputData

noncomputable def step
    {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
    (I : InputData R L) :
    Step S k where
  pre := I.pre
  rawMetric n := by
    change
      ConfiguredRecursiveEdgeRecostedRawMetricGeometry.RawMetricGeometry.Bounded
        (I.pre n).geometric
    exact I.rawMetric n
  targetP0 n := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0
    (globalData (J := J)) (diagonal R n (k + 1))
  targetKhat n := ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
    (globalData (J := J))
  targetQmax n := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
    (globalData (J := J)) (diagonal R n (k + 1))
  nextDisplayed := I.nextDisplayed
  analytic := I.analytic
  terminalFrontReference := I.terminalFrontReference
  terminalFrontPhase := I.terminalFrontPhase
  terminalFront_eq_phase n := by
    exact I.terminalFront_eq_phase n

/-- Configured scalar synchronization of every successor node. -/
def next_configured
    {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
    (I : InputData R L) (n : ℕ) :
    ConfiguredNode R (n + (k + 1))
      ((step (R := R) I).next n) := by
  refine
    { P0_eq := ?_
      khat_eq := ?_
      Qmax_eq := ?_
      stageP0_at_index_eq := rfl
      stageKhat_at_index_eq := rfl
      stageQmax_at_index_eq := rfl }
  · change
      ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 (globalData (J := J))
          (diagonal R n (k + 1)) =
        ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 (globalData (J := J))
          (R.totalShift + (n + (k + 1)))
    congr 1
    simp [diagonal, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · rfl
  · change
      ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap (globalData (J := J))
          (diagonal R n (k + 1)) =
        ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap (globalData (J := J))
          (R.totalShift + (n + (k + 1)))
    congr 1
    simp [diagonal, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The assembled step extends the normalized reachable layer. -/
noncomputable def nextLayer
    {k : ℕ} {S : ℕ → Node} {L : Layer R k S}
    (I : InputData R L) :
    Layer R (k + 1) (step (R := R) I).next := by
  refine ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer.Layer.next
    R L (step (R := R) I)
    (next_configured (R := R) I) ?_ ?_
  · intro n
    exact I.eps_le n
  · intro n
    exact I.periodUpper_le_P1 n

end InputData

end ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
