import UnitTangentIterates.FiniteNonaffineMajorLayer
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing

/-! # Intrinsic multiplier steps over finite diagonal history budgets -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteHistoryMajorBudget
  FiniteNonaffineMajorLayer

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}

abbrev diagonal (H : Output R) (n k : ℕ) : ℕ :=
  (H.totalShift + n) + k

abbrev stateP1 (H : Output R) (q : ℕ) : ℝ :=
  ConfiguredRecursiveEdgeSourceP0Growth.edgeP1
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0 (H.totalShift + q)

abbrev defect (H : Output R) (q : ℕ) : ℝ :=
  ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
      (H.totalShift + q + 1)

/-- One theorem-produced intrinsic step.  Its history error is charged to the
explicit fixed-diagonal budget, while all geometric and public metric data
remain indexed by the closing output. -/
structure InputData
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
    {O : GaugeOutput J} {R : RecostClosingOutput J O}
    (H : Output R)
    (budget : ℕ → MajorBudget
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal)
    {k : ℕ} {S : ℕ → Node}
    (L : FiniteNonaffineMajorLayer.Layer budget (stateP1 H) (defect H) k S) where
  pre : ∀ n, Core (S n).stage
  analytic : ∀ n, ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input
    (pre (n + 1))
    (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0
      (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
        (J := J))
      (diagonal H n (k + 1)))
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
    (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
      (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
        (J := J)))
    (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
      (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
        (J := J))
      (diagonal H n (k + 1)))
  eps_le : ∀ n,
    (analytic n).eps ≤ (budget (n + (k + 1))).major (k + 1)
  periodUpper_le : ∀ n,
    (analytic n).slice.periodUpper ≤
      ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
        (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
          (J := J))
        (diagonal H n (k + 1))
  periodUpper_le_P1 : ∀ n,
    (analytic n).slice.periodUpper ≤ stateP1 H (n + (k + 1))
  rawMetric : ∀ n,
    ConfiguredRecursiveEdgeRecostedRawMetricGeometry.RawMetricGeometry.Bounded
      (pre n).geometric
  edgeBudget_le_error : ∀ n, (rawMetric n).edgeBudget ≤ H.error n k
  nextDisplayed : ℕ → Data
  terminalFrontReference : ℕ → Data
  terminalFrontPhase : ℕ → ℝ
  terminalFront_eq_phase : ∀ n,
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
      (analytic n).source = MarkedShift.shiftData
        (terminalFrontPhase n) (terminalFrontReference n)

namespace InputData

noncomputable def step
    {budget : ℕ → MajorBudget
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal}
    {k : ℕ} {S : ℕ → Node}
    {L : FiniteNonaffineMajorLayer.Layer budget (stateP1 H) (defect H) k S}
    (I : ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.InputData
      J H budget L) : Step S k where
  pre := I.pre
  rawMetric := I.rawMetric
  targetP0 n := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0
    (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
      (J := J)) (diagonal H n (k + 1))
  targetKhat n := ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
    (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
      (J := J))
  targetQmax n := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
    (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
      (J := J)) (diagonal H n (k + 1))
  nextDisplayed := I.nextDisplayed
  analytic := fun n => I.analytic n
  terminalFrontReference := I.terminalFrontReference
  terminalFrontPhase := I.terminalFrontPhase
  terminalFront_eq_phase := fun n => I.terminalFront_eq_phase n

/-- The same finite diagonal budget is used by the predecessor row and its
successor, since both have total index `n+k+1`. -/
noncomputable def nextLayer
    {budget : ℕ → MajorBudget
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal}
    {k : ℕ} {S : ℕ → Node}
    {L : FiniteNonaffineMajorLayer.Layer budget (stateP1 H) (defect H) k S}
    (I : ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.InputData
      J H budget L) :
    FiniteNonaffineMajorLayer.Layer budget (stateP1 H) (defect H) (k + 1)
      I.step.next :=
  FiniteNonaffineMajorLayer.Layer.next budget (stateP1 H) (defect H) L
    I.step
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal_le_eighth
    I.eps_le I.periodUpper_le_P1

end InputData

end ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly
