import UnitTangentIterates.ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalCompositionBase
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackPresentedArray
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenMajorants
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenUnconditionalExactAnalyticSuccessor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionCanonicalPresentedBoundary
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows

/-!
# Configured direct gauge-path provider

This module fixes the depth-zero member of the direct selected-rear recursion
to the gauge-first physical interpolation/source.  At later depths the source
is constructed on the raw path selected by `applyLong`; canonical recosting is
used only by the metric input and never replaces that recursive path.

The all-depth input is deliberately split into its three genuine obligations:
the presented terminal, the analytic successor majorants, and the physical
recost estimate.  It contains no `ReadyColumn`, `RowBounds`, or recursive
source-mass hypothesis.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeActualGaugePathProvider

open ConfiguredCanonicalPairSource
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgePhysicalCompositionBase
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareActualPullbackPresentedArray
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenMajorants
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareChosenUnconditionalExactAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareSmoothSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront

/-- The fixed scalar profiles used by one direct pullback chain rooted at row
`n`.  The physical curvature remains `sourceKh`; no composition scaling is
inserted into the raw successor source. -/
def chainP0 (X : ScalarPackage physicalTransitionCeilings) (n : ℕ) : ℕ → ℝ :=
  fun _ => edgeSourceP0 X.data n

def chainKh (_X : ScalarPackage physicalTransitionCeilings) (_n : ℕ) : ℕ → ℝ :=
  fun _ => sourceKh

def chainKhat (X : ScalarPackage physicalTransitionCeilings) (_n : ℕ) : ℕ → ℝ :=
  fun _ => pathKhat X.jet.scalar

def chainQmax (X : ScalarPackage physicalTransitionCeilings) (n : ℕ) : ℕ → ℝ :=
  fun _ => Qmax X.jet.scalar (X.totalRowShift + n)

/-- The physical defect paired with the step whose scalar data live on the
diagonal `n + j`. -/
def stageDefect (X : ScalarPackage physicalTransitionCeilings) (n : ℕ) : ℕ → ℝ :=
  fun j => edgePhysicalDefect X.data (n + j + 1)

theorem edgeSourceP0_data
    (X : ScalarPackage physicalTransitionCeilings) (n : ℕ) :
    edgeSourceP0 X.data n =
      edgeSourceP0 (D X.jet.scalar) (X.totalRowShift + n) := by
  simp [ScalarPackage.data,
    ConfiguredRecursiveEdgeFiniteColumnScalarClosing.ClosingOutput.data,
    ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data, D,
    ScalarPackage.totalRowShift, ScalarPackage.closingShift, edgeSourceP0,
    ConfiguredRecursiveSourceP0.sourceP0_shift, Nat.add_assoc]

/-- The configured gauge-first source/path at depth zero.  Its displayed rear
is an independent marked datum, as required by the nonaffine endpoint-cap
architecture. -/
def baseStage
    (X : ScalarPackage physicalTransitionCeilings) (n : ℕ)
    (displayed : Data) :
    Stage (chainP0 X n) (chainKh X n) (chainKhat X n) (chainQmax X n) 0 := by
  let B := X.baseColumn
    (K0 := physicalTransitionCeilings.C0)
    (K1 := physicalTransitionCeilings.C1)
    (K2 := physicalTransitionCeilings.C2)
  let source : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      (B.step.richStage (n + 1)).stage.increment
      (chainP0 X n 0) (chainKh X n 0) (chainKhat X n 0)
      (chainQmax X n 0) := by
    simpa [chainP0, chainKh, chainKhat, chainQmax, khRow,
      edgeSourceP0_data, Nat.add_assoc] using B.source n
  exact
    { start := Q X.jet.scalar (X.totalRowShift + (n + 1))
      rear := B.step.next (n + 1)
      Gamma := (B.step.richStage (n + 1)).stage.increment
      source := source
      applied := Classical.choice (exists_applied source)
      displayed := displayed }

/-- The exact chosen-output theorem removes `PresentedOutputCore` as a
geometric callback.  A sound terminal boundary is the remaining local input. -/
def geometricInputOfTerminal
    {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
    {S : Stage P0 kh khat Qmax j}
    (base : Data) (bound : ℝ)
    (terminal : PresentedTerminalInputCore
      (p := S.displayed) (base := base) (bound := bound) S.applied) :
    GeometricInput S where
  base := base
  bound := bound
  terminal := terminal
  output := Classical.choice (exists_presentedOutputCore S.applied terminal)

/-- The actual-pullback stage carried by one retained geometric presented row.
The displayed start is the source's arclength-marked initial rear; no equality
with the raw path start is asserted. -/
noncomputable def stageOfGeometricPresentedRowSelection
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion.GeometricCorrelatedColumn
      Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (R : FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion.GeometricPresentedRowSelection
      (n := n) S) : Stage (fun _ ↦ P0 (n + k)) (fun _ ↦ kh n)
        (fun _ ↦ khat n) (fun _ ↦ Qmax (n + k)) 0 where
  start := S.pathStart n
  rear := S.pathEnd n
  Gamma := S.path n
  source := S.source n
  applied := R.applied
  displayed := S.initial n

/-- A retained geometric row is already a sound geometric input.  In
particular, its exact terminal core and chosen output are reused verbatim. -/
def geometricInputOfGeometricPresentedRowSelection
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion.GeometricCorrelatedColumn
      Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (R : FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion.GeometricPresentedRowSelection
      (n := n) S) : GeometricInput (stageOfGeometricPresentedRowSelection R) where
  base := R.presented
  bound := e n (k + 1)
  terminal := R.terminalInput
  output := R.output

/-- The same retained row, with its genuine triangular indices exposed to the
synchronized recursion. -/
noncomputable def synchronizedStageOfGeometricPresentedRowSelection
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion.GeometricCorrelatedColumn
      Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (R : FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion.GeometricPresentedRowSelection
      (n := n) S) :
    FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows.Stage
      (fun n k ↦ P0 (n + k)) (fun n _ ↦ kh n)
      (fun n _ ↦ khat n) (fun n k ↦ Qmax (n + k)) n k where
  start := S.pathStart n
  rear := S.pathEnd n
  Gamma := S.path n
  source := S.source n
  applied := R.applied
  displayed := S.initial n

/-- A retained geometric row directly discharges the synchronized geometric
input at its true cell `(n,k)`. -/
def synchronizedGeometricInputOfGeometricPresentedRowSelection
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion.GeometricCorrelatedColumn
      Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (R : FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion.GeometricPresentedRowSelection
      (n := n) S) :
    FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows.GeometricInput
      (synchronizedStageOfGeometricPresentedRowSelection R) where
  base := R.presented
  bound := e n (k + 1)
  terminal := R.terminalInput
  output := R.output

/-- The retained composition successor at row `n` is exactly the synchronized
analytic successor built from geometric row `n+1`. -/
def synchronizedAnalyticInputOfGeometricPresentedRowFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion.GeometricCorrelatedColumn
      Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (F : FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion.GeometricPresentedRowFamily S)
    (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows.AnalyticInput
      (fun n ↦ synchronizedStageOfGeometricPresentedRowSelection (F.row n))
      (fun n ↦ synchronizedGeometricInputOfGeometricPresentedRowSelection (F.row n)) n := by
  refine { successor := ?_ }
  simpa [synchronizedGeometricInputOfGeometricPresentedRowSelection,
    synchronizedStageOfGeometricPresentedRowSelection,
    (F.row (n + 1)).output.stage_eq,
    FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.GeometricInput.rawPath]
    using (F.compositionAnalytic n).toRecursiveAnalyticSuccessor.toAnalytic

/-- The following long application is theorem-produced from the exact
diagonal successor source. -/
noncomputable def synchronizedNextAppliedOfGeometricPresentedRowFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion.GeometricCorrelatedColumn
      Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (F : FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion.GeometricPresentedRowFamily S)
    (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareAppliedSource.Applied
      (synchronizedGeometricInputOfGeometricPresentedRowSelection (F.row (n + 1))).rawPath
      (synchronizedAnalyticInputOfGeometricPresentedRowFamily F n).nextSource :=
  Classical.choice (FiniteSmoothRearFamilyMarkingAwareAppliedSource.exists_applied _)

/-- A retained geometric row family supplies both the synchronized geometric
column and its exact diagonal analytic successors.  Only the independent
physical metric package remains an input; the next long application is chosen
from the exact successor source. -/
noncomputable def synchronizedStepOfGeometricPresentedRowFamily
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion.GeometricCorrelatedColumn
      Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    (F : FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion.GeometricPresentedRowFamily S)
    {E C0 C1 C2 : ℕ → ℝ} {d : ℕ → ℕ → ℝ}
    (metric : ∀ n, PhysicalMetricInput
      (synchronizedGeometricInputOfGeometricPresentedRowSelection (F.row n))
      (E n) (C0 n) (C1 n) (C2 n) (d n k)) :
    FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows.Step
      (fun n ↦ synchronizedStageOfGeometricPresentedRowSelection (F.row n))
      E C0 C1 C2 d where
  geometric n := synchronizedGeometricInputOfGeometricPresentedRowSelection (F.row n)
  analytic n := synchronizedAnalyticInputOfGeometricPresentedRowFamily F n
  metric := metric
  nextApplied n := synchronizedNextAppliedOfGeometricPresentedRowFamily F n

/-- The reachable composition boundary, viewed as an actual-pullback stage.
Its displayed start is the preceding selected terminal `step.next n`, exactly
the marking used by the retained initial-alignment theorem. -/
noncomputable def stageOfCanonicalPresentedBoundary
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {K0 K1 K2 : ℝ}
    {S : FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.CorrelatedColumn
      Q current e k P0 P1 khat G1 Cg C c dlt period diagonal kh Qmax K0 K1 K2}
    (H : FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedSlicedInvariant.CompositionRecursiveSlicedCorrelatedColumn S)
    (n : ℕ) : Stage (fun _ ↦ P0 n) (fun _ ↦ kh n)
        (fun _ ↦ khat n) (fun _ ↦ Qmax n) 0 where
  start := current (n + 1)
  rear := S.column.step.next (n + 1)
  Gamma := (S.column.step.richStage (n + 1)).stage.increment
  source := S.source n
  applied := FiniteSmoothRearFamilyMarkingAwareCompositionCanonicalPresentedBoundary.applied H n
  displayed := S.column.step.next n

/-- The canonical base/reachable boundary supplies a sound terminal core and
chosen output without any new analytic callback. -/
noncomputable def geometricInputOfCanonicalPresentedBoundary
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {K0 K1 K2 : ℝ}
    {S : FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.CorrelatedColumn
      Q current e k P0 P1 khat G1 Cg C c dlt period diagonal kh Qmax K0 K1 K2}
    (H : FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedSlicedInvariant.CompositionRecursiveSlicedCorrelatedColumn S)
    (n : ℕ) : GeometricInput (stageOfCanonicalPresentedBoundary H n) where
  base := (FiniteSmoothRearFamilyMarkingAwareCompositionCanonicalPresentedBoundary.geometry H n).presented
  bound := e n (k + 1)
  terminal := FiniteSmoothRearFamilyMarkingAwareCompositionCanonicalPresentedBoundary.terminalInput H n
  output := FiniteSmoothRearFamilyMarkingAwareCompositionCanonicalPresentedBoundary.output H n

/-- Depth-zero synchronized stage supplied by the canonical correlated base
column.  The diagonal profiles reduce to `P0 n` and `Qmax n` at depth zero. -/
noncomputable def synchronizedBaseStageOfCanonicalPresentedBoundary
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {K0 K1 K2 : ℝ}
    {S : FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.CorrelatedColumn
      Q current e k P0 P1 khat G1 Cg C c dlt period diagonal kh Qmax K0 K1 K2}
    (H : FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedSlicedInvariant.CompositionRecursiveSlicedCorrelatedColumn S)
    (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows.Stage
      (fun n k ↦ P0 (n + k)) (fun n _ ↦ kh n)
      (fun n _ ↦ khat n) (fun n k ↦ Qmax (n + k)) n 0 where
  start := current (n + 1)
  rear := S.column.step.next (n + 1)
  Gamma := (S.column.step.richStage (n + 1)).stage.increment
  source := S.source n
  applied := FiniteSmoothRearFamilyMarkingAwareCompositionCanonicalPresentedBoundary.applied H n
  displayed := S.column.step.next n

/-- The canonical boundary directly supplies the depth-zero synchronized
geometric input, retaining its exact terminal core and output. -/
noncomputable def synchronizedGeometricInputOfCanonicalPresentedBoundary
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {K0 K1 K2 : ℝ}
    {S : FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.CorrelatedColumn
      Q current e k P0 P1 khat G1 Cg C c dlt period diagonal kh Qmax K0 K1 K2}
    (H : FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedSlicedInvariant.CompositionRecursiveSlicedCorrelatedColumn S)
    (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows.GeometricInput
      (synchronizedBaseStageOfCanonicalPresentedBoundary H n) where
  base := (FiniteSmoothRearFamilyMarkingAwareCompositionCanonicalPresentedBoundary.geometry H n).presented
  bound := e n (k + 1)
  terminal := FiniteSmoothRearFamilyMarkingAwareCompositionCanonicalPresentedBoundary.terminalInput H n
  output := FiniteSmoothRearFamilyMarkingAwareCompositionCanonicalPresentedBoundary.output H n

/-- The five genuine pinning/scalar facts left after the chosen long-theorem
path supplies its marking certificate and exact density identity. -/
structure AnalyticPinning
    {X : ScalarPackage physicalTransitionCeilings} {n j : ℕ}
    {S : Stage (chainP0 X n) (chainKh X n) (chainKhat X n)
      (chainQmax X n) j} (G : GeometricInput S) where
  smooth : SmoothSource S.source
    (chainP0 X n (j + 1)) (chainKh X n (j + 1))
  steering : NormalizedSteering smooth
  regularity : SuccessorRegularity steering
  tangential_zero : ∀ t, RearFamilyFrame.frameTangential
    (RearOwnHigherRegularity.partialTime
      (nextFront steering regularity.sf))
    (nextAngle steering regularity.sf) t 0 = 0
  periodUpper_le : smooth.periodUpper ≤ chainQmax X n (j + 1)
  rearKappa1_le : GaugeMarkedDataOfRearFamily.rearKappa1
      (chainKh X n (j + 1)) ≤ chainKhat X n (j + 1)
  numerical_A :
    2 + 2 * chainKhat X n (j + 1) *
        GaugeRearFamilyFromFront.rearDriftConst
          (chainQmax X n (j + 1)) (chainKh X n (j + 1)) ≤
      1 / chainP0 X n (j + 1)
  numerical_K :
    (intrinsicSourceConst (chainKh X n (j + 1))
          (intrinsicDerivativeConst (chainKh X n j)) + 2) +
        chainKhat X n (j + 1) ^ 2 +
        2 * GaugeRearFamilyFromFront.rearDriftConst
            (chainQmax X n (j + 1)) (chainKh X n (j + 1)) *
          successorKx (chainKh X n (j + 1)) ≤
      1 / chainP0 X n (j + 1) ^ 2 + chainKhat X n (j + 1) ^ 2

/-- Install the next-source majorants from the actual chosen path. -/
def AnalyticPinning.toAnalyticInput
    {X : ScalarPackage physicalTransitionCeilings} {n j : ℕ}
    {S : Stage (chainP0 X n) (chainKh X n) (chainKhat X n)
      (chainQmax X n) j} {G : GeometricInput S}
    (A : AnalyticPinning G) : AnalyticInput G where
  successor := .legacy A.smooth A.steering A.regularity (by
    rw [GeometricInput.rawPath, G.output.stage_eq]
    exact majorantsOfChosenPath A.regularity S.applied G.output.chosen
      A.tangential_zero A.periodUpper_le A.rearKappa1_le
      A.numerical_A A.numerical_K)

/-- Scalar envelopes for the unconditional exact successor theorem.  The
source itself supplies the curvature strip, while the configured next
parameters supply the target source type. -/
structure ExactAnalyticCeilings
    {X : ScalarPackage physicalTransitionCeilings} {n j : ℕ}
    {S : Stage (chainP0 X n) (chainKh X n) (chainKhat X n)
      (chainQmax X n) j} (G : GeometricInput S) where
  Md : ℝ
  MP : ℝ
  periodLower_pos : 0 < chainP0 X n (j + 1)
  periodLower_le : ∀ t,
    chainP0 X n (j + 1) ≤ period S.source t
  period_le : ∀ t,
    period S.source t ≤ chainQmax X n (j + 1)
  normalizedCurvatureTime_le : ∀ t u,
    |RearOwnHigherRegularity.partialTime
      (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
        (curvature S.source) (period S.source)) t u| ≤ Md
  periodTime_le : ∀ t,
    |SteeringVariablePeriodSelectedInverseJointC1.periodTime
      (period S.source) t| ≤ MP
  curvature_le : ∀ t s,
    |curvature S.source t s| ≤ chainKh X n (j + 1)
  rearKappa1_le : GaugeMarkedDataOfRearFamily.rearKappa1
      (chainKh X n (j + 1)) ≤ chainKhat X n (j + 1)
  numerical_A :
    2 + 2 * chainKhat X n (j + 1) *
        GaugeRearFamilyFromFront.rearDriftConst
          (chainQmax X n (j + 1)) (chainKh X n (j + 1)) ≤
      1 / chainP0 X n (j + 1)
  numerical_K :
    (intrinsicSourceConst (chainKh X n (j + 1))
          (intrinsicDerivativeConst (chainKh X n j)) + 2) +
        chainKhat X n (j + 1) ^ 2 +
        2 * GaugeRearFamilyFromFront.rearDriftConst
            (chainQmax X n (j + 1)) (chainKh X n (j + 1)) *
          successorKx (chainKh X n (j + 1)) ≤
      1 / chainP0 X n (j + 1) ^ 2 + chainKhat X n (j + 1) ^ 2

/-- Build the analytic successor without exposing any qualitative analytic
callbacks. -/
def ExactAnalyticCeilings.toAnalyticInput
    {X : ScalarPackage physicalTransitionCeilings} {n j : ℕ}
    {S : Stage (chainP0 X n) (chainKh X n) (chainKhat X n)
      (chainQmax X n) j} {G : GeometricInput S}
    (C : ExactAnalyticCeilings G) : AnalyticInput G where
  successor := Classical.choice (by
    rw [GeometricInput.rawPath, G.output.stage_eq]
    apply FiniteSmoothRearFamilyMarkingAwareChosenUnconditionalExactAnalyticSuccessor.ChosenPath.exists_exactAnalyticSuccessor
      G.output.chosen
      C.periodLower_pos sourceKh_nonnegative sourceKh_lt_one
      C.periodLower_le C.period_le C.normalizedCurvatureTime_le C.periodTime_le
    exact
      { curvature_le := C.curvature_le
        period_le := C.period_le
        rearKappa1_le := C.rearKappa1_le
        numerical_A := C.numerical_A
        numerical_K := by
          simpa [chainKh] using C.numerical_K })

/-- The three stagewise inputs which remain after fixing the gauge-first base.
Each analytic field constructs the next source with
`exists_markingAwareSuccessorSource_of_majorants`; each metric field controls
only the canonical recost and the outgoing endpoint cap. -/
structure AllDepthInput
    (X : ScalarPackage physicalTransitionCeilings) (n : ℕ)
    (displayed : Data) where
  geometric : ∀ j
    (S : Stage (chainP0 X n) (chainKh X n) (chainKhat X n)
      (chainQmax X n) j),
    GeometricInput S
  analytic : ∀ j
    (S : Stage (chainP0 X n) (chainKh X n) (chainKhat X n)
      (chainQmax X n) j),
    AnalyticInput (geometric j S)
  metric : ∀ j
    (S : Stage (chainP0 X n) (chainKh X n) (chainKhat X n)
      (chainQmax X n) j),
    PhysicalMetricInput (geometric j S)
      distortionTotal physicalTransitionCeilings.C0
      physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
      (stageDefect X n j)
  pathFactor_le : ∀ j
    (S : Stage (chainP0 X n) (chainKh X n) (chainKhat X n)
      (chainQmax X n) j),
    NormalPathC2IncrementVariableSpeed.c2ConstVar
        (metric j S).pathP0 (metric j S).pathP1 (metric j S).pathKhat
        (metric j S).pathG1 (metric j S).pathCg ≤
      edgeConversion X.data (pathKhat X.jet.scalar)
        choice.MA0 choice.NA0 (n + j)
  endpointCap_le : ∀ j
    (S : Stage (chainP0 X n) (chainKh X n) (chainKhat X n)
      (chainQmax X n) j),
    (geometric j S).endpointCap ≤
      edgeEndpointConversion X.data sourceKh X.jet.scalar.Mend (n + j) *
        edgePhysicalDefect X.data (n + j + 1)

/-- Assemble the direct all-depth provider. -/
def AllDepthInput.provider
    {X : ScalarPackage physicalTransitionCeilings} {n : ℕ}
    {displayed : Data}
    (I : AllDepthInput X n displayed) :
    Provider (baseStage X n displayed)
      distortionTotal physicalTransitionCeilings.C0
      physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
      (stageDefect X n) where
  step j S :=
    { geometric := I.geometric j S
      analytic := I.analytic j S
      metric := I.metric j S
      nextApplied := Classical.choice (exists_applied
        ((I.analytic j S).nextSource)) }

/-- The configured displayed base of row `n`. -/
def displayedBase (X : ScalarPackage physicalTransitionCeilings) (n : ℕ) : Data :=
  X.jet.scalar.Q (X.totalRowShift + n)

/-- Package independently constructed row-root providers into the common
two-dimensional actual-stage interface. -/
def configuredRows
    (X : ScalarPackage physicalTransitionCeilings)
    (I : ∀ n, AllDepthInput X n (displayedBase X n)) :
    Rows (fun n => chainP0 X n) (fun n => chainKh X n)
      (fun n => chainKhat X n) (fun n => chainQmax X n)
      (fun _ => distortionTotal)
      (fun _ => physicalTransitionCeilings.C0)
      (fun _ => physicalTransitionCeilings.C1)
      (fun _ => physicalTransitionCeilings.C2)
      (fun n => stageDefect X n) where
  base n := baseStage X n (displayedBase X n)
  provider n := (I n).provider

/-- The all-row input retains precisely the cross-row range coherence that
cannot be inferred from independent one-dimensional source recursions. -/
structure ConfiguredRowsInput
    (X : ScalarPackage physicalTransitionCeilings) where
  input : ∀ n, AllDepthInput X n (displayedBase X n)
  range_edge : ∀ n k,
    Set.range (((configuredRows X input).P n (k + 1)).1) =
      Set.range (UnitTangent.unitTangentMap
        (ev ((configuredRows X input).P (n + 1) k)))

namespace ConfiguredRowsInput

variable {X : ScalarPackage physicalTransitionCeilings}

@[simp] theorem P_zero (I : ConfiguredRowsInput X) (n : ℕ) :
    (configuredRows X I.input).P n 0 = displayedBase X n := rfl

@[simp] theorem Q_zero (I : ConfiguredRowsInput X) :
    (configuredRows X I.input).P 0 0 =
      X.jet.scalar.Q X.totalRowShift := by
  simpa [displayedBase] using I.P_zero 0

end ConfiguredRowsInput

namespace AllDepthInput

variable {X : ScalarPackage physicalTransitionCeilings} {n : ℕ}
  {displayed : Data}

@[simp] theorem stages_zero (I : AllDepthInput X n displayed) :
    I.provider.stages 0 = baseStage X n displayed := rfl

@[simp] theorem stages_succ (I : AllDepthInput X n displayed) (j : ℕ) :
    I.provider.stages (j + 1) =
      (I.provider.step j (I.provider.stages j)).next := rfl

/-- The recursive carrier is exactly the raw selected-rear path produced at
the preceding depth. -/
theorem successor_path (I : AllDepthInput X n displayed) (j : ℕ) :
    (I.provider.stages (j + 1)).Gamma =
      (I.provider.step j (I.provider.stages j)).geometric.rawPath := rfl

/-- The recursive source is exactly the finite-source theorem output on that
raw path; it is not the canonical recost. -/
theorem successor_source (I : AllDepthInput X n displayed) (j : ℕ) :
    (I.provider.stages (j + 1)).source =
      (I.provider.step j (I.provider.stages j)).analytic.nextSource := rfl

/-- The displayed successor is the independent canonical terminal
presentation, leaving the nonaffine discrepancy to the endpoint cap. -/
theorem successor_displayed (I : AllDepthInput X n displayed) (j : ℕ) :
    I.provider.displayed (j + 1) =
      (I.provider.step j (I.provider.stages j)).geometric.base := rfl

theorem error_nonnegative (I : AllDepthInput X n displayed) (j : ℕ) :
    0 ≤ I.provider.error j :=
  I.provider.error_nonnegative j

theorem step_dist (I : AllDepthInput X n displayed) (j : ℕ) :
    dist (I.provider.displayed j) (I.provider.displayed (j + 1)) ≤
      I.provider.error j :=
  I.provider.step_dist j

/-- Exact scalar bridge for one displayed direct step.  The endpoint
conversion is outside the path `c2ConstVar`, matching the paper's single-cap
accounting. -/
theorem error_le_conversion (I : AllDepthInput X n displayed) (j : ℕ) :
    I.provider.error j ≤
      edgeConversion X.data (pathKhat X.jet.scalar)
          choice.MA0 choice.NA0 (n + j) *
        (4 * ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
          distortionTotal physicalTransitionCeilings.C0
          physicalTransitionCeilings.C1 physicalTransitionCeilings.C2 *
            edgePhysicalDefect X.data (n + j + 1)) +
      edgeEndpointConversion X.data sourceKh X.jet.scalar.Mend (n + j) *
        edgePhysicalDefect X.data (n + j + 1) := by
  let S := I.provider.stages j
  let M := (I.provider.step j S).metric
  have hphysical : 0 ≤
      4 * ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
        distortionTotal physicalTransitionCeilings.C0
        physicalTransitionCeilings.C1 physicalTransitionCeilings.C2 *
          edgePhysicalDefect X.data (n + j + 1) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget_nonnegative
          distortionTotal physicalTransitionCeilings.C0
          physicalTransitionCeilings.C1 physicalTransitionCeilings.C2))
      M.d_nonnegative
  exact add_le_add
    (mul_le_mul_of_nonneg_right (I.pathFactor_le j S) hphysical)
    (I.endpointCap_le j S)

end AllDepthInput

end ConfiguredRecursiveEdgeActualGaugePathProvider
