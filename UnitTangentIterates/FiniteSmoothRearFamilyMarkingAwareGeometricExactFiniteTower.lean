import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenUnconditionalExactAnalyticSuccessor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareGeometricRowCanonicalEndpointCap
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor

/-!
# Exact nonaffine finite towers of presented rows

This file separates the finite geometric recursion from component estimates.
Once one actual presented row has been selected, its next marking-aware source,
analytic slice, and nonaffine facts are constructed by the exact successor
theorem.  No affine-marking assertion is made.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareGeometricRowCanonicalEndpointCap
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront

/-- The exact source and slice produced from one chosen path.  The
compatibility field retains the period and marking identities that would be
lost by eliminating through the older `AnalyticSuccessor` sum type. -/
structure ExactSuccessorBundle
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap khatNext QmaxNext : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b) where
  source : MarkingAwareSource W.Delta periodLower kap khatNext QmaxNext
  density_eq : source.m = density W (kap := kap)
  recursive :
    FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor.RecursiveAnalyticSuccessor
      W.Delta A periodLower kap khatNext QmaxNext
  recursive_source_eq : recursive.source = source
  compatibility :
    FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor.Compatibility
      W source
  slice : AnalyticSuccessorSliceFacts source

/-- The unconditional exact successor construction, without erasing its
source and source-tied analytic slice behind `AnalyticSuccessor`. -/
theorem ChosenPath.exists_exactSuccessorBundle
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower periodUpper kap khatNext QmaxNext Md MP : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    (hperiodLower : 0 < periodLower)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ t, periodLower ≤ period A t)
    (hPu : ∀ t, period A t ≤ periodUpper)
    (hKnTbd : ∀ t u,
      |RearOwnHigherRegularity.partialTime
        (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
          (curvature A) (period A)) t u| ≤ Md)
    (hPtbd : ∀ t,
      |SteeringVariablePeriodSelectedInverseJointC1.periodTime (period A) t| ≤ MP)
    (C : Scalar (A := A) (kap := kap) (P0Next := periodLower)
      (khatNext := khatNext) (QmaxNext := QmaxNext)) :
    Nonempty (ExactSuccessorBundle W (periodLower := periodLower)
      (kap := kap) (khatNext := khatNext) (QmaxNext := QmaxNext)) := by
  obtain ⟨S⟩ := exists_exactSelected (A := A)
    hperiodLower hkap0 hkap1 hPl hPu
    (fun t s => (le_abs_self (curvature A t s)).trans (C.curvature_le t s))
    hKnTbd hPtbd
  let R : PreTransport S :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport.exact
      S hkap0 hkap1
  obtain ⟨G⟩ := exists_gauge S R W hkap0 hkap1
  let T : ShiftedTransport R G :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport.exact
      R G hkap0 hkap1
  let B := bounds W S R G T hkap0 hkap1 C hperiodLower
  let A' := source W S R G hkap0 hkap1 T B
  let K := compatibility W S R G hkap0 hkap1 T B
  have hPl' : ∀ t, periodLower ≤ A'.P t := by
    intro t
    rw [K.period_eq]
    simpa [rearPeriod] using hPl t
  have hPu' : ∀ t, A'.P t ≤ periodUpper := by
    intro t
    rw [K.period_eq]
    simpa [rearPeriod] using hPu t
  exact ⟨{
    source := A'
    density_eq := rfl
    recursive :=
      FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor.ofReadySource
        W S R G hkap0 hkap1 T B hperiodLower hPl' hPu'
    recursive_source_eq := rfl
    compatibility := K
    slice :=
      FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor.sliceFacts
        W A' K hperiodLower hPl' hPu' }⟩

/-- Every exact successor bundle canonically supplies the nonaffine facts for
the next presented row. -/
def ExactSuccessorBundle.nonaffineFacts
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap khatNext QmaxNext : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} {W : ChosenPath Gamma A E.Phi a b}
    (X : ExactSuccessorBundle W (periodLower := periodLower)
      (kap := kap) (khatNext := khatNext) (QmaxNext := QmaxNext)) :
    Nonaffine.Facts X.source X.slice.periodUpper
      X.slice.markingLower X.slice.markingUpper :=
  Nonaffine.Facts.ofAnalytic X.slice le_rfl

/-- One actual presented row, retaining exactly the ordinary front tube needed
to identify its physical rear with the phase-zero selected inverse. -/
structure PresentedRow
    {a b : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) where
  applied : Applied Gamma A
  p : Data
  base : Data
  frontEndpoint : Data
  bound : ℝ
  terminalInput : PresentedTerminalInputCore
    (p := p) (base := base) (bound := bound) applied
  output : PresentedOutputCore applied terminalInput
  cFront : ℝ
  kFront : ℝ
  dFront : ℝ
  cFront_pos : 0 < cFront
  front_tube : IsTubeMember cFront kFront dFront terminalInput.frontData
  frontData_eq : terminalInput.frontData =
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData A

/-- The row's ordinary terminal datum is exactly the phase-zero canonical
selected inverse of its ordinary front datum. -/
noncomputable def PresentedRow.canonicalTarget
    {a b : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (R : PresentedRow A) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    FiniteSmoothRearFamilyMarkingAwareChosenCanonicalEndpointCap.PhaseCanonicalTarget
      R.output (SelectedInverseMap.selInv kh R.terminalInput.frontData) where
  phase := 0
  base_eq := by
    rw [MarkedShift.shiftData_zero]
    exact rear_eq_selInv_of_physicalKinematics hkh0 hkh1
      R.output.frontKinematics R.cFront_pos R.front_tube
      R.terminalInput.zero_floor_tube

/-- A heterogeneous analytic state.  Allowing the scalar bounds to vary is
essential for a finite triangular tower. -/
structure State where
  start : Data
  finish : Data
  path : NormalPath start finish
  P0 : ℝ
  kh : ℝ
  khat : ℝ
  Qmax : ℝ
  source : MarkingAwareSource path P0 kh khat Qmax
  P1 : ℝ
  markingLower : ℝ
  markingUpper : ℝ
  facts : Nonaffine.Facts source P1 markingLower markingUpper

/-- One exact geometric recursion step.  Component estimates are deliberately
absent: a coordinate-invariant weighted transition can be attached later
without changing the actual row or successor source. -/
structure Step (X : State) where
  row : PresentedRow X.source
  P0Next : ℝ
  khNext : ℝ
  khatNext : ℝ
  QmaxNext : ℝ
  successor : ExactSuccessorBundle row.output.chosen
    (periodLower := P0Next) (kap := khNext)
    (khatNext := khatNext) (QmaxNext := QmaxNext)

/-- The exact next state of a geometric step. -/
def Step.next {X : State} (R : Step X) : State where
  start := R.row.p
  finish := R.row.output.jets.rear
  path := R.row.output.chosen.Delta
  P0 := R.P0Next
  kh := R.khNext
  khat := R.khatNext
  Qmax := R.QmaxNext
  source := R.successor.source
  P1 := R.successor.slice.periodUpper
  markingLower := R.successor.slice.markingLower
  markingUpper := R.successor.slice.markingUpper
  facts := R.successor.nonaffineFacts

/-- A finite, genuinely dependent tower of exact nonaffine successor rows. -/
inductive Tower : (X : State) → ℕ → Type
  | nil (X : State) : Tower X 0
  | cons {X : State} (R : Step X) {depth : ℕ}
      (tail : Tower R.next depth) : Tower X (depth + 1)

/-- A row producer is the precise remaining geometric input.  It returns an
actual theorem-produced row and its exact analytic successor, not independent
source or slice callbacks. -/
abbrev RowProducer := ∀ X : State, Step X

/-- Iterating a row producer constructs every finite tower. -/
def Tower.ofProducer (G : RowProducer) : ∀ (X : State) (depth : ℕ),
    Tower X depth
  | X, 0 => .nil X
  | X, depth + 1 => .cons (G X) (Tower.ofProducer G (G X).next depth)

end FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower
