import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds

/-!
# Unconditional exact analytic successor of a chosen path

All qualitative choices are made internally.  The inputs below are exactly
the finite scalar envelopes required by the selected-family theorem and the
long rear-family estimate.
-/

noncomputable section

open Function Set RearOwnHigherRegularity

namespace FiniteSmoothRearFamilyMarkingAwareChosenUnconditionalExactAnalyticSuccessor

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence
  FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds

variable {p q a b : MarkedSpace.Data} {Gamma : PathMetric.NormalPath p q}
  {P0 kh khat Qmax periodLower periodUpper kap khatNext QmaxNext Md MP : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}

/-- A chosen path canonically supplies an exact next analytic source.  No
source, steering, inverse, gauge, transport, or slice-facts callback occurs in
the statement. -/
theorem ChosenPath.exists_exactAnalyticSuccessor
    (W : ChosenPath Gamma A E.Phi a b)
    (hperiodLower : 0 < periodLower)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ t, periodLower ≤ period A t)
    (hPu : ∀ t, period A t ≤ periodUpper)
    (hKnTbd : ∀ t u,
      |partialTime
        (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
          (curvature A) (period A)) t u| ≤ Md)
    (hPtbd : ∀ t,
      |SteeringVariablePeriodSelectedInverseJointC1.periodTime (period A) t| ≤ MP)
    (C : Scalar (A := A) (kap := kap) (P0Next := periodLower)
      (khatNext := khatNext) (QmaxNext := QmaxNext)) :
    Nonempty
      (FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.AnalyticSuccessor
        W.Delta A periodLower kap khatNext QmaxNext) := by
  obtain ⟨S⟩ := exists_exactSelected (A := A)
    hperiodLower hkap0 hkap1 hPl hPu
    (fun t s => (le_abs_self (curvature A t s)).trans (C.curvature_le t s))
    hKnTbd hPtbd
  let R : PreTransport S :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport.exact S hkap0 hkap1
  obtain ⟨G⟩ := exists_gauge S R W hkap0 hkap1
  let T : ShiftedTransport R G :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport.exact
      R G hkap0 hkap1
  let B := bounds W S R G T hkap0 hkap1 C hperiodLower
  exact ⟨analyticSuccessor W S R G hkap0 hkap1 T B
    hperiodLower hPl hPu⟩

end FiniteSmoothRearFamilyMarkingAwareChosenUnconditionalExactAnalyticSuccessor
