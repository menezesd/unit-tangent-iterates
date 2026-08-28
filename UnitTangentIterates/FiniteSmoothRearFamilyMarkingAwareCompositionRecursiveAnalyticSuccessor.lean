import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessorTransport
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale

/-!
# Composition-stable recursive analytic successors

This parallel wrapper retains the two source-density inequalities required by
the composed-normal `C²` theorem.  They are source-tied facts, so retaining them
here prevents recursive providers from incorrectly reusing the base-row
composition estimate.
-/

noncomputable section

open Function Set RearOwnHigherRegularity RearTrack RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence
  FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor

variable {p q a b : MarkedSpace.Data} {Gamma : PathMetric.NormalPath p q}
  {Delta : PathMetric.NormalPath a b}
  {P0 kh khat Qmax periodLower periodUpper kap khatNext QmaxNext Md MP : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}

/-- A recursive exact source together with its two composition-density
budgets. -/
structure CompositionRecursiveAnalyticSuccessor
    (Delta : PathMetric.NormalPath a b)
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (periodLower kap khatNext QmaxNext : ℝ)
    extends RecursiveAnalyticSuccessor Delta A periodLower kap khatNext QmaxNext where
  composition_d1 : ∀ t,
    2 * (Delta.m t / Real.sqrt (1 - kap ^ 2)) *
      GaugeFlowDerivCost.costP1 (rearPeriod source 0)
        (GaugeMarkedDataOfRearFamily.rearKappa1 kap)
        (∫ s in (0 : ℝ)..Delta.T, source.m s) ≤ source.m t
  composition_d2 : ∀ t,
    (source.Dd t + 2 * (Delta.m t / Real.sqrt (1 - kap ^ 2))) *
          GaugeFlowDerivCost.costP1 (rearPeriod source 0)
            (GaugeMarkedDataOfRearFamily.rearKappa1 kap)
            (∫ s in (0 : ℝ)..Delta.T, source.m s) ^ 2 +
      2 * (Delta.m t / Real.sqrt (1 - kap ^ 2)) *
        GaugeFlowDerivCost.costG1 (rearPeriod source 0)
          (GaugeMarkedDataOfRearFamily.rearKappa1 kap)
          (GaugeMarkedDataOfRearFamily.rearKappa2 kap)
          (∫ s in (0 : ℝ)..Delta.T, source.m s) ≤ source.m t

namespace CompositionRecursiveAnalyticSuccessor

/-- The retained budgets discharge the composed-normal estimate for every
application of the recursive source. -/
theorem normal_sup
    (X : CompositionRecursiveAnalyticSuccessor Delta A periodLower kap
      khatNext QmaxNext)
    (F : Applied Delta X.source) :
    ∀ t, ∀ j ≤ 2, MarkedTopology.supNorm
      (iteratedDeriv j (fun u ↦ rearNormal X.source t (F.Phi t u))) ≤
        X.source.m t :=
  F.normal_sup_of_spatial X.spatial X.composition_d1 X.composition_d2

/-- Phase/rigid presentation preserves the source density, its Jacobi
majorant, and the path density, hence also both composition budgets. -/
def phaseRigid
    {c d : MarkedSpace.Data} {Delta : PathMetric.NormalPath c d}
    (X : CompositionRecursiveAnalyticSuccessor Delta A periodLower kap
      khatNext QmaxNext)
    (phase : ℝ) (z w : ℂ) (hw : ‖w‖ = 1)
    (terminalRange :
      Set.range ((X.source.phaseRigid phase z w hw).F
        (NormalPathC2IncrementVariableSpeed.rigidPath z w hw
          (MarkedShift.shiftPath phase Delta)).T) =
      Set.range (MarkedRigid.rigidData z w
        (MarkedShift.shiftData phase d)).1) :
    CompositionRecursiveAnalyticSuccessor
      (NormalPathC2IncrementVariableSpeed.rigidPath z w hw
        (MarkedShift.shiftPath phase Delta))
      (A.phaseRigid phase z w hw) periodLower kap khatNext QmaxNext := by
  let R :=
    FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessorTransport.RecursiveAnalyticSuccessor.phaseRigid
      X.toRecursiveAnalyticSuccessor phase z w hw terminalRange
  refine { toRecursiveAnalyticSuccessor := R
           composition_d1 := ?_
           composition_d2 := ?_ }
  · simpa [R, FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessorTransport.RecursiveAnalyticSuccessor.phaseRigid,
      MarkingAwareSource.phaseRigid_m, MarkingAwareSource.phaseRigid_Dd,
      MarkingAwareSource.phaseRigid_delta, MarkingAwareSource.phaseRigid_P,
      rearPeriod, NormalPathC2IncrementVariableSpeed.rigidPath,
      MarkedShift.shiftPath, MarkedShift.shiftPathOf,
      MarkedRigid.NormalPathRigid.rigidPathOf] using X.composition_d1
  · simpa [R, FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessorTransport.RecursiveAnalyticSuccessor.phaseRigid,
      MarkingAwareSource.phaseRigid_m, MarkingAwareSource.phaseRigid_Dd,
      MarkingAwareSource.phaseRigid_delta, MarkingAwareSource.phaseRigid_P,
      rearPeriod, NormalPathC2IncrementVariableSpeed.rigidPath,
      MarkedShift.shiftPath, MarkedShift.shiftPathOf,
      MarkedRigid.NormalPathRigid.rigidPathOf] using X.composition_d2

/-- The complete phase and physical rigid normalization preserves both
composition budgets and constructs terminal range unconditionally. -/
def phasePhysicalRigid
    {c d : MarkedSpace.Data} {Delta : PathMetric.NormalPath c d}
    (X : CompositionRecursiveAnalyticSuccessor Delta A periodLower kap
      khatNext QmaxNext)
    (phase : ℝ) (z w : ℂ) (hw : ‖w‖ = 1) :
    CompositionRecursiveAnalyticSuccessor
      (NormalPathC2IncrementVariableSpeed.rigidPath z w hw
        (MarkedShift.shiftPath phase Delta))
      ((A.phaseRigid phase z w hw).physicalRigidFields z w hw)
      periodLower kap khatNext QmaxNext := by
  let R :=
    FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessorTransport.RecursiveAnalyticSuccessor.phasePhysicalRigid
      X.toRecursiveAnalyticSuccessor phase z w hw
  refine { toRecursiveAnalyticSuccessor := R
           composition_d1 := ?_
           composition_d2 := ?_ }
  · simpa [R, FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessorTransport.RecursiveAnalyticSuccessor.phasePhysicalRigid,
      MarkingAwareSource.physicalRigidFields, MarkingAwareSource.phaseRigid_m,
      MarkingAwareSource.phaseRigid_Dd, MarkingAwareSource.phaseRigid_delta,
      MarkingAwareSource.phaseRigid_P, rearPeriod,
      NormalPathC2IncrementVariableSpeed.rigidPath,
      MarkedShift.shiftPath, MarkedShift.shiftPathOf,
      MarkedRigid.NormalPathRigid.rigidPathOf] using X.composition_d1
  · simpa [R, FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessorTransport.RecursiveAnalyticSuccessor.phasePhysicalRigid,
      MarkingAwareSource.physicalRigidFields, MarkingAwareSource.phaseRigid_m,
      MarkingAwareSource.phaseRigid_Dd, MarkingAwareSource.phaseRigid_delta,
      MarkingAwareSource.phaseRigid_P, rearPeriod,
      NormalPathC2IncrementVariableSpeed.rigidPath,
      MarkedShift.shiftPath, MarkedShift.shiftPathOf,
      MarkedRigid.NormalPathRigid.rigidPathOf] using X.composition_d2

end CompositionRecursiveAnalyticSuccessor

/-- Package a composition-scaled ReadySource without erasing either the fresh
recursive sidecars or its density budgets. -/
def ofScaledReadySource
    (W : ChosenPath Gamma A E.Phi a b)
    (S : ExactSelected A (kap := kap))
    (R : PreTransport S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (T : ShiftedTransport R G)
    (C : FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale.Scalar (A := A) (kap := kap) (P0Next := periodLower)
      (khatNext := khatNext) (QmaxNext := QmaxNext) W)
    (hperiodLower : 0 < periodLower)
    (hPl : ∀ t, periodLower ≤ period A t)
    (hPu : ∀ t, period A t ≤ periodUpper) :
    CompositionRecursiveAnalyticSuccessor W.Delta A periodLower kap
      khatNext QmaxNext := by
  let D := FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale.scaledBounds W S R G T hkap0 hkap1 C hperiodLower
  let X := ofReadySource W S R G hkap0 hkap1 T D
    hperiodLower hPl hPu
  have H := FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale.scaledBounds_composition_budgets
    W S R G T hkap0 hkap1 C hperiodLower
  refine { toRecursiveAnalyticSuccessor := X
           composition_d1 := ?_
           composition_d2 := ?_ }
  · simpa [X, D, rearPeriod, source]
      using H.1
  · simpa [X, D, rearPeriod, source]
      using H.2

/-- The unconditional chosen-path constructor using a scaled source density.
-/
theorem ChosenPath.exists_compositionRecursiveAnalyticSuccessor
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
    (C : FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale.Scalar (A := A) (kap := kap) (P0Next := periodLower)
      (khatNext := khatNext) (QmaxNext := QmaxNext) W) :
    Nonempty (CompositionRecursiveAnalyticSuccessor W.Delta A periodLower kap
      khatNext QmaxNext) := by
  obtain ⟨S⟩ := exists_exactSelected (A := A)
    hperiodLower hkap0 hkap1 hPl hPu
    (fun t s ↦ (le_abs_self (curvature A t s)).trans
      (C.toScalar.curvature_le t s))
    hKnTbd hPtbd
  let R : PreTransport S :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport.exact
      S hkap0 hkap1
  obtain ⟨G⟩ := exists_gauge S R W hkap0 hkap1
  let T : ShiftedTransport R G :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport.exact
      R G hkap0 hkap1
  exact ⟨ofScaledReadySource W S R G hkap0 hkap1 T C
    hperiodLower hPl hPu⟩

end FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor
