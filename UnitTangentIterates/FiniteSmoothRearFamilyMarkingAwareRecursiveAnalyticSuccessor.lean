import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenUnconditionalExactAnalyticSuccessor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareReadySourceRecursiveSidecars

/-!
# Recursive exact analytic successors

`AnalyticSuccessor` deliberately preserves a legacy smooth branch, so it does
not expose a source projection.  This exact-only wrapper retains the source and
the fresh selection bounds derived from that source.  Forgetting the recursive
sidecars recovers the legacy API.
-/

noncomputable section

open Function Set RearOwnHigherRegularity

namespace FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence
  FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareRecursiveExactSidecars
  FiniteSmoothRearFamilyMarkingAwareReadySourceRecursiveSidecars

variable {p q a b : MarkedSpace.Data} {Gamma : PathMetric.NormalPath p q}
  {Delta : PathMetric.NormalPath a b}
  {P0 kh khat Qmax periodLower periodUpper kap khatNext QmaxNext Md MP : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}

/-- An exact analytic successor together with the regularity and fresh
selection bounds needed to select the following successor. -/
structure RecursiveAnalyticSuccessor
    (Delta : PathMetric.NormalPath a b)
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (periodLower kap khatNext QmaxNext : ℝ) where
  source : MarkingAwareSource Delta periodLower kap khatNext QmaxNext
  slice : AnalyticSuccessorSliceFacts source
  sidecars : RecursiveExactSidecars source
  spatial : SpatialFrameRegularity Delta source.Ydot source.Theta source.delta
    source.sf source.P source.m kap QmaxNext
  terminalCurvature_nonnegative : ∀ s, 0 ≤ source.K Delta.T s
  terminalRange : Set.range (source.F Delta.T) = Set.range b.1

namespace RecursiveAnalyticSuccessor

/-- Forget the recursive sidecars and retain the existing exact analytic
successor interface. -/
def toAnalytic
    (R : RecursiveAnalyticSuccessor Delta A periodLower kap khatNext QmaxNext) :
    AnalyticSuccessor Delta A periodLower kap khatNext QmaxNext :=
  AnalyticSuccessor.ofExact R.source R.slice

/-- The slice projection used by recursive row providers. -/
def toSlice
    (R : RecursiveAnalyticSuccessor Delta A periodLower kap khatNext QmaxNext) :
    AnalyticSuccessorSliceFacts R.source :=
  R.slice

/-- The predecessor source is a phantom index of the exact recursive package;
changing it does not alter any source-tied witness. -/
def rebase
    {p' q' : MarkedSpace.Data} {Gamma' : PathMetric.NormalPath p' q'}
    {P0' kh' khat' Qmax' : ℝ}
    (R : RecursiveAnalyticSuccessor Delta A periodLower kap khatNext QmaxNext)
    (A' : MarkingAwareSource Gamma' P0' kh' khat' Qmax') :
    RecursiveAnalyticSuccessor Delta A' periodLower kap khatNext QmaxNext :=
  ⟨R.source, R.slice, R.sidecars, R.spatial, R.terminalCurvature_nonnegative,
    R.terminalRange⟩

/-- Transport the complete recursive package through an equality of its
curvature parameter.  This is the safe boundary for configured sources whose
physical curvature constant is rewritten only after construction. -/
def castKap {kap' : ℝ} (h : kap = kap')
    (R : RecursiveAnalyticSuccessor Delta A periodLower kap khatNext QmaxNext) :
    RecursiveAnalyticSuccessor Delta A periodLower kap' khatNext QmaxNext := by
  subst kap'
  exact R

/-- Package any already configured exact source with its two source-tied
certificates. -/
def ofExact
    (source : MarkingAwareSource Delta periodLower kap khatNext QmaxNext)
    (slice : AnalyticSuccessorSliceFacts source)
    (sidecars : RecursiveExactSidecars source)
    (spatial : SpatialFrameRegularity Delta source.Ydot source.Theta
      source.delta source.sf source.P source.m kap QmaxNext)
    (terminalCurvature_nonnegative : ∀ s, 0 ≤ source.K Delta.T s)
    (terminalRange : Set.range (source.F Delta.T) = Set.range b.1) :
    RecursiveAnalyticSuccessor Delta A periodLower kap khatNext QmaxNext :=
  ⟨source, slice, sidecars, spatial, terminalCurvature_nonnegative, terminalRange⟩

end RecursiveAnalyticSuccessor

/-- Retain the ReadySource construction rather than immediately erasing it to
the legacy analytic-successor sum. -/
def ofReadySource
    (W : ChosenPath Gamma A E.Phi a b)
    (S : ExactSelected A)
    (R : PreTransport S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge
      (FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport.xi R))
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (T : ShiftedTransport R G)
    (D : Bounds (P0Next := periodLower) (khatNext := khatNext)
      (QmaxNext := QmaxNext) W S R G T hkap0 hkap1)
    (hperiodLower : 0 < periodLower)
    (hPl : ∀ t, periodLower ≤
      (source (P0Next := periodLower) (khatNext := khatNext)
        (QmaxNext := QmaxNext) W S R G hkap0 hkap1 T D).P t)
    (hPu : ∀ t,
      (source (P0Next := periodLower) (khatNext := khatNext)
        (QmaxNext := QmaxNext) W S R G hkap0 hkap1 T D).P t ≤ periodUpper) :
    RecursiveAnalyticSuccessor W.Delta A periodLower kap khatNext QmaxNext := by
  let B := source (P0Next := periodLower) (khatNext := khatNext)
    (QmaxNext := QmaxNext) W S R G hkap0 hkap1 T D
  let C : Compatibility W B := compatibility W S R G hkap0 hkap1 T D
  have hc : Continuous (E.Phi W.Delta.T) :=
    continuous_iff_continuousAt.2 fun u ↦
      (W.phi1_deriv W.Delta.T u).continuousAt
  have hs : Surjective (E.Phi W.Delta.T) :=
    surjective_of_continuous_quasiPeriodic
      ((MarkingAwareSource.successorFrontCore A).period_pos W.Delta.T)
      hc (W.shift W.Delta.T)
  exact ⟨B,
    sliceFacts W B C hperiodLower hPl hPu,
    recursiveSidecars W S R G hkap0 hkap1 T D hperiodLower hPl,
    FiniteSmoothRearFamilyMarkingAwareReadySourceRecursiveSidecars.spatialCertificate
      W S R G hkap0 hkap1 T D,
    fun s ↦ (MarkingAwareSource.successorFrontCore A).curvature_nonnegative
      W.Delta.T
        (s + FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
          S G.q W.Delta.T),
    by
      ext z
      constructor
      · rintro ⟨s, rfl⟩
        obtain ⟨u, hu⟩ := hs
          (s + FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
            S G.q W.Delta.T)
        refine ⟨u, ?_⟩
        rw [← W.Delta.finish u, W.position_eq, hu]
        rfl
      · rintro ⟨u, rfl⟩
        refine ⟨E.Phi W.Delta.T u -
          FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
            S G.q W.Delta.T, ?_⟩
        rw [← W.Delta.finish u, W.position_eq]
        change TimeDependentSpatialReanchoring.shift (front A)
          (FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
            S G.q) W.Delta.T
              (E.Phi W.Delta.T u -
                FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
                  S G.q W.Delta.T) =
            RearOwnArclength.rearOwn A.F A.Theta A.delta A.sf
              W.Delta.T (E.Phi W.Delta.T u)
        simp [TimeDependentSpatialReanchoring.shift,
          FiniteSmoothRearFamilyMarkingAwareSuccessorFront.front]⟩

/-- The unconditional chosen-path theorem with the exact source and its fresh
recursive selection bounds retained in the result. -/
theorem ChosenPath.exists_recursiveAnalyticSuccessor
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
      (RecursiveAnalyticSuccessor W.Delta A periodLower kap khatNext QmaxNext) := by
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
  let D := bounds W S R G T hkap0 hkap1 C hperiodLower
  exact ⟨ofReadySource W S R G hkap0 hkap1 T D
    hperiodLower hPl hPu⟩

end FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor
