import UnitTangentIterates.ConfiguredRecursiveEdgeRecostSourceP0
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostBounds

/-! # Configured direct-recost exact-successor bounds -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeDirectRecostBounds

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeSourceP0
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam

variable {p q a b : Data} {Gamma : NormalPath p q}
  {P0 khat Qmax eps : ℝ}
  {A : MarkingAwareSource Gamma P0 sourceKh khat Qmax}
  {E : Applied Gamma A}

/-- At a configured edge, the generic direct-recost bounds are automatic
once the retained normalized chosen jets and period floor are supplied. -/
def directBounds
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ)
    (W : ChosenPath Gamma A E.Phi a b)
    (S : ExactSelected A (kap := sourceKh))
    (R : PreTransport S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
    (T : ShiftedTransport R G)
    (C : Scalar (A := A) (kap := sourceKh)
      (P0Next := edgeSourceP0 D n) (khatNext := analyticKhat D)
      (QmaxNext := edgeSpeedCap D n))
    (heta0 : Continuous (uncurry W.Delta.eta))
    (heta1 : Continuous (uncurry W.c2.eta1))
    (heta2 : Continuous (uncurry W.c2.eta2))
    (J : NormalizedJetBounds W eps) (heps : eps ≤ 1 / 4)
    (hperiod : ∀ t, 1 ≤ rearPeriod A t) (hT : W.Delta.T = 1) :
    DirectBounds W S R G T sourceKh_nonnegative sourceKh_lt_one C
      (edgeSourceP0_pos D n) W.c2 heta0 heta1 heta2 := by
  apply
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostBounds.directBounds
      W S R G T sourceKh_nonnegative sourceKh_lt_one C
      (edgeSourceP0_pos D n) heta0 heta1 heta2 J heps hperiod hT
  simpa [rawSource, rawBounds,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource.source,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.bounds,
    sourceConst, derivativeConst, curvatureConst] using
    (ConfiguredRecursiveEdgeSourceP0.numerical_K_recost D n)

end ConfiguredRecursiveEdgeDirectRecostBounds
