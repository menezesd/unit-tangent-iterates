import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareAppliedSource
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFiniteSource

/-!
# Finite successor majorants from an actual marking-aware chosen path

The long gauge theorem already chooses the next marked path.  Its retained
spatial flow gives the marking certificate, while its exact density identity
gives the density field of the next finite source.  This adapter therefore
leaves only the five genuine pinning and scalar-envelope facts.
-/

noncomputable section

open Function MarkedSpace PathMetric RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareChosenMajorants

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSmoothSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront

/-- The marking selected by the marking-aware long theorem, viewed in the
intrinsic normal velocity and period of the next physical front. -/
def markingCertificate
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {S : SmoothSource A periodLower kap}
    (D : NormalizedSteering S)
    (E : Applied Gamma A)
    (W : ChosenPath Gamma A E.Phi a b) :
    MarkingCertificate W.Delta
      (frontNormalVelocityAt (RearOwnHigherRegularity.partialTime (front A))
        (angle A) D.arclength)
      (period A) where
  phi := E.Phi
  phi1 := W.phi1
  phi2 := W.phi2
  eta_link := by
    intro t u
    rw [frontNormalVelocityAt_successor_eq_frameNormal S D t (E.Phi t u)]
    exact W.eta_eq t u
  shift := W.shift
  deriv := W.phi1_deriv
  deriv2 := W.phi2_deriv
  phi1_continuous := W.phi1_continuous
  phi2_continuous := W.phi2_continuous

/-- Build the complete next-source majorant record from an actual chosen
long-theorem path.  Marking and density are not hypotheses: they are retained
equalities of that same chosen path. -/
def majorantsOfChosenPath
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap khatNext QmaxNext : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {S : SmoothSource A periodLower kap}
    {D : NormalizedSteering S} (R : SuccessorRegularity D)
    (E : Applied Gamma A)
    (W : ChosenPath Gamma A E.Phi a b)
    (htangential : ∀ t, frameTangential
      (RearOwnHigherRegularity.partialTime (nextFront D R.sf))
      (nextAngle D R.sf) t 0 = 0)
    (hperiod : S.periodUpper ≤ QmaxNext)
    (hrearKappa : GaugeMarkedDataOfRearFamily.rearKappa1 kap ≤ khatNext)
    (hnumericalA :
      2 + 2 * khatNext * GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap ≤
        1 / periodLower)
    (hnumericalK :
      (intrinsicSourceConst kap (intrinsicDerivativeConst kh) + 2) +
          khatNext ^ 2 +
          2 * GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap *
            successorKx kap ≤
        1 / periodLower ^ 2 + khatNext ^ 2) :
    MarkingAwareFiniteSourceMajorants W.Delta R khatNext QmaxNext where
  marking := markingCertificate D E W
  density_eq := W.density_eq.symm
  tangential_zero := htangential
  periodUpper_le := hperiod
  rearKappa1_le := hrearKappa
  numerical_A := hnumericalA
  numerical_K := hnumericalK

end FiniteSmoothRearFamilyMarkingAwareChosenMajorants
