import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings
import UnitTangentIterates.ConfiguredRecursiveEdgeRearPeriodFloor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison

/-!
# Split fully physical target comparison

The terminal marking has three genuinely different distortions: inverse
Jacobian in physical `W`, upper Jacobian in normalized `S1`, and the second
jet in normalized `S2`.  Keeping them split is necessary for the chosen
nonaffine marking.
-/

noncomputable section

open MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareFullyPhysicalSplitTarget

open AnchoredJacobiStableTransition

/-- Every configured recursive source has physical period at least one. -/
theorem one_le_configured_rearPeriod
    {p q : Data} {Gamma : NormalPath p q} {P0 khat Qmax : ℝ}
    {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource Gamma P0
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat Qmax}
    (hkh : 0 < ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
    (t : ℝ) :
    1 ≤ FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A t :=
  ConfiguredRecursiveEdgeRearPeriodFloor.one_le_rearPeriodFloor_sourceKh.trans
    (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings.rearPeriodFloor_le
      (A := A) hkh t)

/-- Componentwise target-marking comparison with independent coefficients. -/
structure Comparison
    (intrinsic target : Components) (invLower upper second : ℝ) : Prop where
  w : target.w ≤ invLower * intrinsic.w
  s0 : target.s0 ≤ intrinsic.s0
  s1 : target.s1 ≤ upper * intrinsic.s1
  s2 : target.s2 ≤ upper ^ 2 * intrinsic.s2 + second * intrinsic.s1

namespace Comparison

variable {front intrinsic target : Components}
  {invLower upper second C0 C1 C2 : ℝ}

/-- Compose the sharp split target comparison with an intrinsic fully
physical transition. -/
def composeIntrinsic
    (Hraw : Transition front intrinsic 1 1 0 C0 C1 C2)
    (H : Comparison intrinsic target invLower upper second)
    (hinv : 0 ≤ invLower) (hupper : 0 ≤ upper)
    (hsecond : 0 ≤ second) (hfront : front.Nonnegative)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) :
    Transition front target invLower upper second C0 C1 C2 where
  w := H.w.trans (by
    simpa using mul_le_mul_of_nonneg_left Hraw.w hinv)
  s0 := H.s0.trans Hraw.s0
  s1 := H.s1.trans (by
    have h := mul_le_mul_of_nonneg_left Hraw.s1 hupper
    simpa [mul_assoc] using h)
  s2 := by
    have hfirst := mul_le_mul_of_nonneg_left Hraw.s2 (sq_nonneg upper)
    have hsecond' := mul_le_mul_of_nonneg_left Hraw.s1 hsecond
    exact H.s2.trans (by
      have hw0 : 0 ≤ front.w + front.s0 :=
        add_nonneg hfront.w hfront.s0
      have hs10 : 0 ≤ front.w + front.s0 + front.s1 :=
        add_nonneg hw0 hfront.s1
      have _ := mul_nonneg hC2 hs10
      have _ := mul_nonneg hC1 hw0
      simpa [mul_assoc] using add_le_add hfirst hsecond')

/-- The exact chosen marking supplies the sharp split comparison to the
actual next path components.  Its normalized spatial estimates come from the
fully physical target theorem; its W estimate is the inverse-Jacobian bound
from the retained time-reparametrization input. -/
def ofChosen
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      Gamma P0 kh khat Qmax}
    {E : FiniteSmoothRearFamilyMarkingAwareAppliedSource.Applied Gamma A}
    (W : FiniteSmoothRearFamilyMarkingAwareAppliedSource.ChosenPath
      Gamma A E.Phi a b)
    (hkh : 0 < kh)
    (S : FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.SeparatedFacts
      A P1)
    (F : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable Gamma.eta)
    {eps : ℝ}
    (J : FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.NormalizedJetBounds
      W eps)
    (heps : eps < 1)
    (hfloor : 1 ≤
      FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds.rearPeriodFloor
        P0 kh) :
    Comparison
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A)
        (FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A))
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A)
        W.Delta.eta)
      (1 / (1 - eps)) (1 + eps) eps := by
  let H := FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition.analyticInput
    (E := E) S F
  let T :=
    FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.timeReparamInput
      W S H J heps
  let HT :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison.chosenTargetComparison
      W hkh S F J heps hfloor
  refine
    { w := ?_
      s0 := ?_
      s1 := ?_
      s2 := ?_ }
  · simpa [FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents]
      using T.toVariableFixedReparamBounds.w
  · simpa [HT,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison.markedPhysicalComponents,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents]
      using HT.s0
  · simpa [HT,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison.markedPhysicalComponents,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents]
      using HT.s1
  · simpa [HT,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison.markedPhysicalComponents,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents]
      using HT.s2

end Comparison

/-- The theorem-produced fully physical transition followed by a split
terminal marking comparison. -/
def transition
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      Gamma P0 kh khat Qmax}
    (applied : FiniteSmoothRearFamilyMarkingAwareAppliedSource.Applied Gamma A)
    {target : Components} {invLower upper second : ℝ}
    (hkh : 0 < kh)
    (separated :
      FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.SeparatedFacts
        A P1)
    (integrable :
      ControlledJunctionPathFunctionalBounds.FunctionalIntegrable Gamma.eta)
    (H : Comparison
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A)
        (FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A))
      target invLower upper second)
    (hinv : 0 ≤ invLower) (hupper : 0 ≤ upper)
    (hsecond : 0 ≤ second)
    (hfront :
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        A.P Gamma.eta).Nonnegative)
    (hC1 : 0 ≤ FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1 kh)
    (hC2 : 0 ≤ FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2 kh) :
    Transition
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        A.P Gamma.eta)
      target invLower upper second
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC0 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2 kh) :=
  H.composeIntrinsic
    (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings.fullyPhysicalTransition
      (E := applied) hkh separated integrable)
    hinv hupper hsecond hfront hC1 hC2

/-- Monotonicity in the three split distortion coefficients.  This is the
only scalar step needed to weaken a sharp chosen-marking transition to the
configured paired-major budget. -/
def transition_mono
    {x y : Components} {a MA NA a' MA' NA' C0 C1 C2 : ℝ}
    (H : Transition x y a MA NA C0 C1 C2)
    (hx : x.Nonnegative) (ha : a ≤ a') (hMA : MA ≤ MA')
    (hNA : NA ≤ NA') (ha0 : 0 ≤ a) (hMA0 : 0 ≤ MA)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) :
    Transition x y a' MA' NA' C0 C1 C2 where
  w := H.w.trans (mul_le_mul_of_nonneg_right ha hx.w)
  s0 := H.s0
  s1 := H.s1.trans (by
    have hsum : 0 ≤ C1 * (x.w + x.s0) :=
      mul_nonneg hC1 (add_nonneg hx.w hx.s0)
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hMA hsum)
  s2 := H.s2.trans (by
    have hsum1 : 0 ≤ C2 * (x.w + x.s0 + x.s1) :=
      mul_nonneg hC2 (add_nonneg (add_nonneg hx.w hx.s0) hx.s1)
    have hsum0 : 0 ≤ C1 * (x.w + x.s0) :=
      mul_nonneg hC1 (add_nonneg hx.w hx.s0)
    have hsquare : MA ^ 2 ≤ MA' ^ 2 := by
      nlinarith
    exact add_le_add
      (by simpa [mul_assoc] using
        mul_le_mul_of_nonneg_right hsquare hsum1)
      (by simpa [mul_assoc] using
        mul_le_mul_of_nonneg_right hNA hsum0))

end FiniteSmoothRearFamilyMarkingAwareFullyPhysicalSplitTarget
