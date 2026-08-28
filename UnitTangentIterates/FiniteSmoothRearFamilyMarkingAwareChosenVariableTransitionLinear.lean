import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear

/-!
# Linear variable-period transition for one chosen rear row

This leaf combines the exact pre-gauge physical Jacobi estimate with the
all-time normalized gauge-jet estimate.  The distortion parameter is the
explicit linear expression `chosenJetLinearConst A M * sourceMass A`; no
terminal-only jet bound or fixed-period surrogate is used.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareChosenVariableTransitionLinear

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts
  FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
  FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW
  FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction
  VariableArclengthScaledJacobiTransition

variable {p q a b : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax P1 : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}

/-- A theorem-produced chosen row has a stable variable-period component
transition with distortion linear in the source mass. -/
def transition_of_flow_linear
    (W : ChosenPath Gamma A E.Phi a b)
    (S : SeparatedFacts A P1)
    (F : FunctionalIntegrable Gamma.eta)
    (hunit : Gamma.T = 1) {M : ℝ} (hM : sourceMass A ≤ M)
    (hsmall : chosenJetLinearConst A M * sourceMass A < 1) :
    Transition
      (physicalComponents A.P Gamma.eta)
      (physicalComponents (rearPeriod A) W.Delta.eta)
      (1 / (1 - chosenJetLinearConst A M * sourceMass A))
      (1 + chosenJetLinearConst A M * sourceMass A)
      (chosenJetLinearConst A M * sourceMass A)
      (preGaugeC0 P0 P1 kh)
      (preGaugeC1 P0 P1 kh Qmax)
      (preGaugeC2 P0 P1 kh Qmax) :=
  transition W S F (normalizedJetBounds_linear W S hunit hM) hsmall

end FiniteSmoothRearFamilyMarkingAwareChosenVariableTransitionLinear
