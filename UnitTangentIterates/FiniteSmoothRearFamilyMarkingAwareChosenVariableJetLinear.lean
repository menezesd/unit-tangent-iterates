import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction

/-!
# Linear all-time gauge-jet bounds

The exact all-slice flow estimate is nonlinear in the source mass.  On a
fixed mass interval it is bounded by the same explicit linear coefficient as
the terminal estimate, with the terminal perimeter replaced by the genuine
uniform rear-period floor `sqrt (1 - kh^2) * P0`.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction
  GaugeMarkedDataOfRearFamily
  GaugeTerminalNearIdentityJets

variable {p q a b : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax P1 : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}

/-- A normalized all-time jet certificate may be enlarged without changing
the chosen marking. -/
def normalizedJetBounds_mono
    {W : ChosenPath Gamma A E.Phi a b} {eps eps' : ℝ}
    (J : NormalizedJetBounds W eps) (h : eps ≤ eps') :
    NormalizedJetBounds W eps' where
  eps_nonnegative := J.eps_nonnegative.trans h
  dpsi t ht u := (J.dpsi t ht u).trans h
  ddpsi t ht u := (J.ddpsi t ht u).trans h

/-- Explicit coefficient which linearizes the all-time normalized gauge jets
when the total source mass is at most `M`. -/
def chosenJetLinearConst
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (M : ℝ) : ℝ :=
  jetLinearConst (rearPeriod A 0) (rearPeriodFloor P0 kh)
    (rearKappa1 kh) (rearKappa2 kh) M

theorem sourceMass_nonnegative
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    0 ≤ sourceMass A :=
  intervalIntegral.integral_nonneg Gamma.T_pos.le
    (fun t _ ↦ A.density_nonnegative t)

/-- The exact all-time error is linear in the total source mass on every
fixed mass interval.  The positivity of the replacement period is supplied
by the separated source and is not a terminal-only perimeter assumption. -/
theorem chosenJetError_le_linear
    (S : SeparatedFacts A P1) {M : ℝ} (hM : sourceMass A ≤ M) :
    chosenJetError A ≤ chosenJetLinearConst A M * sourceMass A := by
  exact jetError_le_linear (A.rear_period_pos 0).le
    (rearPeriodFloor_pos S)
    (rearKappa1_nonneg A.kh_nonnegative A.kh_lt_one)
    (rearKappa2_nonneg A.kh_nonnegative A.kh_lt_one)
    (sourceMass_nonnegative A) hM

/-- Uniform-in-time normalized gauge jets with error equal to the configured
linear coefficient times the total path defect. -/
def normalizedJetBounds_linear
    (W : ChosenPath Gamma A E.Phi a b) (S : SeparatedFacts A P1)
    (hunit : Gamma.T = 1) {M : ℝ} (hM : sourceMass A ≤ M) :
    NormalizedJetBounds W (chosenJetLinearConst A M * sourceMass A) :=
  normalizedJetBounds_mono (normalizedJetBounds_of_flow W S hunit)
    (chosenJetError_le_linear S hM)

end FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear
