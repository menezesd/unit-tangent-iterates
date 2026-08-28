import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
import UnitTangentIterates.GaugeTerminalNearIdentityJets
import UnitTangentIterates.SelInvPerimBound

/-!
# Uniform-in-time normalized gauge jets for an exact chosen path

Terminal jet control alone does not bound the components of a whole path.  The
retained gauge-flow equations give the required bound simultaneously for every
time slice.  Prefix integrals are dominated by the total path cost, and the
selected-rear period is bounded below by the standard pinched-arclength floor.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric FlowDerivative
  GaugeFlowTimeDerivative RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily GaugeTerminalNearIdentityJets
  MarkingFlowDefectC2

variable {p q a b : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax P1 : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}

/-- Uniform lower bound for every selected-rear period. -/
def rearPeriodFloor (P0 kh : ℝ) : ℝ := Real.sqrt (1 - kh ^ 2) * P0

/-- Whole-path normalized jet error. -/
def chosenJetError
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : ℝ :=
  jetError (rearPeriod A 0) (rearPeriodFloor P0 kh)
    (rearKappa1 kh * (∫ t in (0 : ℝ)..Gamma.T, A.m t))
    (rearKappa2 kh * (∫ t in (0 : ℝ)..Gamma.T, A.m t))

theorem rearPeriodFloor_pos (S : SeparatedFacts A P1) :
    0 < rearPeriodFloor P0 kh := by
  exact mul_pos (Real.sqrt_pos.2 (by
    nlinarith [A.kh_nonnegative, A.kh_lt_one])) S.P0_pos

theorem rearPeriodFloor_le (S : SeparatedFacts A P1) (t : ℝ) :
    rearPeriodFloor P0 kh ≤ rearPeriod A t := by
  have hroot : 0 ≤ Real.sqrt (1 - kh ^ 2) := Real.sqrt_nonneg _
  refine (mul_le_mul_of_nonneg_left (S.period_lower t) hroot).trans ?_
  exact PinchedPath.mul_le_rearArclength (A.period_pos t).le
    (A.steering_contDiff.continuous.comp
      (continuous_const.prodMk continuous_id))
    (fun s ↦ ⟨A.strip_nonnegative t s, A.strip_le t s⟩)

/-- The retained flow estimates produce the all-slice near-identity sidecar
needed by the variable-period component transition.  Canonical row paths have
unit time; that normalization is stated explicitly here. -/
def normalizedJetBounds_of_flow
    (W : ChosenPath Gamma A E.Phi a b) (S : SeparatedFacts A P1)
    (hunit : Gamma.T = 1) : NormalizedJetBounds W (chosenJetError A) := by
  let D := E.frame.frame
  let hx := GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1
  let hxx := GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2
  let ell := rearPeriod A 0
  let L := rearPeriodFloor P0 kh
  let M := ∫ t in (0 : ℝ)..Gamma.T, A.m t
  let c0 := rearKappa1 kh * M
  let c2 := rearKappa2 kh * M
  have hell : 0 < ell := A.rear_period_pos 0
  have hL : 0 < L := rearPeriodFloor_pos S
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg Gamma.T_pos.le
    (fun t _ ↦ A.density_nonnegative t)
  have hk1 : 0 ≤ rearKappa1 kh := rearKappa1_nonneg A.kh_nonnegative A.kh_lt_one
  have hk2 : 0 ≤ rearKappa2 kh := rearKappa2_nonneg A.kh_nonnegative A.kh_lt_one
  have hc0 : 0 ≤ c0 := mul_nonneg hk1 hM
  have hc2 : 0 ≤ c2 := mul_nonneg hk2 hM
  have hC0 : Continuous (fun t ↦ rearKappa1 kh * A.m t) :=
    continuous_const.mul A.density_continuous
  have hC2 : Continuous (fun t ↦ rearKappa2 kh * A.m t) :=
    continuous_const.mul A.density_continuous
  have hrate1 : ∀ t x, |hx t x| ≤ rearKappa1 kh * A.m t := by
    intro t x
    exact E.frame.rate1_bound t x
  have hrate2 : ∀ t x, |hxx t x| ≤ rearKappa2 kh * A.m t := by
    intro t x
    exact E.frame.rate2_bound t x
  have hLglobal : 0 ≤ D.rateLip :=
    (abs_nonneg (hx 0 0)).trans (D.hrate1 0 0)
  obtain ⟨hlip, hcont, hxd, hxcont, hxxd, hxxcont, hxxbd⟩ :=
    GaugeRate.gaugeRate_flow_hypotheses_of_bounds hLglobal D.hxi D.hxi1
      D.hv D.hv1 D.hvne D.hxic D.hxi1c D.hxi2c D.hvc D.hv1c
      D.hv2c D.hrate1 D.hrate2
  have hphi1 (t u : ℝ) :
      W.phi1 t u = flowDeriv hx E.Phi ell t u := by
    exact (W.phi1_deriv t u).unique
      (hasDerivAt_flow_initial hlip hcont E.frame.flow hell
        E.frame.initial hxd u t)
  have hphi1fun (t : ℝ) : W.phi1 t = flowDeriv hx E.Phi ell t :=
    funext (hphi1 t)
  have hphi2 (t u : ℝ) :
      W.phi2 t u = flowDeriv2 hx hxx E.Phi ell t u := by
    have hw := W.phi2_deriv t u
    rw [hphi1fun t] at hw
    exact hw.unique
      (hasDerivAt_flowDeriv hlip hcont E.frame.flow hell E.frame.initial
        hxd hxcont hxxd hxxcont hxxbd u t)
  have hprefix (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ∫ s in (0 : ℝ)..t, A.m s ≤ M := by
    have htT : t ≤ Gamma.T := by simpa [hunit] using ht.2
    exact intervalIntegral.integral_mono_interval le_rfl ht.1 htT
      (Filter.Eventually.of_forall fun s ↦ A.density_nonnegative s)
      (A.density_continuous.intervalIntegrable 0 Gamma.T)
  have hprefix0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫ s in (0 : ℝ)..t, rearKappa1 kh * A.m s) ≤ c0 := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hprefix t ht) hk1
  have hprefix2 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫ s in (0 : ℝ)..t, rearKappa2 kh * A.m s) ≤ c2 := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hprefix t ht) hk2
  have hprefix2_nonnegative (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      0 ≤ ∫ s in (0 : ℝ)..t, rearKappa2 kh * A.m s :=
    intervalIntegral.integral_nonneg ht.1 fun s _ ↦
      mul_nonneg hk2 (A.density_nonnegative s)
  have hperiod (t : ℝ) : E.Phi t 1 - E.Phi t 0 = rearPeriod A t := by
    have hs := W.shift t 0
    rw [E.base t] at hs
    rw [E.base t]
    simpa using hs
  refine
    { eps_nonnegative := jetError_nonnegative hell.le hL hc0 hc2
      dpsi := ?_
      ddpsi := ?_ }
  · intro t ht u
    have hspace : ∀ v, HasDerivAt (fun v' ↦ E.Phi t v')
        (flowDeriv hx E.Phi ell t v) v := fun v ↦
      hasDerivAt_flow_initial hlip hcont E.frame.flow hell E.frame.initial
        hxd v t
    have hraw := abs_flowDeriv_sub_period_le_int
      (hx := hx) (Phi := E.Phi) hell hrate1 hC0 ht.1 hspace u
    rw [hperiod t, ← hphi1 t u] at hraw
    have hdefect : |W.phi1 t u - rearPeriod A t| ≤
        flowDefectC1Int ell c0 :=
      hraw.trans (flowDefectC1Int_mono hell.le (hprefix0 t ht))
    have hdefect0 : 0 ≤ flowDefectC1Int ell c0 :=
      flowDefectC1Int_nonneg hell.le hc0
    have hRt : 0 < rearPeriod A t := A.rear_period_pos t
    have hfloor := rearPeriodFloor_le S t
    have hdiv : W.phi1 t u / rearPeriod A t - 1 =
        (W.phi1 t u - rearPeriod A t) / rearPeriod A t := by
      field_simp
    calc
      |normalizedPsi1 W t u - 1| =
          |W.phi1 t u - rearPeriod A t| / rearPeriod A t := by
        rw [normalizedPsi1, hdiv, abs_div, abs_of_pos hRt]
      _ ≤ flowDefectC1Int ell c0 / rearPeriod A t :=
        div_le_div_of_nonneg_right hdefect hRt.le
      _ ≤ flowDefectC1Int ell c0 / L :=
        div_le_div_of_nonneg_left hdefect0 hL hfloor
      _ ≤ chosenJetError A := le_max_left _ _
  · intro t ht u
    have hraw := abs_flowDeriv_deriv_le_int
      (hx := hx) (hxx := hxx) (Phi := E.Phi) hell
      hrate1 hC0 hrate2 hC2 ht.1 u
    have hraw' : |W.phi2 t u| ≤ flowDefectC2Int ell
        (∫ s in (0 : ℝ)..t, rearKappa1 kh * A.m s)
        (∫ s in (0 : ℝ)..t, rearKappa2 kh * A.m s) := by
      simpa [hphi2, flowDeriv2] using hraw
    have hdefect := hraw'.trans
      (flowDefectC2Int_mono (ell := ell) (hprefix2_nonnegative t ht)
        (hprefix0 t ht) (hprefix2 t ht))
    have hdefect0 : 0 ≤ flowDefectC2Int ell c0 c2 := by
      dsimp [flowDefectC2Int]
      positivity
    have hRt : 0 < rearPeriod A t := A.rear_period_pos t
    have hfloor := rearPeriodFloor_le S t
    calc
      |normalizedPsi2 W t u| = |W.phi2 t u| / rearPeriod A t := by
        rw [normalizedPsi2, abs_div, abs_of_pos hRt]
      _ ≤ flowDefectC2Int ell c0 c2 / rearPeriod A t :=
        div_le_div_of_nonneg_right hdefect hRt.le
      _ ≤ flowDefectC2Int ell c0 c2 / L :=
        div_le_div_of_nonneg_left hdefect0 hL hfloor
      _ ≤ chosenJetError A := le_max_right _ _

/-- One-call theorem-produced transition for a unit-time exact chosen row. -/
def transition_of_flow
    (W : ChosenPath Gamma A E.Phi a b) (S : SeparatedFacts A P1)
    (F : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable Gamma.eta)
    (hunit : Gamma.T = 1) (hsmall : chosenJetError A < 1) :
    AnchoredJacobiStableTransition.Transition
      (VariableArclengthScaledJacobiTransition.physicalComponents A.P Gamma.eta)
      (VariableArclengthScaledJacobiTransition.physicalComponents
        (rearPeriod A) W.Delta.eta)
      (1 / (1 - chosenJetError A)) (1 + chosenJetError A) (chosenJetError A)
      (FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition.preGaugeC0
        P0 P1 kh)
      (FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition.preGaugeC1
        P0 P1 kh Qmax)
      (FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition.preGaugeC2
        P0 P1 kh Qmax) :=
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.transition
    W S F (normalizedJetBounds_of_flow W S hunit) hsmall

end FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds
