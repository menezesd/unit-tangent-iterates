import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareAutomaticRowFacts
import UnitTangentIterates.FlowSecondDerivativeJointContinuity

/-!
# Functional facts for exact chosen paths

The exact source branch only retains spatial `C2` frame regularity.  Joint
continuity of the chosen normal and its first two spatial derivatives is still
available: the marking is the scalar gauge flow, whose first two derivatives
in the initial value are jointly continuous.  This file reconstructs that
information without strengthening `ChosenPath` or the generic source records.
-/

open Function MeasureTheory Set
open PathMetricCircle RearFamilyFrame RearOwnArclength
open FlowDerivative GaugeFlowTimeDerivative FlowJointContinuity
open FiniteSmoothRearFamilyMarkingAwareSource
open FiniteSmoothRearFamilyMarkingAwareAppliedSource
open FiniteSmoothRearFamilyMarkingAwareChosenTerminal
open FiniteSmoothRearFamilyMarkingAwareConfiguredTransition

namespace FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts

noncomputable section

namespace ChosenPath

variable {p q a b : MarkedSpace.Data} {Gamma : PathMetric.NormalPath p q}
  {P0 kh khat Qmax : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}

/-- Joint continuity retained by every exact chosen path.  This is stronger
than functional integrability and is the precise certificate needed when the
chosen path becomes the carrier of the next recursive row. -/
structure JointC2
    (R : ChosenPath Gamma A E.Phi a b) : Prop where
  eta_continuous : Continuous (uncurry R.Delta.eta)
  eta1_continuous : Continuous (uncurry R.c2.eta1)
  eta2_continuous : Continuous (uncurry R.c2.eta2)

/-- The core composition argument, parameterized by a jointly continuous
spatial normal-frame certificate. -/
theorem jointC2_of_normalSpatialC2
    (R : ChosenPath Gamma A E.Phi a b)
    (N : RearOwnFrameDrift.SpatialC2 (rearNormal A)) : JointC2 R := by
  let D := E.frame.frame
  let h := GaugeRate.gaugeRate D.xi D.v
  let hx := GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1
  let hxx := GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2
  have hL : 0 ≤ D.rateLip :=
    (abs_nonneg (hx 0 0)).trans (D.hrate1 0 0)
  obtain ⟨hlip, hcont, hxd, hxcont, hxxd, hxxcont, hxxbd⟩ :=
    GaugeRate.gaugeRate_flow_hypotheses_of_bounds hL D.hxi D.hxi1
      D.hv D.hv1 D.hvne D.hxic D.hxi1c D.hxi2c D.hvc D.hv1c
      D.hv2c D.hrate1 D.hrate2
  have hPhi : Continuous (uncurry E.Phi) :=
    continuous_flow_prod hlip E.frame.flow E.frame.initial
  have hphi1 (t u : ℝ) :
      R.phi1 t u = flowDeriv hx E.Phi (rearPeriod A 0) t u :=
    (R.phi1_deriv t u).unique
      (hasDerivAt_flow_initial hlip hcont E.frame.flow
        (A.rear_period_pos 0) E.frame.initial hxd u t)
  have hphi1_fun (t : ℝ) :
      R.phi1 t = flowDeriv hx E.Phi (rearPeriod A 0) t :=
    funext (hphi1 t)
  have hphi2 (t u : ℝ) :
      R.phi2 t u = flowDeriv2 hx hxx E.Phi (rearPeriod A 0) t u := by
    have hr := R.phi2_deriv t u
    rw [hphi1_fun t] at hr
    exact hr.unique
      (hasDerivAt_flowDeriv hlip hcont E.frame.flow
        (A.rear_period_pos 0) E.frame.initial hxd hxcont hxxd hxxcont
        hxxbd u t)
  have hphi1c : Continuous (uncurry R.phi1) :=
    (continuous_flowDeriv_prod hlip E.frame.flow E.frame.initial hxcont).congr
      (fun z => (hphi1 z.1 z.2).symm)
  have hphi2c : Continuous (uncurry R.phi2) :=
    (continuous_flowDeriv2_prod hlip E.frame.flow E.frame.initial hxcont
      hxxcont).congr (fun z => (hphi2 z.1 z.2).symm)
  have heta_deriv (t u : ℝ) :
      HasDerivAt (R.Delta.eta t)
        (N.xi1 t (E.Phi t u) * R.phi1 t u) u := by
    rw [funext (R.eta_eq t)]
    exact (N.deriv1 t (E.Phi t u)).comp u (R.phi1_deriv t u)
  have heta1 (t u : ℝ) :
      R.c2.eta1 t u = N.xi1 t (E.Phi t u) * R.phi1 t u :=
    (R.c2.eta_deriv t u).unique (heta_deriv t u)
  have heta1_fun (t : ℝ) :
      R.c2.eta1 t = fun u => N.xi1 t (E.Phi t u) * R.phi1 t u :=
    funext (heta1 t)
  have heta1_deriv (t u : ℝ) :
      HasDerivAt
        (fun v => N.xi1 t (E.Phi t v) * R.phi1 t v)
        (N.xi2 t (E.Phi t u) * R.phi1 t u ^ 2 +
          N.xi1 t (E.Phi t u) * R.phi2 t u) u := by
    convert ((N.deriv2 t (E.Phi t u)).comp u (R.phi1_deriv t u)).mul
      (R.phi2_deriv t u) using 1 <;>
        simp [Function.comp_apply, pow_two, mul_comm, mul_left_comm, mul_assoc]
  have heta2 (t u : ℝ) :
      R.c2.eta2 t u =
        N.xi2 t (E.Phi t u) * R.phi1 t u ^ 2 +
          N.xi1 t (E.Phi t u) * R.phi2 t u := by
    have hr := R.c2.eta1_deriv t u
    rw [heta1_fun t] at hr
    exact hr.unique (heta1_deriv t u)
  have heta0c : Continuous (uncurry R.Delta.eta) :=
    (N.continuous0.comp₂ continuous_fst hPhi).congr
      (fun z => (R.eta_eq z.1 z.2).symm)
  have heta1c : Continuous (uncurry R.c2.eta1) :=
    ((N.continuous1.comp₂ continuous_fst hPhi).mul hphi1c).congr
      (fun z => (heta1 z.1 z.2).symm)
  have heta2c : Continuous (uncurry R.c2.eta2) :=
    (((N.continuous2.comp₂ continuous_fst hPhi).mul
        (hphi1c.pow 2)).add
      ((N.continuous1.comp₂ continuous_fst hPhi).mul hphi2c)).congr
        (fun z => (heta2 z.1 z.2).symm)
  exact ⟨heta0c, heta1c, heta2c⟩

theorem functionalIntegrable_of_normalSpatialC2
    (R : ChosenPath Gamma A E.Phi a b)
    (N : RearOwnFrameDrift.SpatialC2 (rearNormal A)) :
    ControlledJunctionPathFunctionalBounds.FunctionalIntegrable R.Delta.eta := by
  let H := jointC2_of_normalSpatialC2 R N
  exact PeriodicSupNormFunctionalIntegrable.functionalIntegrable_of_jointC2
    R.c2 H.eta_continuous H.eta1_continuous H.eta2_continuous

/-- The source frame certificate automatically supplies the joint `C²`
continuity of the exact chosen carrier. -/
theorem jointC2_of_exactSource
    (R : ChosenPath Gamma A E.Phi a b) : JointC2 R := by
  cases A.frame_regularity with
  | joint hYdot hangle =>
      exact jointC2_of_normalSpatialC2 R
        (RearOwnFrameDrift.SpatialC2.ofContDiff
          (RearOwnTangential.contDiff_frameNormal hYdot hangle))
  | spatial S =>
      exact jointC2_of_normalSpatialC2 R S.normal

/-- A chosen path produced by the retained exact gauge flow is functionally
integrable.  No joint time smoothness beyond either branch of the source's
frame regularity certificate is required. -/
theorem functionalIntegrable_of_exactSource
    (R : ChosenPath Gamma A E.Phi a b) :
    ControlledJunctionPathFunctionalBounds.FunctionalIntegrable R.Delta.eta := by
  cases A.frame_regularity with
  | joint hYdot hangle =>
      exact functionalIntegrable_of_normalSpatialC2 R
        (RearOwnFrameDrift.SpatialC2.ofContDiff
          (RearOwnTangential.contDiff_frameNormal hYdot hangle))
  | spatial S =>
      exact functionalIntegrable_of_normalSpatialC2 R S.normal

/-- Supplying only the front functional certificate now gives the complete
functional sidecar required by the configured transition. -/
def functionalFacts_of_exactSource
    {base : MarkedSpace.Data} {bound : ℝ}
    {B : TerminalInput (p := a) (base := base) (bound := bound) E}
    (O : Output E B)
    (front : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable
      Gamma.eta) : FunctionalFacts O where
  front := front
  rear := functionalIntegrable_of_exactSource O.chosen

end ChosenPath

end

end FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts
