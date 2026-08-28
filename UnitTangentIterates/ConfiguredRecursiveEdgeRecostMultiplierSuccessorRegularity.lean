import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedScaledGeometricStep
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts

/-!
# Automatic regularity of a recost multiplier successor

The exact chosen-path functional proof reconstructs joint continuity of the
normal speed and its first two spatial derivatives, but its public conclusion
retains only integrability.  This module exposes those three intermediate
facts and combines them with the retained time-one predecessor carrier.
-/

noncomputable section

open Function Set MarkedSpace PathMetric
open FlowDerivative GaugeFlowTimeDerivative FlowJointContinuity
  RearFamilyFrame RearOwnArclength

namespace ConfiguredRecursiveEdgeRecostMultiplierSuccessorRegularity

open ConfiguredRecursiveEdgeRecostedGeometricState
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedScaledGeometricStep
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow
  FiniteSmoothRearFamilyMarkingAwareSource

/-- Joint `C²`-in-space regularity of the normal speed of an exact chosen
path. -/
structure JointC2Regularity
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b) : Prop where
  eta_continuous : Continuous (uncurry W.Delta.eta)
  eta1_continuous : Continuous (uncurry W.c2.eta1)
  eta2_continuous : Continuous (uncurry W.c2.eta2)

namespace JointC2Regularity

/-- The composition calculation behind exact chosen-path functional
integrability, retained before passing to interval integrals. -/
theorem of_normalSpatialC2
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    (N : RearOwnFrameDrift.SpatialC2 (rearNormal A)) :
    JointC2Regularity W := by
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
      W.phi1 t u = flowDeriv hx E.Phi (rearPeriod A 0) t u :=
    (W.phi1_deriv t u).unique
      (hasDerivAt_flow_initial hlip hcont E.frame.flow
        (A.rear_period_pos 0) E.frame.initial hxd u t)
  have hphi1_fun (t : ℝ) :
      W.phi1 t = flowDeriv hx E.Phi (rearPeriod A 0) t :=
    funext (hphi1 t)
  have hphi2 (t u : ℝ) :
      W.phi2 t u = flowDeriv2 hx hxx E.Phi (rearPeriod A 0) t u := by
    have hw := W.phi2_deriv t u
    rw [hphi1_fun t] at hw
    exact hw.unique
      (hasDerivAt_flowDeriv hlip hcont E.frame.flow
        (A.rear_period_pos 0) E.frame.initial hxd hxcont hxxd hxxcont
        hxxbd u t)
  have hphi1c : Continuous (uncurry W.phi1) :=
    (continuous_flowDeriv_prod hlip E.frame.flow E.frame.initial hxcont).congr
      (fun z => (hphi1 z.1 z.2).symm)
  have hphi2c : Continuous (uncurry W.phi2) :=
    (continuous_flowDeriv2_prod hlip E.frame.flow E.frame.initial hxcont
      hxxcont).congr (fun z => (hphi2 z.1 z.2).symm)
  have heta_deriv (t u : ℝ) :
      HasDerivAt (W.Delta.eta t)
        (N.xi1 t (E.Phi t u) * W.phi1 t u) u := by
    rw [funext (W.eta_eq t)]
    exact (N.deriv1 t (E.Phi t u)).comp u (W.phi1_deriv t u)
  have heta1 (t u : ℝ) :
      W.c2.eta1 t u = N.xi1 t (E.Phi t u) * W.phi1 t u :=
    (W.c2.eta_deriv t u).unique (heta_deriv t u)
  have heta1_fun (t : ℝ) :
      W.c2.eta1 t = fun u => N.xi1 t (E.Phi t u) * W.phi1 t u :=
    funext (heta1 t)
  have heta1_deriv (t u : ℝ) :
      HasDerivAt
        (fun v => N.xi1 t (E.Phi t v) * W.phi1 t v)
        (N.xi2 t (E.Phi t u) * W.phi1 t u ^ 2 +
          N.xi1 t (E.Phi t u) * W.phi2 t u) u := by
    convert ((N.deriv2 t (E.Phi t u)).comp u (W.phi1_deriv t u)).mul
      (W.phi2_deriv t u) using 1 <;>
        simp [Function.comp_apply, pow_two, mul_comm, mul_left_comm, mul_assoc]
  have heta2 (t u : ℝ) :
      W.c2.eta2 t u =
        N.xi2 t (E.Phi t u) * W.phi1 t u ^ 2 +
          N.xi1 t (E.Phi t u) * W.phi2 t u := by
    have hw := W.c2.eta1_deriv t u
    rw [heta1_fun t] at hw
    exact hw.unique (heta1_deriv t u)
  exact
    { eta_continuous :=
        (N.continuous0.comp₂ continuous_fst hPhi).congr
          (fun z => (W.eta_eq z.1 z.2).symm)
      eta1_continuous :=
        ((N.continuous1.comp₂ continuous_fst hPhi).mul hphi1c).congr
          (fun z => (heta1 z.1 z.2).symm)
      eta2_continuous :=
        (((N.continuous2.comp₂ continuous_fst hPhi).mul
            (hphi1c.pow 2)).add
          ((N.continuous1.comp₂ continuous_fst hPhi).mul hphi2c)).congr
            (fun z => (heta2 z.1 z.2).symm) }

/-- Every exact marking-aware source supplies the spatial frame certificate
needed by `of_normalSpatialC2`. -/
theorem of_exactSource
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b) :
    JointC2Regularity W := by
  cases A.frame_regularity with
  | joint hYdot hangle =>
      exact of_normalSpatialC2 W
        (RearOwnFrameDrift.SpatialC2.ofContDiff
          (RearOwnTangential.contDiff_frameNormal hYdot hangle))
  | spatial S =>
      exact of_normalSpatialC2 W S.normal

end JointC2Regularity

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 G1 Cg C Qmax : ℕ → ℝ}
  {kappaHat c dlt kappa : ℝ}
  {X : State Q e P0 P1 G1 Cg C Qmax kappaHat c dlt kappa}

/-- The successor selected row has automatic joint spatial regularity.  Its
duration is inherited from the retained recost carrier, hence from the
predecessor `Regularity.time_one`. -/
noncomputable def nextRegularity (H : StepInput X) (n : ℕ) :
    Regularity H.next n := by
  let W := (output H.next.invariant n).chosen
  let J := JointC2Regularity.of_exactSource W
  refine
    { eta_continuous := J.eta_continuous
      eta1_continuous := J.eta1_continuous
      eta2_continuous := J.eta2_continuous
      time_one := ?_ }
  rw [(output H.next.invariant n).chosen.time_eq]
  change ((core X (n + 1) (H.regularity (n + 1))).path).T = 1
  exact H.regularity (n + 1) |>.time_one

/-- Family form consumed by persistent successor provenance. -/
noncomputable def nextRegularityFamily (H : StepInput X) :
    ∀ n, Regularity H.next n :=
  nextRegularity H

end ConfiguredRecursiveEdgeRecostMultiplierSuccessorRegularity
