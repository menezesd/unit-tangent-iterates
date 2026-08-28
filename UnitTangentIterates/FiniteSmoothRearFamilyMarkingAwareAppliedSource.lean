import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSource
import UnitTangentIterates.GaugeFlowSupJacobi

/-! The non-erasing marking-aware result of one long gauge construction. -/

noncomputable section

open Set Function MarkedSpace PathMetric RearTrack RearOwnArclength RearFamilyFrame
  NormalPathC2IncrementVariableSpeed GaugeFlowDerivCost FlowDerivative

namespace FiniteSmoothRearFamilyMarkingAwareAppliedSource

open FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily

def rearPeriod {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} (A : MarkingAwareSource Gamma P0 kh khat Qmax) :=
  fun t => rearArclength (A.delta t) (A.P t)

def rearNormal {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} (A : MarkingAwareSource Gamma P0 kh khat Qmax) :=
  frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf)

structure ChosenPath
    {p q : Data} (Gamma : NormalPath p q)
    {P0 kh khat Qmax : ℝ} (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (Phi : ℝ → ℝ → ℝ) (a b : Data) where
  Delta : NormalPath a b
  time_eq : Delta.T = Gamma.T
  position_eq : ∀ t u, Delta.X t u = rearOwn A.F A.Theta A.delta A.sf t (Phi t u)
  eta_eq : ∀ t u, Delta.eta t u = rearNormal A t (Phi t u)
  shift : ∀ t u, Phi t (u + 1) = Phi t u + rearPeriod A t
  phi1 : ℝ → ℝ → ℝ
  phi2 : ℝ → ℝ → ℝ
  phi1_deriv : ∀ t u, HasDerivAt (Phi t) (phi1 t u) u
  phi2_deriv : ∀ t u, HasDerivAt (phi1 t) (phi2 t u) u
  phi1_continuous : ∀ t, Continuous (phi1 t)
  phi2_continuous : ∀ t, Continuous (phi2 t)
  phiRateLip : ℝ
  phiRateLip_nonnegative : 0 ≤ phiRateLip
  phi1_lower : ∀ t u,
    rearPeriod A 0 * Real.exp (-(phiRateLip * |t|)) ≤ phi1 t u
  phi1_upper : ∀ t u, phi1 t u ≤
    GaugeFlowDerivCost.costP1 (rearPeriod A 0) khat
      (∫ t in (0 : ℝ)..Gamma.T, A.m t)
  phi2_abs : ∀ t u, |phi2 t u| ≤
    GaugeFlowDerivCost.costG1 (rearPeriod A 0) khat (rearKappa2 kh)
      (∫ t in (0 : ℝ)..Gamma.T, A.m t)
  density_eq : Delta.m = A.m
  cost_eq : Delta.cost = ∫ t in (0 : ℝ)..Gamma.T, A.m t
  geometry : IsVariableSpeedNormalPath P0
    (GaugeFlowDerivCost.costP1 (rearPeriod A 0) khat
      (∫ t in (0 : ℝ)..Gamma.T, A.m t)) khat
    (GaugeFlowDerivCost.costG1 (rearPeriod A 0) khat (rearKappa2 kh)
      (∫ t in (0 : ℝ)..Gamma.T, A.m t))
    (khat * GaugeFlowDerivCost.costG1 (rearPeriod A 0) khat (rearKappa2 kh)
        (∫ t in (0 : ℝ)..Gamma.T, A.m t) +
      rearKappa2 kh * GaugeFlowDerivCost.costP1 (rearPeriod A 0) khat
        (∫ t in (0 : ℝ)..Gamma.T, A.m t) ^ 2) Delta
  c2 : C2NormalPathData Delta

structure Applied
    {p q : Data} (Gamma : NormalPath p q)
    {P0 kh khat Qmax : ℝ} (A : MarkingAwareSource Gamma P0 kh khat Qmax) where
  Phi : ℝ → ℝ → ℝ
  initial : ∀ u, Phi 0 u = rearPeriod A 0 * u
  base : ∀ t, Phi t 0 = 0
  flow : ∀ u t, HasDerivAt (fun s => Phi s u)
    (-frameTangential A.Ydot (rearOwnAngle A.Theta A.delta A.sf)
      t (Phi t u)) t
  frame : GaugeRearFamilyFundamental.RetainedGaugeFrame Phi
    (rearPeriod A)
    (fun t => (∫ u in (0 : ℝ)..A.P t,
      SelectedChangeOfVariable.cosTimeDeriv A.delta
        (RearOwnHigherRegularity.partialTime A.delta) t u) +
      A.P' t * Real.cos (A.delta t (A.P t)))
    A.m (frameTangential A.Ydot (rearOwnAngle A.Theta A.delta A.sf))
    (rearKappa1 kh) (rearKappa2 kh)
  chosen : ∀ a b,
    (∀ u, rearOwn A.F A.Theta A.delta A.sf 0 (Phi 0 u) = a.1 u) →
    (∀ u, rearOwn A.F A.Theta A.delta A.sf Gamma.T (Phi Gamma.T u) = b.1 u) →
    (∀ t, ∀ j ≤ 2, MarkedTopology.supNorm
      (iteratedDeriv j (fun u => rearNormal A t (Phi t u))) ≤ A.m t) →
    Nonempty (ChosenPath Gamma A Phi a b)

theorem exists_applied
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    Nonempty (Applied Gamma A) := by
  obtain ⟨Phi, hinitial, hbase, hflow, hchosen, hframe⟩ := A.applyLong
  obtain ⟨frame⟩ := hframe
  refine ⟨{
    Phi := Phi
    initial := hinitial
    base := hbase
    flow := hflow
    frame := frame
    chosen := ?_
  }⟩
  intro a b ha hb hsup
  obtain ⟨Delta, hT, hX, heta, hshift,
    ⟨phi1, phi2, hphi1, hphi2, hc1, hc2, hphi1upper, hphi2abs⟩,
    hm, hcost, hgeom, ⟨hC2⟩⟩ := hchosen a b ha hb hsup
  let D := frame.frame
  obtain ⟨hlip, hcont, hrate1d, -, -, -, -⟩ :=
    GaugeRate.gaugeRate_flow_hypotheses_of_bounds D.rateLip_nonneg
      D.hxi D.hxi1 D.hv D.hv1 D.hvne D.hxic D.hxi1c D.hxi2c
      D.hvc D.hv1c D.hv2c D.hrate1 D.hrate2
  have hflowSpace : ∀ t u, HasDerivAt (Phi t)
      (flowDeriv (GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1)
        Phi (rearPeriod A 0) t u) u := by
    intro t u
    exact hasDerivAt_flow_initial hlip hcont frame.flow (A.rear_period_pos 0)
      frame.initial hrate1d u t
  have hphi1eq : ∀ t u, phi1 t u =
      flowDeriv (GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1)
        Phi (rearPeriod A 0) t u := by
    intro t u
    exact (hphi1 t u).unique (hflowSpace t u)
  have hphi1lower : ∀ t u,
      rearPeriod A 0 * Real.exp (-(D.rateLip * |t|)) ≤ phi1 t u := by
    intro t u
    rw [hphi1eq t u]
    have hb := (flowDeriv_bounds (K := Real.toNNReal D.rateLip)
      (hx := GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1)
      (Phi := Phi) (A.rear_period_pos 0)
      (fun s x => by
        rw [Real.coe_toNNReal _ D.rateLip_nonneg]
        exact D.hrate1 s x) t u).1
    simpa [D, Real.coe_toNNReal _ D.rateLip_nonneg] using hb
  exact ⟨{
    Delta := Delta
    time_eq := hT
    position_eq := hX
    eta_eq := heta
    shift := hshift
    phi1 := phi1
    phi2 := phi2
    phi1_deriv := hphi1
    phi2_deriv := hphi2
    phi1_continuous := hc1
    phi2_continuous := hc2
    phiRateLip := D.rateLip
    phiRateLip_nonnegative := D.rateLip_nonneg
    phi1_lower := hphi1lower
    phi1_upper := hphi1upper
    phi2_abs := hphi2abs
    density_eq := hm
    cost_eq := hcost
    geometry := hgeom
    c2 := hC2
  }⟩

/-- The two scalar flow-composition budgets are exactly what is needed to
discharge the composed rear-normal `C²` callback retained by `Applied`. -/
theorem Applied.normal_sup_of_spatial
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A)
    (R : SpatialFrameRegularity Gamma A.Ydot A.Theta A.delta A.sf
      A.P A.m kh Qmax)
    (hd1 : ∀ t, 2 * (Gamma.m t / Real.sqrt (1 - kh ^ 2)) *
      GaugeFlowDerivCost.costP1 (rearPeriod A 0)
        (rearKappa1 kh) (∫ s in (0 : ℝ)..Gamma.T, A.m s) ≤ A.m t)
    (hd2 : ∀ t,
      (A.Dd t + 2 * (Gamma.m t / Real.sqrt (1 - kh ^ 2))) *
          GaugeFlowDerivCost.costP1 (rearPeriod A 0)
            (rearKappa1 kh) (∫ s in (0 : ℝ)..Gamma.T, A.m s) ^ 2 +
        2 * (Gamma.m t / Real.sqrt (1 - kh ^ 2)) *
          GaugeFlowDerivCost.costG1 (rearPeriod A 0)
            (rearKappa1 kh) (rearKappa2 kh)
            (∫ s in (0 : ℝ)..Gamma.T, A.m s) ≤ A.m t) :
    ∀ t, ∀ j ≤ 2, MarkedTopology.supNorm
      (iteratedDeriv j (fun u ↦ rearNormal A t (E.Phi t u))) ≤ A.m t := by
  have hnormalPer : ∀ t, Function.Periodic (rearNormal A t) (rearPeriod A t) :=
    fun t ↦ RearOwnDriftFundamental.periodic_frameNormal_rearOwn
      A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le A.cos_ne_zero
      A.front_frenet A.angle_frenet A.steering A.sf_deriv A.sf_rightInverse
      A.steering_periodic A.front_periodic A.angle_periodic A.front_contDiff
      A.angle_contDiff A.steering_contDiff A.sf_contDiff A.period_contDiff
      A.rear_time_deriv t
  have heta : ∀ t x, |rearNormal A t x| ≤
      Gamma.m t / Real.sqrt (1 - kh ^ 2) := by
    intro t x
    exact RearOwnTangentialCost.abs_frameNormal_le_slice
      A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le
      A.rear_period_pos hnormalPer A.jacobi A.etaF_bound t x
  have hg : ∀ t x,
      |A.etaF t (A.sf t x) / Real.cos (A.delta t (A.sf t x))| ≤
        Gamma.m t / Real.sqrt (1 - kh ^ 2) := by
    intro t x
    exact RearOwnTangential.abs_div_cos_le_strip A.kh_nonnegative A.kh_lt_one
      (A.strip_nonnegative t (A.sf t x)) (A.strip_le t (A.sf t x))
      (A.etaF_bound t (A.sf t x))
  exact GaugeFlowSupJacobi.supNorm_le_of_flow_jacobi
    Gamma.T_pos (A.rear_period_pos 0) R.tangential.continuous0
    R.tangential.deriv1 R.tangential.continuous1 R.tangential.deriv2
    R.tangential.continuous2 R.tangential1_bound R.tangential2_bound
    (rearKappa1_nonneg A.kh_nonnegative A.kh_lt_one)
    (rearKappa2_nonneg A.kh_nonnegative A.kh_lt_one)
    A.density_continuous A.density_nonnegative A.density_support E.initial E.flow
    A.jacobi A.gS_deriv heta hg A.gS_bound A.density_domination hd1 hd2

end FiniteSmoothRearFamilyMarkingAwareAppliedSource
