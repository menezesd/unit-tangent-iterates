import UnitTangentIterates.PhysicalRearLimitStageClosureBridge
import UnitTangentIterates.MarkedUnitTangentRangeClosure

/-!
# Closure of the physical rear-track position identity

The tangent phase itself need not converge.  The exponential of that phase is
the intrinsic physical unit tangent of the marked front, which is continuous
under simultaneous convergence of the marked datum and the physical
parameter.
-/

noncomputable section

open Filter Topology MarkedSpace

namespace PathMetric

open NormalizedSteeringPhysicalRescaling

/-- The intrinsic physical unit tangent read from marked data. -/
def physicalTangent (p : Data) (s : ℝ) : ℂ :=
  p.2.1 (s / perim p) / perim p

theorem continuousAt_ev_pair {p : Data} {s : ℝ} (hP : perim p ≠ 0) :
    ContinuousAt (fun z : Data × ℝ => ev z.1 z.2) (p, s) := by
  unfold ev
  have hp : Continuous fun z : Data × ℝ => perim z.1 := by
    unfold perim
    fun_prop
  have hu : ContinuousAt (fun z : Data × ℝ => z.2 / perim z.1) (p, s) :=
    continuous_snd.continuousAt.div hp.continuousAt hP
  exact continuous_eval.continuousAt.comp
    ((continuous_fst.comp continuous_fst).continuousAt.prodMk hu)

theorem continuousAt_physicalTangent_pair
    {p : Data} {s : ℝ} (hP : perim p ≠ 0) :
    ContinuousAt (fun z : Data × ℝ => physicalTangent z.1 z.2) (p, s) := by
  unfold physicalTangent
  have hp : Continuous fun z : Data × ℝ => perim z.1 := by
    unfold perim
    fun_prop
  have hu : ContinuousAt (fun z : Data × ℝ => z.2 / perim z.1) (p, s) :=
    continuous_snd.continuousAt.div hp.continuousAt hP
  have hv : ContinuousAt
      (fun z : Data × ℝ => z.1.2.1 (z.2 / perim z.1)) (p, s) :=
    continuous_eval.continuousAt.comp
      ((continuous_fst.comp (continuous_snd.comp continuous_fst)).continuousAt.prodMk hu)
  have hPc : (perim p : ℂ) ≠ 0 := by exact_mod_cast hP
  exact hv.div (Complex.continuous_ofReal.comp hp).continuousAt hPc

theorem rearTrack_eq_front_sub_tangent_mul
    (F : ℝ → ℂ) (Theta delta : ℝ → ℝ) (s : ℝ) :
    RearTrack.rearTrack F Theta delta s =
      F s - Complex.exp (Complex.I * (Theta s : ℂ)) *
        Complex.exp (-Complex.I * (delta s : ℂ)) := by
  unfold RearTrack.rearTrack RearTrack.rearAngle
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

set_option maxHeartbeats 800000 in
/-- The rear-track identity passes to a paired marked limit once the physical
inverse coordinates and the steering angle evaluated at those coordinates
converge. -/
theorem rear_track_limit_of_paired_tendsto
    {kh c dlt : ℝ}
    {rearN frontN : ℕ → Data} {rear front : Data}
    (K : ∀ n, PhysicalRearLimitKinematics kh (rearN n) (frontN n))
    (L : PhysicalRearLimitKinematicsWithoutTrack kh rear front)
    (hc : 0 < c)
    (hfrontN : ∀ n, IsTubeMember c 0 dlt (frontN n))
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front)
    (hrearConv : Tendsto rearN atTop (nhds rear))
    (hfrontConv : Tendsto frontN atTop (nhds front))
    (hsf : ∀ x, Tendsto (fun n => (K n).sf x) atTop (nhds (L.sf x)))
    (hdelta : ∀ x, Tendsto
      (fun n => deltaPhys (K n).steering (perim (frontN n)) ((K n).sf x))
      atTop
      (nhds (deltaPhys L.steering (perim front) (L.sf x)))) :
    ∀ x, ev rear x = RearTrack.rearTrack (ev front)
      (thetaPhys L.steering (perim front) L.theta0)
      (deltaPhys L.steering (perim front)) (L.sf x) := by
  intro x
  have hrearP : perim rear ≠ 0 := ne_of_gt (perim_pos hc hrear)
  have hfrontP : perim front ≠ 0 := ne_of_gt (perim_pos hc hfront)
  have hrearPair : Tendsto (fun n => (rearN n, x)) atTop
      (nhds (rear, x)) := by
    rw [nhds_prod_eq]
    exact hrearConv.prodMk
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (nhds x))
  have hrearEval : Tendsto (fun n => ev (rearN n) x) atTop (nhds (ev rear x)) := by
    simpa [Function.comp_def] using
      (continuousAt_ev_pair hrearP).tendsto.comp hrearPair
  have hfrontPair : Tendsto (fun n => (frontN n, (K n).sf x)) atTop
      (nhds (front, L.sf x)) := by
    rw [nhds_prod_eq]
    exact hfrontConv.prodMk (hsf x)
  have hfrontEval : Tendsto
      (fun n => ev (frontN n) ((K n).sf x)) atTop
      (nhds (ev front (L.sf x))) :=
    (continuousAt_ev_pair hfrontP).tendsto.comp hfrontPair
  have htangent : Tendsto
      (fun n => physicalTangent (frontN n) ((K n).sf x)) atTop
      (nhds (physicalTangent front (L.sf x))) :=
    (continuousAt_physicalTangent_pair hfrontP).tendsto.comp hfrontPair
  have htangentN : ∀ n,
      physicalTangent (frontN n) ((K n).sf x) =
        Complex.exp (Complex.I *
          (thetaPhys (K n).steering (perim (frontN n)) (K n).theta0
            ((K n).sf x) : ℂ)) := by
    intro n
    exact (MarkedSpace.hasDerivAt_ev_of_tube
      hc (hfrontN n) ((K n).sf x)).deriv.symm.trans
        ((K n).front_frenet ((K n).sf x)).deriv
  have htangentL : physicalTangent front (L.sf x) =
      Complex.exp (Complex.I *
        (thetaPhys L.steering (perim front) L.theta0 (L.sf x) : ℂ)) :=
    (MarkedSpace.hasDerivAt_ev_of_tube
      hc hfront (L.sf x)).deriv.symm.trans (L.front_frenet (L.sf x)).deriv
  have htheta : Tendsto
      (fun n => Complex.exp (Complex.I *
        (thetaPhys (K n).steering (perim (frontN n)) (K n).theta0
          ((K n).sf x) : ℂ))) atTop
      (nhds (Complex.exp (Complex.I *
        (thetaPhys L.steering (perim front) L.theta0 (L.sf x) : ℂ)))) := by
    simpa only [← htangentN, ← htangentL] using htangent
  have hnegExp : Continuous
      (fun y : ℝ => Complex.exp (-Complex.I * (y : ℂ))) := by
    fun_prop
  have hdeltaExp := hnegExp.continuousAt.tendsto.comp (hdelta x)
  have hformula := hfrontEval.sub (htheta.mul hdeltaExp)
  have htrackT : Tendsto (fun n => ev (rearN n) x) atTop
      (nhds (RearTrack.rearTrack (ev front)
        (thetaPhys L.steering (perim front) L.theta0)
        (deltaPhys L.steering (perim front)) (L.sf x))) := by
    convert hformula using 1
    · funext n
      rw [(K n).rear_track]
      simpa [Function.comp_def] using
        rearTrack_eq_front_sub_tangent_mul (ev (frontN n))
          (thetaPhys (K n).steering (perim (frontN n)) (K n).theta0)
          (deltaPhys (K n).steering (perim (frontN n))) ((K n).sf x)
    · rw [rearTrack_eq_front_sub_tangent_mul]
  exact tendsto_nhds_unique hrearEval htrackT

/-- Package the preceding closed rear-track identity with the independently
constructed limiting kinematic fields. -/
def limitKinematics_of_paired_tendsto
    {kh c dlt : ℝ}
    {rearN frontN : ℕ → Data} {rear front : Data}
    (K : ∀ n, PhysicalRearLimitKinematics kh (rearN n) (frontN n))
    (L : PhysicalRearLimitKinematicsWithoutTrack kh rear front)
    (hc : 0 < c)
    (hfrontN : ∀ n, IsTubeMember c 0 dlt (frontN n))
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front)
    (hrearConv : Tendsto rearN atTop (nhds rear))
    (hfrontConv : Tendsto frontN atTop (nhds front))
    (hsf : ∀ x, Tendsto (fun n => (K n).sf x) atTop (nhds (L.sf x)))
    (hdelta : ∀ x, Tendsto
      (fun n => deltaPhys (K n).steering (perim (frontN n)) ((K n).sf x))
      atTop
      (nhds (deltaPhys L.steering (perim front) (L.sf x)))) :
    PhysicalRearLimitKinematics kh rear front :=
  L.toKinematics (rear_track_limit_of_paired_tendsto K L hc hfrontN
    hrear hfront hrearConv hfrontConv hsf hdelta)

/-- The corresponding full stage-components adapter. -/
def limitStageComponents_of_paired_tendsto
    {kh c dlt : ℝ}
    {rearN frontN : ℕ → Data} {rear front : Data}
    (K : ∀ n, PhysicalRearLimitKinematics kh (rearN n) (frontN n))
    (L : PhysicalRearLimitKinematicsWithoutTrack kh rear front)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hfrontN : ∀ n, IsTubeMember c 0 dlt (frontN n))
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front)
    (hrearConv : Tendsto rearN atTop (nhds rear))
    (hfrontConv : Tendsto frontN atTop (nhds front))
    (hsf : ∀ x, Tendsto (fun n => (K n).sf x) atTop (nhds (L.sf x)))
    (hdelta : ∀ x, Tendsto
      (fun n => deltaPhys (K n).steering (perim (frontN n)) ((K n).sf x))
      atTop
      (nhds (deltaPhys L.steering (perim front) (L.sf x)))) :
    PhysicalRearLimitStageComponents rear front :=
  (limitKinematics_of_paired_tendsto K L hc hfrontN hrear hfront
    hrearConv hfrontConv hsf hdelta).toStageComponents hkh0 hkh1 hc hfront

end PathMetric
