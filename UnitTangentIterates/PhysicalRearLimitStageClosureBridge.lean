import UnitTangentIterates.PhysicalRearLimitCurvatureClosure

/-!
# Limiting physical rear stages: the exact remaining track identity

The existing compactness API closes the normalized steering ODE, reconstructs
the front Frenet phase and the rear-arclength inverse, preserves steering
noncollapse, and passes the rear-period identity to the limit.  This module
packages those conclusions and leaves out exactly the position identity for
the rear track.
-/

noncomputable section

open Filter Topology MarkedSpace

namespace PathMetric

open CurvatureFromMarkedDistance
open NormalizedSelectedRearClosure
open NormalizedSteeringPhysicalRescaling

/-- A physical limiting kinematic package with only the rear-track position
identity omitted. -/
structure PhysicalRearLimitKinematicsWithoutTrack
    (kh : ℝ) (rear front : Data) where
  theta0 : ℝ
  steering : SteeringData kh
  sf : ℝ → ℝ
  curvature_continuous : Continuous steering.K
  arclength_rightInverse : ∀ x,
    RearTrack.rearArclength (deltaPhys steering (perim front)) (sf x) = x
  front_frenet : ∀ s, HasDerivAt (ev front)
    (Complex.exp (Complex.I *
      (thetaPhys steering (perim front) theta0 s : ℂ))) s
  rear_perimeter : perim rear =
    RearTrack.rearArclength (deltaPhys steering (perim front)) (perim front)
  steering_nonzero : ∃ x, deltaPhys steering (perim front) (sf x) ≠ 0

namespace PhysicalRearLimitKinematicsWithoutTrack

/-- The omitted pointwise rear-track identity is sufficient to recover the
ordinary limiting kinematic package. -/
def toKinematics
    {kh : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematicsWithoutTrack kh rear front)
    (hrear_track : ∀ x, ev rear x = RearTrack.rearTrack (ev front)
      (thetaPhys K.steering (perim front) K.theta0)
      (deltaPhys K.steering (perim front)) (K.sf x)) :
    PhysicalRearLimitKinematics kh rear front where
  theta0 := K.theta0
  steering := K.steering
  sf := K.sf
  curvature_continuous := K.curvature_continuous
  arclength_rightInverse := K.arclength_rightInverse
  front_frenet := K.front_frenet
  rear_track := hrear_track
  rear_perimeter := K.rear_perimeter
  steering_nonzero := K.steering_nonzero

/-- Once the track identity is supplied, closed-tube membership of the front
upgrades the partial limiting witness directly to full stage components. -/
def toStageComponents
    {kh c dlt : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematicsWithoutTrack kh rear front)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hfront : IsTubeMember c 0 dlt front)
    (hrear_track : ∀ x, ev rear x = RearTrack.rearTrack (ev front)
      (thetaPhys K.steering (perim front) K.theta0)
      (deltaPhys K.steering (perim front)) (K.sf x)) :
    PhysicalRearLimitStageComponents rear front :=
  (K.toKinematics hrear_track).toStageComponents hkh0 hkh1 hc hfront

end PhysicalRearLimitKinematicsWithoutTrack

/-- Paired marked convergence and a common normalized-steering Lipschitz bound
close every field of `PhysicalRearLimitKinematics` except the rear-track
position formula. -/
theorem exists_limitKinematicsWithoutTrack_of_lipschitz
    {kh c dlt : ℝ}
    {rearN frontN : ℕ → Data} {rear front : Data}
    (K : ∀ n, PhysicalRearLimitKinematics kh (rearN n) (frontN n))
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hfrontN : ∀ n, IsTubeMember c 0 dlt (frontN n))
    (hfront : IsTubeMember c 0 dlt front)
    (hrearConv : Tendsto rearN atTop (nhds rear))
    (hfrontConv : Tendsto frontN atTop (nhds front))
    {C : NNReal}
    (hLip : ∀ n, LipschitzWith C (K n).steering.delta) :
    Nonempty (PhysicalRearLimitKinematicsWithoutTrack kh rear front) := by
  obtain ⟨deltaUnit, phi, hphi, hdeltaUnit, hmemUnit, hend⟩ :=
    exists_uniformSteering_subseq (fun n => (K n).steering) hLip
  let rearS : ℕ → Data := fun n => rearN (phi n)
  let frontS : ℕ → Data := fun n => frontN (phi n)
  let KS : ∀ n, PhysicalRearLimitKinematics kh (rearS n) (frontS n) :=
    fun n => K (phi n)
  have hrearS : Tendsto rearS atTop (nhds rear) := by
    simpa [rearS, Function.comp_def] using
      hrearConv.comp hphi.tendsto_atTop
  have hfrontS : Tendsto frontS atTop (nhds front) := by
    simpa [frontS, Function.comp_def] using
      hfrontConv.comp hphi.tendsto_atTop
  have hfrontSN : ∀ n, IsTubeMember c 0 dlt (frontS n) :=
    fun n => hfrontN (phi n)
  have hdeltaUnitS : Tendsto
      (fun n => steeringOnUnit (KS n).steering) atTop (nhds deltaUnit) := by
    simpa [KS] using hdeltaUnit
  let delta := unitPeriodicExtension deltaUnit
  have hdeltaC : Continuous delta := by
    simpa [delta] using continuous_unitPeriodicExtension deltaUnit hend
  have hperiod : Function.Periodic delta 1 := by
    simpa [delta] using unitPeriodicExtension_periodic deltaUnit
  have hmem : ∀ u, delta u ∈ Set.Icc (0 : ℝ) (Real.arcsin kh) := by
    intro u
    exact hmemUnit _
  have hlimit := normalized_steering_integral_identity_limit_of_unit
    KS hc hfrontSN hfront hfrontS deltaUnit hdeltaUnitS hend
  have hode : ∀ u, HasDerivAt delta
      (perim front * (dataCurv front u - Real.sin (delta u))) u := by
    simpa [delta] using hlimit.2
  let d := intrinsicLimitSteeringData hfront delta hperiod hmem hode
  obtain ⟨theta0, hdC, hfrontFrenet⟩ :=
    exists_intrinsicLimitFrontFrenet hc hfront delta hperiod hmem hode
  obtain ⟨sf, hsf, hnonzero⟩ :=
    exists_intrinsicLimitRearInverse_nonzero hkh0 hkh1 hc hfront
      delta hperiod hmem hode
  have hdeltaUniform : TendstoUniformly
      (fun n => (KS n).steering.delta) delta atTop := by
    simpa [delta] using tendstoUniformly_unitPeriodicExtension
      (fun n => (KS n).steering) deltaUnit hdeltaUnitS
  have hrearPerimRaw := rear_perimeter_limit_of_uniformSteering
    KS hc hfrontSN hfront hrearS hfrontS hdeltaC hdeltaUniform
  have hrearPerim : perim rear =
      RearTrack.rearArclength (deltaPhys d (perim front)) (perim front) := by
    simpa [d, deltaPhys, intrinsicLimitSteeringData] using hrearPerimRaw
  refine ⟨{
    theta0 := theta0
    steering := d
    sf := sf
    curvature_continuous := ?_
    arclength_rightInverse := ?_
    front_frenet := ?_
    rear_perimeter := hrearPerim
    steering_nonzero := ?_ }⟩
  · simpa [d] using hdC
  · simpa [d] using hsf
  · simpa [d] using hfrontFrenet
  · simpa [d] using hnonzero

end PathMetric
