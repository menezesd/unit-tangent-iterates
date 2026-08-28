import UnitTangentIterates.SteeringDataShift
import UnitTangentIterates.PhysicalRearLimitKinematicClosure
import UnitTangentIterates.PhysicalRearLimitCurvatureClosure
import UnitTangentIterates.RearTrackEmbeddedFloorFree
import UnitTangentIterates.SelectedInverseShiftEquivariance

noncomputable section
open Function MarkedSpace RearTrack PathMetric

namespace PhysicalRearKinematicsShift

open NormalizedSelectedRearClosure
  NormalizedSteeringPhysicalRescaling

def sfShift {kh : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front) (b r : ℝ) : ℝ → ℝ :=
  fun x => K.sf (x + perim rear * r) - perim front * b

theorem deltaPhys_shift {kh P b : ℝ} (S : SteeringData kh)
    (hP : P ≠ 0) (s : ℝ) :
    deltaPhys (S.shift (b := b)) P s = deltaPhys S P (s + P * b) := by
  unfold deltaPhys SteeringData.shift
  have harg : (s + P * b) / P = s / P + b := by field_simp
  rw [harg]

/-- The translated inverse rear-arclength map.  The single phase equation
states that the chosen rear marked point corresponds to the chosen front
marked point. -/
theorem arclength_rightInverse_shift
    {kh : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front) (b r : ℝ)
    (hP : perim front ≠ 0)
    (hphase : K.sf (perim rear * r) = perim front * b) (x : ℝ) :
    rearArclength
        (deltaPhys (K.steering.shift (b := b)) (perim front))
        (sfShift K b r x) = x := by
  have hdc : Continuous (deltaPhys K.steering (perim front)) := by
    unfold deltaPhys
    have hd : Continuous K.steering.delta :=
      Differentiable.continuous fun u =>
        (K.steering.steering u).differentiableAt
    fun_prop
  have hdelta : deltaPhys (K.steering.shift (b := b)) (perim front) =
      fun s => deltaPhys K.steering (perim front) (s + perim front * b) := by
    funext s
    exact deltaPhys_shift K.steering hP s
  rw [hdelta]
  rw [SelectedInverseShiftEquivariance.rearArclength_shift hdc]
  unfold sfShift
  have hsum : K.sf (x + perim rear * r) - perim front * b +
      perim front * b = K.sf (x + perim rear * r) := by ring
  rw [hsum, K.arclength_rightInverse (x + perim rear * r),
    ← hphase, K.arclength_rightInverse (perim rear * r)]
  ring

/-- Physical selected-rear kinematics are equivariant under independent
normalized shifts of the front and rear markings, provided the two origins
are related by the old inverse-arclength coordinate. -/
def _root_.PathMetric.PhysicalRearLimitKinematics.shift
    {kh cf kf df cr kr dr : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front)
    (hcf : 0 < cf) (hfront : IsTubeMember cf kf df front)
    (hcr : 0 < cr) (hrear : IsTubeMember cr kr dr rear)
    (b r : ℝ)
    (hphase : K.sf (perim rear * r) = perim front * b) :
    PhysicalRearLimitKinematics kh
      (MarkedShift.shiftData r rear) (MarkedShift.shiftData b front) := by
  have hPpos : 0 < perim front := perim_pos hcf hfront
  have hRpos : 0 < perim rear := perim_pos hcr hrear
  have hP : perim front ≠ 0 := ne_of_gt hPpos
  have hR : perim rear ≠ 0 := ne_of_gt hRpos
  have hdC : Continuous (deltaPhys K.steering (perim front)) := by
    unfold deltaPhys
    have hd : Continuous K.steering.delta :=
      Differentiable.continuous fun u =>
        (K.steering.steering u).differentiableAt
    fun_prop
  have hdelta : deltaPhys (K.steering.shift (b := b)) (perim front) =
      fun s => deltaPhys K.steering (perim front) (s + perim front * b) := by
    funext s
    exact deltaPhys_shift K.steering hP s
  have htheta : ∀ s,
      thetaPhys (K.steering.shift (b := b)) (perim front)
          (thetaPhys K.steering (perim front) K.theta0 (perim front * b)) s =
        thetaPhys K.steering (perim front) K.theta0
          (s + perim front * b) :=
    fun s => K.steering.thetaPhys_shift hP K.curvature_continuous s
  refine
    { theta0 := thetaPhys K.steering (perim front) K.theta0 (perim front * b)
      steering := K.steering.shift (b := b)
      sf := sfShift K b r
      curvature_continuous := K.curvature_continuous.comp
        (continuous_id.add continuous_const)
      arclength_rightInverse := ?_
      front_frenet := ?_
      rear_track := ?_
      rear_perimeter := ?_
      steering_nonzero := ?_ }
  · intro x
    rw [SelectedInverseShiftEquivariance.perim_shiftData hfront]
    exact arclength_rightInverse_shift K b r hP hphase x
  · intro s
    rw [SelectedInverseShiftEquivariance.perim_shiftData hfront]
    have hev : (fun x => ev (MarkedShift.shiftData b front) x) =
        fun x => ev front (x + perim front * b) := by
      funext x
      rw [SelectedInverseShiftEquivariance.ev_shiftData hfront hP]
      congr 1
      ring
    rw [show ev (MarkedShift.shiftData b front) =
        fun x => ev front (x + perim front * b) from hev]
    have htr : HasDerivAt (fun x : ℝ => x + perim front * b) 1 s := by
      simpa using (hasDerivAt_id s).add_const (perim front * b)
    have h := (K.front_frenet (s + perim front * b)).scomp s htr
    simpa [htheta s] using h
  · intro x
    rw [SelectedInverseShiftEquivariance.perim_shiftData hfront]
    rw [SelectedInverseShiftEquivariance.ev_shiftData hrear hR]
    rw [K.rear_track]
    rw [hdelta]
    unfold sfShift rearTrack rearAngle
    rw [htheta]
    rw [show x + r * perim rear = x + perim rear * r by ring]
    dsimp only
    have hsum : K.sf (x + perim rear * r) - perim front * b +
        perim front * b = K.sf (x + perim rear * r) := by ring
    rw [hsum]
    rw [SelectedInverseShiftEquivariance.ev_shiftData hfront hP]
    congr 2 <;> ring
  · rw [SelectedInverseShiftEquivariance.perim_shiftData hrear,
      SelectedInverseShiftEquivariance.perim_shiftData hfront]
    rw [hdelta]
    rw [SelectedInverseShiftEquivariance.rearArclength_shift hdC]
    have hadd := SelectedInverseShiftEquivariance.rearArclength_add_period
      hdC (deltaPhys_periodic K.steering) (perim front * b)
    rw [show perim front + perim front * b =
        perim front * b + perim front by ring, hadd]
    rw [K.rear_perimeter]
    ring
  · obtain ⟨x, hx⟩ := K.steering_nonzero
    refine ⟨x - perim rear * r, ?_⟩
    rw [SelectedInverseShiftEquivariance.perim_shiftData hfront]
    rw [hdelta]
    unfold sfShift
    have hsfx : K.sf (x - perim rear * r + perim rear * r) = K.sf x := by
      congr 1
      ring
    rw [hsfx]
    have harg : K.sf x - perim front * b + perim front * b = K.sf x := by ring
    dsimp only
    rw [harg]
    exact hx

/-- Build physical kinematics from explicit marked selected-rear components.
The resulting record retains `sf` definitionally. -/
theorem _root_.PathMetric.exists_physicalRearLimitKinematics_of_components
    {kh c dlt : ℝ} {rear front : Data}
    (hc : 0 < c) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hfront : IsTubeMember c 0 dlt front)
    (Theta Kappa dl sf : ℝ → ℝ)
    (hX : ∀ s, HasDerivAt (ev front)
      (Complex.exp (Complex.I * (Theta s : ℂ))) s)
    (hTheta : ∀ s, HasDerivAt Theta (Kappa s) s)
    (hdper : Periodic dl (perim front))
    (hdmem : ∀ s, dl s ∈ Set.Icc 0 (Real.arcsin kh))
    (hode : ∀ s, HasDerivAt dl (Kappa s - Real.sin (dl s)) s)
    (hsf : ∀ x, rearArclength dl (sf x) = x)
    (hperim : perim rear = rearArclength dl (perim front))
    (hev : ∀ x, ev rear x = rearTrack (ev front) Theta dl (sf x)) :
    ∃ K : PhysicalRearLimitKinematics kh rear front, K.sf = sf := by
  let P := perim front
  have hPpos : 0 < P := perim_pos hc hfront
  have hP : P ≠ 0 := hPpos.ne'
  let delta : ℝ → ℝ := fun u => dl (P * u)
  have hdper' : Periodic delta 1 := by
    intro u
    dsimp [delta]
    rw [show P * (u + 1) = P * u + P by ring, hdper]
  have hdmem' : ∀ u, delta u ∈ Set.Icc 0 (Real.arcsin kh) :=
    fun u => hdmem (P * u)
  have hKcurv : ∀ s, Kappa s = UnconditionalAssembly.arcCurv front s :=
    RearTrackEmbedded.curvature_eq_arcCurv hc hfront hX hTheta
  have hdelta : ∀ u, HasDerivAt delta
      (P * (CurvatureFromMarkedDistance.dataCurv front u -
        Real.sin (delta u))) u := by
    intro u
    have hi : HasDerivAt (fun v : ℝ => P * v) P u := by
      convert (hasDerivAt_id u).const_mul P using 1 <;> ring
    have h := (hode (P * u)).scomp u hi
    have harg : u * P / perim front = u := by
      dsimp [P]
      rw [mul_div_assoc, div_self hP, mul_one]
    rw [hKcurv (P * u)] at h
    have hfun : (dl ∘ fun v : ℝ => P * v) = delta := by
      funext v
      simp [delta, Function.comp_def, mul_comm]
    rw [hfun] at h
    simpa [delta, UnconditionalAssembly.arcCurv, harg, mul_comm] using h
  let d : SteeringData kh :=
    PathMetric.intrinsicLimitSteeringData hfront delta hdper' hdmem' hdelta
  have hKd : Continuous d.K := by
    simpa [d] using PathMetric.continuous_intrinsicLimitSteeringData_K
      hc hfront delta hdper' hdmem' hdelta
  have hcurv : ∀ s, curvaturePhys d P s = Kappa s := by
    intro s
    rw [show curvaturePhys d P s =
        CurvatureFromMarkedDistance.dataCurv front (s / perim front) by
      simpa [d, P] using PathMetric.intrinsicLimitSteeringData_curvaturePhys
        hc hfront delta hdper' hdmem' hdelta s]
    exact (hKcurv s).symm
  let theta0 := Theta 0
  have hangle : ∀ s, thetaPhys d P theta0 s = Theta s := by
    intro s
    have hz : ∀ x, HasDerivAt
        (fun y => thetaPhys d P theta0 y - Theta y) 0 x := by
      intro x
      simpa [hcurv x] using
        (hasDerivAt_thetaPhys (P := P) (theta0 := theta0) d hKd x).sub
          (hTheta x)
    have hconst := is_const_of_deriv_eq_zero
      (fun x => (hz x).differentiableAt) (fun x => (hz x).deriv) s 0
    have hzero : thetaPhys d P theta0 0 - Theta 0 = 0 := by
      simp [theta0, thetaPhys]
    linarith
  have hdeltaPhys : deltaPhys d P = dl := by
    funext s
    dsimp [d, PathMetric.intrinsicLimitSteeringData, deltaPhys, delta]
    congr 1
    field_simp
  obtain ⟨u, hu⟩ := PathMetric.steering_nonzero_of_normalized_intrinsic_ode
    hc hfront rfl hdelta
  let s := P * u
  let x := rearArclength dl s
  have hdlC : Continuous dl :=
    Differentiable.continuous fun z => (hode z).differentiableAt
  have hmono : StrictMono (rearArclength dl) :=
    RearTrack.strictMono_rearArclength hdlC hkh1 hkh0
      (fun z => (hdmem z).1) (fun z => (hdmem z).2)
  have hsfleft : sf x = s := by
    apply hmono.injective
    simpa [x] using hsf x
  refine ⟨{
    theta0 := theta0
    steering := d
    sf := sf
    curvature_continuous := hKd
    arclength_rightInverse := ?_
    front_frenet := ?_
    rear_track := ?_
    rear_perimeter := ?_
    steering_nonzero := ?_ }, ?_⟩
  · intro y
    rw [hdeltaPhys]
    exact hsf y
  · intro y
    rw [hangle y]
    exact hX y
  · intro y
    rw [hev y, hdeltaPhys]
    congr 1
    funext t
    exact (hangle t).symm
  · rw [hdeltaPhys]
    exact hperim
  · refine ⟨x, ?_⟩
    rw [hdeltaPhys, hsfleft]
    change dl (P * u) ≠ 0
    exact hu
  · rfl

/-- Build physical kinematics from an already chosen marked selected-rear
witness, retaining its exact inverse-arclength map rather than choosing a new
rear and losing the marking equation. -/
theorem _root_.PathMetric.exists_physicalRearLimitKinematics_of_isMarkedSelectedInverse
    {kh c dlt : ℝ} {rear front : Data}
    (hc : 0 < c) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hfront : IsTubeMember c 0 dlt front)
    (H : SelectedInverseMap.IsMarkedSelectedInverse kh front rear) :
    Nonempty (PhysicalRearLimitKinematics kh rear front) := by
  obtain ⟨_, Theta, Kappa, dl, sf, hX, hTheta, hdper, hdmem, hode,
    hsf, hperim, hev⟩ := H
  obtain ⟨Kphys, _⟩ := PathMetric.exists_physicalRearLimitKinematics_of_components
    hc hkh0 hkh1 hfront Theta Kappa dl sf hX hTheta hdper hdmem hode
    hsf hperim hev
  exact ⟨Kphys⟩

end PhysicalRearKinematicsShift
