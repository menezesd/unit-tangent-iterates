import UnitTangentIterates.PhysicalRearLimitHarnackAdapter
import UnitTangentIterates.PhysicalRearLimitCurvatureClosure
import UnitTangentIterates.LocalPullbackEndpointCurvature

/-!
# Aligned finite pullback physical rear kinematics

The finite edge at row `n` and depth `k` is

`pullback n (k+1) = selInv kh (pullback (n+1) k)`.

The floor-free selected-rear construction already supplies its physical
steering, inverse marking, rear track, and rear period.  Rescaling that
steering to period one gives the `SteeringData` representation required by
`PhysicalRearLimitKinematics`.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace RearTrack ArclengthInverse
open NormalizedSelectedRearClosure NormalizedSteeringPhysicalRescaling
open PathMetric PathMetric.NormalPath

namespace FinitePullbackPhysicalRearKinematicsConstructor

/-- One positive-speed floor-free selected-inverse edge carries the complete
physical kinematic package. -/
theorem exists_kinematics_selInv_of_curvature_turning
    {c dlt kh : ℝ} (hc : 0 < c) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    {p : Data} (hp : IsTubeMember c 0 dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤
      kh * ‖p.2.1 u‖ ^ 3)
    (hturn : ∃ Theta K : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p)
        (Complex.exp (Complex.I * (Theta s : ℂ))) s) ∧
      (∀ s, HasDerivAt Theta (K s) s) ∧
      (∀ s, Theta (s + perim p) = Theta s + 2 * Real.pi)) :
    Nonempty (PathMetric.PhysicalRearLimitKinematics kh
      (SelectedInverseMap.selInv kh p) p) := by
  have hinj : ∀ Theta K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p)
        (Complex.exp (Complex.I * (Theta s : ℂ))) s) →
      (∀ s, HasDerivAt Theta (K s) s) →
      Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Theta dl) (Ico 0 (perim p)) :=
    RearTrackEmbedded.injOn_rearTrack_of_tube_floor_free
      hc hkh0 hkh1 hp hub hturn
  obtain ⟨q, Theta, K, dl, sf, dR, hX, hTheta, _hKlow, _hKhigh,
      hdper, hdmem, hode, hsf, _hdRpos, hqmem, hperim, _hoval,
      _hqub, _hrange, hev, _hmark⟩ :=
    SelectedInverseRearOwn.exists_marked_rearOwn_floor_free
      hc hkh1 hp hub hinj
  have hqeq : q = SelectedInverseMap.selInv kh p := by
    apply SelectedInverseMap.eq_selInv_of_isMarkedSelectedInverse
      hc hkh0 hkh1 hp
    exact ⟨⟨perim q, 0, dR, hqmem⟩, Theta, K, dl, sf, hX, hTheta,
      hdper, hdmem, hode, hsf, hperim, hev⟩
  let P := perim p
  have hP : 0 < P := perim_pos hc hp
  have hPne : P ≠ 0 := hP.ne'
  let delta : ℝ → ℝ := fun u => dl (P * u)
  have hdper' : Periodic delta 1 := by
    intro u
    dsimp [delta]
    rw [show P * (u + 1) = P * u + P by ring, hdper]
  have hdmem' : ∀ u, delta u ∈ Icc 0 (Real.arcsin kh) :=
    fun u => hdmem (P * u)
  have hKcurv : ∀ s, K s = UnconditionalAssembly.arcCurv p s :=
    RearTrackEmbedded.curvature_eq_arcCurv hc hp hX hTheta
  have hdelta : ∀ u, HasDerivAt delta
      (P * (CurvatureFromMarkedDistance.dataCurv p u - Real.sin (delta u))) u := by
    intro u
    have hi : HasDerivAt (fun v : ℝ => P * v) P u := by
      convert (hasDerivAt_id u).const_mul P using 1 <;> ring
    have h := (hode (P * u)).scomp u hi
    have harg : u * P / perim p = u := by
      dsimp [P]
      rw [mul_div_assoc, div_self (perim_pos hc hp).ne', mul_one]
    rw [hKcurv (P * u)] at h
    have hfun : (dl ∘ fun v : ℝ => P * v) = delta := by
      funext v
      simp [delta, Function.comp_def, mul_comm]
    rw [hfun] at h
    simpa [delta, UnconditionalAssembly.arcCurv, harg, mul_comm] using h
  let d : SteeringData kh :=
    PathMetric.intrinsicLimitSteeringData hp delta hdper' hdmem' hdelta
  have hKd : Continuous d.K := by
    simpa [d] using
      PathMetric.continuous_intrinsicLimitSteeringData_K
        hc hp delta hdper' hdmem' hdelta
  have hcurv : ∀ s, curvaturePhys d P s = K s := by
    intro s
    rw [show curvaturePhys d P s =
        CurvatureFromMarkedDistance.dataCurv p (s / perim p) by
      simpa [d, P] using
        PathMetric.intrinsicLimitSteeringData_curvaturePhys
          hc hp delta hdper' hdmem' hdelta s]
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
  have hfront : ∀ s, HasDerivAt (ev p)
      (Complex.exp (Complex.I * (thetaPhys d P theta0 s : ℂ))) s := by
    intro s
    rw [hangle s]
    exact hX s
  have hdlC : Continuous dl :=
    Differentiable.continuous fun s => (hode s).differentiableAt
  have hmono : StrictMono (rearArclength dl) :=
    RearTrack.strictMono_rearArclength hdlC hkh1 hkh0
      (fun s => (hdmem s).1) (fun s => (hdmem s).2)
  obtain ⟨u, hu⟩ := PathMetric.steering_nonzero_of_normalized_intrinsic_ode
    hc hp rfl hdelta
  let s := P * u
  let x := rearArclength dl s
  have hsfleft : sf x = s := by
    apply hmono.injective
    simpa [x] using hsf x
  have hnonzero : ∃ x, deltaPhys d P (sf x) ≠ 0 := by
    refine ⟨x, ?_⟩
    rw [hdeltaPhys, hsfleft]
    change dl (P * u) ≠ 0
    exact hu
  refine ⟨{
    theta0 := theta0
    steering := d
    sf := sf
    curvature_continuous := hKd
    arclength_rightInverse := ?_
    front_frenet := hfront
    rear_track := ?_
    rear_perimeter := ?_
    steering_nonzero := hnonzero }⟩
  · intro y
    rw [hdeltaPhys]
    exact hsf y
  · intro y
    rw [← hqeq, hev y, hdeltaPhys]
    congr 1
    funext t
    exact (hangle t).symm
  · rw [← hqeq, hperim, hdeltaPhys]

/-- Local approximate pullback transport constructs every aligned finite
physical rear witness.  Only turning-one of each actual finite front is
retained. -/
theorem finitePullbackKinematics_of_localTransport_and_turning
    {kh : ℝ} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K P0 P1 G1 Cg c dlt Mtotal : ℝ}
    (hK : 1 ≤ K) (hc : 0 < c) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hmap : ∀ (p q : Data) (Gamma : PathMetric.NormalPath p q),
      IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        P0 P1 kh G1 Cg Gamma →
      cost Gamma ≤ Mtotal →
      ∀ eps : ℝ, 0 < eps →
        ∃ Delta : PathMetric.NormalPath (SelectedInverseMap.selInv kh p)
            (SelectedInverseMap.selInv kh q),
          cost Delta ≤ K * cost Gamma + eps ∧
          NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
            P0 P1 kh G1 Cg Delta)
    (hdefect : ∀ n : ℕ, ∀ eps : ℝ, 0 < eps →
      ∃ Lambda : PathMetric.NormalPath (Q n)
          (SelectedInverseMap.selInv kh (Q (n + 1))),
        cost Lambda ≤ d n + eps ∧
        NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
          P0 P1 kh G1 Cg Lambda)
    (hmem : ∀ n k, IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n k))
    (hcap : ∀ n k, K ^ k * d (n + k) < Mtotal)
    (hturn : ∀ n k, ∃ Theta Kappa : ℝ → ℝ,
      (∀ s, HasDerivAt
        (ev (TubePullbackLimit.pullback
          (SelectedInverseMap.selInv kh) Q (n + 1) k))
        (Complex.exp (Complex.I * (Theta s : ℂ))) s) ∧
      (∀ s, HasDerivAt Theta (Kappa s) s) ∧
      (∀ s, Theta
          (s + perim (TubePullbackLimit.pullback
            (SelectedInverseMap.selInv kh) Q (n + 1) k)) =
        Theta s + 2 * Real.pi)) :
    PathMetric.FinitePullbackPhysicalRearKinematics kh
      (fun n k => TubePullbackLimit.pullback
        (SelectedInverseMap.selInv kh) Q n k) := by
  have hub := LocalPullbackEndpointCurvature.pullback_front_orientedCurvature_le
    hK hmap hdefect hmem hcap
  refine ⟨?_⟩
  intro n k
  rw [TubePullbackLimit.pullback_succ]
  exact exists_kinematics_selInv_of_curvature_turning
    hc hkh0 hkh1 (hmem (n + 1) k) (hub n k) (hturn n k)

end FinitePullbackPhysicalRearKinematicsConstructor
