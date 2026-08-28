import UnitTangentIterates.PhysicalRearLimitComponents

/-!
# Physical rear components from kinematic closure

This module isolates the exact compactness statement still needed to pass the
finite selected-rear formulas to simultaneous marked limits.  The residual
retains only the limiting steering, inverse-arclength, and front/rear
identities.  Positivity of the period and both rear-curvature fields are
derived from the closed tube and the fixed selected strip.
-/

noncomputable section

open Function Set Filter Topology MarkedSpace

namespace PathMetric

open NormalizedSelectedRearClosure
open NormalizedSteeringPhysicalRescaling

/-- Kinematic data for one physical selected-rear edge.  The physical period
is fixed to the perimeter of the front, as in the finite-stage construction.
`steering_nonzero` is the sole quantitative noncollapse fact retained at the
limit. -/
structure PhysicalRearLimitKinematics (kh : ℝ) (rear front : Data) where
  theta0 : ℝ
  steering : SteeringData kh
  sf : ℝ → ℝ
  curvature_continuous : Continuous steering.K
  arclength_rightInverse : ∀ x,
    RearTrack.rearArclength (deltaPhys steering (perim front)) (sf x) = x
  front_frenet : ∀ s, HasDerivAt (ev front)
    (Complex.exp (Complex.I *
      (thetaPhys steering (perim front) theta0 s : ℂ))) s
  rear_track : ∀ x, ev rear x = RearTrack.rearTrack (ev front)
    (thetaPhys steering (perim front) theta0)
    (deltaPhys steering (perim front)) (sf x)
  rear_perimeter : perim rear =
    RearTrack.rearArclength (deltaPhys steering (perim front)) (perim front)
  steering_nonzero : ∃ x, deltaPhys steering (perim front) (sf x) ≠ 0

namespace PhysicalRearLimitKinematics

/-- All algebraic and Frenet fields of a physical rear stage follow from the
kinematic limit, the fixed selected strip, and closed-tube membership of the
front. -/
def toStageComponents
    {kh c dlt : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hfront : IsTubeMember c 0 dlt front) :
    PhysicalRearLimitStageComponents rear front := by
  have hP : 0 < perim front := perim_pos hc hfront
  refine
    { kap := kh
      period := perim front
      theta0 := K.theta0
      steering := K.steering
      sf := K.sf
      kap_nonnegative := hkh0
      kap_lt_one := hkh1
      period_positive := hP
      curvature_continuous := K.curvature_continuous
      arclength_rightInverse := K.arclength_rightInverse
      front_frenet := K.front_frenet
      rear_track := K.rear_track
      rear_perimeter := K.rear_perimeter
      rear_curvature_nonnegative := ?_
      rear_curvature_nonzero := ?_ }
  · intro x
    have hm := deltaPhys_mem K.steering (P := perim front) (K.sf x)
    exact RearTrack.rear_curvature_nonneg hkh1 hkh0 hm.1 hm.2
  · obtain ⟨x, hx⟩ := K.steering_nonzero
    refine ⟨x, ?_⟩
    have hm := deltaPhys_mem K.steering (P := perim front) (K.sf x)
    have hdelta : 0 < deltaPhys K.steering (perim front) (K.sf x) :=
      lt_of_le_of_ne hm.1 hx.symm
    have harc : Real.arcsin kh < Real.pi / 2 := by
      rw [show Real.pi / 2 = Real.arcsin 1 by simp [Real.arcsin_one]]
      exact Real.arcsin_lt_arcsin (by linarith) hkh1 (le_refl 1)
    exact ne_of_gt (Real.tan_pos_of_pos_of_lt_pi_div_two hdelta
      (lt_of_le_of_lt hm.2 harc))

end PhysicalRearLimitKinematics

/-- Finite pullback edges carry the exact physical selected-rear kinematics.
This is the input furnished by the finite selected-rear formulas before taking
the simultaneous limit. -/
structure FinitePhysicalRearKinematics
    (kh : ℝ) (Q : ℕ → ℕ → Data) : Prop where
  stage : ∀ n k, Nonempty
    (PhysicalRearLimitKinematics kh (Q n k) (Q (n + 1) k))

/-- **Minimal remaining compactness residual.**  If every finite edge carries
the exact kinematic package and both rows converge in marked `Data`, then those
kinematic witnesses admit a limiting package.  Proving this field requires the
currently unexported common subsequence/uniform convergence theorem for the
normalized steering lifts and inverse rear-arclength maps. -/
structure PhysicalRearKinematicClosureResidual
    (kh : ℝ) (Q : ℕ → ℕ → Data) : Prop where
  closed : ∀ (X : ℕ → Data),
    (∀ n, Tendsto (Q n) atTop (nhds (X n))) →
    (∀ n k, Nonempty
      (PhysicalRearLimitKinematics kh (Q n k) (Q (n + 1) k))) →
    ∀ n, Nonempty (PhysicalRearLimitKinematics kh (X n) (X (n + 1)))

/-- Kinematic closure plus the finite selected-rear formulas constructs the
full component family consumed by the approximate paper assembly.  Closed-tube
membership passes to each limit by closedness; every remaining stage field is
then discharged by `PhysicalRearLimitKinematics.toStageComponents`. -/
theorem physicalRearLimitComponentFamily_of_kinematicClosure
    {kh c dlt : ℝ} {Q : ℕ → ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (htube : ∀ n k, IsTubeMember c 0 dlt (Q n k))
    (finite : FinitePhysicalRearKinematics kh Q)
    (closure : PhysicalRearKinematicClosureResidual kh Q) :
    PhysicalRearLimitComponentFamily Q := by
  refine ⟨?_⟩
  intro X hX n
  have hfront : IsTubeMember c 0 dlt (X (n + 1)) :=
    (isClosed_tube c 0 dlt).mem_of_tendsto (hX (n + 1))
      (Eventually.of_forall (htube (n + 1)))
  let K := Nonempty.some (closure.closed X hX finite.stage n)
  exact ⟨K.toStageComponents hkh0 hkh1 hc hfront⟩

end PathMetric

