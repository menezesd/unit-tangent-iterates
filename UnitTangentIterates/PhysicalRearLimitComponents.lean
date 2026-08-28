import UnitTangentIterates.ConfiguredModelGaugeFamily

/-! # Componentwise construction of the physical rear-limit package

The legacy `PhysicalRearLimitReconstructionFamily` stores one large
existential reconstruction callback.  This file exposes the analytic facts
used by the Frenet and tube-compatibility lemmas as named stage fields, derives
the full rear-arclength inverse package, and then assembles the legacy record.
-/

noncomputable section

open Function Set Filter Topology MarkedSpace

namespace PathMetric

open NormalizedSelectedRearClosure
open NormalizedSteeringPhysicalRescaling

/-- Minimal physical selected-rear data for one limiting orbit edge.
`rear` is the lower orbit level and `front` its unit-tangent successor. -/
structure PhysicalRearLimitStageComponents (rear front : Data) where
  kap : ℝ
  period : ℝ
  theta0 : ℝ
  steering : SteeringData kap
  sf : ℝ → ℝ
  kap_nonnegative : 0 ≤ kap
  kap_lt_one : kap < 1
  period_positive : 0 < period
  curvature_continuous : Continuous steering.K
  arclength_rightInverse : ∀ x,
    RearTrack.rearArclength (deltaPhys steering period) (sf x) = x
  front_frenet : ∀ s, HasDerivAt (ev front)
    (Complex.exp (Complex.I *
      (thetaPhys steering period theta0 s : ℂ))) s
  rear_track : ∀ x, ev rear x = RearTrack.rearTrack (ev front)
    (thetaPhys steering period theta0) (deltaPhys steering period) (sf x)
  rear_perimeter : perim rear =
    RearTrack.rearArclength (deltaPhys steering period) period
  rear_curvature_nonnegative : ∀ x,
    0 ≤ SelectedRearFrenetChain.rearK steering period sf x
  rear_curvature_nonzero : ∃ x,
    SelectedRearFrenetChain.rearK steering period sf x ≠ 0

namespace PhysicalRearLimitStageComponents

/-- The single right-inverse field suffices for all inverse regularity and
periodicity facts needed by the physical rear Frenet calculation. -/
def inverseData {rear front : Data}
    (S : PhysicalRearLimitStageComponents rear front) :
    RearArclengthInverseBridge.Data
      (deltaPhys S.steering S.period) S.sf S.period := by
  have hdeltaC : Continuous (deltaPhys S.steering S.period) :=
    Differentiable.continuous fun s =>
      (hasDerivAt_deltaPhys S.steering S.period_positive s).differentiableAt
  exact RearArclengthInverseBridge.data_of_rightInverse
    S.kap_nonnegative S.kap_lt_one hdeltaC
    (deltaPhys_periodic S.steering)
    (fun s => (deltaPhys_mem S.steering s).1)
    (fun s => (deltaPhys_mem S.steering s).2)
    S.arclength_rightInverse

theorem perimeter_eq_inverseRearPeriod {rear front : Data}
    (S : PhysicalRearLimitStageComponents rear front) :
    perim rear = S.inverseData.rearPeriod := by
  simpa [inverseData, RearArclengthInverseBridge.data_of_rightInverse] using
    S.rear_perimeter

/-- The named component fields assemble exactly the Frenet core consumed by
the successor-tube compatibility lemma. -/
def rearFrenetCore {rear front : Data}
    (S : PhysicalRearLimitStageComponents rear front) :
    SelectedRearFrenetChain.RearFrenetCoreCertificate rear :=
  SelectedRearFrenetChain.rearFrenetCore_of_physicalRear S.steering
    S.kap_nonnegative S.kap_lt_one S.period_positive S.curvature_continuous
    S.inverseData S.front_frenet S.rear_track S.perimeter_eq_inverseRearPeriod
    S.rear_curvature_nonnegative S.rear_curvature_nonzero

/-- A physical selected-rear stage already realizes the front as the
unit-tangent transform of the rear, up to parameterization.  No total forward
map on marked data and no positive uniform curvature pinch are needed. -/
theorem range_front_eq_unitTangent_rear {rear front : Data}
    (S : PhysicalRearLimitStageComponents rear front) :
    range (ev front) = range (UnitTangent.unitTangentMap (ev rear)) := by
  have hsf : Surjective S.sf := by
    intro s
    exact ⟨RearTrack.rearArclength (deltaPhys S.steering S.period) s,
      S.inverseData.leftInverse s⟩
  have hpoint : ∀ x, UnitTangent.unitTangentMap (ev rear) x = ev front (S.sf x) := by
    intro x
    rw [UnitTangent.unitTangentMap,
      (S.rearFrenetCore.curve_deriv x).deriv, S.rear_track x]
    change RearTrack.rearTrack (ev front)
        (thetaPhys S.steering S.period S.theta0)
        (deltaPhys S.steering S.period) (S.sf x) +
      Complex.exp (Complex.I *
        (RearTrack.rearAngle (thetaPhys S.steering S.period S.theta0)
          (deltaPhys S.steering S.period) (S.sf x) : ℂ)) = ev front (S.sf x)
    exact RearTrack.unitTangentMap_rearTrack (s := S.sf x)
  apply Set.Subset.antisymm
  · rintro z ⟨s, rfl⟩
    obtain ⟨x, rfl⟩ := hsf s
    exact ⟨x, hpoint x⟩
  · rintro z ⟨x, rfl⟩
    exact ⟨S.sf x, (hpoint x).symm⟩

/-- Once the successor belongs to the closed tube, the component package
already contains everything needed for strict weak convexity of the rear. -/
def limitStrictness {rear front : Data} {c dlt : ℝ}
    (S : PhysicalRearLimitStageComponents rear front)
    (hc : 0 < c) (hfront : IsTubeMember c 0 dlt front) :
    UnconditionalAssembly.LimitStrictnessData rear :=
  FrontFrenetTubeCompatibility.limitStrictness_of_rearCore_and_successor_tube
    S.steering S.sf S.rearFrenetCore hfront hc S.kap_nonnegative S.kap_lt_one
    S.curvature_continuous S.front_frenet rfl rfl

end PhysicalRearLimitStageComponents

/-- Componentwise physical reconstruction at every simultaneous marked
limit.  The stage record makes each analytic obligation visible by name. -/
structure PhysicalRearLimitComponentFamily (Q : ℕ → ℕ → Data) : Prop where
  stage : ∀ (X : ℕ → Data),
    (∀ n, Tendsto (Q n) atTop (nhds (X n))) → ∀ n,
      Nonempty (PhysicalRearLimitStageComponents (X n) (X (n + 1)))

/-- Assemble the legacy physical-reconstruction boundary from the explicit
stage components. -/
def PhysicalRearLimitComponentFamily.toPhysicalRearLimitReconstructionFamily
    {Q : ℕ → ℕ → Data} (F : PhysicalRearLimitComponentFamily Q) :
    PhysicalRearLimitReconstructionFamily Q where
  reconstruct := by
    intro X hX n
    let S := Nonempty.some (F.stage X hX n)
    refine ⟨S.kap, S.period, S.theta0, S.steering, S.sf,
      S.kap_nonnegative, S.kap_lt_one, S.period_positive,
      S.curvature_continuous, ?_⟩
    exact ⟨S.inverseData, S.front_frenet, S.rear_track,
      S.perimeter_eq_inverseRearPeriod,
      S.rear_curvature_nonnegative, S.rear_curvature_nonzero⟩

/-- Direct strictness consequence of the componentwise family. -/
def PhysicalRearLimitComponentFamily.limitStrictness
    {Q : ℕ → ℕ → Data} {c dlt : ℝ}
    (F : PhysicalRearLimitComponentFamily Q) (hc : 0 < c)
    (htube : ∀ n k, IsTubeMember c 0 dlt (Q n k)) :
    ∀ (X : ℕ → Data), (∀ n, Tendsto (Q n) atTop (nhds (X n))) →
      ∀ n, UnconditionalAssembly.LimitStrictnessData (X n) :=
  F.toPhysicalRearLimitReconstructionFamily.limitStrictness hc htube

end PathMetric
