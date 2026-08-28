import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource

/-!
# Exact physical `W` before the rear gauge reparametrization

The inverse-Jacobi estimate is exactly nonexpansive in physical arclength.
The later rear gauge is generally nonaffine, so its unweighted normalized
`W` carries a marking-distortion factor.  This file records the exact
variable-period statement at the preceding, rear-own arclength stage.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace MarkedTopology PathMetric
  RearTrack ArclengthInverse

namespace FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource

/-- The pre-gauge rear normal velocity in the normalized unit marking. -/
def normalizedRearDensity
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : ℝ → ℝ → ℝ :=
  fun t u ↦ rearNormal A t (rearPeriod A t * u)

/-- Exact slicewise physical-arclength nonexpansiveness before applying the
nonaffine rear gauge.  Both period factors vary with the time slice. -/
theorem normalizedRearDensity_physicalW_le
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (S : SeparatedFacts A P1) (t : ℝ) :
    rearPeriod A t *
        (∫ u in (0 : ℝ)..1, |normalizedRearDensity A t u|) ≤
      A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u| := by
  have hrearPer : Periodic (rearNormal A t) (rearPeriod A t) := by
    simpa [rearNormal, rearPeriod] using
      RearOwnDriftFundamental.periodic_frameNormal_rearOwn
        A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le
        A.cos_ne_zero A.front_frenet A.angle_frenet A.steering A.sf_deriv
        A.sf_rightInverse A.steering_periodic A.front_periodic
        A.angle_periodic A.front_contDiff A.angle_contDiff
        A.steering_contDiff A.sf_contDiff A.period_contDiff
        A.rear_time_deriv t
  let C := GaugeGeometrySeparatedSliceCertificate.certificate
    (P0 := A.P t) (P1 := A.P t) (kh := kh)
    (P := fun _ ↦ A.P t)
    (delta := fun _ ↦ A.delta t) (K := fun _ ↦ A.K t)
    (etaF := fun _ ↦ A.etaF t) (etaFs := fun _ ↦ S.etaFs t)
    (etaR := fun _ ↦ rearNormal A t) (sf := fun _ ↦ A.sf t)
    (A.period_pos t) A.kh_nonnegative A.kh_lt_one
    (fun _ ↦ le_rfl) (fun _ ↦ le_rfl)
    (fun _ ↦ A.steering t) (fun _ ↦ A.strip_nonnegative t)
    (fun _ ↦ A.strip_le t) (fun _ ↦ A.steering_periodic t)
    (fun _ ↦ A.curvature_le t) (fun _ ↦ S.etaF_deriv t)
    (fun _ ↦ S.etaFs_continuous t) (fun _ ↦ S.etaF_periodic t)
    (fun _ ↦ A.sf_rightInverse t) (fun _ ↦ A.jacobi t)
    (fun _ ↦ hrearPer)
  have hraw := C.w 0
  have hR : 0 < rearPeriod A t := A.rear_period_pos t
  have hchange :
      (∫ x in (0 : ℝ)..rearPeriod A t, |rearNormal A t x|) =
        rearPeriod A t *
          ∫ u in (0 : ℝ)..1, |rearNormal A t (rearPeriod A t * u)| := by
    rw [JacobiNormalized.integral_abs_comp_mul hR.ne' (rearNormal A t)]
    field_simp [hR.ne']
  change
    (∫ x in (0 : ℝ)..rearPeriod A t, |rearNormal A t x|) ≤
      A.P t * (∫ u in (0 : ℝ)..1, |A.etaF t (A.P t * u)|) at hraw
  rw [hchange] at hraw
  simpa [normalizedRearDensity, S.eta_link_affine t] using hraw

end FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW
