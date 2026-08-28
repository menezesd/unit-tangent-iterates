import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence
import UnitTangentIterates.SteeringNormalizedPeriodC1
import UnitTangentIterates.ArclengthInverse

/-! # Taylor-free exact selection for an arbitrary successor front -/

noncomputable section

open Function Set RearTrack RearOwnArclength RearOwnHigherRegularity

namespace FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport

variable {p q : MarkedSpace.Data} {Gamma : PathMetric.NormalPath p q}
  {P0 kh khat Qmax kap periodLower periodUpper Md MP : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}

theorem curvature_periodic (t : ℝ) :
    Periodic (curvature A t) (period A t) := by
  intro s
  have hl := ((MarkingAwareSource.successorFrontCore A).angle_frenet t
    (s + period A t)).comp s ((hasDerivAt_id s).add_const (period A t))
  have hr := ((MarkingAwareSource.successorFrontCore A).angle_frenet t s).const_add
    (2 * Real.pi)
  have heq : angle A t ∘ (fun y => id y + period A t) =
      fun y => 2 * Real.pi + angle A t y := by
    funext y
    simp only [Function.comp_apply, id_eq]
    rw [(MarkingAwareSource.successorFrontCore A).angle_periodic t y]
    ring
  rw [heq] at hl
  simpa using hl.unique hr

theorem curvatureTime_eq (t s : ℝ) :
    partialTime (curvature A) t s = A.kT t s :=
  (hasDerivAt_partialTime
    (A.rear_curvature_contDiff.differentiable (by norm_num)) t s).unique
      (A.rear_curvature_time_deriv t s)

/-- Joint C1 curvature and moving period produce the exact selected steering
and inverse required by the generic pretransport.  The only quantitative
inputs are compact uniform bounds on the normalized time derivative and the
period derivative, as in the Taylor-free Green theorem. -/
theorem exists_exactSelected
    (hperiodLower : 0 < periodLower)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hPl : ∀ t, periodLower ≤ period A t)
    (hPu : ∀ t, period A t ≤ periodUpper)
    (hKle : ∀ t s, curvature A t s ≤ kap)
    (hKnTbd : ∀ t u,
      |partialTime
        (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
          (curvature A) (period A)) t u| ≤ Md)
    (hPtbd : ∀ t,
      |SteeringVariablePeriodSelectedInverseJointC1.periodTime (period A) t| ≤ MP) :
    Nonempty (ExactSelected A (kap := kap)) := by
  have hPC : ContDiff ℝ 1 (period A) := by
    simpa [period] using SelInvDriftRigidity.contDiff_rearPeriod
      A.steering_contDiff A.period_contDiff
  obtain ⟨delta, sf, hper, hstrip, hsteer, hinv, hdeltaC, hsfC, htimeS⟩ :=
    SteeringNormalizedPeriodC1.exists_physical_selected_with_inverse_of_contDiff_one
      hperiodLower hkap0 hkap1 hPl hPu A.rear_curvature_contDiff hPC
      (curvature_periodic (A := A))
      (MarkingAwareSource.successorFrontCore A).curvature_nonnegative hKle
      hKnTbd hPtbd
  have hsfDeriv : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (delta t (sf t x))) x := by
    intro t x
    have hdc : Continuous (delta t) := hdeltaC.continuous.comp
      (continuous_const.prodMk continuous_id)
    exact ArclengthInverse.hasDerivAt_of_rightInverse
      (Real.sqrt_pos.mpr (by nlinarith))
      (RearTrack.hasDerivAt_rearArclength hdc)
      (fun s => Shadowing.cos_ge_of_mem_strip
        (hstrip t s).1 (hstrip t s).2)
      (hinv t) x
  exact ⟨
    { delta := delta
      sf := sf
      periodic := hper
      strip_nonnegative := fun t s => (hstrip t s).1
      strip_le := fun t s => (hstrip t s).2
      steering := hsteer
      delta_contDiff := hdeltaC
      sf_contDiff := hsfC
      sf_rightInverse := hinv
      sf_deriv := hsfDeriv
      steeringTime_spatial := by
        intro t s
        convert htimeS t s using 1
        simpa [curvature] using (curvatureTime_eq (A := A) t s).symm }⟩

end FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1
