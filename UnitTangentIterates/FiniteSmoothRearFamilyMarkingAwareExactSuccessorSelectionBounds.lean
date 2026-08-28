import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSuccessorFront
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1
import UnitTangentIterates.SteeringVariablePeriodSelectedInverseJointC1
import UnitTangentIterates.StoppedPeriodicUniformBound
import UnitTangentIterates.SelInvPerimBound

/-!
# Fresh selection bounds retained by an exact source

The derivative bounds consumed when selecting a source belong to its
predecessor.  Recursive use therefore needs fresh bounds for the successor
front canonically carried by the newly assembled source.  This module packages
those source-tied bounds and supplies their compactness construction from
joint `C¹`, spatial periodicity, and exact stopping.
-/

noncomputable section

open Function Set MarkedSpace PathMetric RearOwnHigherRegularity

namespace FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront

/-- Finite quantitative data for applying the Taylor-free selected-steering
construction to the intrinsic successor front of `A`. -/
structure SelectionBounds
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : Type where
  periodLower : ℝ
  periodUpper : ℝ
  Md : ℝ
  MP : ℝ
  periodLower_pos : 0 < periodLower
  period_lower : ∀ t, periodLower ≤ period A t
  period_upper : ∀ t, period A t ≤ periodUpper
  Md_nonnegative : 0 ≤ Md
  MP_nonnegative : 0 ≤ MP
  normalizedCurvatureTime_le : ∀ t u,
    |partialTime
      (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
        (curvature A) (period A)) t u| ≤ Md
  periodTime_le : ∀ t,
    |SteeringVariablePeriodSelectedInverseJointC1.periodTime (period A) t| ≤ MP

/-- Compactness construction of fresh derivative envelopes.  Stopping is
stated on the actual derivative fields, avoiding any false inference from the
bounds consumed by the preceding selection. -/
theorem SelectionBounds.ofStoppedC1
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {periodLower periodUpper : ℝ}
    (hperiodLowerPos : 0 < periodLower)
    (hperiodLower : ∀ t, periodLower ≤ period A t)
    (hperiodUpper : ∀ t, period A t ≤ periodUpper)
    (hKnC1 : ContDiff ℝ 1 (uncurry
      (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
        (curvature A) (period A))))
    (hKnper : ∀ t, Periodic
      (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
        (curvature A) (period A) t) 1)
    (hKnstop : ∀ t ∉ Icc (0 : ℝ) Gamma.T,
      partialTime
        (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
          (curvature A) (period A)) t = fun _ ↦ 0)
    (hperiodC1 : ContDiff ℝ 1 (period A))
    (hPtstop : ∀ t ∉ Icc (0 : ℝ) Gamma.T,
      SteeringVariablePeriodSelectedInverseJointC1.periodTime (period A) t = 0) :
    Nonempty (SelectionBounds A) := by
  let Kn := SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
    (curvature A) (period A)
  have hKnTC : Continuous (uncurry (partialTime Kn)) :=
    (contDiff_partialTime_self (n := 0) hKnC1).continuous
  have hKnTper : ∀ t, Periodic (partialTime Kn t) 1 := fun t ↦
    SteeringVariablePeriodSelectedInverseJointC1.partialTime_periodic_of_periodic
      hKnC1 hKnper t
  obtain ⟨Md, hMd0, hMd⟩ := StoppedPeriodicUniformBound.exists_bound
    Gamma.T_pos.le hKnTC hKnTper hKnstop
  have hPtC : Continuous
      (SteeringVariablePeriodSelectedInverseJointC1.periodTime (period A)) := by
    simpa [SteeringVariablePeriodSelectedInverseJointC1.periodTime] using
      hperiodC1.continuous_deriv (by norm_num : (1 : WithTop ℕ∞) ≤ 1)
  obtain ⟨MP, hMP0, hMP⟩ := StoppedPeriodicUniformBound.exists_bound_time
    Gamma.T_pos.le hPtC hPtstop
  exact ⟨⟨periodLower, periodUpper, Md, MP, hperiodLowerPos,
    hperiodLower, hperiodUpper, hMd0, hMP0, hMd, hMP⟩⟩

/-- For an exact source, all fresh-bound hypotheses except stopping follow
from its stored `C¹` and selected-inverse geometry.  The next period floor is
the sharp strip floor `sqrt (1-kh²) * P0`, and its ceiling is the source's
stored rear-period ceiling `Qmax`. -/
theorem SelectionBounds.ofExactSourceStopped
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (hP0 : 0 < P0)
    (hPl : ∀ t, P0 ≤ A.P t)
    (hKnstop : ∀ t ∉ Icc (0 : ℝ) Gamma.T,
      partialTime
        (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
          (curvature A) (period A)) t = fun _ ↦ 0)
    (hPtstop : ∀ t ∉ Icc (0 : ℝ) Gamma.T,
      SteeringVariablePeriodSelectedInverseJointC1.periodTime (period A) t = 0) :
    Nonempty (SelectionBounds A) := by
  have hperiodC1 : ContDiff ℝ 1 (period A) := by
    have hRA := RearOwnHigherRegularity.contDiff_rearArclengthFamily
      (n := 1) A.steering_contDiff
    exact hRA.comp (contDiff_id.prodMk A.period_contDiff)
  have hKnC1 : ContDiff ℝ 1 (uncurry
      (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
        (curvature A) (period A))) := by
    have hmap : ContDiff ℝ 1 (fun z : ℝ × ℝ ↦
        (z.1, period A z.1 * z.2)) :=
      contDiff_fst.prodMk ((hperiodC1.comp contDiff_fst).mul contDiff_snd)
    simpa only [SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature,
      Function.uncurry_apply_pair] using
      A.rear_curvature_contDiff.comp hmap
  have hKnper : ∀ t, Periodic
      (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
        (curvature A) (period A) t) 1 := fun t ↦
    SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature_periodic
      (fun r ↦
        FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1.curvature_periodic
          (A := A) r) t
  have hsqrt : 0 < Real.sqrt (1 - kh ^ 2) := by
    exact Real.sqrt_pos.2 (by
      nlinarith [A.kh_nonnegative, A.kh_lt_one])
  have hperiodLower : ∀ t,
      Real.sqrt (1 - kh ^ 2) * P0 ≤ period A t := by
    intro t
    refine (mul_le_mul_of_nonneg_left (hPl t) hsqrt.le).trans ?_
    exact PinchedPath.mul_le_rearArclength (A.period_pos t).le
      (A.steering_contDiff.continuous.comp
        (continuous_const.prodMk continuous_id))
      (fun s ↦ ⟨A.strip_nonnegative t s, A.strip_le t s⟩)
  exact SelectionBounds.ofStoppedC1
    (mul_pos hsqrt hP0) hperiodLower A.rear_period_le hKnC1 hKnper
    hKnstop hperiodC1 hPtstop

end FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds
