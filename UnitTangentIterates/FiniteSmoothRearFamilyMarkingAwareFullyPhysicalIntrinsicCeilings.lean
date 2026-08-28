import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition

/-!
# Intrinsic fixed ceilings for the fully physical Jacobi components

The historical pre-gauge estimate first takes a global upper perimeter and
then differentiates in the unit parameter.  Here the slice certificate is
specialized at its actual front period.  Total turning supplies the uniform
front floor, while selected-inverse arclength supplies the rear floor.  Thus
the inverse damping coefficient is fixed and no perimeter ceiling occurs.
-/

noncomputable section

open Function Set MeasureTheory intervalIntegral MarkedSpace MarkedTopology PathMetric
  RearTrack RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi
  FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource

variable {p q : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax P1 : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}

/-- The total-turning identity and the curvature ceiling force the paper's
front-period floor. -/
theorem frontPeriodFloor_le (hkh : 0 < kh) (t : ℝ) :
    frontPeriodFloor kh ≤ A.P t := by
  have htheta : ContDiff ℝ 1 (A.Theta t) :=
    A.angle_contDiff.comp (contDiff_const.prodMk contDiff_id)
  have heq : deriv (A.Theta t) = A.K t :=
    funext fun s => (A.angle_frenet t s).deriv
  have hKc : Continuous (A.K t) := by
    rw [← heq]
    exact htheta.continuous_deriv (by norm_num)
  have hKint : IntervalIntegrable (A.K t) volume 0 (A.P t) :=
    hKc.intervalIntegrable 0 (A.P t)
  have hturn : (∫ s in (0 : ℝ)..A.P t, A.K t s) = 2 * Real.pi := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => A.angle_frenet t s) hKint]
    have hp := A.angle_periodic t 0
    simp only [zero_add] at hp
    rw [hp]
    ring
  have hupper : (∫ s in (0 : ℝ)..A.P t, A.K t s) ≤
      ∫ _s in (0 : ℝ)..A.P t, kh := by
    refine intervalIntegral.integral_mono_on (A.period_pos t).le hKint
      _root_.intervalIntegrable_const ?_
    exact fun s _ => (le_abs_self (A.K t s)).trans (A.curvature_le t s)
  rw [hturn] at hupper
  have hconst : (∫ _s in (0 : ℝ)..A.P t, kh) = kh * A.P t := by
    simp [mul_comm]
  rw [hconst] at hupper
  rw [frontPeriodFloor, div_le_iff₀ hkh]
  simpa [mul_comm] using hupper

/-- The rear period has the fixed floor appearing in the damping
denominator. -/
theorem rearPeriodFloor_le (hkh : 0 < kh) (t : ℝ) :
    rearPeriodFloor kh ≤ rearPeriod A t := by
  have hc : 0 ≤ Real.sqrt (1 - kh ^ 2) := Real.sqrt_nonneg _
  have hfront := frontPeriodFloor_le (A := A) hkh t
  have hdelta : Continuous (A.delta t) :=
    Differentiable.continuous fun s => (A.steering t s).differentiableAt
  have hcos : ∀ s, Real.sqrt (1 - kh ^ 2) ≤ Real.cos (A.delta t s) :=
    fun s => Shadowing.cos_ge_of_mem_strip
      (A.strip_nonnegative t s) (A.strip_le t s)
  calc
    rearPeriodFloor kh = Real.sqrt (1 - kh ^ 2) * frontPeriodFloor kh := rfl
    _ ≤ Real.sqrt (1 - kh ^ 2) * A.P t :=
      mul_le_mul_of_nonneg_left hfront hc
    _ ≤ rearPeriod A t := by
      exact ArclengthInverse.rearArclength_ge hdelta hcos (A.period_pos t).le

/-- The local inverse damping factor is bounded by one constant depending
only on the curvature cap. -/
theorem inverseDamping_le (hkh : 0 < kh) (t : ℝ) :
    1 / (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * A.P t))) ≤ ceilingC0 kh := by
  have hc : 0 < Real.sqrt (1 - kh ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [A.kh_nonnegative, A.kh_lt_one])
  have hscale : rearPeriodFloor kh ≤ Real.sqrt (1 - kh ^ 2) * A.P t := by
    exact mul_le_mul_of_nonneg_left (frontPeriodFloor_le (A := A) hkh t) hc.le
  have hfloorPos : 0 < rearPeriodFloor kh :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.rearPeriodFloor_pos
      hkh A.kh_lt_one
  have hlocalPos : 0 < Real.sqrt (1 - kh ^ 2) * A.P t :=
    mul_pos hc (A.period_pos t)
  have hexp : Real.exp (-(Real.sqrt (1 - kh ^ 2) * A.P t)) ≤
      Real.exp (-(rearPeriodFloor kh)) :=
    Real.exp_le_exp.mpr (neg_le_neg hscale)
  have hden : 1 - Real.exp (-(rearPeriodFloor kh)) ≤
      1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * A.P t)) := by linarith
  have hdenFloor : 0 < 1 - Real.exp (-(rearPeriodFloor kh)) :=
    JacobiNormalized.one_sub_exp_pos hfloorPos
  have hdenLocal : 0 <
      1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * A.P t)) :=
    JacobiNormalized.one_sub_exp_pos hlocalPos
  rw [ceilingC0]
  exact one_div_le_one_div_of_le hdenFloor hden

/-- The sharp slice certificate uses the actual period at the slice as both
its local lower and upper period. -/
def sliceCertificate (S : SeparatedFacts A P1) (t : ℝ) :
    GaugeGeometrySeparatedSliceCertificate.Certificate
      (fun _ u => A.etaF t (A.P t * u)) (fun _ => rearNormal A t)
      (fun _ => rearPeriod A t)
      (A.P t)
      (A.P t / (1 - Real.exp
        (-(Real.sqrt (1 - kh ^ 2) * A.P t))))
      (A.P t / (1 - Real.exp
        (-(Real.sqrt (1 - kh ^ 2) * A.P t))))
      (1 / Real.sqrt (1 - kh ^ 2))
      (A.P t / (1 - Real.exp
        (-(Real.sqrt (1 - kh ^ 2) * A.P t))))
      (2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
        1 / Real.sqrt (1 - kh ^ 2))
      (1 / (A.P t * Real.sqrt (1 - kh ^ 2) ^ 2)) := by
  simpa [rearPeriod] using
    (GaugeGeometrySeparatedSliceCertificate.certificate
      (P0 := A.P t) (P1 := A.P t) (kh := kh)
      (P := fun _ => A.P t)
      (delta := fun _ => A.delta t) (K := fun _ => A.K t)
      (etaF := fun _ => A.etaF t) (etaFs := fun _ => S.etaFs t)
      (etaR := fun _ => rearNormal A t) (sf := fun _ => A.sf t)
      (A.period_pos t) A.kh_nonnegative A.kh_lt_one
      (fun _ => le_rfl) (fun _ => le_rfl)
      (fun _ => A.steering t) (fun _ => A.strip_nonnegative t)
      (fun _ => A.strip_le t) (fun _ => A.steering_periodic t)
      (fun _ => A.curvature_le t) (fun _ => S.etaF_deriv t)
      (fun _ => S.etaFs_continuous t) (fun _ => S.etaF_periodic t)
      (fun _ => A.sf_rightInverse t) (fun _ => A.jacobi t)
      (fun _ => rearNormal_periodic (A := A) t))

/-- The sharp slicewise certificate integrates to the paper's fully physical
inverse-Jacobi transition.  Unlike the historical pre-gauge transition, the
spatial components are divided by their actual periods, so the three
coefficients depend only on the curvature cap. -/
private def fullyPhysicalAnalyticInputOfSpatial
    {E : Applied Gamma A}
    (N : RearOwnFrameDrift.SpatialC2 (rearNormal A))
    (hkh : 0 < kh)
    (S : SeparatedFacts A P1)
    (F : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable Gamma.eta) :
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.AnalyticInput
      A.P (rearPeriod A) Gamma.eta
        (FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A)
      (ceilingC0 kh) (ceilingC1 kh) (ceilingC2 kh) := by
  let R := FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition.normalizedRearFunctionalIntegrable
    (A := A) (E := E)
  have hPc : Continuous A.P := A.period_contDiff.continuous
  have hRc : Continuous (rearPeriod A) :=
    Differentiable.continuous fun t => (E.frame.period_deriv t).differentiableAt
  have hPinv : Continuous (fun t => (A.P t)⁻¹) :=
    hPc.inv₀ fun t => (A.period_pos t).ne'
  have hRinv : Continuous (fun t => (rearPeriod A t)⁻¹) :=
    hRc.inv₀ fun t => (A.rear_period_pos t).ne'
  have hR2inv : Continuous (fun t => (rearPeriod A t ^ 2)⁻¹) :=
    (hRc.pow 2).inv₀ fun t => (sq_pos_of_pos (A.rear_period_pos t)).ne'
  have hfrontW : IntervalIntegrable
      (fun t => A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) volume 0 1 := by
    simpa [mul_comm] using
      F.w.mul_continuousOn hPc.continuousOn
  have hrearW : IntervalIntegrable
      (fun t => rearPeriod A t *
        ∫ u in (0 : ℝ)..1,
          |FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A t u|)
        volume 0 1 := by
    simpa [mul_comm] using R.w.mul_continuousOn hRc.continuousOn
  have hrearS1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1
        (FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A t)) /
        rearPeriod A t) volume 0 1 := by
    simpa [div_eq_mul_inv] using R.s1.mul_continuousOn hRinv.continuousOn
  have hfrontS1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (Gamma.eta t)) / A.P t)
        volume 0 1 := by
    simpa [div_eq_mul_inv] using F.s1.mul_continuousOn hPinv.continuousOn
  have hrearS2 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 2
        (FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A t)) /
        rearPeriod A t ^ 2) volume 0 1 := by
    simpa [div_eq_mul_inv] using R.s2.mul_continuousOn hR2inv.continuousOn
  have hroot : 0 < Real.sqrt (1 - kh ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith [A.kh_nonnegative, A.kh_lt_one])
  have hc0 : 0 <= ceilingC0 kh := ceilingC0_nonnegative hkh A.kh_lt_one
  have hc11 : 0 <= 1 / Real.sqrt (1 - kh ^ 2) := one_div_nonneg.mpr hroot.le
  have hc21 : 0 <= 2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
      1 / Real.sqrt (1 - kh ^ 2) :=
    add_nonneg
      (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg kh))
        (pow_nonneg hroot.le 3)) hc11
  have hc22 : 0 <= 1 / Real.sqrt (1 - kh ^ 2) ^ 2 :=
    one_div_nonneg.mpr (sq_nonneg _)
  refine
    { frontW_integrable := hfrontW
      rearW_integrable := hrearW
      w := fun t _ =>
        FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity_physicalW_le S t
      rearS0_integrable := R.s0
      frontS0_integrable := F.s0
      s0 := ?_
      rearS1_integrable := hrearS1
      frontS1_integrable := hfrontS1
      s1 := ?_
      rearS2_integrable := hrearS2
      s2 := ?_ }
  · intro t
    have H := (sliceCertificate S t).s0 t
    change supNorm (fun u => rearNormal A t (rearPeriod A t * u)) <= _
    simp only [rearPeriod]
    rw [JacobiNormalized.supNorm_comp_mul
      (by simpa [rearPeriod] using (A.rear_period_pos t).ne') (rearNormal A t)]
    change supNorm (rearNormal A t) <= _
    simp_rw [← S.eta_link_affine t] at H
    have hW : 0 <= A.P t *
        (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) :=
      mul_nonneg (A.period_pos t).le
        (intervalIntegral.integral_nonneg zero_le_one fun _ _ => abs_nonneg _)
    calc
      supNorm (rearNormal A t) <=
          (1 / (1 - Real.exp
            (-(Real.sqrt (1 - kh ^ 2) * A.P t)))) *
            (A.P t * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|)) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using H
      _ <= ceilingC0 kh *
          (A.P t * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|)) :=
        mul_le_mul_of_nonneg_right (inverseDamping_le (A := A) hkh t) hW
  · intro t
    have H := (sliceCertificate S t).separated t |>.s1
    have hRt : 0 <= rearPeriod A t := (A.rear_period_pos t).le
    have hW : 0 <= A.P t *
        (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) :=
      mul_nonneg (A.period_pos t).le
        (intervalIntegral.integral_nonneg zero_le_one fun _ _ => abs_nonneg _)
    have hS0 : 0 <= supNorm (Gamma.eta t) := supNorm_nonneg _
    change supNorm (iteratedDeriv 1
      (fun u => rearNormal A t (rearPeriod A t * u))) /
        rearPeriod A t <= _
    simp only [rearPeriod]
    rw [JacobiNormalized.iteratedDeriv_one_comp_mul
        (L := rearArclength (A.delta t) (A.P t)) (N.deriv1 t),
      JacobiNormalized.supNorm_const_mul (by simpa [rearPeriod] using hRt),
      JacobiNormalized.supNorm_comp_mul
        (by simpa [rearPeriod] using (A.rear_period_pos t).ne') (N.xi1 t),
      mul_div_cancel_left₀ _ (by simpa [rearPeriod] using (A.rear_period_pos t).ne')]
    have hd1 : deriv (rearNormal A t) = N.xi1 t :=
      funext fun x => (N.deriv1 t x).deriv
    rw [<- hd1]
    simp_rw [← S.eta_link_affine t] at H
    change supNorm (deriv (rearNormal A t)) <=
      (A.P t / (1 - Real.exp
        (-(Real.sqrt (1 - kh ^ 2) * A.P t)))) *
          (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
        (1 / Real.sqrt (1 - kh ^ 2)) * supNorm (Gamma.eta t) at H
    have h0 : 1 / (1 - Real.exp
        (-(Real.sqrt (1 - kh ^ 2) * A.P t))) <= ceilingC0 kh :=
      inverseDamping_le (A := A) hkh t
    have h1 : ceilingC0 kh <= ceilingC1 kh := le_max_left _ _
    have h2 : 1 / Real.sqrt (1 - kh ^ 2) <= ceilingC1 kh := le_max_right _ _
    calc
      supNorm (deriv (rearNormal A t)) <= _ := H
      _ = (1 / (1 - Real.exp
            (-(Real.sqrt (1 - kh ^ 2) * A.P t)))) *
            (A.P t * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|)) +
          (1 / Real.sqrt (1 - kh ^ 2)) * supNorm (Gamma.eta t) := by ring
      _ <= ceilingC1 kh *
            (A.P t * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|)) +
          ceilingC1 kh * supNorm (Gamma.eta t) :=
        add_le_add
          (mul_le_mul_of_nonneg_right (h0.trans h1) hW)
          (mul_le_mul_of_nonneg_right h2 hS0)
      _ = ceilingC1 kh * (A.P t *
            (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
          supNorm (Gamma.eta t)) := by ring
  · intro t
    have H := (sliceCertificate S t).separated t |>.s2
    have hRt2 : 0 <= rearPeriod A t ^ 2 := sq_nonneg _
    have hW : 0 <= A.P t *
        (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) :=
      mul_nonneg (A.period_pos t).le
        (intervalIntegral.integral_nonneg zero_le_one fun _ _ => abs_nonneg _)
    have hS0 : 0 <= supNorm (Gamma.eta t) := supNorm_nonneg _
    have hS1 : 0 <= supNorm (iteratedDeriv 1 (Gamma.eta t)) / A.P t :=
      div_nonneg (supNorm_nonneg _) (A.period_pos t).le
    change supNorm (iteratedDeriv 2
      (fun u => rearNormal A t (rearPeriod A t * u))) /
        rearPeriod A t ^ 2 <= _
    simp only [rearPeriod]
    rw [JacobiNormalized.iteratedDeriv_two_comp_mul
        (L := rearArclength (A.delta t) (A.P t)) (N.deriv1 t) (N.deriv2 t),
      JacobiNormalized.supNorm_const_mul (by simpa [rearPeriod] using hRt2),
      JacobiNormalized.supNorm_comp_mul
        (by simpa [rearPeriod] using (A.rear_period_pos t).ne') (N.xi2 t),
      mul_div_cancel_left₀ _ (by
        simpa [rearPeriod] using (sq_pos_of_pos (A.rear_period_pos t)).ne')]
    have hd1 : deriv (rearNormal A t) = N.xi1 t :=
      funext fun x => (N.deriv1 t x).deriv
    have hd2 : deriv (deriv (rearNormal A t)) = N.xi2 t := by
      rw [hd1]
      exact funext fun x => (N.deriv2 t x).deriv
    rw [<- hd2]
    simp_rw [← S.eta_link_affine t] at H
    have h0 : 1 / (1 - Real.exp
        (-(Real.sqrt (1 - kh ^ 2) * A.P t))) <= ceilingC2 kh :=
      (inverseDamping_le (A := A) hkh t).trans
        (le_max_left _ _)
    have h1 : 2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
        1 / Real.sqrt (1 - kh ^ 2) <= ceilingC2 kh :=
      (le_max_left _ _).trans (le_max_right _ _)
    have h2 : 1 / Real.sqrt (1 - kh ^ 2) ^ 2 <= ceilingC2 kh :=
      (le_max_right _ _).trans (le_max_right _ _)
    have hfirst :
        A.P t / (1 - Real.exp
            (-(Real.sqrt (1 - kh ^ 2) * A.P t))) *
              (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) <=
          ceilingC2 kh *
            (A.P t * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|)) := by
      calc
        _ = (1 / (1 - Real.exp
              (-(Real.sqrt (1 - kh ^ 2) * A.P t)))) *
              (A.P t * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|)) := by ring
        _ <= _ := mul_le_mul_of_nonneg_right h0 hW
    have hsecond :
        (2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
            1 / Real.sqrt (1 - kh ^ 2)) * supNorm (Gamma.eta t) <=
          ceilingC2 kh * supNorm (Gamma.eta t) :=
      mul_le_mul_of_nonneg_right h1 hS0
    have hthird :
        1 / (A.P t * Real.sqrt (1 - kh ^ 2) ^ 2) *
            supNorm (iteratedDeriv 1 (Gamma.eta t)) <=
          ceilingC2 kh *
            (supNorm (iteratedDeriv 1 (Gamma.eta t)) / A.P t) := by
      calc
        _ = (1 / Real.sqrt (1 - kh ^ 2) ^ 2) *
            (supNorm (iteratedDeriv 1 (Gamma.eta t)) / A.P t) := by
          field_simp [(A.period_pos t).ne']
        _ <= _ := mul_le_mul_of_nonneg_right h2 hS1
    calc
      supNorm (deriv (deriv (rearNormal A t))) <= _ := H
      _ <= (ceilingC2 kh *
            (A.P t * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|)) +
          ceilingC2 kh * supNorm (Gamma.eta t)) +
          ceilingC2 kh *
            (supNorm (iteratedDeriv 1 (Gamma.eta t)) / A.P t) :=
        add_le_add (add_le_add hfirst hsecond) hthird
      _ = ceilingC2 kh * (A.P t *
            (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
          supNorm (Gamma.eta t) +
          supNorm (iteratedDeriv 1 (Gamma.eta t)) / A.P t) := by ring

def fullyPhysicalAnalyticInput
    {E : Applied Gamma A}
    (hkh : 0 < kh)
    (S : SeparatedFacts A P1)
    (F : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable Gamma.eta) :
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.AnalyticInput
      A.P (rearPeriod A) Gamma.eta
        (FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A)
      (ceilingC0 kh) (ceilingC1 kh) (ceilingC2 kh) := by
  cases A.frame_regularity with
  | joint hYdot hangle =>
      exact fullyPhysicalAnalyticInputOfSpatial (E := E)
        (RearOwnFrameDrift.SpatialC2.ofContDiff
          (RearOwnTangential.contDiff_frameNormal hYdot hangle)) hkh S F
  | spatial R =>
      exact fullyPhysicalAnalyticInputOfSpatial (E := E) R.normal hkh S F

/-- The intrinsic Jacobi part of every separated marking-aware row is a
fixed-coefficient transition between its fully physical front and rear
component vectors.  Marking comparisons can compose with this result without
reopening the slice estimates. -/
noncomputable def fullyPhysicalTransition
    {E : Applied Gamma A}
    (hkh : 0 < kh)
    (S : SeparatedFacts A P1)
    (F : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable Gamma.eta) :=
  (fullyPhysicalAnalyticInput (E := E) hkh S F).toRawBounds.toTransition

end FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings
