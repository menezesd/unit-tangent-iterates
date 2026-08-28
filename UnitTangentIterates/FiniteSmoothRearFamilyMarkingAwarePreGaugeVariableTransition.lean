import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW
import UnitTangentIterates.MarkingAwareSourceSelectedRearData
import UnitTangentIterates.VariableArclengthScaledJacobiTransition
import UnitTangentIterates.PeriodicSupNormFunctionalIntegrable

/-!
# Variable-period transition data before the rear gauge

The rear-own family is normalized affinely on each time slice.  This produces
canonical endpoint `Data` and the exact physical Jacobi estimates.  It is not
asserted to be a `NormalPath`: before the rear gauge its time velocity generally
has a tangential component.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace MarkedTopology PathMetric
  RearTrack RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition

open ControlledJunctionPathFunctionalBounds
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  PeriodicSupNormFunctionalIntegrable
  VariableArclengthScaledJacobiTransition

variable {p q : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax P1 : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}

/-- The canonical affine-arclength rear data at a time slice. -/
def affineRearData (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) : Data :=
  A.selectedRearData t

@[simp] theorem affineRearData_perim (t : ℝ) :
    perim (affineRearData A t) = rearPeriod A t :=
  A.selectedRearData_perim t

theorem affineRearData_range (t : ℝ) :
    range (affineRearData A t).1 =
      range (rearOwn A.F A.Theta A.delta A.sf t) := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨rearPeriod A t * u, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨x / rearPeriod A t, ?_⟩
    simp only [affineRearData, MarkingAwareSource.selectedRearData_curve,
      MarkingAwareSource.selectedRearCurve]
    congr 1
    exact mul_div_cancel₀ x (A.rear_period_pos t).ne'

/-- First normalized spatial derivative of the pre-gauge density. -/
def normalizedRearDensity1
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : ℝ → ℝ → ℝ :=
  fun t u ↦ rearPeriod A t *
    deriv (rearNormal A t) (rearPeriod A t * u)

/-- Second normalized spatial derivative of the pre-gauge density. -/
def normalizedRearDensity2
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : ℝ → ℝ → ℝ :=
  fun t u ↦ rearPeriod A t ^ 2 *
    deriv (deriv (rearNormal A t)) (rearPeriod A t * u)

theorem normalizedRearDensity_deriv
    (N : RearOwnFrameDrift.SpatialC2 (rearNormal A)) (t u : ℝ) :
    HasDerivAt (normalizedRearDensity A t) (normalizedRearDensity1 A t u) u := by
  have hs : HasDerivAt (fun v : ℝ ↦ rearPeriod A t * v) (rearPeriod A t) u := by
    simpa using (hasDerivAt_id u).const_mul (rearPeriod A t)
  have h := (N.deriv1 t (rearPeriod A t * u)).comp u hs
  simpa only [normalizedRearDensity, normalizedRearDensity1,
    (N.deriv1 t _).deriv, mul_comm] using h

theorem normalizedRearDensity1_deriv
    (N : RearOwnFrameDrift.SpatialC2 (rearNormal A)) (t u : ℝ) :
    HasDerivAt (normalizedRearDensity1 A t) (normalizedRearDensity2 A t u) u := by
  have hs : HasDerivAt (fun v : ℝ ↦ rearPeriod A t * v) (rearPeriod A t) u := by
    simpa using (hasDerivAt_id u).const_mul (rearPeriod A t)
  have h := ((N.deriv2 t (rearPeriod A t * u)).comp u hs).const_mul
    (rearPeriod A t)
  have hd1 : deriv (rearNormal A t) = N.xi1 t :=
    funext fun x ↦ (N.deriv1 t x).deriv
  have hd2 : deriv (deriv (rearNormal A t)) = N.xi2 t := by
    rw [hd1]
    exact funext fun x ↦ (N.deriv2 t x).deriv
  have hd2N : deriv (N.xi1 t) = N.xi2 t :=
    funext fun x ↦ (N.deriv2 t x).deriv
  change HasDerivAt
    (fun y ↦ rearPeriod A t * deriv (rearNormal A t) (rearPeriod A t * y))
    (rearPeriod A t ^ 2 *
      deriv (deriv (rearNormal A t)) (rearPeriod A t * u)) u
  rw [hd1, hd2N]
  convert h using 1 <;> ring

theorem rearNormal_periodic (t : ℝ) :
    Periodic (rearNormal A t) (rearPeriod A t) := by
  simpa [rearNormal, rearPeriod] using
    RearOwnDriftFundamental.periodic_frameNormal_rearOwn
      A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le
      A.cos_ne_zero A.front_frenet A.angle_frenet A.steering A.sf_deriv
      A.sf_rightInverse A.steering_periodic A.front_periodic
      A.angle_periodic A.front_contDiff A.angle_contDiff
      A.steering_contDiff A.sf_contDiff A.period_contDiff
      A.rear_time_deriv t

theorem normalizedRearDensity_periodic (t : ℝ) :
    Periodic (normalizedRearDensity A t) 1 := by
  intro u
  simpa [normalizedRearDensity, mul_add] using
    rearNormal_periodic (A := A) t (rearPeriod A t * u)

/-- Functional integrability of the affine-normalized rear density follows
from the joint spatial certificate and the retained differentiability of its
time-dependent period. -/
private def normalizedRearFunctionalIntegrableOfSpatial
    {E : Applied Gamma A} (N : RearOwnFrameDrift.SpatialC2 (rearNormal A)) :
    FunctionalIntegrable (normalizedRearDensity A) := by
  have hR : Continuous (rearPeriod A) :=
    Differentiable.continuous fun t ↦ (E.frame.period_deriv t).differentiableAt
  have hpair : Continuous (fun z : ℝ × ℝ ↦
      (z.1, rearPeriod A z.1 * z.2)) :=
    continuous_fst.prodMk ((hR.comp continuous_fst).mul continuous_snd)
  have hderiv1 : ∀ t, deriv (rearNormal A t) = N.xi1 t :=
    fun t ↦ funext fun x ↦ (N.deriv1 t x).deriv
  have hderiv2 : ∀ t, deriv (deriv (rearNormal A t)) = N.xi2 t := by
    intro t
    rw [hderiv1 t]
    exact funext fun x ↦ (N.deriv2 t x).deriv
  have hc0 : Continuous (uncurry (normalizedRearDensity A)) := by
    simpa [normalizedRearDensity, uncurry] using N.continuous0.comp hpair
  have hc1 : Continuous (uncurry (normalizedRearDensity1 A)) := by
    exact ((hR.comp continuous_fst).mul (N.continuous1.comp hpair)).congr
      fun z ↦ by simp [normalizedRearDensity1, uncurry, hderiv1]
  have hc2 : Continuous (uncurry (normalizedRearDensity2 A)) := by
    exact (((hR.comp continuous_fst).pow 2).mul (N.continuous2.comp hpair)).congr
      fun z ↦ by
        simp [normalizedRearDensity2, uncurry, hderiv2]
  have hd1 : ∀ t, iteratedDeriv 1 (normalizedRearDensity A t) =
      normalizedRearDensity1 A t := by
    intro t
    rw [iteratedDeriv_one]
    funext u
    exact (normalizedRearDensity_deriv (A := A) N t u).deriv
  have hd2 : ∀ t, iteratedDeriv 2 (normalizedRearDensity A t) =
      normalizedRearDensity2 A t := by
    intro t
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, hd1 t]
    funext u
    exact (normalizedRearDensity1_deriv (A := A) N t u).deriv
  have hp1 : ∀ t, Periodic (normalizedRearDensity1 A t) 1 := fun t ↦
    ArclengthInverse.periodic_of_hasDerivAt
      (normalizedRearDensity_deriv (A := A) N t)
      (normalizedRearDensity_periodic (A := A) t)
  have hp2 : ∀ t, Periodic (normalizedRearDensity2 A t) 1 := fun t ↦
    ArclengthInverse.periodic_of_hasDerivAt
      (normalizedRearDensity1_deriv (A := A) N t) (hp1 t)
  refine
    { w := (continuous_L1_density_of_joint_continuous hc0).intervalIntegrable 0 1
      s0 := (continuous_supNorm_of_joint_continuous_periodic one_pos hc0
        (normalizedRearDensity_periodic (A := A))).intervalIntegrable 0 1
      s1 := ?_
      s2 := ?_ }
  · simpa only [hd1] using
      (continuous_supNorm_of_joint_continuous_periodic one_pos hc1 hp1).intervalIntegrable 0 1
  · simpa only [hd2] using
      (continuous_supNorm_of_joint_continuous_periodic one_pos hc2 hp2).intervalIntegrable 0 1

def normalizedRearFunctionalIntegrable
    {E : Applied Gamma A} : FunctionalIntegrable (normalizedRearDensity A) := by
  cases A.frame_regularity with
  | joint hYdot hangle =>
      exact normalizedRearFunctionalIntegrableOfSpatial (E := E)
        (RearOwnFrameDrift.SpatialC2.ofContDiff
          (RearOwnTangential.contDiff_frameNormal hYdot hangle))
  | spatial S => exact normalizedRearFunctionalIntegrableOfSpatial (E := E) S.normal

private def sliceCertificate (S : SeparatedFacts A P1) :=
  GaugeGeometrySeparatedSliceCertificate.certificate
    S.P0_pos A.kh_nonnegative A.kh_lt_one S.period_lower S.period_upper
    A.steering A.strip_nonnegative A.strip_le A.steering_periodic A.curvature_le
    S.etaF_deriv S.etaFs_continuous S.etaF_periodic A.sf_rightInverse A.jacobi
    (rearNormal_periodic (A := A))

/-- Coarse zeroth-order coefficient in the variable physical scale. -/
def preGaugeC0 (P0 P1 kh : ℝ) : ℝ :=
  P1 / (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0))) / P0

/-- Coarse first-order coefficient after affine rear normalization. -/
def preGaugeC1 (P0 P1 kh Qmax : ℝ) : ℝ :=
  Qmax * (P1 / (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0))) / P0 +
    1 / Real.sqrt (1 - kh ^ 2))

/-- Coarse second-order coefficient after affine rear normalization. -/
def preGaugeC2 (P0 P1 kh Qmax : ℝ) : ℝ :=
  Qmax ^ 2 *
    (P1 / (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0))) / P0 +
      (2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
        1 / Real.sqrt (1 - kh ^ 2)) +
      1 / (P0 * Real.sqrt (1 - kh ^ 2) ^ 2))

theorem preGaugeCoefficients_nonnegative (S : SeparatedFacts A P1) :
    0 ≤ preGaugeC0 P0 P1 kh ∧
      0 ≤ preGaugeC1 P0 P1 kh Qmax ∧
      0 ≤ preGaugeC2 P0 P1 kh Qmax := by
  have hroot : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by
    nlinarith [A.kh_nonnegative, A.kh_lt_one])
  have hP1 : 0 < P1 := S.P0_pos.trans_le
    ((S.period_lower 0).trans (S.period_upper 0))
  have hden : 0 < 1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0)) :=
    JacobiNormalized.one_sub_exp_pos (mul_pos hroot S.P0_pos)
  have hQ : 0 ≤ Qmax := (A.rear_period_pos 0).le.trans (A.rear_period_le 0)
  have ha0 : 0 ≤ P1 / (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0))) :=
    div_nonneg hP1.le hden.le
  have hb0 : 0 ≤
      P1 / (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0))) / P0 :=
    div_nonneg ha0 S.P0_pos.le
  have hb1 : 0 ≤ 1 / Real.sqrt (1 - kh ^ 2) := one_div_nonneg.mpr hroot.le
  have hb21 : 0 ≤ 2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
      1 / Real.sqrt (1 - kh ^ 2) := by
    exact add_nonneg
      (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg kh))
        (pow_nonneg hroot.le 3)) hb1
  have hb22 : 0 ≤ 1 / (P0 * Real.sqrt (1 - kh ^ 2) ^ 2) :=
    one_div_nonneg.mpr (mul_nonneg S.P0_pos.le (sq_nonneg _))
  exact ⟨hb0, mul_nonneg hQ (add_nonneg hb0 hb1),
    mul_nonneg (sq_nonneg Qmax) (add_nonneg (add_nonneg hb0 hb21) hb22)⟩

/-- Complete exact variable-period analytic input for the affine pre-gauge
rear density.  Only the already-standard front functional certificate is an
argument; rear integrability is reconstructed from the source. -/
private def analyticInputOfSpatial
    {E : Applied Gamma A}
    (N : RearOwnFrameDrift.SpatialC2 (rearNormal A))
    (S : SeparatedFacts A P1) (F : FunctionalIntegrable Gamma.eta) :
    VariableArclengthScaledJacobiTransition.AnalyticInput
      A.P (rearPeriod A) Gamma.eta (normalizedRearDensity A)
      (preGaugeC0 P0 P1 kh) (preGaugeC1 P0 P1 kh Qmax)
      (preGaugeC2 P0 P1 kh Qmax) := by
  let C := sliceCertificate S
  let R := normalizedRearFunctionalIntegrableOfSpatial (A := A) (E := E) N
  have hRcont : Continuous (rearPeriod A) :=
    Differentiable.continuous fun t ↦ (E.frame.period_deriv t).differentiableAt
  have hfrontPhysical : IntervalIntegrable
      (fun t ↦ A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) volume 0 1 := by
    simpa [mul_comm] using F.w.mul_continuousOn A.period_contDiff.continuous.continuousOn
  have hrearPhysical : IntervalIntegrable
      (fun t ↦ rearPeriod A t *
        ∫ u in (0 : ℝ)..1, |normalizedRearDensity A t u|) volume 0 1 := by
    simpa [mul_comm] using R.w.mul_continuousOn hRcont.continuousOn
  have hroot : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by
    nlinarith [A.kh_nonnegative, A.kh_lt_one])
  have hP1 : 0 < P1 := S.P0_pos.trans_le
    ((S.period_lower 0).trans (S.period_upper 0))
  have hden : 0 < 1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0)) :=
    JacobiNormalized.one_sub_exp_pos (mul_pos hroot S.P0_pos)
  have hQ : 0 ≤ Qmax := (A.rear_period_pos 0).le.trans (A.rear_period_le 0)
  let a0 := P1 / (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0)))
  let a11 := 1 / Real.sqrt (1 - kh ^ 2)
  let a21 := 2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
    1 / Real.sqrt (1 - kh ^ 2)
  let a22 := 1 / (P0 * Real.sqrt (1 - kh ^ 2) ^ 2)
  have ha0 : 0 ≤ a0 := by dsimp [a0]; exact div_nonneg hP1.le hden.le
  have ha11 : 0 ≤ a11 := by dsimp [a11]; exact one_div_nonneg.mpr hroot.le
  have ha21 : 0 ≤ a21 := by
    dsimp [a21]
    exact add_nonneg
      (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg kh))
        (pow_nonneg hroot.le 3)) ha11
  have ha22 : 0 ≤ a22 := by
    dsimp [a22]
    exact one_div_nonneg.mpr (mul_nonneg S.P0_pos.le (sq_nonneg _))
  have hscaled (t : ℝ) : a0 ≤ (a0 / P0) * A.P t := by
    rw [div_mul_eq_mul_div, le_div_iff₀ S.P0_pos]
    exact mul_le_mul_of_nonneg_left (S.period_lower t) ha0
  have hd1 (t : ℝ) : deriv (rearNormal A t) = N.xi1 t :=
    funext fun x ↦ (N.deriv1 t x).deriv
  have hd2 (t : ℝ) : deriv (deriv (rearNormal A t)) = N.xi2 t := by
    rw [hd1 t]
    exact funext fun x ↦ (N.deriv2 t x).deriv
  refine
    { frontPhysicalW_integrable := hfrontPhysical
      rearPhysicalW_integrable := hrearPhysical
      W_slice := fun t _ ↦ normalizedRearDensity_physicalW_le S t
      rearS0_integrable := R.s0
      S0_slice := ?_
      rearS1_integrable := R.s1
      frontS0_integrable := F.s0
      S1_slice := ?_
      rearS2_integrable := R.s2
      frontS1_integrable := F.s1
      S2_slice := ?_ }
  · intro t
    have H := C.s0 t
    have heta : (fun u ↦ A.etaF t (A.P t * u)) = Gamma.eta t :=
      funext fun u ↦ (S.eta_link_affine t u).symm
    change supNorm (fun u ↦ rearNormal A t (rearPeriod A t * u)) ≤ _
    rw [JacobiNormalized.supNorm_comp_mul (L := rearPeriod A t)
      (A.rear_period_pos t).ne'
      (rearNormal A t)]
    calc
      supNorm (rearNormal A t) ≤ a0 *
          (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) := by
        change supNorm (rearNormal A t) ≤
          a0 * (∫ u in (0 : ℝ)..1, |A.etaF t (A.P t * u)|) at H
        simpa only [← S.eta_link_affine t] using H
      _ ≤ (a0 / P0 * A.P t) *
          (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) :=
        mul_le_mul_of_nonneg_right (hscaled t)
          (intervalIntegral.integral_nonneg zero_le_one fun _ _ ↦ abs_nonneg _)
      _ = preGaugeC0 P0 P1 kh *
          (A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) := by
        simp [preGaugeC0, a0]; ring
  · intro t
    have H := (C.separated t).s1
    have heta : (fun u ↦ A.etaF t (A.P t * u)) = Gamma.eta t :=
      funext fun u ↦ (S.eta_link_affine t u).symm
    have hRt : 0 ≤ rearPeriod A t := (A.rear_period_pos t).le
    have hRQ : rearPeriod A t ≤ Qmax := A.rear_period_le t
    have hw : 0 ≤ A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      mul_nonneg (A.period_pos t).le
        (intervalIntegral.integral_nonneg zero_le_one fun _ _ ↦ abs_nonneg _)
    have hs : 0 ≤ supNorm (Gamma.eta t) := supNorm_nonneg _
    have hw0 : 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      intervalIntegral.integral_nonneg zero_le_one fun _ _ ↦ abs_nonneg _
    have hWscale : a0 * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) ≤
        (a0 / P0) * (A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) := by
      calc
        a0 * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) ≤
            (a0 / P0 * A.P t) *
              (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) :=
          mul_le_mul_of_nonneg_right (hscaled t) hw0
        _ = _ := by ring
    change supNorm (iteratedDeriv 1
      (fun u ↦ rearNormal A t (rearPeriod A t * u))) ≤ _
    rw [JacobiNormalized.iteratedDeriv_one_comp_mul
        (L := rearPeriod A t) (N.deriv1 t),
      JacobiNormalized.supNorm_const_mul hRt,
      JacobiNormalized.supNorm_comp_mul (L := rearPeriod A t)
        (A.rear_period_pos t).ne' (N.xi1 t)]
    rw [← hd1 t]
    have H' : supNorm (deriv (rearNormal A t)) ≤
        a0 * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
          a11 * supNorm (Gamma.eta t) := by
      change supNorm (deriv (rearNormal A t)) ≤
        a0 * (∫ u in (0 : ℝ)..1, |A.etaF t (A.P t * u)|) +
          a11 * supNorm (fun u ↦ A.etaF t (A.P t * u)) at H
      simpa only [← S.eta_link_affine t] using H
    calc
      rearPeriod A t * supNorm (deriv (rearNormal A t)) ≤
          rearPeriod A t * ((a0 / P0) *
            (A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
              a11 * supNorm (Gamma.eta t)) := by
        apply mul_le_mul_of_nonneg_left _ hRt
        exact H'.trans (add_le_add hWscale le_rfl)
      _ ≤ Qmax * ((a0 / P0) *
            (A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
              a11 * supNorm (Gamma.eta t)) := by
        exact mul_le_mul_of_nonneg_right hRQ
          (add_nonneg (mul_nonneg (div_nonneg ha0 S.P0_pos.le) hw)
            (mul_nonneg ha11 hs))
      _ ≤ preGaugeC1 P0 P1 kh Qmax *
          (supNorm (Gamma.eta t) +
            A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) := by
        calc
          Qmax * ((a0 / P0) *
                (A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
              a11 * supNorm (Gamma.eta t)) ≤
              Qmax * ((a0 / P0 + a11) *
                (supNorm (Gamma.eta t) +
                  A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|)) := by
            apply mul_le_mul_of_nonneg_left _ hQ
            nlinarith [mul_nonneg (div_nonneg ha0 S.P0_pos.le) hs,
              mul_nonneg ha11 hw]
          _ = _ := by simp [preGaugeC1, a0, a11]; ring
  · intro t
    have H := (C.separated t).s2
    have heta : (fun u ↦ A.etaF t (A.P t * u)) = Gamma.eta t :=
      funext fun u ↦ (S.eta_link_affine t u).symm
    have hRt : 0 ≤ rearPeriod A t := (A.rear_period_pos t).le
    have hR2Q : rearPeriod A t ^ 2 ≤ Qmax ^ 2 := by
      calc
        rearPeriod A t ^ 2 = rearPeriod A t * rearPeriod A t := by ring
        _ ≤ Qmax * Qmax := mul_le_mul (A.rear_period_le t)
          (A.rear_period_le t) hRt hQ
        _ = Qmax ^ 2 := by ring
    have hw : 0 ≤ A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      mul_nonneg (A.period_pos t).le
        (intervalIntegral.integral_nonneg zero_le_one fun _ _ ↦ abs_nonneg _)
    have hs0 : 0 ≤ supNorm (Gamma.eta t) := supNorm_nonneg _
    have hs1 : 0 ≤ supNorm (iteratedDeriv 1 (Gamma.eta t)) := supNorm_nonneg _
    have hw0 : 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      intervalIntegral.integral_nonneg zero_le_one fun _ _ ↦ abs_nonneg _
    have hWscale : a0 * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) ≤
        (a0 / P0) * (A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) := by
      calc
        a0 * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) ≤
            (a0 / P0 * A.P t) *
              (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) :=
          mul_le_mul_of_nonneg_right (hscaled t) hw0
        _ = _ := by ring
    change supNorm (iteratedDeriv 2
      (fun u ↦ rearNormal A t (rearPeriod A t * u))) ≤ _
    rw [JacobiNormalized.iteratedDeriv_two_comp_mul
        (L := rearPeriod A t) (N.deriv1 t) (N.deriv2 t),
      JacobiNormalized.supNorm_const_mul (sq_nonneg (rearPeriod A t)),
      JacobiNormalized.supNorm_comp_mul (L := rearPeriod A t)
        (A.rear_period_pos t).ne' (N.xi2 t)]
    rw [← hd2 t]
    have H' : supNorm (deriv (deriv (rearNormal A t))) ≤
        a0 * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
          a21 * supNorm (Gamma.eta t) +
          a22 * supNorm (iteratedDeriv 1 (Gamma.eta t)) := by
      change supNorm (deriv (deriv (rearNormal A t))) ≤
        a0 * (∫ u in (0 : ℝ)..1, |A.etaF t (A.P t * u)|) +
          a21 * supNorm (fun u ↦ A.etaF t (A.P t * u)) +
          a22 * supNorm (iteratedDeriv 1
            (fun u ↦ A.etaF t (A.P t * u))) at H
      simpa only [← S.eta_link_affine t] using H
    calc
      rearPeriod A t ^ 2 * supNorm (deriv (deriv (rearNormal A t))) ≤
          rearPeriod A t ^ 2 * ((a0 / P0) *
              (A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            a21 * supNorm (Gamma.eta t) +
            a22 * supNorm (iteratedDeriv 1 (Gamma.eta t))) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact H'.trans (add_le_add (add_le_add hWscale le_rfl) le_rfl)
      _ ≤ Qmax ^ 2 * ((a0 / P0) *
              (A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            a21 * supNorm (Gamma.eta t) +
            a22 * supNorm (iteratedDeriv 1 (Gamma.eta t))) := by
        exact mul_le_mul_of_nonneg_right hR2Q
          (add_nonneg (add_nonneg
            (mul_nonneg (div_nonneg ha0 S.P0_pos.le) hw)
            (mul_nonneg ha21 hs0)) (mul_nonneg ha22 hs1))
      _ ≤ preGaugeC2 P0 P1 kh Qmax *
          (supNorm (Gamma.eta t) + supNorm (iteratedDeriv 1 (Gamma.eta t)) +
            A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) := by
        calc
          Qmax ^ 2 * ((a0 / P0) *
                (A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
              a21 * supNorm (Gamma.eta t) +
              a22 * supNorm (iteratedDeriv 1 (Gamma.eta t))) ≤
              Qmax ^ 2 * ((a0 / P0 + a21 + a22) *
                (supNorm (Gamma.eta t) +
                  supNorm (iteratedDeriv 1 (Gamma.eta t)) +
                  A.P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|)) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg Qmax)
            nlinarith [mul_nonneg (div_nonneg ha0 S.P0_pos.le) hs0,
              mul_nonneg (div_nonneg ha0 S.P0_pos.le) hs1,
              mul_nonneg ha21 hw, mul_nonneg ha21 hs1, mul_nonneg ha22 hw,
              mul_nonneg ha22 hs0]
          _ = _ := by simp [preGaugeC2, a0, a21, a22]; ring

def analyticInput
    {E : Applied Gamma A}
    (S : SeparatedFacts A P1) (F : FunctionalIntegrable Gamma.eta) :
    VariableArclengthScaledJacobiTransition.AnalyticInput
      A.P (rearPeriod A) Gamma.eta (normalizedRearDensity A)
      (preGaugeC0 P0 P1 kh) (preGaugeC1 P0 P1 kh Qmax)
      (preGaugeC2 P0 P1 kh Qmax) := by
  cases A.frame_regularity with
  | joint hYdot hangle =>
      exact analyticInputOfSpatial (E := E)
        (RearOwnFrameDrift.SpatialC2.ofContDiff
          (RearOwnTangential.contDiff_frameNormal hYdot hangle)) S F
  | spatial R => exact analyticInputOfSpatial (E := E) R.normal S F

end FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition
