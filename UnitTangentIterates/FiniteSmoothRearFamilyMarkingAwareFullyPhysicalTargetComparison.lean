import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds

/-!
# Fully physical comparison with the actual chosen marking

The intrinsic selected rear is affinely marked by rear arclength, whereas the
theorem-produced chosen path uses a time-dependent gauge marking.  The
physical `W` component therefore keeps the exact marking Jacobian, while the
spatial components are divided by the rear period and its square.  The second
chain-rule term loses one rear-period factor; the configured floor `1 <= PR`
absorbs it.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  VariableArclengthScaledTimeReparamTransition

/-- Coordinate-correct components in an arbitrary normalized marking. -/
def markedPhysicalComponents
    (J : ℝ → ℝ → ℝ) (P : ℝ → ℝ) (eta : ℝ → ℝ → ℝ) :
    Components where
  w := jacobianPhysicalW J eta
  s0 := S 0 eta
  s1 := FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.spatialS1 P eta
  s2 := FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.spatialS2 P eta

/-- The chosen Jacobian integral is exactly the intrinsic rear-arclength
integral on every time slice. -/
theorem chosen_jacobian_slice_eq_intrinsic
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b)
    (S : SeparatedFacts A P1) (t : ℝ) :
    (∫ u in (0 : ℝ)..1, W.phi1 t u * |W.Delta.eta t u|) =
      ∫ x in (0 : ℝ)..rearPeriod A t, |rearNormal A t x| := by
  have hrearPer : Periodic (rearNormal A t) (rearPeriod A t) := by
    simpa [rearNormal, rearPeriod] using
      RearOwnDriftFundamental.periodic_frameNormal_rearOwn
        A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le
        A.cos_ne_zero A.front_frenet A.angle_frenet A.steering A.sf_deriv
        A.sf_rightInverse A.steering_periodic A.front_periodic
        A.angle_periodic A.front_contDiff A.angle_contDiff
        A.steering_contDiff A.sf_contDiff A.period_contDiff A.rear_time_deriv t
  have hshift : E.Phi t 1 = E.Phi t 0 + rearPeriod A t := by
    simpa using W.shift t 0
  calc
    (∫ u in (0 : ℝ)..1, W.phi1 t u * |W.Delta.eta t u|) =
        ∫ u in (0 : ℝ)..1, W.phi1 t u * |rearNormal A t (E.Phi t u)| := by
      congr 1
      funext u
      rw [W.eta_eq t u]
    _ = ∫ x in (0 : ℝ)..rearPeriod A t, |rearNormal A t x| :=
      FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW.integral_jacobian_abs_comp_eq_period
        (S.rearNormal_c2 t).continuous hrearPer (W.phi1_deriv t)
        (W.phi1_continuous t) hshift

/-- Exact `W` identity between the chosen marking and the intrinsic affine
rear-arclength representative. -/
theorem chosen_jacobianPhysicalW_eq
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b)
    (S : SeparatedFacts A P1) :
    jacobianPhysicalW W.phi1 W.Delta.eta =
      VariableArclengthScaledJacobiTransition.physicalW (rearPeriod A)
        (FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A) := by
  unfold jacobianPhysicalW VariableArclengthScaledJacobiTransition.physicalW
  apply intervalIntegral.integral_congr
  intro t _
  change (∫ u in (0 : ℝ)..1, W.phi1 t u * |W.Delta.eta t u|) =
    rearPeriod A t * (∫ u in (0 : ℝ)..1,
      |FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A t u|)
  rw [chosen_jacobian_slice_eq_intrinsic W S t]
  have hR : rearPeriod A t ≠ 0 := (A.rear_period_pos t).ne'
  change (∫ x in (0 : ℝ)..rearPeriod A t, |rearNormal A t x|) =
    rearPeriod A t * (∫ u in (0 : ℝ)..1,
      |rearNormal A t (rearPeriod A t * u)|)
  rw [JacobiNormalized.integral_abs_comp_mul hR (rearNormal A t)]
  field_simp [hR]

/-- A normalized time-dependent marking preserves the fully physical
component inequalities.  The hypothesis `1 <= P` absorbs the extra `P⁻¹`
in the second chain-rule term. -/
def targetComparison_of_timeReparamInput
    {P : ℝ → ℝ} {source target J : ℝ → ℝ → ℝ}
    {mA upper second : ℝ}
    (H : TimeReparamInput P source target mA upper second)
    (hJ : ∀ t u, J t u = P t * H.psi1 t u)
    (hP1 : ∀ t ∈ Icc (0 : ℝ) 1, 1 ≤ P t)
    (hsourceS1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (source t)) / P t) volume 0 1)
    (htargetS1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (target t)) / P t) volume 0 1)
    (hsourceS2 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 2 (source t)) / P t ^ 2) volume 0 1)
    (htargetS2 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 2 (target t)) / P t ^ 2) volume 0 1) :
    TargetMarkingComparison
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents P source)
      (markedPhysicalComponents J P target) upper second := by
  have hupper0 : 0 ≤ upper := by
    have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    exact (abs_nonneg (H.psi1 0 0)).trans (H.jacobian_upper 0 hzero 0)
  have hsecond0 : 0 ≤ second := by
    have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    exact (abs_nonneg (H.psi2 0 0)).trans (H.second_upper 0 hzero 0)
  have hS0 := H.toVariableFixedReparamBounds
  refine { w := ?_, s0 := hS0.s0, s1 := ?_, s2 := ?_ }
  · unfold markedPhysicalComponents jacobianPhysicalW
    unfold FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
      VariableArclengthScaledJacobiTransition.physicalW
    apply le_of_eq
    apply intervalIntegral.integral_congr
    intro t _
    calc
      (∫ u in (0 : ℝ)..1, J t u * |target t u|) =
          P t * (∫ u in (0 : ℝ)..1,
            H.psi1 t u * |source t (H.psi t u)|) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro u _
        change J t u * |target t u| =
          P t * (H.psi1 t u * |source t (H.psi t u)|)
        rw [hJ t u, H.target_eq t u]
        ring
      _ = P t * (∫ u in (0 : ℝ)..1, |source t u|) := by
        have hchange := intervalIntegral.integral_comp_smul_deriv
          (a := (0 : ℝ)) (b := 1) (f := H.psi t) (f' := H.psi1 t)
          (g := fun x => |source t x|)
          (fun u _ => H.psi_deriv t u) (H.psi1_continuous t).continuousOn
          (Differentiable.continuous fun u => H.source_differentiable t u).abs
        have hslice :
            (∫ u in (0 : ℝ)..1, H.psi1 t u * |source t (H.psi t u)|) =
              ∫ u in (0 : ℝ)..1, |source t u| := by
          simpa [H.psi_zero t, H.psi_one t, smul_eq_mul] using hchange
        exact congrArg (fun z => P t * z) hslice
  · unfold markedPhysicalComponents
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.spatialS1
    have hslice : ∀ t ∈ Icc (0 : ℝ) 1,
        supNorm (iteratedDeriv 1 (target t)) / P t ≤
          upper * (supNorm (iteratedDeriv 1 (source t)) / P t) := by
      intro t ht
      have h := PathFunctionalsReparam.supNorm_iteratedDeriv_one_comp_le
        (fun u => (H.source_differentiable t u).hasDerivAt)
        (H.psi_deriv t) (H.source_bdd1 t) (H.jacobian_upper t ht)
      have htarget : target t = fun u => source t (H.psi t u) :=
        funext (H.target_eq t)
      rw [htarget]
      have hraw : supNorm (iteratedDeriv 1 (fun u => source t (H.psi t u))) ≤
          upper * supNorm (iteratedDeriv 1 (source t)) := by
        calc
          _ ≤ supNorm (deriv (source t)) * upper := h
          _ = _ := by rw [iteratedDeriv_one]; ring
      calc
        supNorm (iteratedDeriv 1 (fun u => source t (H.psi t u))) / P t ≤
            (upper * supNorm (iteratedDeriv 1 (source t))) / P t :=
          (div_le_div_iff_of_pos_right
            (lt_of_lt_of_le zero_lt_one (hP1 t ht))).2 hraw
        _ = upper * (supNorm (iteratedDeriv 1 (source t)) / P t) := by ring
    calc
      (∫ t in (0 : ℝ)..1, supNorm (iteratedDeriv 1 (target t)) / P t) ≤
          ∫ t in (0 : ℝ)..1,
            upper * (supNorm (iteratedDeriv 1 (source t)) / P t) :=
        intervalIntegral.integral_mono_on zero_le_one htargetS1
          (hsourceS1.const_mul upper) hslice
      _ = upper * (∫ t in (0 : ℝ)..1,
          supNorm (iteratedDeriv 1 (source t)) / P t) := by
        rw [intervalIntegral.integral_const_mul]
  · unfold markedPhysicalComponents
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.spatialS1
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.spatialS2
    have hslice : ∀ t ∈ Icc (0 : ℝ) 1,
        supNorm (iteratedDeriv 2 (target t)) / P t ^ 2 ≤
          upper ^ 2 * (supNorm (iteratedDeriv 2 (source t)) / P t ^ 2) +
            second * (supNorm (iteratedDeriv 1 (source t)) / P t) := by
      intro t ht
      have h := PathFunctionalsReparam.supNorm_iteratedDeriv_two_comp_le
        (fun u => (H.source_differentiable t u).hasDerivAt)
        (fun u => (H.source_deriv_differentiable t u).hasDerivAt)
        (H.psi_deriv t) (H.psi1_deriv t) (H.source_bdd1 t)
        (H.source_bdd2 t) (H.jacobian_upper t ht) (H.second_upper t ht)
      have htarget : target t = fun u => source t (H.psi t u) :=
        funext (H.target_eq t)
      rw [htarget]
      have hraw : supNorm (iteratedDeriv 2 (fun u => source t (H.psi t u))) ≤
          upper ^ 2 * supNorm (iteratedDeriv 2 (source t)) +
            second * supNorm (iteratedDeriv 1 (source t)) := by
        calc
          _ ≤ supNorm (deriv (deriv (source t))) * upper ^ 2 +
              supNorm (deriv (source t)) * second := h
          _ = _ := by
            simp only [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
              iteratedDeriv_zero, iteratedDeriv_one]
            ring
      have hPpos : 0 < P t := lt_of_lt_of_le zero_lt_one (hP1 t ht)
      have hdiv : supNorm (iteratedDeriv 1 (source t)) / P t ^ 2 ≤
          supNorm (iteratedDeriv 1 (source t)) / P t := by
        exact div_le_div_of_nonneg_left (supNorm_nonneg _) hPpos
          (by nlinarith [hP1 t ht])
      calc
        _ ≤ (upper ^ 2 * supNorm (iteratedDeriv 2 (source t)) +
            second * supNorm (iteratedDeriv 1 (source t))) / P t ^ 2 :=
          (div_le_div_iff_of_pos_right (sq_pos_of_pos hPpos)).2 hraw
        _ = upper ^ 2 * (supNorm (iteratedDeriv 2 (source t)) / P t ^ 2) +
            second * (supNorm (iteratedDeriv 1 (source t)) / P t ^ 2) := by ring
        _ ≤ _ := add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hdiv hsecond0)
    have hrhs : IntervalIntegrable (fun t =>
        upper ^ 2 * (supNorm (iteratedDeriv 2 (source t)) / P t ^ 2) +
          second * (supNorm (iteratedDeriv 1 (source t)) / P t)) volume 0 1 :=
      (hsourceS2.const_mul _).add (hsourceS1.const_mul _)
    calc
      (∫ t in (0 : ℝ)..1, supNorm (iteratedDeriv 2 (target t)) / P t ^ 2) ≤
          ∫ t in (0 : ℝ)..1,
            (upper ^ 2 * (supNorm (iteratedDeriv 2 (source t)) / P t ^ 2) +
              second * (supNorm (iteratedDeriv 1 (source t)) / P t)) :=
        intervalIntegral.integral_mono_on zero_le_one htargetS2 hrhs hslice
      _ = upper ^ 2 * (∫ t in (0 : ℝ)..1,
            supNorm (iteratedDeriv 2 (source t)) / P t ^ 2) +
          second * (∫ t in (0 : ℝ)..1,
            supNorm (iteratedDeriv 1 (source t)) / P t) := by
        rw [intervalIntegral.integral_add
          (hsourceS2.const_mul _) (hsourceS1.const_mul _),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]

/-- The actual chosen gauge marking is a fully physical target comparison
from the intrinsic normalized rear density.  The only scalar input beyond the
standard row certificates is the paper's unit lower bound for the rear-period
floor. -/
def chosenTargetComparison_of_one_le_rearPeriod
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b)
    (hkh : 0 < kh) (S : SeparatedFacts A P1)
    (F : FunctionalIntegrable Gamma.eta)
    {eps : ℝ} (J : NormalizedJetBounds W eps) (heps : eps < 1)
    (hperiod : ∀ t, 1 ≤ rearPeriod A t) :
    TargetMarkingComparison
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        (rearPeriod A)
        (FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A))
      (markedPhysicalComponents W.phi1 (rearPeriod A) W.Delta.eta)
      (1 + eps) eps := by
  let Hraw :=
    FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition.analyticInput
      (E := E) S F
  let Htime := timeReparamInput W S Hraw J heps
  let Hphysical :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings.fullyPhysicalAnalyticInput
      (E := E) hkh S F
  let Ftarget :=
    FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.functionalIntegrable_of_exactSource W
  have hRcont : Continuous (rearPeriod A) :=
    Differentiable.continuous fun t => (E.frame.period_deriv t).differentiableAt
  have hRinv : Continuous (fun t => (rearPeriod A t)⁻¹) :=
    hRcont.inv₀ fun t => (A.rear_period_pos t).ne'
  have hR2inv : Continuous (fun t => (rearPeriod A t ^ 2)⁻¹) :=
    (hRcont.pow 2).inv₀ fun t => (sq_pos_of_pos (A.rear_period_pos t)).ne'
  have htargetS1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (W.Delta.eta t)) / rearPeriod A t)
      volume 0 1 := by
    simpa [div_eq_mul_inv] using
      Ftarget.s1.mul_continuousOn hRinv.continuousOn
  have htargetS2 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 2 (W.Delta.eta t)) / rearPeriod A t ^ 2)
      volume 0 1 := by
    simpa [div_eq_mul_inv] using
      Ftarget.s2.mul_continuousOn hR2inv.continuousOn
  apply targetComparison_of_timeReparamInput Htime
  · intro t u
    change W.phi1 t u = rearPeriod A t * normalizedPsi1 W t u
    unfold normalizedPsi1
    have hR : rearPeriod A t ≠ 0 := (A.rear_period_pos t).ne'
    calc
      W.phi1 t u = (rearPeriod A t / rearPeriod A t) * W.phi1 t u := by
        rw [div_self hR, one_mul]
      _ = rearPeriod A t * (W.phi1 t u / rearPeriod A t) := by ring
  · intro t ht
    exact hperiod t
  · exact Hphysical.rearS1_integrable
  · exact htargetS1
  · exact Hphysical.rearS2_integrable
  · exact htargetS2

/-- Floor-based compatibility wrapper for the chosen-variable-jet API. -/
def chosenTargetComparison
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b)
    (hkh : 0 < kh) (S : SeparatedFacts A P1)
    (F : FunctionalIntegrable Gamma.eta)
    {eps : ℝ} (J : NormalizedJetBounds W eps) (heps : eps < 1)
    (hfloor : 1 ≤
      FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds.rearPeriodFloor P0 kh) :
    TargetMarkingComparison
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        (rearPeriod A)
        (FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A))
      (markedPhysicalComponents W.phi1 (rearPeriod A) W.Delta.eta)
      (1 + eps) eps :=
  chosenTargetComparison_of_one_le_rearPeriod W hkh S F J heps fun t =>
    hfloor.trans
      (FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds.rearPeriodFloor_le S t)

/-- A direct wrapper for target comparisons stated in the fully physical
period-weighted components.  This keeps the history API honest: an actual
nonaffine chosen marking generally supplies the split comparison below, not
this stronger nonexpansive-`W` interface. -/
structure TargetSlices
    (P : ℝ → ℝ) (source target : ℝ → ℝ → ℝ)
    (upper second : ℝ) : Prop where
  comparison : TargetMarkingComparison
    (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
      P source)
    (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
      P target) upper second

def TargetSlices.toTargetMarkingComparison
    {P : ℝ → ℝ} {source target : ℝ → ℝ → ℝ}
    {upper second : ℝ} (H : TargetSlices P source target upper second) :
    TargetMarkingComparison
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        P source)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        P target) upper second :=
  H.comparison

end FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison
