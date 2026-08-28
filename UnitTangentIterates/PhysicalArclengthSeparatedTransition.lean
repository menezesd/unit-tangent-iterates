import UnitTangentIterates.PhysicalArclengthJacobiTransition
import UnitTangentIterates.GaugeNormalPathSeparated

/-!
# Separated gauge densities in physical arclength components

This is the lossless bridge from the seven density coefficients retained by
the long gauge construction to the four physical recursive components.  The
two first-derivative and three second-derivative coefficients are not replaced
by a common maximum before the perimeter normalization is applied.
-/

noncomputable section

open Set MeasureTheory MarkedTopology MarkedSpace PathMetric

namespace PhysicalArclengthSeparatedTransition

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds
  PhysicalArclengthJacobiTransition

structure IntegratedBounds
    (front rear : ℝ → ℝ → ℝ)
    (CW C0 C10 C11 C20 C21 C22 : ℝ) : Prop where
  w : W rear 1 ≤ CW * W front 1
  s0 : S 0 rear ≤ C0 * W front 1
  s1 : S 1 rear ≤ C10 * W front 1 + C11 * S 0 front
  s2 : S 2 rear ≤
    C20 * W front 1 + C21 * S 0 front + C22 * S 1 front

def IntegratedBounds.of_flowed
    {front rear : ℝ → ℝ → ℝ}
    {CW C0 C10 C11 C20 C21 C22 : ℝ}
    (hfront : FunctionalIntegrable front)
    (hrear : FunctionalIntegrable rear)
    (B : GaugeNormalPathSeparated.FlowedBounds front rear
      CW C0 C10 C11 C20 C21 C22) :
    IntegratedBounds front rear CW C0 C10 C11 C20 C21 C22 where
  w := by
    unfold W
    calc
      (∫ t in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, |rear t x|) ≤
          ∫ t in (0 : ℝ)..1, CW * ∫ x in (0 : ℝ)..1, |front t x| :=
        intervalIntegral.integral_mono_on (by norm_num) hrear.w
          (hfront.w.const_mul CW) (fun t _ => B.w t)
      _ = CW * ∫ t in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, |front t x| := by
        rw [intervalIntegral.integral_const_mul]
  s0 := by
    unfold S W
    calc
      (∫ t in (0 : ℝ)..1, supNorm (rear t)) ≤
          ∫ t in (0 : ℝ)..1, C0 * ∫ x in (0 : ℝ)..1, |front t x| :=
        intervalIntegral.integral_mono_on (by norm_num) hrear.s0
          (hfront.w.const_mul C0) (fun t _ => B.s0 t)
      _ = C0 * ∫ t in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, |front t x| := by
        rw [intervalIntegral.integral_const_mul]
  s1 := by
    unfold S W
    calc
      (∫ t in (0 : ℝ)..1, supNorm (iteratedDeriv 1 (rear t))) ≤
          ∫ t in (0 : ℝ)..1,
            (C10 * (∫ x in (0 : ℝ)..1, |front t x|) +
              C11 * supNorm (front t)) :=
        intervalIntegral.integral_mono_on (by norm_num) hrear.s1
          ((hfront.w.const_mul C10).add (hfront.s0.const_mul C11))
          (fun t _ => B.s1 t)
      _ = C10 * (∫ t in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, |front t x|) +
          C11 * ∫ t in (0 : ℝ)..1, supNorm (front t) := by
        rw [intervalIntegral.integral_add
          (hfront.w.const_mul C10) (hfront.s0.const_mul C11),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  s2 := by
    unfold S W
    have hcalc :
      (∫ t in (0 : ℝ)..1, supNorm (iteratedDeriv 2 (rear t))) ≤
        C20 * (∫ t in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, |front t x|) +
          C21 * (∫ t in (0 : ℝ)..1, supNorm (front t)) +
          C22 * (∫ t in (0 : ℝ)..1,
            supNorm (iteratedDeriv 1 (front t))) := by
      calc
        (∫ t in (0 : ℝ)..1, supNorm (iteratedDeriv 2 (rear t))) ≤
            ∫ t in (0 : ℝ)..1,
            (C20 * (∫ x in (0 : ℝ)..1, |front t x|) +
              C21 * supNorm (front t) +
              C22 * supNorm (iteratedDeriv 1 (front t))) :=
          intervalIntegral.integral_mono_on (by norm_num) hrear.s2
            (((hfront.w.const_mul C20).add (hfront.s0.const_mul C21)).add
              (hfront.s1.const_mul C22)) (fun t _ => B.s2 t)
        _ = C20 * (∫ t in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, |front t x|) +
            C21 * (∫ t in (0 : ℝ)..1, supNorm (front t)) +
            C22 * (∫ t in (0 : ℝ)..1,
              supNorm (iteratedDeriv 1 (front t))) := by
          calc
            (∫ t in (0 : ℝ)..1,
                ((C20 * (∫ x in (0 : ℝ)..1, |front t x|) +
                  C21 * supNorm (front t)) +
                  C22 * supNorm (iteratedDeriv 1 (front t)))) =
                (∫ t in (0 : ℝ)..1,
                  (C20 * (∫ x in (0 : ℝ)..1, |front t x|) +
                    C21 * supNorm (front t))) +
                ∫ t in (0 : ℝ)..1,
                  C22 * supNorm (iteratedDeriv 1 (front t)) :=
              intervalIntegral.integral_add
                ((hfront.w.const_mul C20).add (hfront.s0.const_mul C21))
                (hfront.s1.const_mul C22)
            _ = ((∫ t in (0 : ℝ)..1,
                    C20 * (∫ x in (0 : ℝ)..1, |front t x|)) +
                  (∫ t in (0 : ℝ)..1, C21 * supNorm (front t))) +
                (∫ t in (0 : ℝ)..1,
                  C22 * supNorm (iteratedDeriv 1 (front t))) := by
              rw [intervalIntegral.integral_add
                (hfront.w.const_mul C20) (hfront.s0.const_mul C21)]
            _ = _ := by
              have h20 :
                  (∫ t in (0 : ℝ)..1,
                    C20 * (∫ x in (0 : ℝ)..1, |front t x|)) =
                    C20 * (∫ t in (0 : ℝ)..1,
                      ∫ x in (0 : ℝ)..1, |front t x|) :=
                intervalIntegral.integral_const_mul C20
                  (fun t => ∫ x in (0 : ℝ)..1, |front t x|)
              have h21 :
                  (∫ t in (0 : ℝ)..1, C21 * supNorm (front t)) =
                    C21 * (∫ t in (0 : ℝ)..1, supNorm (front t)) :=
                intervalIntegral.integral_const_mul C21 (fun t => supNorm (front t))
              have h22 :
                  (∫ t in (0 : ℝ)..1,
                    C22 * supNorm (iteratedDeriv 1 (front t))) =
                    C22 * (∫ t in (0 : ℝ)..1,
                      supNorm (iteratedDeriv 1 (front t))) :=
                intervalIntegral.integral_const_mul C22
                  (fun t => supNorm (iteratedDeriv 1 (front t)))
              rw [h20, h21, h22]
    have hs0fun : (fun t => supNorm (iteratedDeriv 0 (front t))) =
        fun t => supNorm (front t) := by
      funext t
      rw [iteratedDeriv_zero]
    rw [hs0fun]
    simpa only [add_assoc] using hcalc

structure Domination
    (PF PR a CW C0 C10 C11 C20 C21 C22 K0 K1 K2 : ℝ) : Prop where
  PF_pos : 0 < PF
  PR_pos : 0 < PR
  w : PR * CW ≤ a * PF
  s0 : C0 ≤ K0 * PF
  s1w : C10 / PR ≤ K1 * PF
  s1s : C11 / PR ≤ K1
  s2w : C20 / PR ^ 2 ≤ K2 * PF
  s2s : C21 / PR ^ 2 ≤ K2
  s2d : (C22 / PR ^ 2) * PF ≤ K2

def IntegratedBounds.toPhysical
    {front rear : ℝ → ℝ → ℝ}
    {PF PR a CW C0 C10 C11 C20 C21 C22 K0 K1 K2 : ℝ}
    (B : IntegratedBounds front rear CW C0 C10 C11 C20 C21 C22)
    (H : Domination PF PR a CW C0 C10 C11 C20 C21 C22 K0 K1 K2) :
    PhysicalArclengthJacobiTransition.RawBounds PF PR front rear a K0 K1 K2 where
  w := by
    have hw : 0 ≤ W front 1 := by
      unfold W
      exact intervalIntegral.integral_nonneg zero_le_one (fun t _ =>
        intervalIntegral.integral_nonneg zero_le_one (fun u _ => abs_nonneg _))
    calc
      (PhysicalArclengthJacobiTransition.components PR rear).w = PR * W rear 1 := rfl
      _ ≤ PR * (CW * W front 1) := mul_le_mul_of_nonneg_left B.w H.PR_pos.le
      _ = (PR * CW) * W front 1 := by ring
      _ ≤ (a * PF) * W front 1 := mul_le_mul_of_nonneg_right H.w hw
      _ = a * (PhysicalArclengthJacobiTransition.components PF front).w := by
        change a * PF * W front 1 = a * (PF * W front 1)
        ring
  s0 := by
    have hw : 0 ≤ W front 1 := by
      unfold W
      exact intervalIntegral.integral_nonneg zero_le_one (fun t _ =>
        intervalIntegral.integral_nonneg zero_le_one (fun u _ => abs_nonneg _))
    calc
      (PhysicalArclengthJacobiTransition.components PR rear).s0 = S 0 rear := rfl
      _ ≤ C0 * W front 1 := B.s0
      _ ≤ (K0 * PF) * W front 1 := mul_le_mul_of_nonneg_right H.s0 hw
      _ = K0 * (PhysicalArclengthJacobiTransition.components PF front).w := by
        change K0 * PF * W front 1 = K0 * (PF * W front 1)
        ring
  s1 := by
    have hw : 0 ≤ W front 1 := by
      unfold W
      exact intervalIntegral.integral_nonneg zero_le_one (fun t _ =>
        intervalIntegral.integral_nonneg zero_le_one (fun u _ => abs_nonneg _))
    have hs0 : 0 ≤ S 0 front := by
      unfold S
      exact intervalIntegral.integral_nonneg zero_le_one (fun _ _ => supNorm_nonneg _)
    calc
      (PhysicalArclengthJacobiTransition.components PR rear).s1 = S 1 rear / PR := rfl
      _ ≤ (C10 * W front 1 + C11 * S 0 front) / PR :=
        (div_le_div_iff_of_pos_right H.PR_pos).2 B.s1
      _ = (C10 / PR) * W front 1 + (C11 / PR) * S 0 front := by ring
      _ ≤ (K1 * PF) * W front 1 + K1 * S 0 front := add_le_add
        (mul_le_mul_of_nonneg_right H.s1w hw)
        (mul_le_mul_of_nonneg_right H.s1s hs0)
      _ = K1 * ((PhysicalArclengthJacobiTransition.components PF front).w +
          (PhysicalArclengthJacobiTransition.components PF front).s0) := by
        change K1 * PF * W front 1 + K1 * S 0 front =
          K1 * (PF * W front 1 + S 0 front)
        ring
  s2 := by
    have hw : 0 ≤ W front 1 := by
      unfold W
      exact intervalIntegral.integral_nonneg zero_le_one (fun t _ =>
        intervalIntegral.integral_nonneg zero_le_one (fun u _ => abs_nonneg _))
    have hs0 : 0 ≤ S 0 front := by
      unfold S
      exact intervalIntegral.integral_nonneg zero_le_one (fun _ _ => supNorm_nonneg _)
    have hs1 : 0 ≤ S 1 front / PF := div_nonneg (by
      unfold S
      exact intervalIntegral.integral_nonneg zero_le_one (fun _ _ => supNorm_nonneg _)) H.PF_pos.le
    calc
      (PhysicalArclengthJacobiTransition.components PR rear).s2 = S 2 rear / PR ^ 2 := rfl
      _ ≤ (C20 * W front 1 + C21 * S 0 front + C22 * S 1 front) / PR ^ 2 :=
        (div_le_div_iff_of_pos_right (sq_pos_of_pos H.PR_pos)).2 B.s2
      _ = (C20 / PR ^ 2) * W front 1 +
          (C21 / PR ^ 2) * S 0 front +
          ((C22 / PR ^ 2) * PF) * (S 1 front / PF) := by
        field_simp [H.PF_pos.ne', H.PR_pos.ne']
        <;> ring
      _ ≤ (K2 * PF) * W front 1 + K2 * S 0 front +
          K2 * (S 1 front / PF) :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right H.s2w hw)
          (mul_le_mul_of_nonneg_right H.s2s hs0))
          (mul_le_mul_of_nonneg_right H.s2d hs1)
      _ = K2 * ((PhysicalArclengthJacobiTransition.components PF front).w +
          (PhysicalArclengthJacobiTransition.components PF front).s0 +
          (PhysicalArclengthJacobiTransition.components PF front).s1) := by
        change K2 * PF * W front 1 + K2 * S 0 front + K2 * (S 1 front / PF) =
          K2 * (PF * W front 1 + S 0 front + S 1 front / PF)
        ring

end PhysicalArclengthSeparatedTransition
