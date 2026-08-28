import UnitTangentIterates.JacobiControlledJunctionComponents

/-!
# Physical-arclength Jacobi components

For a unit-periodic constant-speed representative of physical perimeter `P`,
arclength differentiation is `P⁻¹ ∂u`.  Thus the four intrinsic paper
components are `P*W, S0, S1/P, S2/P²`.  This file keeps those powers through
the raw gauge estimates and the terminal fixed reparametrization.
-/

noncomputable section

open Set MeasureTheory MarkedTopology MarkedSpace PathMetric

namespace PhysicalArclengthJacobiTransition

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds PathMetric.NormalPath

def components (P : ℝ) (eta : ℝ → ℝ → ℝ) : Components where
  w := P * W eta 1
  s0 := S 0 eta
  s1 := S 1 eta / P
  s2 := S 2 eta / P ^ 2

theorem components_nonnegative {P : ℝ} (hP : 0 < P) (eta : ℝ → ℝ → ℝ) :
    (components P eta).Nonnegative := by
  have hw : 0 ≤ W eta 1 := by
    unfold W
    exact intervalIntegral.integral_nonneg zero_le_one (fun t _ =>
      intervalIntegral.integral_nonneg zero_le_one (fun u _ => abs_nonneg _))
  have hs (j : ℕ) : 0 ≤ S j eta := by
    unfold S
    exact intervalIntegral.integral_nonneg zero_le_one (fun _ _ => supNorm_nonneg _)
  exact
    { w := mul_nonneg hP.le hw
      s0 := hs 0
      s1 := div_nonneg (hs 1) hP.le
      s2 := div_nonneg (hs 2) (sq_nonneg P) }

/-- For a unit-time normal path, the stored cost dominates every normalized
component.  After physical arclength normalization and `1 ≤ P`, one common
honest bound is `P * cost`. -/
theorem components_le_perim_mul_cost
    {p q : Data} (Gamma : NormalPath p q) (hT : Gamma.T = 1)
    (F : FunctionalIntegrable Gamma.eta) {P : ℝ} (hP : 1 ≤ P) :
    (components P Gamma.eta).w ≤ P * cost Gamma ∧
    (components P Gamma.eta).s0 ≤ P * cost Gamma ∧
    (components P Gamma.eta).s1 ≤ P * cost Gamma ∧
    (components P Gamma.eta).s2 ≤ P * cost Gamma := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hm : IntervalIntegrable Gamma.m volume 0 1 := by
    simpa [hT] using Gamma.cont_m.intervalIntegrable 0 Gamma.T
  have hW : W Gamma.eta 1 ≤ cost Gamma := by
    unfold W cost
    rw [hT]
    exact intervalIntegral.integral_mono_on zero_le_one F.w hm
      (fun t _ => Gamma.le_m_L1 t)
  have hS0 : S 0 Gamma.eta ≤ cost Gamma := by
    unfold S cost
    rw [hT]
    exact intervalIntegral.integral_mono_on zero_le_one F.s0 hm
      (fun t _ => by simpa using Gamma.le_m_sup t 0 (by norm_num))
  have hS1 : S 1 Gamma.eta ≤ cost Gamma := by
    unfold S cost
    rw [hT]
    exact intervalIntegral.integral_mono_on zero_le_one F.s1 hm
      (fun t _ => Gamma.le_m_sup t 1 (by norm_num))
  have hS2 : S 2 Gamma.eta ≤ cost Gamma := by
    unfold S cost
    rw [hT]
    exact intervalIntegral.integral_mono_on zero_le_one F.s2 hm
      (fun t _ => Gamma.le_m_sup t 2 (by norm_num))
  have hcost0 : 0 ≤ cost Gamma := by
    unfold cost
    exact intervalIntegral.integral_nonneg Gamma.T_pos.le
      (fun t _ => Gamma.m_nonneg t)
  have hcostP : cost Gamma ≤ P * cost Gamma := by
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_left hW hPpos.le
  · exact hS0.trans hcostP
  · have hdiv : S 1 Gamma.eta / P ≤ S 1 Gamma.eta := by
      apply (div_le_iff₀ hPpos).2
      have hS10 : 0 ≤ S 1 Gamma.eta := by
        unfold S
        exact intervalIntegral.integral_nonneg zero_le_one
          (fun _ _ => supNorm_nonneg _)
      nlinarith
    exact hdiv.trans (hS1.trans hcostP)
  · have hP2 : 1 ≤ P ^ 2 := by nlinarith
    have hdiv : S 2 Gamma.eta / P ^ 2 ≤ S 2 Gamma.eta := by
      apply (div_le_iff₀ (sq_pos_of_pos hPpos)).2
      have hS20 : 0 ≤ S 2 Gamma.eta := by
        unfold S
        exact intervalIntegral.integral_nonneg zero_le_one
          (fun _ _ => supNorm_nonneg _)
      nlinarith
    exact hdiv.trans (hS2.trans hcostP)

/-- Scalar comparison between the normalized long-gauge constants and fixed
physical-arclength Jacobi constants.  Unlike the obsolete scaled-only-W
interface, the first and second derivative coefficients are divided by the
correct perimeter powers. -/
structure Domination
    (PF PR a CW c0 c1 c2 C0 C1 C2 : ℝ) : Prop where
  PF_pos : 0 < PF
  PR_pos : 0 < PR
  a_nonnegative : 0 ≤ a
  C0_nonnegative : 0 ≤ C0
  C1_nonnegative : 0 ≤ C1
  C2_nonnegative : 0 ≤ C2
  w : PR * CW ≤ a * PF
  s0 : c0 ≤ C0 * PF
  s1w : c1 / PR ≤ C1 * PF
  s1s : c1 / PR ≤ C1
  s2w : c2 / PR ^ 2 ≤ C2 * PF
  s2s : c2 / PR ^ 2 ≤ C2
  s2d : (c2 / PR ^ 2) * PF ≤ C2

/-- Integrated raw selected-rear estimates in physical components. -/
structure RawBounds
    (PF PR : ℝ) (front rear : ℝ → ℝ → ℝ)
    (a C0 C1 C2 : ℝ) : Prop where
  w : (components PR rear).w ≤ a * (components PF front).w
  s0 : (components PR rear).s0 ≤ C0 * (components PF front).w
  s1 : (components PR rear).s1 ≤
    C1 * ((components PF front).w + (components PF front).s0)
  s2 : (components PR rear).s2 ≤
    C2 * ((components PF front).w + (components PF front).s0 +
      (components PF front).s1)

/-- Convert the normalized integrated gauge bounds by elementary perimeter
scaling. -/
def RawBounds.of_normalized
    {PF PR a CW c0 c1 c2 C0 C1 C2 : ℝ}
    {front rear : ℝ → ℝ → ℝ}
    (B : JacobiControlledJunctionComponents.ScaledRawJacobiBounds
      front rear CW c0 c1 c2)
    (H : Domination PF PR a CW c0 c1 c2 C0 C1 C2) :
    RawBounds PF PR front rear a C0 C1 C2 where
  w := by
    have hw0 : 0 ≤ W front 1 := by
      unfold W
      exact intervalIntegral.integral_nonneg zero_le_one (fun t _ =>
        intervalIntegral.integral_nonneg zero_le_one (fun u _ => abs_nonneg _))
    calc
      (components PR rear).w = PR * W rear 1 := rfl
      _ ≤ PR * (CW * W front 1) := mul_le_mul_of_nonneg_left B.w H.PR_pos.le
      _ = (PR * CW) * W front 1 := by ring
      _ ≤ (a * PF) * W front 1 := mul_le_mul_of_nonneg_right H.w hw0
      _ = a * (components PF front).w := by simp [components]; ring
  s0 := by
    have hw0 : 0 ≤ W front 1 := by
      unfold W
      exact intervalIntegral.integral_nonneg zero_le_one (fun t _ =>
        intervalIntegral.integral_nonneg zero_le_one (fun u _ => abs_nonneg _))
    calc
      (components PR rear).s0 = S 0 rear := rfl
      _ ≤ c0 * W front 1 := B.s0
      _ ≤ (C0 * PF) * W front 1 := mul_le_mul_of_nonneg_right H.s0 hw0
      _ = C0 * (components PF front).w := by simp [components]; ring
  s1 := by
    have hw : 0 ≤ W front 1 := by
      unfold W
      exact intervalIntegral.integral_nonneg zero_le_one (fun t _ =>
        intervalIntegral.integral_nonneg zero_le_one (fun u _ => abs_nonneg _))
    have hs : 0 ≤ S 0 front := by
      unfold S
      exact intervalIntegral.integral_nonneg zero_le_one (fun _ _ => supNorm_nonneg _)
    calc
      (components PR rear).s1 = S 1 rear / PR := rfl
      _ ≤ (c1 * (W front 1 + S 0 front)) / PR :=
        (div_le_div_iff_of_pos_right H.PR_pos).2 B.s1
      _ = (c1 / PR) * W front 1 + (c1 / PR) * S 0 front := by ring
      _ ≤ (C1 * PF) * W front 1 + C1 * S 0 front := add_le_add
        (mul_le_mul_of_nonneg_right H.s1w hw)
        (mul_le_mul_of_nonneg_right H.s1s hs)
      _ = C1 * ((components PF front).w + (components PF front).s0) := by
        simp [components]; ring
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
      (components PR rear).s2 = S 2 rear / PR ^ 2 := rfl
      _ ≤ (c2 * (W front 1 + S 0 front + S 1 front)) / PR ^ 2 :=
        (div_le_div_iff_of_pos_right (sq_pos_of_pos H.PR_pos)).2 B.s2
      _ = (c2 / PR ^ 2) * W front 1 +
          (c2 / PR ^ 2) * S 0 front +
          ((c2 / PR ^ 2) * PF) * (S 1 front / PF) := by
        field_simp [H.PF_pos.ne', H.PR_pos.ne']
        <;> ring
      _ ≤ (C2 * PF) * W front 1 + C2 * S 0 front +
          C2 * (S 1 front / PF) :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right H.s2w hw)
          (mul_le_mul_of_nonneg_right H.s2s hs0))
          (mul_le_mul_of_nonneg_right H.s2d hs1)
      _ = C2 * ((components PF front).w + (components PF front).s0 +
          (components PF front).s1) := by
        simp [components]
        field_simp [H.PF_pos.ne']

/-- The raw physical transition followed by the terminal fixed spatial
marking.  Gauge-flow and terminal-marking distortions multiply only in `W`;
the derivative gains retain fixed coefficients. -/
theorem transition_of_raw_and_fixedReparam
    {PF PR a mA MA NA C0 C1 C2 : ℝ}
    {front rear anchored : ℝ → ℝ → ℝ}
    (hPR1 : 1 ≤ PR) (hmA : 0 < mA)
    (hMA : 0 ≤ MA) (hNA : 0 ≤ NA)
    (B : RawBounds PF PR front rear a C0 C1 C2)
    (J : FixedReparamBounds rear anchored mA MA NA) :
    Transition (components PF front) (components PR anchored)
      (a * (1 / mA)) MA NA C0 C1 C2 := by
  have hPR : 0 < PR := zero_lt_one.trans_le hPR1
  have hinv : 1 / PR ≤ 1 := (div_le_one hPR).2 hPR1
  have hs1rear : 0 ≤ S 1 rear / PR := div_nonneg (by
    unfold S
    exact intervalIntegral.integral_nonneg zero_le_one (fun _ _ => supNorm_nonneg _)) hPR.le
  refine
    { w := ?_
      s0 := J.s0.trans B.s0
      s1 := ?_
      s2 := ?_ }
  · calc
      (components PR anchored).w = PR * W anchored 1 := rfl
      _ ≤ PR * ((1 / mA) * W rear 1) :=
        mul_le_mul_of_nonneg_left J.w hPR.le
      _ = (1 / mA) * (components PR rear).w := by simp [components]; ring
      _ ≤ (1 / mA) * (a * (components PF front).w) :=
        mul_le_mul_of_nonneg_left B.w (by positivity)
      _ = (a * (1 / mA)) * (components PF front).w := by ring
  · calc
      (components PR anchored).s1 = S 1 anchored / PR := rfl
      _ ≤ (MA * S 1 rear) / PR :=
        (div_le_div_iff_of_pos_right hPR).2 J.s1
      _ = MA * (S 1 rear / PR) := by ring
      _ ≤ MA * (C1 * ((components PF front).w + (components PF front).s0)) :=
        mul_le_mul_of_nonneg_left B.s1 hMA
      _ = MA * C1 * ((components PF front).w + (components PF front).s0) := by ring
  · have hsecond : (NA * S 1 rear) / PR ^ 2 ≤
        NA * (S 1 rear / PR) := by
      calc
        (NA * S 1 rear) / PR ^ 2 = NA * (S 1 rear / PR) * (1 / PR) := by
          field_simp [hPR.ne']
        _ ≤ NA * (S 1 rear / PR) * 1 := mul_le_mul_of_nonneg_left hinv
          (mul_nonneg hNA hs1rear)
        _ = NA * (S 1 rear / PR) := by ring
    calc
      (components PR anchored).s2 = S 2 anchored / PR ^ 2 := rfl
      _ ≤ (MA ^ 2 * S 2 rear + NA * S 1 rear) / PR ^ 2 :=
        (div_le_div_iff_of_pos_right (sq_pos_of_pos hPR)).2 J.s2
      _ = MA ^ 2 * (S 2 rear / PR ^ 2) +
          (NA * S 1 rear) / PR ^ 2 := by ring
      _ ≤ MA ^ 2 * (components PR rear).s2 +
          NA * (components PR rear).s1 := by
        exact add_le_add le_rfl hsecond
      _ ≤ MA ^ 2 *
            (C2 * ((components PF front).w + (components PF front).s0 +
              (components PF front).s1)) +
          NA * (C1 * ((components PF front).w + (components PF front).s0)) :=
        add_le_add (mul_le_mul_of_nonneg_left B.s2 (sq_nonneg MA))
          (mul_le_mul_of_nonneg_left B.s1 hNA)
      _ = MA ^ 2 * C2 *
            ((components PF front).w + (components PF front).s0 +
              (components PF front).s1) +
          NA * C1 * ((components PF front).w + (components PF front).s0) := by ring

end PhysicalArclengthJacobiTransition
