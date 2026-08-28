import UnitTangentIterates.VariableArclengthScaledJacobiTransition
import UnitTangentIterates.ConfiguredRecursiveSourceP0

/-!
# Fully physical variable-period Jacobi components

The variable-period `W` component must be accompanied by spatial, rather than
unit-parameter, derivative components.  Thus the first and second marked
derivatives are divided slicewise by the physical period and its square.  This
is the component realization used by the inverse-Jacobi lemma in the paper.

The constants below are the explicit uniform coefficients from that lemma.
They use only the curvature ceiling: total turning gives the front-period
floor `2*pi/kh`, and the rear arclength is at least
`sqrt (1-kh^2)` times the front arclength.
-/

noncomputable section

open Set MeasureTheory MarkedTopology

namespace FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds
  VariableArclengthScaledJacobiTransition

/-- First spatial component in a moving physical period. -/
def spatialS1 (P : ℝ → ℝ) (eta : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, supNorm (iteratedDeriv 1 (eta t)) / P t

/-- Second spatial component in a moving physical period. -/
def spatialS2 (P : ℝ → ℝ) (eta : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, supNorm (iteratedDeriv 2 (eta t)) / P t ^ 2

/-- The coordinate-correct physical components for a moving period. -/
def physicalComponents (P : ℝ → ℝ) (eta : ℝ → ℝ → ℝ) : Components where
  w := physicalW P eta
  s0 := S 0 eta
  s1 := spatialS1 P eta
  s2 := spatialS2 P eta

theorem physicalComponents_nonnegative
    {P : ℝ → ℝ} (hP : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ P t)
    (eta : ℝ → ℝ → ℝ) :
    (physicalComponents P eta).Nonnegative := by
  refine
    { w := VariableArclengthScaledJacobiTransition.physicalW_nonnegative hP eta
      s0 := by simpa [physicalComponents] using S_nonneg 0 eta
      s1 := ?_
      s2 := ?_ }
  · unfold physicalComponents spatialS1
    exact intervalIntegral.integral_nonneg zero_le_one fun t ht =>
      div_nonneg (supNorm_nonneg _) (hP t ht)
  · unfold physicalComponents spatialS2
    exact intervalIntegral.integral_nonneg zero_le_one fun t ht =>
      div_nonneg (supNorm_nonneg _) (sq_nonneg (P t))

/-- Slicewise fully physical estimates, together with exactly the
integrability needed to pass to the path components. -/
structure AnalyticInput
    (PF PR : ℝ → ℝ) (front rear : ℝ → ℝ → ℝ)
    (C0 C1 C2 : ℝ) : Prop where
  frontW_integrable : IntervalIntegrable
    (fun t => PF t * ∫ u in (0 : ℝ)..1, |front t u|) volume 0 1
  rearW_integrable : IntervalIntegrable
    (fun t => PR t * ∫ u in (0 : ℝ)..1, |rear t u|) volume 0 1
  w : ∀ t ∈ Icc (0 : ℝ) 1,
    PR t * (∫ u in (0 : ℝ)..1, |rear t u|) ≤
      PF t * ∫ u in (0 : ℝ)..1, |front t u|
  rearS0_integrable : IntervalIntegrable
    (fun t => supNorm (rear t)) volume 0 1
  frontS0_integrable : IntervalIntegrable
    (fun t => supNorm (front t)) volume 0 1
  s0 : ∀ t, supNorm (rear t) ≤
    C0 * (PF t * ∫ u in (0 : ℝ)..1, |front t u|)
  rearS1_integrable : IntervalIntegrable
    (fun t => supNorm (iteratedDeriv 1 (rear t)) / PR t) volume 0 1
  frontS1_integrable : IntervalIntegrable
    (fun t => supNorm (iteratedDeriv 1 (front t)) / PF t) volume 0 1
  s1 : ∀ t, supNorm (iteratedDeriv 1 (rear t)) / PR t ≤
    C1 * (PF t * (∫ u in (0 : ℝ)..1, |front t u|) +
      supNorm (front t))
  rearS2_integrable : IntervalIntegrable
    (fun t => supNorm (iteratedDeriv 2 (rear t)) / PR t ^ 2) volume 0 1
  s2 : ∀ t, supNorm (iteratedDeriv 2 (rear t)) / PR t ^ 2 ≤
    C2 * (PF t * (∫ u in (0 : ℝ)..1, |front t u|) +
      supNorm (front t) + supNorm (iteratedDeriv 1 (front t)) / PF t)

/-- Integrated fully physical inverse-Jacobi estimates. -/
structure RawBounds
    (PF PR : ℝ → ℝ) (front rear : ℝ → ℝ → ℝ)
    (C0 C1 C2 : ℝ) : Prop where
  w : (physicalComponents PR rear).w ≤ (physicalComponents PF front).w
  s0 : (physicalComponents PR rear).s0 ≤
    C0 * (physicalComponents PF front).w
  s1 : (physicalComponents PR rear).s1 ≤
    C1 * ((physicalComponents PF front).w +
      (physicalComponents PF front).s0)
  s2 : (physicalComponents PR rear).s2 ≤
    C2 * ((physicalComponents PF front).w +
      (physicalComponents PF front).s0 +
      (physicalComponents PF front).s1)

def AnalyticInput.toRawBounds
    {PF PR : ℝ → ℝ} {front rear : ℝ → ℝ → ℝ}
    {C0 C1 C2 : ℝ} (H : AnalyticInput PF PR front rear C0 C1 C2) :
    RawBounds PF PR front rear C0 C1 C2 := by
  refine { w := ?_, s0 := ?_, s1 := ?_, s2 := ?_ }
  · exact intervalIntegral.integral_mono_on zero_le_one
      H.rearW_integrable H.frontW_integrable H.w
  · unfold physicalComponents S physicalW
    calc
      (∫ t in (0 : ℝ)..1, supNorm (rear t)) ≤
          ∫ t in (0 : ℝ)..1,
            C0 * (PF t * ∫ u in (0 : ℝ)..1, |front t u|) :=
        intervalIntegral.integral_mono_on zero_le_one H.rearS0_integrable
          (H.frontW_integrable.const_mul C0) (fun t _ => H.s0 t)
      _ = C0 * ∫ t in (0 : ℝ)..1,
          PF t * ∫ u in (0 : ℝ)..1, |front t u| := by
        rw [intervalIntegral.integral_const_mul]
  · unfold physicalComponents spatialS1 S physicalW
    calc
      (∫ t in (0 : ℝ)..1,
          supNorm (iteratedDeriv 1 (rear t)) / PR t) ≤
          ∫ t in (0 : ℝ)..1,
            C1 * (PF t * (∫ u in (0 : ℝ)..1, |front t u|) +
              supNorm (front t)) :=
        intervalIntegral.integral_mono_on zero_le_one H.rearS1_integrable
          ((H.frontW_integrable.add H.frontS0_integrable).const_mul C1)
          (fun t _ => H.s1 t)
      _ = C1 * ((∫ t in (0 : ℝ)..1,
          PF t * ∫ u in (0 : ℝ)..1, |front t u|) +
          ∫ t in (0 : ℝ)..1, supNorm (front t)) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add H.frontW_integrable H.frontS0_integrable]
  · unfold physicalComponents spatialS1 spatialS2 S physicalW
    calc
      (∫ t in (0 : ℝ)..1,
          supNorm (iteratedDeriv 2 (rear t)) / PR t ^ 2) ≤
          ∫ t in (0 : ℝ)..1,
            C2 * (PF t * (∫ u in (0 : ℝ)..1, |front t u|) +
              supNorm (front t) +
              supNorm (iteratedDeriv 1 (front t)) / PF t) :=
        intervalIntegral.integral_mono_on zero_le_one H.rearS2_integrable
          (((H.frontW_integrable.add H.frontS0_integrable).add
            H.frontS1_integrable).const_mul C2) (fun t _ => H.s2 t)
      _ = C2 * ((∫ t in (0 : ℝ)..1,
          PF t * ∫ u in (0 : ℝ)..1, |front t u|) +
          (∫ t in (0 : ℝ)..1, supNorm (front t)) +
          ∫ t in (0 : ℝ)..1,
            supNorm (iteratedDeriv 1 (front t)) / PF t) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add
            (H.frontW_integrable.add H.frontS0_integrable)
            H.frontS1_integrable,
          intervalIntegral.integral_add H.frontW_integrable H.frontS0_integrable]

/-- The intrinsic estimate is an identity-distortion stable transition. -/
def RawBounds.toTransition
    {PF PR : ℝ → ℝ} {front rear : ℝ → ℝ → ℝ}
    {C0 C1 C2 : ℝ} (H : RawBounds PF PR front rear C0 C1 C2) :
    Transition (physicalComponents PF front) (physicalComponents PR rear)
      1 1 0 C0 C1 C2 where
  w := by simpa using H.w
  s0 := H.s0
  s1 := by simpa using H.s1
  s2 := by simpa using H.s2

/-- Turning-number lower bound for the front period. -/
def frontPeriodFloor (kh : ℝ) : ℝ := 2 * Real.pi / kh

/-- Corresponding lower bound for the selected-rear arclength period. -/
def rearPeriodFloor (kh : ℝ) : ℝ :=
  Real.sqrt (1 - kh ^ 2) * frontPeriodFloor kh

/-- Zeroth-order inverse-Jacobi gain. -/
def ceilingC0 (kh : ℝ) : ℝ :=
  1 / (1 - Real.exp (-(rearPeriodFloor kh)))

/-- First spatial inverse-Jacobi gain. -/
def ceilingC1 (kh : ℝ) : ℝ :=
  max (ceilingC0 kh) (1 / Real.sqrt (1 - kh ^ 2))

/-- Second spatial inverse-Jacobi gain. -/
def ceilingC2 (kh : ℝ) : ℝ :=
  max (ceilingC0 kh) <| max
    (2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
      1 / Real.sqrt (1 - kh ^ 2))
    (1 / Real.sqrt (1 - kh ^ 2) ^ 2)

theorem frontPeriodFloor_pos {kh : ℝ} (hkh : 0 < kh) :
    0 < frontPeriodFloor kh := by
  exact div_pos (mul_pos (by norm_num) Real.pi_pos) hkh

theorem rearPeriodFloor_pos {kh : ℝ} (hkh0 : 0 < kh) (hkh1 : kh < 1) :
    0 < rearPeriodFloor kh := by
  exact mul_pos (Real.sqrt_pos.2 (by nlinarith)) (frontPeriodFloor_pos hkh0)

theorem ceilingC0_nonnegative {kh : ℝ} (hkh0 : 0 < kh) (hkh1 : kh < 1) :
    0 ≤ ceilingC0 kh := by
  have hfloor := rearPeriodFloor_pos hkh0 hkh1
  exact (one_div_pos.mpr (JacobiNormalized.one_sub_exp_pos hfloor)).le

theorem ceilingC1_nonnegative {kh : ℝ} (hkh0 : 0 < kh) (hkh1 : kh < 1) :
    0 ≤ ceilingC1 kh := by
  exact (ceilingC0_nonnegative hkh0 hkh1).trans (le_max_left _ _)

theorem ceilingC2_nonnegative {kh : ℝ} (hkh0 : 0 < kh) (hkh1 : kh < 1) :
    0 ≤ ceilingC2 kh := by
  exact (ceilingC0_nonnegative hkh0 hkh1).trans (le_max_left _ _)

/-- The fixed configured ceilings used by every row of the finite tower. -/
def configuredC0 : ℝ :=
  ceilingC0 ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
def configuredC1 : ℝ :=
  ceilingC1 ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
def configuredC2 : ℝ :=
  ceilingC2 ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh

private theorem configuredSourceKh_pos :
    0 < ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh := by
  rw [ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_eq]
  norm_num

theorem configuredC0_nonnegative : 0 ≤ configuredC0 := by
  exact ceilingC0_nonnegative
    configuredSourceKh_pos
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one

theorem configuredC1_nonnegative : 0 ≤ configuredC1 := by
  exact ceilingC1_nonnegative
    configuredSourceKh_pos
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one

theorem configuredC2_nonnegative : 0 ≤ configuredC2 := by
  exact ceilingC2_nonnegative
    configuredSourceKh_pos
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one

end FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi
