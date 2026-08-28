import UnitTangentIterates.VariableArclengthScaledJacobiTransition
import UnitTangentIterates.ControlledJunctionPathFunctionalBounds

/-!
# Time-dependent spatial reparametrization of variable-period components

The affine selected-rear density is a virtual component stage when its period
depends on time.  This module transports those components directly through a
time-dependent normalized spatial marking.  No intermediate `NormalPath` is
introduced.
-/

noncomputable section

open Set Function MeasureTheory MarkedTopology MarkedSpace PathMetric

namespace VariableArclengthScaledTimeReparamTransition

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds
  VariableArclengthScaledJacobiTransition

/-- Analytic data for a time-dependent normalized spatial marking. -/
structure TimeReparamInput
    (P : ℝ → ℝ) (source target : ℝ → ℝ → ℝ)
    (mA MA NA : ℝ) where
  psi : ℝ → ℝ → ℝ
  psi1 : ℝ → ℝ → ℝ
  psi2 : ℝ → ℝ → ℝ
  target_eq : ∀ t u, target t u = source t (psi t u)
  source_differentiable : ∀ t u, DifferentiableAt ℝ (source t) u
  source_deriv_differentiable : ∀ t u,
    DifferentiableAt ℝ (deriv (source t)) u
  psi_deriv : ∀ t u, HasDerivAt (psi t) (psi1 t u) u
  psi1_deriv : ∀ t u, HasDerivAt (psi1 t) (psi2 t u) u
  psi1_continuous : ∀ t, Continuous (psi1 t)
  psi_zero : ∀ t, psi t 0 = 0
  psi_one : ∀ t, psi t 1 = 1
  mA_pos : 0 < mA
  jacobian_lower : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, mA ≤ psi1 t u
  jacobian_upper : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, |psi1 t u| ≤ MA
  second_upper : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, |psi2 t u| ≤ NA
  period_nonnegative : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ P t
  source_bdd0 : ∀ t, BddAbove (Set.range fun u ↦ |source t u|)
  source_bdd1 : ∀ t, BddAbove (Set.range fun u ↦ |deriv (source t) u|)
  source_bdd2 : ∀ t, BddAbove
    (Set.range fun u ↦ |deriv (deriv (source t)) u|)
  source_functional : FunctionalIntegrable source
  target_functional : FunctionalIntegrable target
  source_physicalW : IntervalIntegrable
    (fun t ↦ P t * ∫ u in (0 : ℝ)..1, |source t u|) volume 0 1
  target_physicalW : IntervalIntegrable
    (fun t ↦ P t * ∫ u in (0 : ℝ)..1, |target t u|) volume 0 1

/-- A time-dependent normalized marking has the same componentwise bounds as
a fixed junction, with the physical period retained inside each time slice. -/
def TimeReparamInput.toVariableFixedReparamBounds
    {P : ℝ → ℝ} {source target : ℝ → ℝ → ℝ}
    {mA MA NA : ℝ} (H : TimeReparamInput P source target mA MA NA) :
    VariableFixedReparamBounds P source target mA MA NA := by
  have hWslice : ∀ t ∈ Icc (0 : ℝ) 1,
      P t * (∫ u in (0 : ℝ)..1, |target t u|) ≤
        (1 / mA) * (P t * ∫ u in (0 : ℝ)..1, |source t u|) := by
    intro t ht
    have hcomp := PathFunctionalsReparam.integral_abs_comp_le
      (m := mA) (a := 0) (b := 1) (eta := source t)
      (phi := H.psi t) (phi1 := H.psi1 t) H.mA_pos zero_le_one
      (Differentiable.continuous fun u ↦ H.source_differentiable t u)
      (H.psi_deriv t) (H.psi1_continuous t) (H.jacobian_lower t ht)
    have hslice : (∫ u in (0 : ℝ)..1, |target t u|) ≤
        (1 / mA) * ∫ u in (0 : ℝ)..1, |source t u| := by
      simpa [H.target_eq, H.psi_zero t, H.psi_one t] using hcomp
    calc
      P t * (∫ u in (0 : ℝ)..1, |target t u|) ≤
          P t * ((1 / mA) * ∫ u in (0 : ℝ)..1, |source t u|) :=
        mul_le_mul_of_nonneg_left hslice (H.period_nonnegative t ht)
      _ = (1 / mA) * (P t * ∫ u in (0 : ℝ)..1, |source t u|) := by ring
  have hw : physicalW P target ≤ (1 / mA) * physicalW P source := by
    unfold physicalW
    calc
      (∫ t in (0 : ℝ)..1, P t * ∫ u in (0 : ℝ)..1, |target t u|) ≤
          ∫ t in (0 : ℝ)..1,
            (1 / mA) * (P t * ∫ u in (0 : ℝ)..1, |source t u|) :=
        intervalIntegral.integral_mono_on zero_le_one H.target_physicalW
          (H.source_physicalW.const_mul _) hWslice
      _ = (1 / mA) *
          ∫ t in (0 : ℝ)..1,
            P t * ∫ u in (0 : ℝ)..1, |source t u| := by
        rw [intervalIntegral.integral_const_mul]
  have hS0slice : ∀ t ∈ Icc (0 : ℝ) 1,
      supNorm (target t) ≤ supNorm (source t) := by
    intro t _
    rw [show target t = fun u ↦ source t (H.psi t u) from funext (H.target_eq t)]
    exact PathFunctionalsReparam.supNorm_comp_le (H.source_bdd0 t) (H.psi t)
  have hs0 : S 0 target ≤ S 0 source := by
    rw [S_zero, S_zero]
    exact intervalIntegral.integral_mono_on zero_le_one
      H.target_functional.s0 H.source_functional.s0 hS0slice
  have hS1slice : ∀ t ∈ Icc (0 : ℝ) 1,
      supNorm (iteratedDeriv 1 (target t)) ≤
        MA * supNorm (iteratedDeriv 1 (source t)) := by
    intro t _
    have h := PathFunctionalsReparam.supNorm_iteratedDeriv_one_comp_le
      (fun u ↦ (H.source_differentiable t u).hasDerivAt)
      (H.psi_deriv t) (H.source_bdd1 t)
      (H.jacobian_upper t ‹t ∈ Icc (0 : ℝ) 1›)
    have htarget : target t = fun u ↦ source t (H.psi t u) :=
      funext (H.target_eq t)
    rw [htarget]
    calc
      supNorm (iteratedDeriv 1 (fun u ↦ source t (H.psi t u))) ≤
          supNorm (deriv (source t)) * MA := h
      _ = MA * supNorm (iteratedDeriv 1 (source t)) := by
        rw [iteratedDeriv_one]; ring
  have hs1 : S 1 target ≤ MA * S 1 source := by
    unfold S
    calc
      (∫ t in (0 : ℝ)..1, supNorm (iteratedDeriv 1 (target t))) ≤
          ∫ t in (0 : ℝ)..1,
            MA * supNorm (iteratedDeriv 1 (source t)) :=
        intervalIntegral.integral_mono_on zero_le_one H.target_functional.s1
          (H.source_functional.s1.const_mul _) hS1slice
      _ = MA * ∫ t in (0 : ℝ)..1,
          supNorm (iteratedDeriv 1 (source t)) := by
        rw [intervalIntegral.integral_const_mul]
  have hS2slice : ∀ t ∈ Icc (0 : ℝ) 1,
      supNorm (iteratedDeriv 2 (target t)) ≤
        MA ^ 2 * supNorm (iteratedDeriv 2 (source t)) +
          NA * supNorm (iteratedDeriv 1 (source t)) := by
    intro t _
    have h := PathFunctionalsReparam.supNorm_iteratedDeriv_two_comp_le
      (fun u ↦ (H.source_differentiable t u).hasDerivAt)
      (fun u ↦ (H.source_deriv_differentiable t u).hasDerivAt)
      (H.psi_deriv t) (H.psi1_deriv t)
      (H.source_bdd1 t) (H.source_bdd2 t)
      (H.jacobian_upper t ‹t ∈ Icc (0 : ℝ) 1›)
      (H.second_upper t ‹t ∈ Icc (0 : ℝ) 1›)
    have htarget : target t = fun u ↦ source t (H.psi t u) :=
      funext (H.target_eq t)
    rw [htarget]
    calc
      supNorm (iteratedDeriv 2 (fun u ↦ source t (H.psi t u))) ≤
          supNorm (deriv (deriv (source t))) * MA ^ 2 +
            supNorm (deriv (source t)) * NA := h
      _ = MA ^ 2 * supNorm (iteratedDeriv 2 (source t)) +
          NA * supNorm (iteratedDeriv 1 (source t)) := by
        simp only [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
          iteratedDeriv_zero, iteratedDeriv_one]
        ring
  have hs2 : S 2 target ≤ MA ^ 2 * S 2 source + NA * S 1 source := by
    unfold S
    have hrhs : IntervalIntegrable (fun t ↦
        MA ^ 2 * supNorm (iteratedDeriv 2 (source t)) +
          NA * supNorm (iteratedDeriv 1 (source t))) volume 0 1 :=
      (H.source_functional.s2.const_mul _).add
        (H.source_functional.s1.const_mul _)
    calc
      (∫ t in (0 : ℝ)..1, supNorm (iteratedDeriv 2 (target t))) ≤
          ∫ t in (0 : ℝ)..1,
            (MA ^ 2 * supNorm (iteratedDeriv 2 (source t)) +
              NA * supNorm (iteratedDeriv 1 (source t))) :=
        intervalIntegral.integral_mono_on zero_le_one
          H.target_functional.s2 hrhs hS2slice
      _ = MA ^ 2 * (∫ t in (0 : ℝ)..1,
            supNorm (iteratedDeriv 2 (source t))) +
          NA * (∫ t in (0 : ℝ)..1,
            supNorm (iteratedDeriv 1 (source t))) := by
        rw [intervalIntegral.integral_add
          (H.source_functional.s2.const_mul _)
          (H.source_functional.s1.const_mul _),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  exact ⟨hw, hs0, hs1, hs2⟩

/-- Compose exact variable-period affine Jacobi bounds with the actual
time-dependent normalized gauge marking. -/
def transition_of_raw_and_timeReparam
    {PF PR : ℝ → ℝ} {front rear target : ℝ → ℝ → ℝ}
    {mA MA NA C0 C1 C2 : ℝ}
    (R : RawBounds PF PR front rear C0 C1 C2)
    (J : TimeReparamInput PR rear target mA MA NA) :
    Transition (physicalComponents PF front) (physicalComponents PR target)
      (1 / mA) MA NA C0 C1 C2 := by
  let A := J.toVariableFixedReparamBounds
  have hInv : 0 ≤ 1 / mA := (one_div_pos.mpr J.mA_pos).le
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hMA : 0 ≤ MA := (abs_nonneg (J.psi1 0 0)).trans
    (J.jacobian_upper 0 hzero 0)
  have hNA : 0 ≤ NA := (abs_nonneg (J.psi2 0 0)).trans
    (J.second_upper 0 hzero 0)
  refine
    { w := A.w.trans (mul_le_mul_of_nonneg_left R.w hInv)
      s0 := A.s0.trans R.s0
      s1 := ?_
      s2 := ?_ }
  · exact A.s1.trans (by
      simpa [physicalComponents, mul_assoc] using
        (mul_le_mul_of_nonneg_left R.s1 hMA))
  · have hfirst := mul_le_mul_of_nonneg_left R.s2 (sq_nonneg MA)
    have hsecond := mul_le_mul_of_nonneg_left R.s1 hNA
    exact A.s2.trans (by
      simpa [physicalComponents, mul_assoc] using add_le_add hfirst hsecond)

end VariableArclengthScaledTimeReparamTransition
