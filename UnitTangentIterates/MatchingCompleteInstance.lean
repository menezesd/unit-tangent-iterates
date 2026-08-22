import Mathlib
import UnitTangentIterates.MatchingComplete
import UnitTangentIterates.MatchingExponentialInstance

/-!
# The complete matching estimate is not vacuous

`MatchingComplete.curvature_measure_matching_complete` carries the hypotheses
of the exponential matching estimate together with those of the front
periodization error.  This file checks that they are simultaneously
satisfiable, by verifying every one of them for the degenerate configuration in
which all pulses vanish: `y = Y = yu = yu' = 0`, so that the rear arclength is
the identity, the curvature profile and both curvatures vanish, the fundamental
interval is `[−H/2, H/2]` itself and the period is `H`.

This is only a consistency check on the hypotheses; the substance of the
estimate is in `MatchingComplete.lean`.
-/

noncomputable section

open MeasureTheory Set

namespace MatchingCompleteInstance

open MatchingExponentialInstance

lemma exp_neg_quarter_Hval_le : Real.exp (-((1 / 4 : ℝ) * Hval)) ≤ 1 / 2 := by
  have h : (7 / 2 : ℝ) ≤ Real.exp (5 / 2) := by
    have := Real.add_one_le_exp (5 / 2 : ℝ)
    linarith
  have hpos : (0 : ℝ) < Real.exp (5 / 2) := Real.exp_pos _
  have hrw : Real.exp (-((1 / 4 : ℝ) * Hval)) = (Real.exp (5 / 2))⁻¹ := by
    rw [show (-((1 / 4 : ℝ) * Hval)) = -(5 / 2 : ℝ) by norm_num [Hval], Real.exp_neg]
  rw [hrw, inv_le_iff_one_le_mul₀ hpos]
  linarith

/-- **The hypotheses of the complete matching estimate are satisfiable.**
Every hypothesis of `MatchingComplete.curvature_measure_matching_complete` — in
particular those of the front periodization error — is verified for the
vanishing pulse, so the estimate is not vacuous. -/
theorem trivial_instance :
    (∫ u in (id (-(Hval / 2)))..(id (Hval / 2)), |(0 : ℝ → ℝ) u - (0 : ℝ → ℝ) u|)
      ≤ (MatchingExponential.pulseConst 0 0 0
            ((1 / 2 : ℝ) / Real.sqrt (1 - (1 / 2 : ℝ) ^ 2)) 1 (1 / 4)
          + MatchingExponential.rearTailConst 0 1 0
          + MatchingComplete.frontConst (1 / 2) 0 0 1 (1 / 4) 0)
        * Real.exp (-((1 / 4) * Hval)) := by
  have hHval : (0 : ℝ) < Hval := by norm_num [Hval]
  refine MatchingComplete.curvature_measure_matching_complete
    (Y := (0 : ℝ → ℝ)) (y := (0 : ℝ → ℝ)) (xH := id) (x := id)
    (Kstar := (0 : ℝ → ℝ)) (Kstar' := (0 : ℝ → ℝ)) (kH := (0 : ℝ → ℝ))
    (Kbar := (0 : ℝ → ℝ)) (KP := (0 : ℝ → ℝ))
    (yu := (0 : ℝ → ℝ)) (yu' := (0 : ℝ → ℝ))
    (a := 1 / 2) (au := 1 / 2) (C := 0) (CU := 0) (CK := 0) (DU := 0)
    (alpha := 1) (beta := 1 / 4) (H := Hval) (P := Hval) (B := 0) (Km := 0) (Kd := 0)
    (by norm_num) (fun s => le_refl 0) (fun s => by positivity) hHval exp_neg_Hval_le
    (fun s => by simp) (by norm_num) (by norm_num)
    continuous_const continuous_const (fun s => by norm_num) (fun s => by norm_num)
    (fun t => by simpa [sqrt_one_sub_zero] using (hasDerivAt_id t))
    (fun t => by simpa [sqrt_one_sub_zero] using (hasDerivAt_id t))
    rfl (fun t => by simp) (fun u => by norm_num)
    (fun u => hasDerivAt_const u 0) (fun u => by norm_num) continuous_const
    (by norm_num) (by norm_num) (fun t => by simp) (by simpa using continuous_const)
    (fun u => by simp) ?_ ?_ ?_ (by simp [Hval]; ring) hHval
    (integrable_zero _ _ _) (fun u => le_refl 0) (fun s => by simp)
    (by norm_num [Hval]) (by norm_num [Hval]) (by norm_num [Hval]) (by norm_num [Hval])
    exp_neg_quarter_Hval_le continuous_const continuous_const
    (fun s => le_refl 0) (fun s => by positivity) (by norm_num) (fun s => by norm_num)
    (by norm_num) (by norm_num) (fun u => by simp)
    (fun s => by simp [FrontPeriodization.G])
    (fun u => by simp [FrontPeriodization.G]) (by norm_num [Hval])
  · simp
  · simp
  · simp

end MatchingCompleteInstance
