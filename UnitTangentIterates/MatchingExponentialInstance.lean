import Mathlib
import UnitTangentIterates.MatchingExponential

/-!
# The exponential matching estimate is not vacuous

`MatchingExponential.curvature_measure_matching_exp_of_pulse` carries a long
list of hypotheses — the decay and the periodization of the steering pulse, the
bounds on the curvature profile, the position of the endpoints of the
fundamental interval, and the integrability of the data.  This file checks that
they are simultaneously satisfiable, by verifying every one of them for the
degenerate configuration in which the pulse vanishes: `y = Y = 0`, so that the
rear arclength is the identity, the curvature profile and both curvatures
vanish, the fundamental interval is `[−H/2, H/2]` itself and the period is `H`.

This is only a consistency check on the hypotheses; the substance of the
estimate is in `MatchingExponential.lean`.
-/

noncomputable section

open MeasureTheory Set

namespace MatchingExponentialInstance

/-- The period used in the check. -/
def Hval : ℝ := 10

lemma exp_neg_Hval_le : Real.exp (-(1 : ℝ) * Hval) ≤ 1 / 2 := by
  have h : (11 : ℝ) ≤ Real.exp 10 := by
    have := Real.add_one_le_exp (10 : ℝ)
    linarith
  have hpos : (0 : ℝ) < Real.exp 10 := Real.exp_pos _
  have : Real.exp (-(1 : ℝ) * Hval) = (Real.exp 10)⁻¹ := by
    rw [show (-(1 : ℝ) * Hval) = -(10 : ℝ) by norm_num [Hval], Real.exp_neg]
  rw [this]
  rw [inv_le_iff_one_le_mul₀ hpos]
  linarith

lemma sqrt_one_sub_zero : Real.sqrt (1 - (0 : ℝ) ^ 2) = 1 := by
  norm_num

/-- **The hypotheses of the exponential matching estimate are satisfiable.**
Every hypothesis of `MatchingExponential.curvature_measure_matching_exp_of_pulse`
is verified for the vanishing pulse, so the estimate is not vacuous. -/
theorem trivial_instance :
    (∫ u in (id (-(Hval / 2)))..(id (Hval / 2)), |(0 : ℝ → ℝ) u - (0 : ℝ → ℝ) u|)
      ≤ (MatchingExponential.pulseConst 0 0 0
            ((1 / 2 : ℝ) / Real.sqrt (1 - (1 / 2 : ℝ) ^ 2)) 1 (1 / 4)
          + MatchingExponential.rearTailConst 0 1 0 + 0) * Real.exp (-((1 / 4) * Hval)) := by
  have hHval : (0 : ℝ) < Hval := by norm_num [Hval]
  have hzero : ∀ s : ℝ, ((0 : ℝ → ℝ) s) = 0 := fun _ => rfl
  have htsum : ∀ s : ℝ, ((0 : ℝ → ℝ) s) = ∑' _ : ℤ, ((0 : ℝ → ℝ) (s - 0)) := by
    intro s; simp
  refine MatchingExponential.curvature_measure_matching_exp_of_pulse
    (Y := (0 : ℝ → ℝ)) (y := (0 : ℝ → ℝ)) (xH := id) (x := id)
    (Kstar := (0 : ℝ → ℝ)) (Kstar' := (0 : ℝ → ℝ)) (kH := (0 : ℝ → ℝ))
    (Kbar := (0 : ℝ → ℝ)) (KP := (0 : ℝ → ℝ))
    (a := 1 / 2) (C := 0) (CK := 0) (alpha := 1) (beta := 1 / 4) (H := Hval)
    (P := Hval) (B := 0) (Km := 0) (Kd := 0) (C4 := 0)
    (by norm_num) (fun s => le_refl 0) (fun s => by positivity) hHval exp_neg_Hval_le
    (fun s => by simp) (by norm_num) (by norm_num)
    continuous_const continuous_const (fun s => by norm_num) (fun s => by norm_num)
    (fun t => by simpa [sqrt_one_sub_zero] using (hasDerivAt_id t))
    (fun t => by simpa [sqrt_one_sub_zero] using (hasDerivAt_id t))
    rfl (fun t => by simp) (fun u => by norm_num)
    (fun u => hasDerivAt_const u 0) (fun u => by norm_num) continuous_const
    (by norm_num) (fun t => by simp) (by simpa using continuous_const)
    (fun u => by simp) ?_ ?_ ?_ (by simp [Hval]; ring) hHval
    (integrable_zero _ _ _) (fun u => le_refl 0) (fun s => by simp)
    (by norm_num [Hval]) (by norm_num [Hval]) (by norm_num [Hval]) (by norm_num [Hval])
    (by simp)
  · simp
  · simp
  · simp

end MatchingExponentialInstance
