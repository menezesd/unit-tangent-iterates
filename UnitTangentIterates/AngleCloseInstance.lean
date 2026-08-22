import Mathlib
import UnitTangentIterates.AngleClose

/-!
# The angle comparison is not vacuous

`AngleClose.angle_sup_close` carries the decay hypotheses of the isolated
pulse, the identification of the two curvatures and the common origin of the
two tangent angles.  This file checks that they are simultaneously satisfiable,
by verifying every one of them for the degenerate configuration in which the
pulse vanishes: `y = y' = 0`, so that both curvatures vanish and both tangent
angles are constant.

This is only a consistency check on the hypotheses; the substance of the
estimate is in `AngleClose.lean`.
-/

noncomputable section

open MeasureTheory Set Real

namespace AngleCloseInstance

/-- **The hypotheses of the angle comparison are satisfiable.** -/
theorem trivial_instance :
    |(0 : ℝ → ℝ) 0 - (0 : ℝ → ℝ) 0|
      ≤ (FrontPeriodization.lipConst (1 / 2) * 0 * (8 * 0 ^ 2 / (1 - 1 / 8))
          + 2 * 0 / 1) * Real.exp (-(1 / 8 * (8 : ℝ))) := by
  refine AngleClose.angle_sup_close (y := (0 : ℝ → ℝ)) (yp := (0 : ℝ → ℝ))
    (Kstar := (0 : ℝ → ℝ)) (KH := (0 : ℝ → ℝ)) (ThH := (0 : ℝ → ℝ)) (Ths := (0 : ℝ → ℝ))
    (C := 0) (CK := 0) (D := 0) (a := 1 / 2) (alpha := 1) (beta := 1 / 8) (H := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    continuous_const continuous_const (fun s => le_refl 0) (fun s => by positivity)
    (by norm_num) (fun s => by norm_num) (by norm_num) (by norm_num)
    (fun u => by simp) (fun s => by simp [FrontPeriodization.G])
    (fun t => by simp [FrontPeriodization.G]) (integrable_zero _ _ _)
    (fun u => le_refl 0) (fun s => by simp)
    (fun t => hasDerivAt_const t 0) (fun t => hasDerivAt_const t 0) rfl
    (by norm_num)
  · have h : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
    have hrw : Real.exp (-(1 / 8 * (8:ℝ))) = (Real.exp 1)⁻¹ := by
      rw [show (-(1 / 8 * (8:ℝ))) = -(1 : ℝ) by norm_num, Real.exp_neg]
    rw [hrw, inv_le_iff_one_le_mul₀ hpos]
    linarith

end AngleCloseInstance
