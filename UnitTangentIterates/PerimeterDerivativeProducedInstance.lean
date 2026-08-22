import Mathlib
import UnitTangentIterates.PerimeterDerivativeProduced

/-!
# The produced derivative clause is not vacuous

`PerimeterDerivativeProduced.hasDerivAt_perimeter_of_pulse` carries the decay
hypotheses of the pulse, the identification of the defect integrand with the
periodized profile, the Leibniz rule at the period in question and the
smallness of the interior term.  This file checks that they are simultaneously
satisfiable, on the degenerate configuration with vanishing pulse: the defect
vanishes identically, `P(H) = H` and `P'(H) = 1`.

This is only a consistency check on the hypotheses; the substance of the
estimate is in `PerimeterDerivativeProduced.lean`.
-/

noncomputable section

open Real Set MeasureTheory

namespace PerimeterDerivativeProducedInstance

open PerimeterAsymptotics

/-- **The hypotheses of the produced derivative clause are satisfiable.** -/
theorem trivial_instance :
    ∃ p : ℝ, HasDerivAt (fun H' : ℝ => H') p 8 ∧
      |p - 1| ≤ (25 * 0 ^ 2 + 0) * Real.exp (-(1 : ℝ) * (8 : ℝ)) := by
  have hq : Real.exp (-(1 : ℝ) * (8 : ℝ)) ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
    have hle : Real.exp (-(1 : ℝ) * (8 : ℝ)) ≤ Real.exp (-(1 : ℝ)) :=
      Real.exp_le_exp.mpr (by norm_num)
    refine hle.trans ?_
    rw [Real.exp_neg 1, inv_le_iff_one_le_mul₀ hpos]
    linarith
  refine PerimeterDerivativeProduced.hasDerivAt_perimeter_of_pulse
    (y := fun _ => 0) (C := 0) (alpha := 1) (H0 := 8) (P := fun H' => H')
    (g := fun _ _ => 0) (gH := fun _ => 0) (Ci := 0)
    (by norm_num) (by norm_num) hq (fun _ => le_refl 0) (fun s => by positivity)
    (fun u => by simp) (fun H' s => by simp [Phi]) (fun H' => by simp) ?_ (by simp)
  · simpa using hasDerivAt_const (8 : ℝ) (0 : ℝ)

end PerimeterDerivativeProducedInstance
