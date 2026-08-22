import Mathlib
import UnitTangentIterates.PerimeterInteriorTerm

/-!
# The produced derivative clause with the interior term is not vacuous

`PerimeterInteriorTerm.hasDerivAt_perimeter_of_pulse_full` carries the decay
hypotheses of the pulse and of its derivative, the identification of the defect
integrand and of the interior integrand with the periodized profile, and the
Leibniz rule at the period in question.  This file checks that they are
simultaneously satisfiable, on the degenerate configuration with vanishing
pulse: the defect vanishes identically, `P(H) = H` and `P'(H) = 1`.

This is only a consistency check on the hypotheses; the substance of the
estimate is in `PerimeterInteriorTerm.lean`.
-/

noncomputable section

open Real Set MeasureTheory

namespace PerimeterInteriorTermInstance

open PerimeterAsymptotics

/-- **The hypotheses of the produced derivative clause are satisfiable.** -/
theorem trivial_instance :
    ∃ p : ℝ, HasDerivAt (fun H' : ℝ => H') p 8 ∧
      |p - 1| ≤ (25 * 0 ^ 2
        + (1 / 2) / Real.sqrt (1 - (1 / 2 : ℝ) ^ 2) * (8 * 0)
            / ((1 / 2 - 1 / 4) * Real.exp 1)) * Real.exp (-(1 / 4) * (8 : ℝ)) := by
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
  refine PerimeterInteriorTerm.hasDerivAt_perimeter_of_pulse_full
    (y := fun _ => 0) (yp := fun _ => 0) (C := 0) (a := 1 / 2) (alpha := 1) (H := 8)
    (beta' := 1 / 4) (P := fun H' => H') (g := fun _ _ => 0) (gH := fun _ => 0)
    (by norm_num) (by norm_num) (by norm_num) hq
    (fun _ => le_refl 0) (fun x => by positivity) (fun x => by simp)
    (by norm_num) (by norm_num) (fun u => by simp)
    (fun H' u => by simp [Phi]) (fun u => by simp) (fun H' => by simp) ?_
  · simpa using hasDerivAt_const (8 : ℝ) (0 : ℝ)

end PerimeterInteriorTermInstance
