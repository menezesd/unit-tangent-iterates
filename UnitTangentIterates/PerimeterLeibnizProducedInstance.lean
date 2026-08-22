import Mathlib
import UnitTangentIterates.PerimeterLeibnizProduced

/-!
# The derivative clause with the Leibniz rule discharged is not vacuous

`PerimeterLeibnizProduced.hasDerivAt_perimeter_of_pulse_leibniz` carries the
decay hypotheses of the pulse and of its derivative, the bound on the
periodizations and the identification of the perimeter defect with the centred
cell integral.  This file checks that they are simultaneously satisfiable, on
the degenerate configuration with vanishing pulse: the defect vanishes
identically, `P(H) = H` and `P'(H) = 1`.

This is only a consistency check on the hypotheses; the substance of the
estimate is in `PerimeterLeibnizProduced.lean`.
-/

noncomputable section

open Real Set MeasureTheory

namespace PerimeterLeibnizProducedInstance

open PerimeterAsymptotics

/-- **The hypotheses of the derivative clause with the Leibniz rule discharged
are satisfiable.** -/
theorem trivial_instance :
    ∃ p : ℝ, HasDerivAt (fun H : ℝ => H) p 8 ∧
      |p - 1| ≤ (25 * 0 ^ 2
        + (1 / 2) / Real.sqrt (1 - (1 / 2 : ℝ) ^ 2) * (8 * 0)
            / ((1 / 2 - 1 / 4) * Real.exp 1)) * Real.exp (-(1 / 4) * (8 : ℝ)) := by
  have hthr : Real.exp (-(1 : ℝ) * ((8 : ℝ) / 2)) ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
    have hle : Real.exp (-(1 : ℝ) * ((8 : ℝ) / 2)) ≤ Real.exp (-(1 : ℝ)) :=
      Real.exp_le_exp.mpr (by norm_num)
    refine hle.trans ?_
    rw [Real.exp_neg 1, inv_le_iff_one_le_mul₀ hpos]
    linarith
  exact PerimeterLeibnizProduced.hasDerivAt_perimeter_of_pulse_leibniz
    (y := fun _ => 0) (yp := fun _ => 0) (C := 0) (a := 1 / 2) (alpha := 1) (H0 := 8)
    (beta' := 1 / 4) (P := fun H => H)
    (by norm_num) (by norm_num) (by norm_num) hthr
    (fun x => hasDerivAt_const x 0) continuous_const (fun _ => le_refl 0)
    (fun x => by simp) (fun x => by simp)
    (by norm_num) (by norm_num) (fun Q _ v => by simp)
    (fun H => by simp [Phi])

end PerimeterLeibnizProducedInstance
