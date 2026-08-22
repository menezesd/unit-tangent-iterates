import Mathlib
import UnitTangentIterates.PerimeterAsymptoticsProduced

/-!
# The produced defect asymptotics is not vacuous

`PerimeterAsymptoticsProduced.abs_defect_sub_delta_le_pulse` carries the decay
hypotheses of the isolated pulse, the identification of the periodized profile
and the integrability hypotheses of the defect.  This file checks that they are
simultaneously satisfiable, by verifying every one of them for the degenerate
configuration in which the pulse vanishes: `y = 0`, hence `Y_H = 0`, the rear
half-perimeter is `P(H) = H` and the defect and its whole-line limit both
vanish.

This is only a consistency check on the hypotheses; the substance of the
estimate is in `PerimeterAsymptoticsProduced.lean`.
-/

noncomputable section

open Real Set MeasureTheory

namespace PerimeterAsymptoticsProducedInstance

open PerimeterAsymptotics

/-- The defect integrand of the vanishing pulse vanishes. -/
lemma Phi_zero : Phi 0 = 0 := by simp [Phi]

/-- **The hypotheses of the produced defect asymptotics are satisfiable.** -/
theorem trivial_instance :
    |((8 : ℝ) - (∫ _s in (0:ℝ)..(8:ℝ), Real.sqrt (1 - (0:ℝ) ^ 2))) - ∫ _s : ℝ, Phi 0|
      ≤ ((1 / 2) / Real.sqrt (1 - (1 / 2 : ℝ) ^ 2) * (4 * 0)
          / ((1 / 2 - 1 / 4) * Real.exp 1) + 2 * 0 ^ 2 / 1) * Real.exp (-(1 / 4) * (8 : ℝ)) := by
  have hq : Real.exp (-(1 : ℝ) * (8 : ℝ)) ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
    have hle : Real.exp (-(1 : ℝ) * (8 : ℝ)) ≤ Real.exp (-(1 : ℝ)) :=
      Real.exp_le_exp.mpr (by norm_num)
    have hrw : Real.exp (-(1 : ℝ)) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    refine hle.trans ?_
    rw [hrw, inv_le_iff_one_le_mul₀ hpos]
    linarith
  exact PerimeterAsymptoticsProduced.abs_defect_sub_delta_le_pulse
    (y := fun _ => 0) (Y := fun _ => 0) (C := 0) (a := 1 / 2) (alpha := 1) (H := 8)
    (beta' := 1 / 4) (by norm_num) (by norm_num) (by norm_num) hq
    (fun _ => le_refl 0) (fun _ => by norm_num) (fun s => by positivity)
    (by norm_num) (by norm_num) (fun u => by simp) (fun s => by simp)
    (by simp)
    (fun _ => rfl)
    (by simp [Phi_zero])
    (by simp)

end PerimeterAsymptoticsProducedInstance
