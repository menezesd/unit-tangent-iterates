import UnitTangentIterates.SteeringJointC1

/-!
# Strict positivity of the selected-steering linearization

This exports the strict form of the zeroth-order coefficient estimate used in
the proof of TeX Lemma `lem:path-inverse`.  The quantitative lower bound is in
`SteeringJointC1.linCoeff_ge`; the statements below turn it into the positivity
and nonvanishing certificates required by periodic linear inversion.
-/

open Set Real

namespace SteeringJointC1

variable {q delta : ℝ → ℝ → ℝ} {kap : ℝ}

/-- On the selected strip, the coefficient `q cos δ` in the periodic
linearized steering equation is strictly positive. -/
theorem linCoeff_pos (hkap : 0 < kap) (hkap1 : kap < 1)
    (hqlow : ∀ a x, kap⁻¹ ≤ q a x)
    (hstrip : ∀ a x, delta a x ∈ Icc (0 : ℝ) (arcsin kap))
    (a x : ℝ) : 0 < linCoeff q delta a x := by
  have hs : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  apply lt_of_lt_of_le (div_pos hs hkap)
  exact linCoeff_ge hkap hqlow hstrip a x

/-- Consequently the selected-steering linearization coefficient never
vanishes on any parameter slice. -/
theorem linCoeff_ne_zero (hkap : 0 < kap) (hkap1 : kap < 1)
    (hqlow : ∀ a x, kap⁻¹ ≤ q a x)
    (hstrip : ∀ a x, delta a x ∈ Icc (0 : ℝ) (arcsin kap))
    (a x : ℝ) : linCoeff q delta a x ≠ 0 :=
  ne_of_gt (linCoeff_pos hkap hkap1 hqlow hstrip a x)

end SteeringJointC1
