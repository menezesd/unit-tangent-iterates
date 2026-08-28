import Mathlib

/-!
# Differentiation in the period parameter

This file formalizes the elementary summand calculation used in the proof of
the TeX lemma `lem:periodization` (Exponential periodization).  The spatial
variable is held fixed while the period parameter varies.
-/

noncomputable section

open Real Set

namespace PeriodizationParameterDerivative

/-- The first period derivative of one translated summand:
`d/dH z(s-mH) = -m z'(s-mH)`. -/
theorem hasDerivAt_period_translate
    {z zd : ℝ → ℝ} (hz : ∀ x, HasDerivAt z (zd x) x)
    (s m H : ℝ) :
    HasDerivAt (fun h => z (s - m * h)) (-m * zd (s - m * H)) H := by
  have hin : HasDerivAt (fun h : ℝ => s - m * h) (-m) H := by
    convert (hasDerivAt_const H s).sub
      ((hasDerivAt_const H m).mul (hasDerivAt_id H)) using 1 <;> ring
  convert (hz (s - m * H)).comp H hin using 1 <;> ring

/-- Integer-indexed version used termwise in the periodization series. -/
theorem hasDerivAt_period_translate_int
    {z zd : ℝ → ℝ} (hz : ∀ x, HasDerivAt z (zd x) x)
    (s H : ℝ) (m : ℤ) :
    HasDerivAt (fun h => z (s - (m : ℝ) * h))
      (-(m : ℝ) * zd (s - (m : ℝ) * H)) H :=
  hasDerivAt_period_translate hz s (m : ℝ) H

/-- Fundamental-cell tail geometry from the TeX proof: if
`|s| <= H/2`, then a translate with `|m| >= 1` lies at least
`(|m|-1/2)H` from its center. -/
theorem translate_distance_ge
    {s m H : ℝ} (hH : 0 ≤ H) (hs : |s| ≤ H / 2) (hm : 1 ≤ |m|) :
    (|m| - 1 / 2) * H ≤ |s - m * H| := by
  have htri : |m * H| - |s| ≤ |s - m * H| := by
    calc
      |m * H| - |s| ≤ abs (|m * H| - |s|) := le_abs_self _
      _ = abs (|s| - |m * H|) := abs_sub_comm _ _
      _ ≤ |s - m * H| := abs_abs_sub_abs_le_abs_sub _ _
  rw [abs_mul, abs_of_nonneg hH] at htri
  nlinarith

/-- The exact form used for nonzero integer translates. -/
theorem translate_distance_ge_int
    {s H : ℝ} (hH : 0 ≤ H) (hs : |s| ≤ H / 2) {m : ℤ} (hm : m ≠ 0) :
    (|(m : ℝ)| - 1 / 2) * H ≤ |s - (m : ℝ) * H| := by
  apply translate_distance_ge hH hs
  have hmnat : 1 ≤ m.natAbs := (Nat.one_le_iff_ne_zero).2 (Int.natAbs_ne_zero.2 hm)
  calc
    (1 : ℝ) ≤ (m.natAbs : ℝ) := by exact_mod_cast hmnat
    _ = |(m : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]

end PeriodizationParameterDerivative
