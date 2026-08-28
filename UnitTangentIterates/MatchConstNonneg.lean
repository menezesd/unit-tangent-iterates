import UnitTangentIterates.PaperHairpinConfig

/-!
# The matching constant is nonnegative

`ModelOrbitDefect.matchConst` is the constant in front of the exponential in the
paper's curvature-matching estimate.  Its nonnegativity is a hypothesis of the
configured-model capstone, but it is not an independent assumption: it follows
from the sign conditions already recorded in `ProfileConstants`, together with
`0 ≤ C` and `0 ≤ CU`.

This removes `hmatch0` from the list of things a caller must supply by hand.
-/

noncomputable section

open Real

namespace PaperHairpinConfig

variable {alpha beta a au C CU CK DU DU2 D Km Kd B kstar kd : ℝ}

/-- **The matching constant is nonnegative.**  Every constituent of
`matchConst` is a product of nonnegative factors once `ProfileConstants` is
available. -/
theorem matchConst_nonneg
    (profile : ProfileConstants (alpha := alpha) (beta := beta) (a := a)
      (au := au) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (kstar := kstar) (kd := kd))
    (halpha : 0 < alpha) (hC : 0 ≤ C) (hCU0 : 0 ≤ CU) :
    0 ≤ ModelOrbitDefect.matchConst a C CK CU DU Km Kd au alpha beta B := by
  have hG : 0 ≤ FrontPeriodization.G au := by
    rw [FrontPeriodization.G]
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hGa : 0 ≤ FrontPeriodization.G a := by
    rw [FrontPeriodization.G]
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hfac : 0 ≤ 1 + FrontPeriodization.G au * DU := by
    nlinarith [mul_nonneg hG profile.prior_derivative_nonneg]
  have hKm : 0 ≤ Km :=
    le_trans (mul_nonneg hfac profile.prior_strip_nonneg) profile.isolated_sup
  have hCK : 0 ≤ CK :=
    le_trans (mul_nonneg hfac hCU0) profile.isolated_decay
  have hlip : 0 ≤ FrontPeriodization.lipConst au :=
    FrontPeriodization.lipConst_nonneg profile.prior_strip_nonneg
      profile.prior_strip_lt
  have hKd : 0 ≤ Kd := by
    refine le_trans ?_ profile.isolated_deriv_sup
    have h1 : 0 ≤ DU * au :=
      mul_nonneg profile.prior_derivative_nonneg profile.prior_strip_nonneg
    have h2 : 0 ≤ FrontPeriodization.lipConst au * (DU ^ 2 * au ^ 2) :=
      mul_nonneg hlip (by positivity)
    have h3 : 0 ≤ FrontPeriodization.G au * (DU2 * au) :=
      mul_nonneg hG (mul_nonneg profile.prior_second_nonneg
        profile.prior_strip_nonneg)
    linarith
  have hLam : 0 ≤ a / Real.sqrt (1 - a ^ 2) :=
    div_nonneg profile.current_strip_nonneg (Real.sqrt_nonneg _)
  have hab : 0 < alpha / 2 - beta := by linarith [profile.beta_lt]
  have hab2 : 0 < alpha - beta := by linarith [profile.beta_lt]
  rw [ModelOrbitDefect.matchConst]
  have hpulse : 0 ≤ MatchingExponential.pulseConst C Km Kd
      (a / Real.sqrt (1 - a ^ 2)) alpha beta := by
    rw [MatchingExponential.pulseConst]
    have he : 0 < (alpha / 2 - beta) * Real.exp 1 := by positivity
    have h1 : 0 ≤ 4 * C * (1 + Km * (a / Real.sqrt (1 - a ^ 2))) *
        (1 / ((alpha / 2 - beta) * Real.exp 1)) := by
      have : 0 ≤ 1 + Km * (a / Real.sqrt (1 - a ^ 2)) := by
        nlinarith [mul_nonneg hKm hLam]
      positivity
    have h2 : 0 ≤ 4 * C * Kd * (a / Real.sqrt (1 - a ^ 2)) *
        (2 / ((alpha / 2 - beta) * Real.exp 1)) ^ 2 := by positivity
    linarith
  have hrear : 0 ≤ MatchingExponential.rearTailConst CK alpha B := by
    rw [MatchingExponential.rearTailConst]; positivity
  have hfront : 0 ≤ MatchingComplete.frontConst au CU DU alpha beta B := by
    rw [MatchingComplete.frontConst]
    have : 0 ≤ FrontPeriodization.lipConst au * DU :=
      mul_nonneg hlip profile.prior_derivative_nonneg
    have h8 : 0 ≤ 8 * CU ^ 2 / (alpha - beta) := by positivity
    positivity
  linarith

end PaperHairpinConfig
