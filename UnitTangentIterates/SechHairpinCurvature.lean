import Mathlib
import UnitTangentIterates.SechPulse
import UnitTangentIterates.FrontPeriodization

/-!
# The isolated curvature of the explicit pulse

A matching configuration of *A Noncircular Oval with Convex Unit-Tangent
Iterates* carries, besides the steering pulse `y` of the isolated pair, the
*intrinsic curvature of the isolated hairpin*

```
  K_*(u) = y_u(u) + G(y_u(u))·y_u'(u),        G(z) = (1-z²)^{-1/2},
```

built from the steering pulse `y_u` of the previous model.  This file computes
`K_*` for the explicit pulse `y_u = A·sech²(λ·)` of `SechPulse.lean`, with
`A = πλ/2`, so that `∫ y_u = π`:

* `curv_nonneg`, `pulse_le_two_mul_curv`, `curv_le_two_mul_pulse` — `K_*` is
  nonnegative and comparable with `y_u`;
* `hasDerivAt_curv`, `continuous_curv`, `continuous_curvD` — `K_*` is `C¹`, with
  derivative `K_*' = y_u' + G'(y_u)(y_u')² + G(y_u)y_u''`;
* `abs_curvD_le_pulse`, `abs_curvD_le_curv` — the relative derivative bounds
  `|K_*'| ≤ 3λ y_u ≤ 6λ K_*`;
* `curv_le_exp`, `abs_curvD_le_exp` — the exponential majorants;
* `integral_curv` — the total curvature `∫_ℝ K_* = π`.

All of it under `0 < λ ≤ 1/100`, which makes the amplitude `A = πλ/2 ≤ 1/50`
small enough for the crude bounds `G ≤ 2`, `G' ≤ 8z` on the strip.
-/

noncomputable section

open Real MeasureTheory Filter Topology Set

namespace SechHairpin

open FrontPeriodization

/-- The amplitude `A = πλ/2` making the mass of `A·sech²(λ·)` equal to `π`. -/
def amp (lam : ℝ) : ℝ := Real.pi * lam / 2

/-- The steering pulse of the previous model. -/
def pul (lam : ℝ) : ℝ → ℝ := SechPulse.pulse (amp lam) lam

/-- Its derivative. -/
def pulD (lam : ℝ) : ℝ → ℝ := SechPulse.pulseD (amp lam) lam

/-- Its second derivative. -/
def pulD2 (lam : ℝ) : ℝ → ℝ := SechPulse.pulseD2 (amp lam) lam

/-- The intrinsic curvature of the isolated hairpin, `K_* = y + G(y)y'`. -/
def curv (lam : ℝ) : ℝ → ℝ := fun u => pul lam u + G (pul lam u) * pulD lam u

/-- Its derivative, `K_*' = y' + G'(y)(y')² + G(y)y''`. -/
def curvD (lam : ℝ) : ℝ → ℝ := fun u =>
  pulD lam u + (lipConst (pul lam u) * (pulD lam u) ^ 2 + G (pul lam u) * pulD2 lam u)

variable {lam : ℝ}

/-! ### Crude bounds for `G` and `G'` on a small strip -/

/-- `G(z) ≤ 2` on `[0, 1/2]`. -/
theorem G_le_two {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 2) : G z ≤ 2 := by
  have h1 : (1:ℝ) / 4 ≤ 1 - z ^ 2 := by nlinarith
  have h2 : (1:ℝ) / 2 ≤ Real.sqrt (1 - z ^ 2) := by
    have := Real.sqrt_le_sqrt h1
    rwa [show Real.sqrt (1/4) = 1/2 by
      rw [show (1:ℝ)/4 = (1/2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
  have hpos : (0:ℝ) < Real.sqrt (1 - z ^ 2) := lt_of_lt_of_le (by norm_num) h2
  rw [G, inv_le_comm₀ hpos (by norm_num)]
  linarith

/-- `G'(z) = z/((1-z²)√(1-z²)) ≤ 8z` on `[0, 1/2]`. -/
theorem lipConst_le_eight {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 2) : lipConst z ≤ 8 * z := by
  have h1 : (1:ℝ) / 4 ≤ 1 - z ^ 2 := by nlinarith
  have h2 : (1:ℝ) / 2 ≤ Real.sqrt (1 - z ^ 2) := by
    have := Real.sqrt_le_sqrt h1
    rwa [show Real.sqrt (1/4) = 1/2 by
      rw [show (1:ℝ)/4 = (1/2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
  have hprod : (1:ℝ) / 8 ≤ (1 - z ^ 2) * Real.sqrt (1 - z ^ 2) := by nlinarith
  have hpos : (0:ℝ) < (1 - z ^ 2) * Real.sqrt (1 - z ^ 2) := lt_of_lt_of_le (by norm_num) hprod
  rw [lipConst, div_le_iff₀ hpos]
  nlinarith

/-! ### The amplitude -/

theorem amp_pos (hlam : 0 < lam) : 0 < amp lam := by
  rw [amp]; positivity

theorem amp_le_two_mul (hlam : 0 < lam) : amp lam ≤ 2 * lam := by
  rw [amp]
  nlinarith [Real.pi_le_four, hlam]

theorem amp_le (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) : amp lam ≤ 1 / 50 := by
  have := amp_le_two_mul hlam
  linarith

theorem amp_nonneg (hlam : 0 < lam) : 0 ≤ amp lam := (amp_pos hlam).le

/-! ### The pulse -/

theorem pul_nonneg (hlam : 0 < lam) (s : ℝ) : 0 ≤ pul lam s :=
  SechPulse.pulse_nonneg (amp_nonneg hlam) s

theorem pul_le_amp (hlam : 0 < lam) (s : ℝ) : pul lam s ≤ amp lam :=
  SechPulse.pulse_le (amp_nonneg hlam) s

theorem pul_le_half (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) (s : ℝ) : pul lam s ≤ 1 / 2 := by
  have := pul_le_amp hlam s
  have := amp_le hlam hlam'
  linarith

theorem pul_le_exp (hlam : 0 < lam) (s : ℝ) :
    pul lam s ≤ 4 * amp lam * Real.exp (-(2 * lam) * |s|) :=
  SechPulse.pulse_le_exp (amp_nonneg hlam) hlam.le s

theorem abs_pulD_le (hlam : 0 < lam) (s : ℝ) : |pulD lam s| ≤ 2 * lam * pul lam s :=
  SechPulse.abs_pulseD_le (amp_nonneg hlam) hlam.le s

theorem abs_pulD2_le (hlam : 0 < lam) (s : ℝ) : |pulD2 lam s| ≤ 8 * lam ^ 2 * pul lam s :=
  SechPulse.abs_pulseD2_le (amp_nonneg hlam) s

theorem hasDerivAt_pul (s : ℝ) : HasDerivAt (pul lam) (pulD lam s) s :=
  SechPulse.hasDerivAt_pulse s

theorem hasDerivAt_pulD (s : ℝ) : HasDerivAt (pulD lam) (pulD2 lam s) s :=
  SechPulse.hasDerivAt_pulseD s

theorem continuous_pul : Continuous (pul lam) := SechPulse.continuous_pulse

theorem continuous_pulD : Continuous (pulD lam) := SechPulse.continuous_pulseD

theorem continuous_pulD2 : Continuous (pulD2 lam) := SechPulse.continuous_pulseD2

theorem integrable_pul (hlam : 0 < lam) : Integrable (pul lam) :=
  SechPulse.integrable_pulse (amp_nonneg hlam) hlam

/-- The mass of the pulse is `π`. -/
theorem integral_pul (hlam : 0 < lam) : (∫ s, pul lam s) = Real.pi := by
  rw [pul, SechPulse.integral_pulse (amp_nonneg hlam) hlam, amp]
  field_simp

/-- The pulse is even. -/
theorem pul_neg (s : ℝ) : pul lam (-s) = pul lam s := by
  simp [pul, SechPulse.pulse, mul_neg, Real.cosh_neg]

/-! ### The curvature -/

theorem G_pul_le (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) (u : ℝ) : G (pul lam u) ≤ 2 :=
  G_le_two (pul_nonneg hlam u) (pul_le_half hlam hlam' u)

theorem G_pul_nonneg (u : ℝ) : 0 ≤ G (pul lam u) := by
  rw [G]
  positivity

/-- `|G(y)y'| ≤ 4λ y`. -/
theorem abs_G_mul_pulD_le (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) (u : ℝ) :
    |G (pul lam u) * pulD lam u| ≤ 4 * lam * pul lam u := by
  rw [abs_mul, abs_of_nonneg (G_pul_nonneg u)]
  have h1 := abs_pulD_le hlam u
  have h2 := G_pul_le hlam hlam' u
  have h3 : 0 ≤ |pulD lam u| := abs_nonneg _
  nlinarith [pul_nonneg hlam u]

/-- The curvature is nonnegative. -/
theorem curv_nonneg (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) (u : ℝ) : 0 ≤ curv lam u := by
  have h := abs_G_mul_pulD_le hlam hlam' u
  have h2 := abs_le.mp h
  have h3 := pul_nonneg hlam u
  rw [curv]
  nlinarith

/-- The pulse is at most twice the curvature. -/
theorem pul_le_two_mul_curv (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) (u : ℝ) :
    pul lam u ≤ 2 * curv lam u := by
  have h := abs_le.mp (abs_G_mul_pulD_le hlam hlam' u)
  have h3 := pul_nonneg hlam u
  rw [curv]
  nlinarith

/-- The curvature is at most twice the pulse. -/
theorem curv_le_two_mul_pul (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) (u : ℝ) :
    curv lam u ≤ 2 * pul lam u := by
  have h := abs_le.mp (abs_G_mul_pulD_le hlam hlam' u)
  have h3 := pul_nonneg hlam u
  rw [curv]
  nlinarith

/-- The sup bound for the curvature. -/
theorem curv_le (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) (u : ℝ) :
    curv lam u ≤ 2 * amp lam :=
  le_trans (curv_le_two_mul_pul hlam hlam' u) (by linarith [pul_le_amp hlam u])

/-- The exponential majorant for the curvature. -/
theorem curv_le_exp (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) (u : ℝ) :
    curv lam u ≤ 8 * amp lam * Real.exp (-(2 * lam) * |u|) := by
  have h1 := curv_le_two_mul_pul hlam hlam' u
  have h2 := pul_le_exp hlam u
  linarith

/-! ### The derivative of the curvature -/

theorem hasDerivAt_curv (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) (u : ℝ) :
    HasDerivAt (curv lam) (curvD lam u) u := by
  have hY : HasDerivAt (pul lam) (pulD lam u) u := hasDerivAt_pul u
  have hY' : HasDerivAt (pulD lam) (pulD2 lam u) u := hasDerivAt_pulD u
  have habs : |pul lam u| < 1 := by
    rw [abs_of_nonneg (pul_nonneg hlam u)]
    have := pul_le_half hlam hlam' u
    linarith
  have hG : HasDerivAt (fun v => G (pul lam v)) (lipConst (pul lam u) * pulD lam u) u := by
    have h := (hasDerivAt_G habs).comp u hY
    simpa [lipConst] using h
  have h := hY.add (hG.mul hY')
  rw [curvD]
  convert h using 1
  ring

theorem continuous_curv (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) : Continuous (curv lam) :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_curv hlam hlam' u).continuousAt

theorem continuous_curvD (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) : Continuous (curvD lam) := by
  have hpos : ∀ u : ℝ, 0 < 1 - pul lam u ^ 2 := by
    intro u
    have h0 := pul_nonneg hlam u
    have h1 := pul_le_half hlam hlam' u
    nlinarith
  have hsq : Continuous fun u : ℝ => Real.sqrt (1 - pul lam u ^ 2) :=
    Real.continuous_sqrt.comp (continuous_const.sub (continuous_pul.pow 2))
  have hsqpos : ∀ u : ℝ, 0 < Real.sqrt (1 - pul lam u ^ 2) := fun u => Real.sqrt_pos.mpr (hpos u)
  have hcG : Continuous fun u : ℝ => G (pul lam u) := by
    unfold G
    exact hsq.inv₀ fun u => (hsqpos u).ne'
  have hcL : Continuous fun u : ℝ => lipConst (pul lam u) := by
    unfold lipConst
    refine continuous_pul.div
      (Continuous.mul (continuous_const.sub (continuous_pul.pow 2)) hsq) fun u => ?_
    have h1 := hpos u
    have h2 := hsqpos u
    positivity
  have : Continuous fun u : ℝ =>
      pulD lam u + (lipConst (pul lam u) * (pulD lam u) ^ 2 + G (pul lam u) * pulD2 lam u) := by
    have h1 : Continuous (pulD lam) := continuous_pulD
    have h2 : Continuous (pulD2 lam) := continuous_pulD2
    fun_prop
  exact this

/-- The relative derivative bound `|K_*'| ≤ 3λ y`. -/
theorem abs_curvD_le_pul (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) (u : ℝ) :
    |curvD lam u| ≤ 3 * lam * pul lam u := by
  have hp0 := pul_nonneg hlam u
  have hpA := pul_le_amp hlam u
  have hA := amp_le hlam hlam'
  have hy50 : pul lam u ≤ 1 / 50 := le_trans hpA hA
  have hd := abs_pulD_le hlam u
  have hd2 := abs_pulD2_le hlam u
  have hlip : lipConst (pul lam u) ≤ 8 * pul lam u :=
    lipConst_le_eight hp0 (pul_le_half hlam hlam' u)
  have hlip0 : 0 ≤ lipConst (pul lam u) := by
    rw [lipConst]
    have h1 : 0 < 1 - pul lam u ^ 2 := by nlinarith
    have h2 : 0 < Real.sqrt (1 - pul lam u ^ 2) := Real.sqrt_pos.mpr h1
    positivity
  have hG := G_pul_le hlam hlam' u
  have hG0 := G_pul_nonneg (lam := lam) u
  have hsq : (pulD lam u) ^ 2 ≤ (2 * lam * pul lam u) ^ 2 := by
    nlinarith [abs_nonneg (pulD lam u), sq_abs (pulD lam u)]
  have hterm1 : lipConst (pul lam u) * (pulD lam u) ^ 2 ≤ 32 * lam ^ 2 * pul lam u ^ 3 := by
    have h1 : lipConst (pul lam u) * (pulD lam u) ^ 2
        ≤ lipConst (pul lam u) * (2 * lam * pul lam u) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hlip0
    nlinarith [sq_nonneg (2 * lam * pul lam u), hlam.le]
  have hterm2 : G (pul lam u) * |pulD2 lam u| ≤ 16 * lam ^ 2 * pul lam u := by
    nlinarith [abs_nonneg (pulD2 lam u)]
  have hbound : |curvD lam u|
      ≤ |pulD lam u|
        + (lipConst (pul lam u) * (pulD lam u) ^ 2 + G (pul lam u) * |pulD2 lam u|) := by
    rw [curvD]
    refine le_trans (abs_add_le _ _) ?_
    gcongr
    refine le_trans (abs_add_le _ _) ?_
    gcongr
    · rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ lipConst (pul lam u) * (pulD lam u) ^ 2)]
    · rw [abs_mul, abs_of_nonneg hG0]
  have hcube : pul lam u ^ 3 ≤ pul lam u := by
    nlinarith [hp0, hy50, mul_nonneg hp0 hp0, sq_nonneg (pul lam u)]
  have key : 32 * lam ^ 2 * pul lam u ^ 3 + 16 * lam ^ 2 * pul lam u ≤ lam * pul lam u := by
    nlinarith [hlam.le, mul_nonneg hlam.le hp0]
  linarith

/-- Hence the relative derivative bound against the curvature itself. -/
theorem abs_curvD_le_curv (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) (u : ℝ) :
    |curvD lam u| ≤ 6 * lam * curv lam u := by
  have h1 := abs_curvD_le_pul hlam hlam' u
  have h2 := pul_le_two_mul_curv hlam hlam' u
  nlinarith [hlam.le]

/-- The exponential majorant for the derivative of the curvature. -/
theorem abs_curvD_le_exp (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) (u : ℝ) :
    |curvD lam u| ≤ 12 * lam * amp lam * Real.exp (-(2 * lam) * |u|) := by
  have h1 := abs_curvD_le_pul hlam hlam' u
  have h2 := pul_le_exp hlam u
  nlinarith [hlam.le]

/-! ### The mass of the curvature -/

theorem integrable_curv (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) : Integrable (curv lam) := by
  refine Integrable.mono' ((integrable_pul hlam).const_mul 2)
    (continuous_curv hlam hlam').aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (curv_nonneg hlam hlam' u)]
  exact curv_le_two_mul_pul hlam hlam' u

theorem integrable_G_mul_pulD (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) :
    Integrable (fun u => G (pul lam u) * pulD lam u) := by
  have hcont : Continuous fun u => G (pul lam u) * pulD lam u := by
    have h1 : Continuous (curv lam) := continuous_curv hlam hlam'
    have h2 : Continuous (pul lam) := continuous_pul
    have : (fun u => G (pul lam u) * pulD lam u) = fun u => curv lam u - pul lam u := by
      funext u; rw [curv]; ring
    rw [this]
    exact h1.sub h2
  refine Integrable.mono' ((integrable_pul hlam).const_mul (4 * lam)) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs]
  exact abs_G_mul_pulD_le hlam hlam' u

/-- **The transverse term integrates to zero**: `∫_ℝ G(y)y' = 0`, since
`arcsin y` is even and tends to the same limit at both ends. -/
theorem integral_G_mul_pulD (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) :
    (∫ u, G (pul lam u) * pulD lam u) = 0 := by
  have hint := integrable_G_mul_pulD hlam hlam'
  have hFTC : ∀ R : ℝ, (∫ u in (-R)..R, G (pul lam u) * pulD lam u) = 0 := by
    intro R
    have hderiv : ∀ u ∈ Set.uIcc (-R) R,
        HasDerivAt (fun v => Real.arcsin (pul lam v)) (G (pul lam u) * pulD lam u) u := by
      intro u _
      have h0 := pul_nonneg hlam u
      have hh := pul_le_half hlam hlam' u
      have hne1 : pul lam u ≠ 1 := by intro h; rw [h] at hh; linarith
      have hne2 : pul lam u ≠ -1 := by intro h; rw [h] at h0; linarith
      have h := (Real.hasDerivAt_arcsin hne2 hne1).comp u (hasDerivAt_pul (lam := lam) u)
      have hval : 1 / Real.sqrt (1 - pul lam u ^ 2) * pulD lam u
          = G (pul lam u) * pulD lam u := by rw [G, one_div]
      rw [← hval]
      exact h
    have hintg : IntervalIntegrable (fun u => G (pul lam u) * pulD lam u) volume (-R) R :=
      hint.intervalIntegrable
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintg, pul_neg]
    ring
  have hlim : Filter.Tendsto (fun R : ℝ => ∫ u in (-R)..R, G (pul lam u) * pulD lam u)
      atTop (nhds (∫ u, G (pul lam u) * pulD lam u)) :=
    intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot (tendsto_id (α := ℝ))
  have hzero : Filter.Tendsto (fun R : ℝ => ∫ u in (-R)..R, G (pul lam u) * pulD lam u)
      atTop (nhds 0) := by
    simp only [hFTC]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hzero

/-- **The total curvature of the isolated hairpin is `π`.** -/
theorem integral_curv (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) :
    (∫ u, curv lam u) = Real.pi := by
  have hsplit : (∫ u, curv lam u)
      = (∫ u, pul lam u) + ∫ u, G (pul lam u) * pulD lam u := by
    rw [← MeasureTheory.integral_add (integrable_pul hlam) (integrable_G_mul_pulD hlam hlam')]
    rfl
  rw [hsplit, integral_pul hlam, integral_G_mul_pulD hlam hlam', add_zero]

end SechHairpin
