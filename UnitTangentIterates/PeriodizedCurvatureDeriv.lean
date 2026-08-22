import Mathlib
import UnitTangentIterates.PeriodizedTurning

/-!
# The derivative of the periodized front curvature

The model fronts of *A Noncircular Oval with Convex Unit-Tangent Iterates* carry
the periodized front curvature

```
  K_P(u) = Y_P(u) + G(Y_P(u)) · Y_P'(u) ,   Y_P(u) = ∑_{m ∈ ℤ} y(u − mP) ,
```

`G(z) = (1 − z²)^{−1/2}`.  The interpolation estimates for the marked path
pseudodistance (`InterpolationPathDist`) need `K_P` to be `C¹` with a **uniform
derivative bound** `|K_P'| ≤ kd`.  This file supplies both, from the pulse
alone:

* `hasDerivAt_frontCurv` — `K_P` is differentiable with
  `K_P' = Y_P' + G'(Y_P)(Y_P')² + G(Y_P)Y_P''`, where
  `G'(z) = z/((1−z²)√(1−z²)) = lipConst z`;
* `lipConst_le_lipConst` — `G'` is monotone on `[0,a]`, `a < 1`;
* `abs_deriv_periodization_le_two` — the relative bound `|y''| ≤ D₂ y` passes to
  the periodization, `|Y_P''| ≤ D₂ Y_P`;
* `abs_deriv_frontCurv_le` — hence the explicit uniform bound
  `|K_P'| ≤ D a + G'(a) D² a² + G(a) D₂ a` under `|y'| ≤ D y`, `|y''| ≤ D₂ y`
  and `Y_P ≤ a < 1`;
* `continuous_deriv_frontCurv` — the derivative is continuous.

The hypotheses are the standing assumptions of the two-cap configuration: `y`
nonnegative and `C²` with `y`, `y'`, `y''` dominated by `Ce^{−α|s|}`, the
relative bounds `|y'| ≤ D y`, `|y''| ≤ D₂ y`, and `Y_P ≤ a < 1`.
-/

noncomputable section

open MeasureTheory Set Function

namespace PeriodizedCurvatureDeriv

open FrontPeriodization PeriodizedTurning

variable {y y' y'' : ℝ → ℝ} {C alpha P a : ℝ}

/-! ### Differentiability of the periodized curvature -/

/-- **The periodized front curvature is differentiable**, with
`K_P' = Y_P' + G'(Y_P)(Y_P')² + G(Y_P)Y_P''`. -/
theorem hasDerivAt_frontCurv (halpha : 0 < alpha) (hP : 0 < P)
    (hy : ∀ x, HasDerivAt y (y' x) x) (hy' : ∀ x, HasDerivAt y' (y'' x) x)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hy'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|))
    (hy''b : ∀ x, |y'' x| ≤ C * Real.exp (-alpha * |x|))
    (ha1 : a < 1) (hYa : ∀ v, |∑' m : ℤ, y (v - m * P)| ≤ a) (u : ℝ) :
    HasDerivAt (fun v => (∑' m : ℤ, y (v - m * P))
        + G (∑' m : ℤ, y (v - m * P)) * ∑' m : ℤ, y' (v - m * P))
      ((∑' m : ℤ, y' (u - m * P))
        + (lipConst (∑' m : ℤ, y (u - m * P)) * (∑' m : ℤ, y' (u - m * P)) ^ 2
          + G (∑' m : ℤ, y (u - m * P)) * ∑' m : ℤ, y'' (u - m * P))) u := by
  have hY : HasDerivAt (fun v => ∑' m : ℤ, y (v - m * P)) (∑' m : ℤ, y' (u - m * P)) u :=
    hasDerivAt_periodization halpha hP hy hyb hy'b u
  have hY' : HasDerivAt (fun v => ∑' m : ℤ, y' (v - m * P)) (∑' m : ℤ, y'' (u - m * P)) u :=
    hasDerivAt_periodization halpha hP hy' hy'b hy''b u
  have habs : |∑' m : ℤ, y (u - m * P)| < 1 := lt_of_le_of_lt (hYa u) ha1
  have hG : HasDerivAt (fun v => G (∑' m : ℤ, y (v - m * P)))
      (lipConst (∑' m : ℤ, y (u - m * P)) * ∑' m : ℤ, y' (u - m * P)) u := by
    have h := (hasDerivAt_G habs).comp u hY
    simpa [lipConst] using h
  have hmul := hG.mul hY'
  have h := hY.add hmul
  convert h using 1
  ring

/-- The derivative of the periodized front curvature is continuous. -/
theorem continuous_deriv_frontCurv (halpha : 0 < alpha) (hP : 0 < P)
    (hy'cont : Continuous y') (hy''cont : Continuous y'')
    (hycont : Continuous y)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hy'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|))
    (hy''b : ∀ x, |y'' x| ≤ C * Real.exp (-alpha * |x|))
    (ha1 : a < 1) (hYa : ∀ v, |∑' m : ℤ, y (v - m * P)| ≤ a) :
    Continuous fun u => (∑' m : ℤ, y' (u - m * P))
      + (lipConst (∑' m : ℤ, y (u - m * P)) * (∑' m : ℤ, y' (u - m * P)) ^ 2
        + G (∑' m : ℤ, y (u - m * P)) * ∑' m : ℤ, y'' (u - m * P)) := by
  have hcY : Continuous fun u : ℝ => ∑' m : ℤ, y (u - m * P) :=
    continuous_periodization halpha hP hycont hyb
  have hcY' : Continuous fun u : ℝ => ∑' m : ℤ, y' (u - m * P) :=
    continuous_periodization halpha hP hy'cont hy'b
  have hcY'' : Continuous fun u : ℝ => ∑' m : ℤ, y'' (u - m * P) :=
    continuous_periodization halpha hP hy''cont hy''b
  have hpos : ∀ u : ℝ, 0 < 1 - (∑' m : ℤ, y (u - m * P)) ^ 2 := by
    intro u
    have h := lt_of_le_of_lt (hYa u) ha1
    nlinarith [sq_abs (∑' m : ℤ, y (u - m * P)), abs_lt.mp h]
  have hsq : Continuous fun u : ℝ => Real.sqrt (1 - (∑' m : ℤ, y (u - m * P)) ^ 2) :=
    (Real.continuous_sqrt.comp (by fun_prop))
  have hsqpos : ∀ u : ℝ, 0 < Real.sqrt (1 - (∑' m : ℤ, y (u - m * P)) ^ 2) := fun u =>
    Real.sqrt_pos.mpr (hpos u)
  have hcG : Continuous fun u : ℝ => G (∑' m : ℤ, y (u - m * P)) := by
    unfold G
    exact hsq.inv₀ fun u => ne_of_gt (hsqpos u)
  have hcL : Continuous fun u : ℝ => lipConst (∑' m : ℤ, y (u - m * P)) := by
    unfold lipConst
    refine hcY.div (Continuous.mul (by fun_prop) hsq) ?_
    intro u
    have h1 := hpos u
    have h2 := hsqpos u
    positivity
  fun_prop

/-! ### Monotonicity of `G'` -/

/-- `G'(z) = z/((1−z²)√(1−z²))` is monotone on `[0,a]`, `a < 1`. -/
theorem lipConst_le_lipConst {z : ℝ} (hz0 : 0 ≤ z) (hza : z ≤ a) (ha1 : a < 1) :
    lipConst z ≤ lipConst a := by
  have ha0 : 0 ≤ a := le_trans hz0 hza
  have ha2 : 0 < 1 - a ^ 2 := by nlinarith
  have hsa : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.mpr ha2
  have hz2 : 0 < 1 - z ^ 2 := by nlinarith
  have hmono : Real.sqrt (1 - a ^ 2) ≤ Real.sqrt (1 - z ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  unfold lipConst
  refine div_le_div₀ ha0 hza (by positivity) ?_
  exact mul_le_mul (by nlinarith) hmono hsa.le (by nlinarith)

/-! ### The uniform derivative bound -/

/-- **The second relative derivative bound survives the periodization**: if
`|y''| ≤ D₂ y` then `|Y_P''| ≤ D₂ Y_P`. -/
theorem abs_deriv_periodization_le_two (halpha : 0 < alpha) (hP : 0 < P) {D2 : ℝ}
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hy''b : ∀ x, |y'' x| ≤ C * Real.exp (-alpha * |x|))
    (hrel : ∀ s, |y'' s| ≤ D2 * y s) (u : ℝ) :
    |∑' m : ℤ, y'' (u - m * P)| ≤ D2 * ∑' m : ℤ, y (u - m * P) :=
  abs_deriv_periodization_le (y := y) (y' := y'') halpha hP hyb hy''b hrel u

/-- **A uniform bound for the derivative of the periodized front curvature.**
With the relative derivative bounds `|y'| ≤ D y`, `|y''| ≤ D₂ y` and a
periodization below `a < 1`,
`|K_P'| ≤ D a + G'(a) D² a² + G(a) D₂ a`. -/
theorem abs_deriv_frontCurv_le (halpha : 0 < alpha) (hP : 0 < P) {D D2 : ℝ}
    (hD : 0 ≤ D) (hD2 : 0 ≤ D2) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hy'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|))
    (hy''b : ∀ x, |y'' x| ≤ C * Real.exp (-alpha * |x|))
    (hrel : ∀ s, |y' s| ≤ D * y s) (hrel2 : ∀ s, |y'' s| ≤ D2 * y s)
    (ha1 : a < 1) (hYa : ∀ v, (∑' m : ℤ, y (v - m * P)) ≤ a) (u : ℝ) :
    |(∑' m : ℤ, y' (u - m * P))
        + (lipConst (∑' m : ℤ, y (u - m * P)) * (∑' m : ℤ, y' (u - m * P)) ^ 2
          + G (∑' m : ℤ, y (u - m * P)) * ∑' m : ℤ, y'' (u - m * P))|
      ≤ D * a + lipConst a * (D ^ 2 * a ^ 2) + G a * (D2 * a) := by
  set Y : ℝ := ∑' m : ℤ, y (u - m * P) with hYdef
  set Y' : ℝ := ∑' m : ℤ, y' (u - m * P) with hY'def
  set Y'' : ℝ := ∑' m : ℤ, y'' (u - m * P) with hY''def
  have hY0 : 0 ≤ Y := tsum_nonneg fun m => hy0 _
  have hYle : Y ≤ a := hYa u
  have ha0 : 0 ≤ a := le_trans hY0 hYle
  have hY'le : |Y'| ≤ D * Y := abs_deriv_periodization_le halpha hP hyb hy'b hrel u
  have hY''le : |Y''| ≤ D2 * Y :=
    abs_deriv_periodization_le_two halpha hP hyb hy''b hrel2 u
  have hGle : G Y ≤ G a := G_le_G_of_le hY0 hYle ha1
  have hG0 : 0 ≤ G Y := by simp [G]
  have hGa0 : 0 ≤ G a := le_trans hG0 hGle
  have hLle : lipConst Y ≤ lipConst a := lipConst_le_lipConst hY0 hYle ha1
  have hL0 : 0 ≤ lipConst Y := lipConst_nonneg hY0 (lt_of_le_of_lt hYle ha1)
  have hLa0 : 0 ≤ lipConst a := le_trans hL0 hLle
  -- the three pieces
  have h1 : |Y'| ≤ D * a := le_trans hY'le (mul_le_mul_of_nonneg_left hYle hD)
  have hsq : Y' ^ 2 ≤ D ^ 2 * a ^ 2 := by
    have : |Y'| ^ 2 ≤ (D * a) ^ 2 := by
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc Y' ^ 2 = |Y'| ^ 2 := (sq_abs Y').symm
      _ ≤ (D * a) ^ 2 := this
      _ = D ^ 2 * a ^ 2 := by ring
  have h2 : |lipConst Y * Y' ^ 2| ≤ lipConst a * (D ^ 2 * a ^ 2) := by
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul hLle hsq (by positivity) hLa0
  have h3 : |G Y * Y''| ≤ G a * (D2 * a) := by
    rw [abs_mul, abs_of_nonneg hG0]
    refine mul_le_mul hGle (le_trans hY''le (mul_le_mul_of_nonneg_left hYle hD2))
      (abs_nonneg _) hGa0
  calc |Y' + (lipConst Y * Y' ^ 2 + G Y * Y'')|
      ≤ |Y'| + |lipConst Y * Y' ^ 2 + G Y * Y''| := abs_add_le _ _
    _ ≤ |Y'| + (|lipConst Y * Y' ^ 2| + |G Y * Y''|) := by
        have := abs_add_le (lipConst Y * Y' ^ 2) (G Y * Y'')
        linarith
    _ ≤ D * a + (lipConst a * (D ^ 2 * a ^ 2) + G a * (D2 * a)) := by linarith
    _ = D * a + lipConst a * (D ^ 2 * a ^ 2) + G a * (D2 * a) := by ring

/-! ### The periodized curvature as the curvature of a marked oval -/

/-- **The periodized front curvature is an admissible marked-oval curvature.**
From the pulse alone — nonnegative, `C²`, with `y`, `y'`, `y''` dominated by
`Ce^{−α|s|}`, relative derivative bounds `|y'| ≤ D y`, `|y''| ≤ D₂ y`, mass `π`,
and periodization below `a < 1` with `G(a)D ≤ 1` — the periodized curvature
`K_P` is continuous, `P`-periodic, has total turning `π` over one period, is
differentiable with a continuous derivative bounded by
`kd = D a + G'(a)D²a² + G(a)D₂a`, and satisfies `0 ≤ K_P ≤ (1 + G(a)D)a`.
These are exactly the hypotheses that the interpolation estimates for the
marked path pseudodistance put on the curvature of a marked oval of half
perimeter `P`. -/
theorem frontCurv_marked_oval_data (halpha : 0 < alpha) (hP : 0 < P) {D D2 : ℝ}
    (hD : 0 ≤ D) (hD2 : 0 ≤ D2)
    (hy : ∀ x, HasDerivAt y (y' x) x) (hy' : ∀ x, HasDerivAt y' (y'' x) x)
    (hy''cont : Continuous y'')
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hy'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|))
    (hy''b : ∀ x, |y'' x| ≤ C * Real.exp (-alpha * |x|))
    (hy0 : ∀ s, 0 ≤ y s) (hyint : Integrable y) (hmass : (∫ s : ℝ, y s) = Real.pi)
    (hrel : ∀ s, |y' s| ≤ D * y s) (hrel2 : ∀ s, |y'' s| ≤ D2 * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ v, (∑' m : ℤ, y (v - m * P)) ≤ a) (hsmall : G a * D ≤ 1) :
    ∃ K K' : ℝ → ℝ,
      (∀ u, K u = (∑' m : ℤ, y (u - m * P))
        + G (∑' m : ℤ, y (u - m * P)) * ∑' m : ℤ, y' (u - m * P)) ∧
      Continuous K ∧ Continuous K' ∧ Periodic K P ∧
      (∫ r in (0:ℝ)..P, K r) = Real.pi ∧
      (∀ r, HasDerivAt K (K' r) r) ∧
      (∀ r, |K' r| ≤ D * a + lipConst a * (D ^ 2 * a ^ 2) + G a * (D2 * a)) ∧
      (∀ r, 0 ≤ K r) ∧ (∀ r, K r ≤ (1 + G a * D) * a) := by
  have hydiff : Differentiable ℝ y := fun x => (hy x).differentiableAt
  have hy'diff : Differentiable ℝ y' := fun x => (hy' x).differentiableAt
  have hycont : Continuous y := hydiff.continuous
  have hy'cont : Continuous y' := hy'diff.continuous
  have hYcont : Continuous fun u : ℝ => ∑' m : ℤ, y (u - m * P) :=
    continuous_periodization halpha hP hycont hyb
  have hY'cont : Continuous fun u : ℝ => ∑' m : ℤ, y' (u - m * P) :=
    continuous_periodization halpha hP hy'cont hy'b
  have hY0 : ∀ u : ℝ, 0 ≤ ∑' m : ℤ, y (u - m * P) := fun u => tsum_nonneg fun m => hy0 _
  have hGcont : Continuous fun u : ℝ => G (∑' m : ℤ, y (u - m * P)) :=
    FrontPeriodizationIntegral.continuous_G_comp ha0 ha1 hYcont hY0 hYa
  have hYabs : ∀ v : ℝ, |∑' m : ℤ, y (v - m * P)| ≤ a := fun v => by
    rw [abs_of_nonneg (hY0 v)]; exact hYa v
  refine ⟨fun u => (∑' m : ℤ, y (u - m * P))
      + G (∑' m : ℤ, y (u - m * P)) * ∑' m : ℤ, y' (u - m * P),
    fun u => (∑' m : ℤ, y' (u - m * P))
      + (lipConst (∑' m : ℤ, y (u - m * P)) * (∑' m : ℤ, y' (u - m * P)) ^ 2
        + G (∑' m : ℤ, y (u - m * P)) * ∑' m : ℤ, y'' (u - m * P)),
    fun _ => rfl, hYcont.add (hGcont.mul hY'cont),
    continuous_deriv_frontCurv halpha hP hy'cont hy''cont hycont hyb hy'b hy''b ha1 hYabs,
    periodic_frontCurv y y' P, ?_,
    hasDerivAt_frontCurv halpha hP hy hy' hyb hy'b hy''b ha1 hYabs,
    abs_deriv_frontCurv_le halpha hP hD hD2 hy0 hyb hy'b hy''b hrel hrel2 ha1 hYa,
    frontCurv_nonneg halpha hP hD hy0 hyb hy'b hrel ha1 hYa hsmall, fun r => ?_⟩
  · have h := integral_frontCurv_eq_pi (y := y) (y' := y') halpha hP hycont hy'cont hy
      hyb hy'b hy0 hyint ha0 ha1 hYabs hmass 0
    simpa using h
  · exact le_trans (le_abs_self _)
      (abs_frontCurv_le halpha hP hD hy0 hyb hy'b hrel ha1 hYa r)

end PeriodizedCurvatureDeriv
