import Mathlib
import UnitTangentIterates.FrontPeriodizationIntegral
import UnitTangentIterates.OverlapIntegral

/-!
# The total turning of the periodized front curvature

The model fronts of *A Noncircular Oval with Convex Unit-Tangent Iterates* carry
the **periodized** front curvature

```
  K_P(u) = Y_P(u) + G(Y_P(u)) · Y_P'(u) ,   Y_P(u) = ∑_{m ∈ ℤ} y(u − mP) ,
```

`G(z) = (1 − z²)^{−1/2}`, built from the hairpin pulse `y`.  Every statement of
this project that reads such a curvature as the curvature of a closed convex
curve — in particular the two-cap statements and the interpolation bounds for
the marked path pseudodistance — needs its **total turning over one period**,
`∫_c^{c+P} K_P = π`.

This file proves it, from the pulse alone:

* `hasDerivAt_periodization` — the periodization may be differentiated
  termwise, `Y_P' = ∑_m y'(· − mP)`, for an exponentially decaying pulse with
  exponentially decaying derivative;
* `periodic_periodization`, `continuous_periodization` — the periodization is
  `P`-periodic and continuous;
* `integral_periodization_eq_integral` — its mass over one period is the total
  mass of the pulse, `∫_c^{c+P} Y_P = ∫_ℝ y` (the translates of a cell tile the
  line);
* `integral_G_mul_deriv_eq_zero` — the second term integrates to zero over a
  period: `G(Y_P)Y_P'` is the derivative of `arcsin ∘ Y_P`, which is periodic;
* `integral_frontCurv_eq_integral` — hence `∫_c^{c+P} K_P = ∫_ℝ y`, and
* `integral_frontCurv_eq_pi` — the total turning is `π` exactly when the pulse
  has mass `π`, which is the steering mass of the paper's hairpin
  (`HairpinPulseMass`).

The only hypotheses are: `y` and `y'` continuous with `y' = y′`, both dominated
by `Ce^{−α|s|}`, `y ≥ 0`, and the periodization bounded by some `a < 1` — the
standing assumptions of the two-cap configuration.
-/

noncomputable section

open MeasureTheory Set Function

namespace PeriodizedTurning

open FrontPeriodization FrontPeriodizationIntegral

variable {y y' : ℝ → ℝ} {C alpha P a c : ℝ}

/-! ### Termwise differentiation of the periodization -/

/-- **The periodization may be differentiated termwise in its argument.**  For a
pulse `y` with exponentially decaying values and derivative, the periodization
`Y_P(u) = ∑_m y(u − mP)` is differentiable with derivative
`∑_m y'(u − mP)`. -/
theorem hasDerivAt_periodization (halpha : 0 < alpha) (hP : 0 < P)
    (hy : ∀ x, HasDerivAt y (y' x) x)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hy'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|)) (u : ℝ) :
    HasDerivAt (fun t => ∑' m : ℤ, y (t - m * P)) (∑' m : ℤ, y' (u - m * P)) u := by
  have hC : 0 ≤ C := by
    have h := hyb 0
    have h0 := abs_nonneg (y 0)
    simp at h
    linarith
  set q : ℝ := Real.exp (-alpha * P) with hq
  have hq0 : (0:ℝ) ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  set K : ℝ := C * Real.exp (alpha * (|u| + 1)) with hK
  have hsummaj : Summable fun m : ℤ => K * q ^ m.natAbs := summable_geom_natAbs hq0 hq1
  set t : Set ℝ := Ioo (u - 1) (u + 1) with ht
  have hut : u ∈ t := by constructor <;> linarith
  have hderiv : ∀ (m : ℤ), ∀ z ∈ t, HasDerivAt (fun r : ℝ => y (r - m * P)) (y' (z - m * P)) z := by
    intro m z _
    simpa using (hy (z - m * P)).comp z ((hasDerivAt_id z).sub_const ((m : ℝ) * P))
  have hbound : ∀ (m : ℤ), ∀ z ∈ t, ‖y' (z - m * P)‖ ≤ K * q ^ m.natAbs := by
    intro m z hz
    have hzabs : |z| ≤ |u| + 1 := by
      rcases hz with ⟨h1, h2⟩
      rcases abs_cases z with ⟨he, _⟩ | ⟨he, _⟩ <;>
        rw [he] <;> [skip; skip] <;>
        · have := abs_nonneg u
          rcases abs_cases u with ⟨hu, _⟩ | ⟨hu, _⟩ <;> rw [hu] at * <;> linarith
    have h := abs_term_le (F := y') (C := C) halpha hP hy'b z m
    refine le_trans (le_of_eq (Real.norm_eq_abs _)) (le_trans h ?_)
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hq0 _)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hzabs halpha.le)) hC
  exact hasDerivAt_tsum_of_isPreconnected hsummaj isOpen_Ioo isPreconnected_Ioo
    hderiv hbound hut (summable_translates halpha hP hyb u) hut

/-! ### Periodicity, continuity, mass -/

/-- The periodization is `P`-periodic. -/
theorem periodic_periodization (F : ℝ → ℝ) (P : ℝ) :
    Periodic (fun u => ∑' m : ℤ, F (u - m * P)) P :=
  periodic_tsum_translates F P

/-- The periodization of a continuous, exponentially decaying pulse is
continuous. -/
theorem continuous_periodization (halpha : 0 < alpha) (hP : 0 < P)
    (hycont : Continuous y) (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|)) :
    Continuous fun u => ∑' m : ℤ, y (u - m * P) :=
  continuous_tsum_translates halpha hP hycont hyb

/-- **The mass of the periodization over one period is the total mass of the
pulse.**  The translates of a cell of length `P` tile the line. -/
theorem integral_periodization_eq_integral (hP : 0 < P) (hyint : Integrable y)
    (hy0 : ∀ u, 0 ≤ y u) (c : ℝ) :
    (∫ u in c..(c + P), ∑' m : ℤ, y (u - m * P)) = ∫ u : ℝ, y u := by
  have hle : c ≤ c + P := by linarith
  rw [intervalIntegral.integral_of_le hle]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← MeasureTheory.integral_Ico_eq_integral_Ioo]
  exact OverlapIntegral.integral_tsum_translates_all (p := c) hP hyint hy0

/-! ### The exact-derivative term -/

/-- `G(Y_P) Y_P'` is the derivative of `arcsin ∘ Y_P`. -/
theorem hasDerivAt_arcsin_periodization (halpha : 0 < alpha) (hP : 0 < P)
    (hy : ∀ x, HasDerivAt y (y' x) x)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hy'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|))
    (ha1 : a < 1) (hYa : ∀ v, |∑' m : ℤ, y (v - m * P)| ≤ a) (u : ℝ) :
    HasDerivAt (fun v => Real.arcsin (∑' m : ℤ, y (v - m * P)))
      (G (∑' m : ℤ, y (u - m * P)) * ∑' m : ℤ, y' (u - m * P)) u := by
  set Yu : ℝ := ∑' m : ℤ, y (u - m * P) with hYu
  have habs : |Yu| ≤ a := hYa u
  have hne1 : Yu ≠ 1 := by
    intro h
    have : |Yu| = 1 := by rw [h]; norm_num
    linarith [this ▸ habs]
  have hnem1 : Yu ≠ -1 := by
    intro h
    have : |Yu| = 1 := by rw [h]; norm_num
    linarith [this ▸ habs]
  have hinner := hasDerivAt_periodization halpha hP hy hyb hy'b u
  have h := (Real.hasDerivAt_arcsin hnem1 hne1).comp u hinner
  simpa [G, one_div] using h

/-- **The second term of the periodized curvature integrates to zero over one
period**: it is the derivative of the periodic function `arcsin ∘ Y_P`. -/
theorem integral_G_mul_deriv_eq_zero (halpha : 0 < alpha) (hP : 0 < P)
    (hycont : Continuous y) (hy'cont : Continuous y')
    (hy : ∀ x, HasDerivAt y (y' x) x)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hy'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|))
    (hy0 : ∀ u, 0 ≤ y u)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hYa : ∀ v, |∑' m : ℤ, y (v - m * P)| ≤ a) (c : ℝ) :
    (∫ u in c..(c + P), G (∑' m : ℤ, y (u - m * P)) * ∑' m : ℤ, y' (u - m * P)) = 0 := by
  have hYcont : Continuous fun u => ∑' m : ℤ, y (u - m * P) :=
    continuous_periodization halpha hP hycont hyb
  have hY'cont : Continuous fun u => ∑' m : ℤ, y' (u - m * P) :=
    continuous_tsum_translates halpha hP hy'cont hy'b
  have hY0 : ∀ u, 0 ≤ ∑' m : ℤ, y (u - m * P) := fun u => tsum_nonneg fun m => hy0 _
  have hYle : ∀ u, (∑' m : ℤ, y (u - m * P)) ≤ a := fun u => le_trans (le_abs_self _) (hYa u)
  have hGcont : Continuous fun u => G (∑' m : ℤ, y (u - m * P)) :=
    continuous_G_comp ha0 ha1 hYcont hY0 hYle
  have hint : IntervalIntegrable
      (fun u => G (∑' m : ℤ, y (u - m * P)) * ∑' m : ℤ, y' (u - m * P)) volume c (c + P) :=
    (hGcont.mul hY'cont).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_arcsin_periodization halpha hP hy hyb hy'b ha1 hYa u) hint]
  have hper : (∑' m : ℤ, y (c + P - m * P)) = ∑' m : ℤ, y (c - m * P) :=
    periodic_periodization y P c
  simp only [hper, sub_self]

/-! ### The total turning -/

/-- **The total turning of the periodized front curvature over one period is the
mass of the pulse.**  `∫_c^{c+P} (Y_P + G(Y_P)Y_P') = ∫_ℝ y`. -/
theorem integral_frontCurv_eq_integral (halpha : 0 < alpha) (hP : 0 < P)
    (hycont : Continuous y) (hy'cont : Continuous y')
    (hy : ∀ x, HasDerivAt y (y' x) x)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hy'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|))
    (hy0 : ∀ u, 0 ≤ y u) (hyint : Integrable y)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hYa : ∀ v, |∑' m : ℤ, y (v - m * P)| ≤ a) (c : ℝ) :
    (∫ u in c..(c + P), ((∑' m : ℤ, y (u - m * P))
        + G (∑' m : ℤ, y (u - m * P)) * ∑' m : ℤ, y' (u - m * P)))
      = ∫ u : ℝ, y u := by
  have hYcont : Continuous fun u => ∑' m : ℤ, y (u - m * P) :=
    continuous_periodization halpha hP hycont hyb
  have hY'cont : Continuous fun u => ∑' m : ℤ, y' (u - m * P) :=
    continuous_tsum_translates halpha hP hy'cont hy'b
  have hY0 : ∀ u, 0 ≤ ∑' m : ℤ, y (u - m * P) := fun u => tsum_nonneg fun m => hy0 _
  have hYle : ∀ u, (∑' m : ℤ, y (u - m * P)) ≤ a := fun u => le_trans (le_abs_self _) (hYa u)
  have hGcont : Continuous fun u => G (∑' m : ℤ, y (u - m * P)) :=
    continuous_G_comp ha0 ha1 hYcont hY0 hYle
  have hint1 : IntervalIntegrable (fun u => ∑' m : ℤ, y (u - m * P)) volume c (c + P) :=
    hYcont.intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun u => G (∑' m : ℤ, y (u - m * P)) * ∑' m : ℤ, y' (u - m * P)) volume c (c + P) :=
    (hGcont.mul hY'cont).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hint1 hint2,
    integral_G_mul_deriv_eq_zero halpha hP hycont hy'cont hy hyb hy'b hy0 ha0 ha1 hYa c,
    add_zero]
  exact integral_periodization_eq_integral hP hyint hy0 c

/-- **The periodized front curvature has total turning `π` over one period**,
the pulse having mass `π` — which for the paper's hairpin is the steering mass
`∫_ℝ y = π` of `HairpinPulseMass`. -/
theorem integral_frontCurv_eq_pi (halpha : 0 < alpha) (hP : 0 < P)
    (hycont : Continuous y) (hy'cont : Continuous y')
    (hy : ∀ x, HasDerivAt y (y' x) x)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hy'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|))
    (hy0 : ∀ u, 0 ≤ y u) (hyint : Integrable y)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hYa : ∀ v, |∑' m : ℤ, y (v - m * P)| ≤ a)
    (hmass : (∫ u : ℝ, y u) = Real.pi) (c : ℝ) :
    (∫ u in c..(c + P), ((∑' m : ℤ, y (u - m * P))
        + G (∑' m : ℤ, y (u - m * P)) * ∑' m : ℤ, y' (u - m * P)))
      = Real.pi := by
  rw [integral_frontCurv_eq_integral halpha hP hycont hy'cont hy hyb hy'b hy0 hyint
    ha0 ha1 hYa c, hmass]

/-- The periodized front curvature is `P`-periodic. -/
theorem periodic_frontCurv (y y' : ℝ → ℝ) (P : ℝ) :
    Periodic (fun u => (∑' m : ℤ, y (u - m * P))
      + G (∑' m : ℤ, y (u - m * P)) * ∑' m : ℤ, y' (u - m * P)) P := by
  intro u
  have h1 : (∑' m : ℤ, y (u + P - m * P)) = ∑' m : ℤ, y (u - m * P) :=
    periodic_periodization y P u
  have h2 : (∑' m : ℤ, y' (u + P - m * P)) = ∑' m : ℤ, y' (u - m * P) :=
    periodic_periodization y' P u
  simp only [h1, h2]

/-! ### Sup bounds for the periodized curvature -/

/-- `G` is monotone on `[0, a]`, `a < 1`. -/
theorem G_le_G_of_le {z : ℝ} (hz0 : 0 ≤ z) (hza : z ≤ a) (ha1 : a < 1) : G z ≤ G a := by
  have ha0 : 0 ≤ a := le_trans hz0 hza
  have h1 : 0 < 1 - a ^ 2 := by nlinarith
  have h2 : 1 - a ^ 2 ≤ 1 - z ^ 2 := by nlinarith
  have h3 : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.mpr h1
  have h4 : Real.sqrt (1 - a ^ 2) ≤ Real.sqrt (1 - z ^ 2) := Real.sqrt_le_sqrt h2
  have h5 : 1 / Real.sqrt (1 - z ^ 2) ≤ 1 / Real.sqrt (1 - a ^ 2) :=
    one_div_le_one_div_of_le h3 h4
  simpa [G, one_div] using h5

/-- **The relative derivative bound survives the periodization.**  If
`|y'| ≤ D y` then `|Y_P'| ≤ D Y_P`. -/
theorem abs_deriv_periodization_le (halpha : 0 < alpha) (hP : 0 < P) {D : ℝ}
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hy'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|))
    (hrel : ∀ s, |y' s| ≤ D * y s) (u : ℝ) :
    |∑' m : ℤ, y' (u - m * P)| ≤ D * ∑' m : ℤ, y (u - m * P) := by
  have hsy : Summable fun m : ℤ => y (u - m * P) := summable_translates halpha hP hyb u
  have hsy' : Summable fun m : ℤ => y' (u - m * P) := summable_translates halpha hP hy'b u
  have hsabs : Summable fun m : ℤ => |y' (u - m * P)| := by
    simpa [Real.norm_eq_abs] using hsy'.abs
  have hnorm : Summable fun m : ℤ => ‖y' (u - m * P)‖ := by
    simpa [Real.norm_eq_abs] using hsabs
  have hfirst : |∑' m : ℤ, y' (u - m * P)| ≤ ∑' m : ℤ, |y' (u - m * P)| := by
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
  calc |∑' m : ℤ, y' (u - m * P)| ≤ ∑' m : ℤ, |y' (u - m * P)| := hfirst
    _ ≤ ∑' m : ℤ, D * y (u - m * P) :=
        hsabs.tsum_le_tsum (fun m => hrel _) (hsy.mul_left D)
    _ = D * ∑' m : ℤ, y (u - m * P) := tsum_mul_left

/-- **A sup bound for the periodized front curvature.**  With a relative
derivative bound `|y'| ≤ D y` and a periodization below `a < 1`,
`|K_P| ≤ (1 + G(a)D) Y_P ≤ (1 + G(a)D) a`. -/
theorem abs_frontCurv_le (halpha : 0 < alpha) (hP : 0 < P) {D : ℝ} (hD : 0 ≤ D)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hy'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|))
    (hrel : ∀ s, |y' s| ≤ D * y s)
    (ha1 : a < 1) (hYa : ∀ v, (∑' m : ℤ, y (v - m * P)) ≤ a) (u : ℝ) :
    |(∑' m : ℤ, y (u - m * P))
        + G (∑' m : ℤ, y (u - m * P)) * ∑' m : ℤ, y' (u - m * P)|
      ≤ (1 + G a * D) * a := by
  set Y : ℝ := ∑' m : ℤ, y (u - m * P) with hY
  set Y' : ℝ := ∑' m : ℤ, y' (u - m * P) with hY'
  have hY0 : 0 ≤ Y := tsum_nonneg fun m => hy0 _
  have hYle : Y ≤ a := hYa u
  have hGle : G Y ≤ G a := G_le_G_of_le hY0 hYle ha1
  have hG0 : 0 ≤ G Y := by simp [G]
  have hY'le : |Y'| ≤ D * Y := abs_deriv_periodization_le halpha hP hyb hy'b hrel u
  have hprod : |G Y * Y'| ≤ G a * (D * Y) := by
    rw [abs_mul, abs_of_nonneg hG0]
    exact mul_le_mul hGle hY'le (abs_nonneg _) (le_trans hG0 hGle)
  have hGa0 : 0 ≤ G a := le_trans hG0 hGle
  calc |Y + G Y * Y'| ≤ |Y| + |G Y * Y'| := abs_add_le _ _
    _ ≤ Y + G a * (D * Y) := by rw [abs_of_nonneg hY0]; linarith
    _ = (1 + G a * D) * Y := by ring
    _ ≤ (1 + G a * D) * a := by
        have : 0 ≤ 1 + G a * D := by positivity
        exact mul_le_mul_of_nonneg_left hYle this

/-- **The periodized front curvature is nonnegative** when the relative
derivative bound is small enough for the periodization bound, `G(a)D ≤ 1`. -/
theorem frontCurv_nonneg (halpha : 0 < alpha) (hP : 0 < P) {D : ℝ} (hD : 0 ≤ D)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hy'b : ∀ x, |y' x| ≤ C * Real.exp (-alpha * |x|))
    (hrel : ∀ s, |y' s| ≤ D * y s)
    (ha1 : a < 1) (hYa : ∀ v, (∑' m : ℤ, y (v - m * P)) ≤ a) (hsmall : G a * D ≤ 1) (u : ℝ) :
    0 ≤ (∑' m : ℤ, y (u - m * P))
      + G (∑' m : ℤ, y (u - m * P)) * ∑' m : ℤ, y' (u - m * P) := by
  set Y : ℝ := ∑' m : ℤ, y (u - m * P) with hY
  set Y' : ℝ := ∑' m : ℤ, y' (u - m * P) with hY'
  have hY0 : 0 ≤ Y := tsum_nonneg fun m => hy0 _
  have hYle : Y ≤ a := hYa u
  have hGle : G Y ≤ G a := G_le_G_of_le hY0 hYle ha1
  have hG0 : 0 ≤ G Y := by simp [G]
  have hY'le : |Y'| ≤ D * Y := abs_deriv_periodization_le halpha hP hyb hy'b hrel u
  have hlow : -(D * Y) ≤ Y' := neg_le_of_abs_le hY'le
  have hGa0 : 0 ≤ G a := le_trans hG0 hGle
  have hprod : G Y * Y' ≥ -(G a * (D * Y)) := by
    rcases le_or_gt 0 Y' with h | h
    · have h1 : 0 ≤ G Y * Y' := mul_nonneg hG0 h
      have h2 : 0 ≤ G a * (D * Y) := mul_nonneg hGa0 (mul_nonneg hD hY0)
      linarith
    · have h1 : G a * Y' ≤ G Y * Y' := by nlinarith
      have h2 : G a * (-(D * Y)) ≤ G a * Y' := mul_le_mul_of_nonneg_left hlow hGa0
      nlinarith
  have hfin : 0 ≤ Y - G a * (D * Y) := by nlinarith
  linarith

end PeriodizedTurning
