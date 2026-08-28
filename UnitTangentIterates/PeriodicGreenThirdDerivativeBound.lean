import UnitTangentIterates.PeriodicGreen
import UnitTangentIterates.PeriodicGreenSecondDerivativeBound

/-!
# Third derivative bound for the periodic Green solution

The next ODE bootstrap step gives
`w''' = f'' - a''w - 2a'w' - aw''`.  This supplies the finite-order
regularity estimate used by the smooth selected-rear construction in TeX
Lemma `lem:path-inverse`.
-/

open Real

namespace PeriodicGreen

/-- The exact third derivative identity for the periodic Green solution. -/
theorem deriv3_periodicGreen_eq {a a1 a2 f f1 f2 : ℝ → ℝ} {l x : ℝ}
    (ha : Continuous a) (haper : Function.Periodic a l)
    (hA : 0 < prim a l) (hf : Continuous f) (hfper : Function.Periodic f l)
    (ha1 : ∀ t, HasDerivAt a (a1 t) t) (ha2 : ∀ t, HasDerivAt a1 (a2 t) t)
    (hf1 : ∀ t, HasDerivAt f (f1 t) t) (hf2 : ∀ t, HasDerivAt f1 (f2 t) t) :
    deriv (deriv (deriv (periodicGreen a l f))) x
      = f2 x - a2 x * periodicGreen a l f x
        - 2 * a1 x * deriv (periodicGreen a l f) x
        - a x * deriv (deriv (periodicGreen a l f)) x := by
  have hw : ∀ t, HasDerivAt (periodicGreen a l f)
      (f t - a t * periodicGreen a l f t) t :=
    fun t => periodicGreen_hasDerivAt ha haper hA hf hfper t
  have hw1 : ∀ t, HasDerivAt (fun y => f y - a y * periodicGreen a l f y)
      (f1 t - a1 t * periodicGreen a l f t
        - a t * (f t - a t * periodicGreen a l f t)) t := by
    intro t
    refine ((hf1 t).sub ((ha1 t).mul (hw t))).congr_deriv ?_
    ring
  have hfirst : deriv (periodicGreen a l f)
      = fun t => f t - a t * periodicGreen a l f t :=
    funext fun t => (hw t).deriv
  have hsecond : deriv (deriv (periodicGreen a l f))
      = fun t => f1 t - a1 t * periodicGreen a l f t
        - a t * (f t - a t * periodicGreen a l f t) := by
    rw [hfirst]
    exact funext fun t => (hw1 t).deriv
  rw [hsecond]
  have hcalc : HasDerivAt
      (fun t => f1 t - a1 t * periodicGreen a l f t
        - a t * (f t - a t * periodicGreen a l f t))
      (f2 x - (a2 x * periodicGreen a l f x + a1 x * (f x - a x * periodicGreen a l f x))
        - (a1 x * (f x - a x * periodicGreen a l f x)
          + a x * (f1 x - a1 x * periodicGreen a l f x
            - a x * (f x - a x * periodicGreen a l f x)))) x := by
    exact ((hf2 x).sub ((ha2 x).mul (hw x))).sub ((ha1 x).mul (hw1 x))
  refine hcalc.deriv.trans ?_
  rw [hfirst]
  ring

/-- Recursive explicit uniform estimate for the third derivative. -/
theorem abs_deriv3_periodicGreen_le_uniform
    {a a1 a2 f f1 f2 : ℝ → ℝ} {c A A1 A2 l x : ℝ}
    (ha : Continuous a) (haper : Function.Periodic a l)
    (hac : ∀ t, c ≤ a t) (hc : 0 < c)
    (haA : ∀ t, |a t| ≤ A) (ha1A : ∀ t, |a1 t| ≤ A1)
    (ha2A : ∀ t, |a2 t| ≤ A2)
    (hf : Continuous f) (hfper : Function.Periodic f l)
    (ha1 : ∀ t, HasDerivAt a (a1 t) t) (ha2 : ∀ t, HasDerivAt a1 (a2 t) t)
    (hf1 : ∀ t, HasDerivAt f (f1 t) t) (hf2 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hl : 0 < l) :
    |deriv (deriv (deriv (periodicGreen a l f))) x|
      ≤ |f2 x|
        + A2 * ((1 - Real.exp (-(c * l)))⁻¹ * ∫ t in (x - l)..x, |f t|)
        + 2 * A1 * (|f x| + A * ((1 - Real.exp (-(c * l)))⁻¹
          * ∫ t in (x - l)..x, |f t|))
        + A * (|f1 x|
          + A1 * ((1 - Real.exp (-(c * l)))⁻¹ * ∫ t in (x - l)..x, |f t|)
          + A * (|f x| + A * ((1 - Real.exp (-(c * l)))⁻¹
            * ∫ t in (x - l)..x, |f t|))) := by
  have hprim : c * l ≤ prim a l := by
    simpa [prim] using
      (const_mul_sub_le_prim_sub ha hac hl.le : c * (l - 0) ≤ prim a l - prim a 0)
  have hApos : 0 < prim a l := lt_of_lt_of_le (mul_pos hc hl) hprim
  rw [deriv3_periodicGreen_eq ha haper hApos hf hfper ha1 ha2 hf1 hf2]
  have hw := periodicGreen_abs_le_uniform ha hac hc hf hl (x := x)
  have hw1 := abs_deriv_periodicGreen_le_uniform ha haper hac hc haA hf hfper hl (x := x)
  have hw2 := abs_deriv_deriv_periodicGreen_le_uniform ha haper hac hc haA ha1A hf hfper
    ha1 hf1 hl (x := x)
  calc
    |f2 x - a2 x * periodicGreen a l f x
        - 2 * a1 x * deriv (periodicGreen a l f) x
        - a x * deriv (deriv (periodicGreen a l f)) x|
      ≤ |f2 x| + |a2 x| * |periodicGreen a l f x|
        + 2 * |a1 x| * |deriv (periodicGreen a l f) x|
        + |a x| * |deriv (deriv (periodicGreen a l f)) x| := by
          have h1 := abs_add_le (f2 x - a2 x * periodicGreen a l f x
              - 2 * a1 x * deriv (periodicGreen a l f) x)
            (-(a x * deriv (deriv (periodicGreen a l f)) x))
          have h2 := abs_add_le (f2 x - a2 x * periodicGreen a l f x)
            (-(2 * a1 x * deriv (periodicGreen a l f) x))
          have h3 := abs_add_le (f2 x) (-(a2 x * periodicGreen a l f x))
          have e1 : |a2 x * periodicGreen a l f x|
              = |a2 x| * |periodicGreen a l f x| := abs_mul _ _
          have e2 : |2 * a1 x * deriv (periodicGreen a l f) x|
              = 2 * |a1 x| * |deriv (periodicGreen a l f) x| := by
            rw [abs_mul, abs_mul]
            norm_num
          have e3 : |a x * deriv (deriv (periodicGreen a l f)) x|
              = |a x| * |deriv (deriv (periodicGreen a l f)) x| := abs_mul _ _
          simp only [sub_eq_add_neg, abs_neg] at h1 h2 h3 ⊢
          linarith
    _ ≤ _ := by
      have hA2 : (0:ℝ) ≤ A2 := le_trans (abs_nonneg (a2 x)) (ha2A x)
      have hA1 : (0:ℝ) ≤ A1 := le_trans (abs_nonneg (a1 x)) (ha1A x)
      have hA0 : (0:ℝ) ≤ A := le_trans (abs_nonneg (a x)) (haA x)
      have hb1 := mul_le_mul (ha2A x) hw (abs_nonneg _) hA2
      have hb2 := mul_le_mul (ha1A x) hw1 (abs_nonneg _) hA1
      have hb3 := mul_le_mul (haA x) hw2 (abs_nonneg _) hA0
      linarith

end PeriodicGreen
