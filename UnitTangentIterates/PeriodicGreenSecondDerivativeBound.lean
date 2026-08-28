import UnitTangentIterates.PeriodicGreen
import UnitTangentIterates.PeriodicGreenDerivativeBound

/-!
# Second derivative bound for the periodic Green solution

Differentiating `w' = f - a w` once gives
`w'' = f' - a' w - a w'`.  This file records the identity and the uniform
bound used in the regularity bootstrap of TeX Lemma `lem:path-inverse`.
-/

open Real

namespace PeriodicGreen

/-- The second derivative of the periodic Green solution, expressed only in
terms of the coefficient, source, and their first derivatives. -/
theorem deriv_deriv_periodicGreen_eq {a a1 f f1 : ℝ → ℝ} {l x : ℝ}
    (ha : Continuous a) (haper : Function.Periodic a l)
    (hA : 0 < prim a l) (hf : Continuous f) (hfper : Function.Periodic f l)
    (ha1 : ∀ t, HasDerivAt a (a1 t) t) (hf1 : ∀ t, HasDerivAt f (f1 t) t) :
    deriv (deriv (periodicGreen a l f)) x
      = f1 x - a1 x * periodicGreen a l f x
        - a x * (f x - a x * periodicGreen a l f x) := by
  have hw : ∀ t, HasDerivAt (periodicGreen a l f)
      (f t - a t * periodicGreen a l f t) t :=
    fun t => periodicGreen_hasDerivAt ha haper hA hf hfper t
  have hfirst : deriv (periodicGreen a l f)
      = fun t => f t - a t * periodicGreen a l f t :=
    funext fun t => (hw t).deriv
  rw [hfirst]
  have h : HasDerivAt (fun t => f t - a t * periodicGreen a l f t)
      (f1 x - (a1 x * periodicGreen a l f x
        + a x * (f x - a x * periodicGreen a l f x))) x :=
    (hf1 x).sub ((ha1 x).mul (hw x))
  rw [h.deriv]
  ring

/-- Uniform second-derivative estimate.  The displayed nested expression is
the direct quantitative bootstrap of the zeroth- and first-order Green
bounds. -/
theorem abs_deriv_deriv_periodicGreen_le_uniform
    {a a1 f f1 : ℝ → ℝ} {c A A1 l x : ℝ}
    (ha : Continuous a) (haper : Function.Periodic a l)
    (hac : ∀ t, c ≤ a t) (hc : 0 < c)
    (haA : ∀ t, |a t| ≤ A) (ha1A : ∀ t, |a1 t| ≤ A1)
    (hf : Continuous f) (hfper : Function.Periodic f l)
    (ha1 : ∀ t, HasDerivAt a (a1 t) t) (hf1 : ∀ t, HasDerivAt f (f1 t) t)
    (hl : 0 < l) :
    |deriv (deriv (periodicGreen a l f)) x|
      ≤ |f1 x|
        + A1 * ((1 - Real.exp (-(c * l)))⁻¹ * ∫ t in (x - l)..x, |f t|)
        + A * (|f x| + A * ((1 - Real.exp (-(c * l)))⁻¹
          * ∫ t in (x - l)..x, |f t|)) := by
  have hprim : c * l ≤ prim a l := by
    simpa [prim] using
      (const_mul_sub_le_prim_sub ha hac hl.le : c * (l - 0) ≤ prim a l - prim a 0)
  have hApos : 0 < prim a l := lt_of_lt_of_le (mul_pos hc hl) hprim
  have hw := periodicGreen_abs_le_uniform ha hac hc hf hl (x := x)
  have hw1 := abs_deriv_periodicGreen_le_uniform ha haper hac hc haA hf hfper hl (x := x)
  rw [deriv_deriv_periodicGreen_eq ha haper hApos hf hfper ha1 hf1]
  calc
    |f1 x - a1 x * periodicGreen a l f x
        - a x * (f x - a x * periodicGreen a l f x)|
      ≤ |f1 x| + |a1 x| * |periodicGreen a l f x|
        + |a x| * |f x - a x * periodicGreen a l f x| := by
          have hA : |f1 x - a1 x * periodicGreen a l f x
                - a x * (f x - a x * periodicGreen a l f x)|
              ≤ |f1 x| + |a1 x * periodicGreen a l f x|
                + |a x * (f x - a x * periodicGreen a l f x)| := by
            have t1 := abs_add_le (f1 x - a1 x * periodicGreen a l f x)
              (-(a x * (f x - a x * periodicGreen a l f x)))
            have t2 := abs_add_le (f1 x) (-(a1 x * periodicGreen a l f x))
            simp only [sub_eq_add_neg, abs_neg] at t1 t2 ⊢
            linarith
          rw [abs_mul, abs_mul] at hA
          exact hA
    _ ≤ |f1 x|
        + A1 * ((1 - Real.exp (-(c * l)))⁻¹ * ∫ t in (x - l)..x, |f t|)
        + A * (|f x| + A * ((1 - Real.exp (-(c * l)))⁻¹
          * ∫ t in (x - l)..x, |f t|)) := by
      have hfirst : |f x - a x * periodicGreen a l f x|
          = |deriv (periodicGreen a l f) x| := by
        rw [(periodicGreen_hasDerivAt ha haper hApos hf hfper x).deriv]
      rw [hfirst]
      have hb1 : |a1 x| * |periodicGreen a l f x|
          ≤ A1 * ((1 - Real.exp (-(c * l)))⁻¹ * ∫ t in (x - l)..x, |f t|) :=
        mul_le_mul (ha1A x) hw (abs_nonneg _)
          (le_trans (abs_nonneg _) (ha1A x))
      have hb2 : |a x| * |deriv (periodicGreen a l f) x|
          ≤ A * (|f x| + A * ((1 - Real.exp (-(c * l)))⁻¹
            * ∫ t in (x - l)..x, |f t|)) :=
        mul_le_mul (haA x) hw1 (abs_nonneg _) (le_trans (abs_nonneg _) (haA x))
      linarith

end PeriodicGreen
