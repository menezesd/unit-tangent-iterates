import UnitTangentIterates.PeriodicGreen
import UnitTangentIterates.PeriodicGreenUniformBound

/-!
# First derivative bound for the periodic Green solution

The periodic solution of `w' + a w = f` satisfies `w' = f - a w`.
Combining this identity with the uniform Green estimate gives the derivative
bound used in the smooth-dependence argument of TeX Lemma `lem:path-inverse`.
-/

open Real

namespace PeriodicGreen

/-- Pointwise first-derivative estimate for a periodic Green solution, with
the inverse constant expressed only through `c ≤ a` and the period. -/
theorem abs_deriv_periodicGreen_le_uniform {a f : ℝ → ℝ} {c A l x : ℝ}
    (ha : Continuous a) (haper : Function.Periodic a l)
    (hac : ∀ t, c ≤ a t) (hc : 0 < c) (haA : ∀ t, |a t| ≤ A)
    (hf : Continuous f) (hfper : Function.Periodic f l) (hl : 0 < l) :
    |deriv (periodicGreen a l f) x|
      ≤ |f x| + A * ((1 - Real.exp (-(c * l)))⁻¹
        * ∫ t in (x - l)..x, |f t|) := by
  have hprim : c * l ≤ prim a l := by
    simpa [prim] using
      (const_mul_sub_le_prim_sub ha hac hl.le : c * (l - 0) ≤ prim a l - prim a 0)
  have hApos : 0 < prim a l := lt_of_lt_of_le (mul_pos hc hl) hprim
  have hderiv : deriv (periodicGreen a l f) x
      = f x - a x * periodicGreen a l f x :=
    (periodicGreen_hasDerivAt ha haper hApos hf hfper x).deriv
  have hw := periodicGreen_abs_le_uniform ha hac hc hf hl (x := x)
  calc
    |deriv (periodicGreen a l f) x|
        = |f x - a x * periodicGreen a l f x| := by rw [hderiv]
    _ ≤ |f x| + |a x * periodicGreen a l f x| := abs_sub _ _
    _ = |f x| + |a x| * |periodicGreen a l f x| := by rw [abs_mul]
    _ ≤ |f x| + A * ((1 - Real.exp (-(c * l)))⁻¹
          * ∫ t in (x - l)..x, |f t|) := by
      have hA0 : 0 ≤ A := le_trans (abs_nonneg (a x)) (haA x)
      have hmul := mul_le_mul (haA x) hw (abs_nonneg _) hA0
      linarith

end PeriodicGreen
