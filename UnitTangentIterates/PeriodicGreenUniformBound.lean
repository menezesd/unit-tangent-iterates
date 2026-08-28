import UnitTangentIterates.PeriodicGreen
import UnitTangentIterates.PeriodicGreenCoefficientDecay

/-!
# A uniform inverse bound for positive periodic first-order equations

The Green estimate in `PeriodicGreen` retains the exact normalization
`(1-exp(-A(P)))⁻¹`.  A coefficient lower bound `c ≤ a` replaces it by the
fixed constant `(1-exp(-cP))⁻¹`, which is the uniform inverse estimate used
in TeX Lemma `lem:path-inverse`.
-/

open Real

namespace PeriodicGreen

/-- The Green normalization is controlled solely by a positive coefficient
lower bound and the period. -/
theorem normalization_inv_le {a : ℝ → ℝ} {c l : ℝ}
    (ha : Continuous a) (hac : ∀ t, c ≤ a t) (hc : 0 < c) (hl : 0 < l) :
    (1 - Real.exp (-prim a l))⁻¹ ≤ (1 - Real.exp (-(c * l)))⁻¹ := by
  have hprim : c * l ≤ prim a l := by
    simpa [prim] using
      (const_mul_sub_le_prim_sub ha hac hl.le : c * (l - 0) ≤ prim a l - prim a 0)
  have hexp : Real.exp (-prim a l) ≤ Real.exp (-(c * l)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hleft : 0 < 1 - Real.exp (-(c * l)) := by
    have hlt : Real.exp (-(c * l)) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith)
    linarith
  have hA : 0 < prim a l := lt_of_lt_of_le (mul_pos hc hl) hprim
  exact (inv_le_inv₀ (one_sub_exp_pos hA) hleft).mpr (by linarith)

/-- Uniform `L¹ → L∞` estimate for the periodic inverse of `∂ₓ+a`, with a
constant depending only on the lower coefficient bound and the period. -/
theorem periodicGreen_abs_le_uniform {a f : ℝ → ℝ} {c l x : ℝ}
    (ha : Continuous a) (hac : ∀ t, c ≤ a t) (hc : 0 < c)
    (hf : Continuous f) (hl : 0 < l) :
    |periodicGreen a l f x|
      ≤ (1 - Real.exp (-(c * l)))⁻¹ * ∫ t in (x - l)..x, |f t| := by
  have ha0 : ∀ t, 0 ≤ a t := fun t => le_trans hc.le (hac t)
  have hprim : c * l ≤ prim a l := by
    simpa [prim] using
      (const_mul_sub_le_prim_sub ha hac hl.le : c * (l - 0) ≤ prim a l - prim a 0)
  have hA : 0 < prim a l := lt_of_lt_of_le (mul_pos hc hl) hprim
  calc
    |periodicGreen a l f x|
        ≤ (1 - Real.exp (-prim a l))⁻¹ * ∫ t in (x - l)..x, |f t| :=
      periodicGreen_abs_le ha ha0 hA hf hl x
    _ ≤ (1 - Real.exp (-(c * l)))⁻¹ * ∫ t in (x - l)..x, |f t| := by
      exact mul_le_mul_of_nonneg_right (normalization_inv_le ha hac hc hl)
        (intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _))

end PeriodicGreen
