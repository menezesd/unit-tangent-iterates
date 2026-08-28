import UnitTangentIterates.PeriodicGreen
import UnitTangentIterates.SelectedSteeringCoefficientPos

/-!
# Decay of the periodic linearized steering propagator

For the scalar equation `w' + a w = f`, a positive uniform lower bound on
`a` gives exponential decay of the homogeneous propagator.  This is the
coefficient estimate used implicitly in TeX Lemma `lem:path-inverse` before
the periodic Green inverse is applied.
-/

open Real Set

namespace PeriodicGreen

/-- A uniform lower bound for a coefficient gives the corresponding lower
bound for its primitive on every positively oriented interval. -/
theorem const_mul_sub_le_prim_sub {a : ℝ → ℝ} {c x y : ℝ}
    (ha : Continuous a) (hac : ∀ t, c ≤ a t) (hyx : y ≤ x) :
    c * (x - y) ≤ prim a x - prim a y := by
  rw [prim_sub_eq ha]
  have hc : IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume y x :=
    intervalIntegrable_const
  have ha' : IntervalIntegrable a MeasureTheory.volume y x :=
    ha.intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on hyx hc ha' (fun t _ => hac t)
  simpa [mul_comm] using h

/-- Quantitative decay of the homogeneous fundamental solution
`exp (-(A(x)-A(y)))`. -/
theorem exp_neg_prim_sub_le {a : ℝ → ℝ} {c x y : ℝ}
    (ha : Continuous a) (hac : ∀ t, c ≤ a t) (hyx : y ≤ x) :
    Real.exp (-(prim a x - prim a y)) ≤ Real.exp (-c * (x - y)) := by
  apply Real.exp_le_exp.mpr
  have h := const_mul_sub_le_prim_sub ha hac hyx
  linarith

end PeriodicGreen

namespace SteeringJointC1

variable {q delta : ℝ → ℝ → ℝ} {kap : ℝ}

/-- The homogeneous propagator of the selected-steering linearization decays
at the explicit paper rate `sqrt (1-kap²) / kap`. -/
theorem exp_neg_linCoeff_prim_sub_le (hkap : 0 < kap)
    (hqlow : ∀ a x, kap⁻¹ ≤ q a x)
    (hstrip : ∀ a x, delta a x ∈ Icc (0 : ℝ) (arcsin kap))
    (hqcont : Continuous (Function.uncurry q))
    (hdelta : ∀ a, Continuous (delta a)) {p x y : ℝ} (hyx : y ≤ x) :
    Real.exp (-(PeriodicGreen.prim (linCoeff q delta p) x
      - PeriodicGreen.prim (linCoeff q delta p) y))
      ≤ Real.exp (-(Real.sqrt (1 - kap ^ 2) / kap) * (x - y)) := by
  apply PeriodicGreen.exp_neg_prim_sub_le
  · exact ((hqcont.comp (continuous_const.prodMk continuous_id)).mul
      (Real.continuous_cos.comp (hdelta p)))
  · exact fun t => linCoeff_ge hkap hqlow hstrip p t
  · exact hyx

end SteeringJointC1
