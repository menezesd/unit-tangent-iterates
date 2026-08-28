import Mathlib

/-!
# Analytic core of strictness for consecutive convex tracks

This is the integrating-factor argument in the TeX lemma `Convex consecutive
tracks`, separated from the Frenet calculation and parameter normalization.
-/

open Set Function

namespace ConvexConsecutiveStrictnessCore

/-- A nonnegative nontrivial periodic profile is strictly positive when its
exponentially weighted profile is nondecreasing.  `hrepresentative` is the
only periodic-parameter input used by the proof: every value occurs on the
chosen closed fundamental interval. -/
theorem positive_of_exp_mul_monotone
    {u : ℝ → ℝ} {x0 P : ℝ}
    (hP : 0 < P)
    (hu : ∀ x, 0 ≤ u x)
    (hper : Periodic u P)
    (hmono : Monotone fun x => Real.exp x * u x)
    (hrepresentative : ∀ z, ∃ y ∈ Icc x0 (x0 + P), u y = u z)
    (hnontrivial : ∃ z, 0 < u z) :
    ∀ x, 0 < u x := by
  intro x
  by_contra hx
  have hux : u x = 0 := le_antisymm (le_of_not_gt hx) (hu x)
  obtain ⟨z, hz⟩ := hnontrivial
  obtain ⟨y, hy, hyz⟩ := hrepresentative z
  obtain ⟨yx, hyx, hyxx⟩ := hrepresentative x
  have hyxzero : u yx = 0 := hyxx.trans hux
  by_cases horder : y ≤ yx
  · have hupper := hmono horder
    change Real.exp y * u y ≤ Real.exp yx * u yx at hupper
    rw [hyz, hyxzero, mul_zero] at hupper
    exact (not_lt_of_ge hupper) (mul_pos (Real.exp_pos y) hz)
  · have hyshift : u (y - P) = u y := by
      have hp := hper (y - P)
      convert hp.symm using 1 <;> ring
    have hshiftOrder : y - P ≤ yx := by linarith [hy.2, hyx.1]
    have hupper := hmono hshiftOrder
    change Real.exp (y - P) * u (y - P) ≤ Real.exp yx * u yx at hupper
    rw [hyshift, hyz, hyxzero, mul_zero] at hupper
    exact (not_lt_of_ge hupper) (mul_pos (Real.exp_pos (y - P)) hz)

/-- Direct integrating-factor form used after the Frenet identity
`K = u' + u`: a globally nonnegative derivative of `exp(x)u(x)` supplies the
monotonicity hypothesis of `positive_of_exp_mul_monotone`. -/
theorem positive_of_integratingFactor_deriv
    {u F : ℝ → ℝ} {x0 P : ℝ}
    (hP : 0 < P)
    (hu : ∀ x, 0 ≤ u x)
    (hper : Periodic u P)
    (hF : ∀ x, HasDerivAt (fun y => Real.exp y * u y) (F x) x)
    (hFnonneg : ∀ x, 0 ≤ F x)
    (hrepresentative : ∀ z, ∃ y ∈ Icc x0 (x0 + P), u y = u z)
    (hnontrivial : ∃ z, 0 < u z) :
    ∀ x, 0 < u x := by
  apply positive_of_exp_mul_monotone hP hu hper
  · exact monotone_of_deriv_nonneg
      (fun x => (hF x).differentiableAt)
      (fun x => by rw [(hF x).deriv]; exact hFnonneg x)
  · exact hrepresentative
  · exact hnontrivial

end ConvexConsecutiveStrictnessCore
