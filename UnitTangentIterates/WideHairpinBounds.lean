import Mathlib
import UnitTangentIterates.ProfileBarrierBounds
import UnitTangentIterates.HairpinRelativeDerivatives

/-!
# Quantitative small-curvature bounds for wide hairpins

The two-cap construction in the paper begins by choosing a translating hairpin
whose profile is wide.  The barrier construction gives this quantitatively:
if `f >= eps^{-1} - eps`, then both its intrinsic curvature and its steering
pulse are bounded by `1 / (eps^{-1} - eps)` on the hairpin angle interval.

These are the first strip-smallness estimates needed to instantiate
`ModelOrbitDefect.Config` from the paper's hairpin.
-/

noncomputable section

open Real Set

open scoped ContDiff

namespace WideHairpinBounds

open HairpinRelative ProfileBarrierBounds

variable {eps : ℝ} {f : ℝ -> ℝ}

/-- The intrinsic curvature of a profile above the lower barrier is
nonnegative on the hairpin angle interval. -/
theorem curvField_nonneg_of_lower_barrier (heps : 0 < eps) (heps' : eps <= 1 / 10)
    (hfl : forall theta, Barriers.fMinus eps theta <= f theta)
    {theta : ℝ} (htheta : theta ∈ Icc 0 Real.pi) :
    0 <= curvField f theta := by
  refine HairpinRelative.curvField_nonneg (fun t => ?_) htheta
  have hgap := ProfileBarrierBounds.profile_pos_of_lower_barrier heps heps' hfl t
  exact lt_of_lt_of_le hgap.1 hgap.2

/-- A wide barrier lower bound makes the intrinsic curvature uniformly small. -/
theorem curvField_le_inv_gap (heps : 0 < eps) (heps' : eps <= 1 / 10)
    (hfl : forall theta, Barriers.fMinus eps theta <= f theta)
    {theta : ℝ} (htheta : theta ∈ Icc 0 Real.pi) :
    curvField f theta <= 1 / (eps⁻¹ - eps) := by
  have hgap := ProfileBarrierBounds.profile_pos_of_lower_barrier heps heps' hfl theta
  have hfpos : 0 < f theta := lt_of_lt_of_le hgap.1 hgap.2
  calc
    curvField f theta = Real.sin theta / f theta := rfl
    _ <= 1 / f theta := by
      exact div_le_div_of_nonneg_right (Real.sin_le_one theta) hfpos.le
    _ <= 1 / (eps⁻¹ - eps) := one_div_le_one_div_of_le hgap.1 hgap.2

/-- The steering pulse is no larger than the intrinsic curvature, hence obeys
the same wide-hairpin bound. -/
theorem pulseField_le_inv_gap (heps : 0 < eps) (heps' : eps <= 1 / 10)
    (hfl : forall theta, Barriers.fMinus eps theta <= f theta)
    {theta : ℝ} (htheta : theta ∈ Icc 0 Real.pi) :
    pulseField f theta <= 1 / (eps⁻¹ - eps) := by
  have hcurv := curvField_nonneg_of_lower_barrier heps heps' hfl htheta
  have hsqrt : 1 <= Real.sqrt (1 + curvField f theta ^ 2) := by
    have h1 : (1 : ℝ) ≤ 1 + curvField f theta ^ 2 := by
      nlinarith [sq_nonneg (curvField f theta)]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + curvField f theta ^ 2) := Real.sqrt_le_sqrt h1
  have hsqrtpos : 0 < Real.sqrt (1 + curvField f theta ^ 2) := by positivity
  have hle : pulseField f theta <= curvField f theta := by
    rw [pulseField, div_le_iff₀ hsqrtpos]
    exact le_mul_of_one_le_right hcurv hsqrt
  exact hle.trans (curvField_le_inv_gap heps heps' hfl htheta)

/-- A barrier-wide smooth hairpin has an explicitly small steering pulse and
the first two relative derivative bounds needed by periodization.  The
constants `D₁,D₂` come from smoothness of the particular translator profile;
the barrier estimate controls the pulse amplitude independently of them. -/
theorem exists_wide_pulse_relative_data
    (heps : 0 < eps) (heps' : eps <= 1 / 10)
    (hfl : forall theta, Barriers.fMinus eps theta <= f theta)
    (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ theta x : ℝ → ℝ, ∃ D₁ D₂ : ℝ,
      (∀ u, theta u ∈ Ioo 0 Real.pi) ∧
      (∀ s, HairpinRelative.frontArclength f theta (x s) = s) ∧
      (∀ s, pulseField f (theta (x s)) ≤ 1 / (eps⁻¹ - eps)) ∧
      (0 ≤ D₁) ∧
      (∀ s, |iteratedDeriv 1 (fun r => pulseField f (theta (x r))) s|
        ≤ D₁ * pulseField f (theta (x s))) ∧
      (0 ≤ D₂) ∧
      (∀ s, |iteratedDeriv 2 (fun r => pulseField f (theta (x r))) s|
        ≤ D₂ * pulseField f (theta (x s))) := by
  obtain ⟨theta, htheta, -, htheta', -, x, hx, hx' , hrel⟩ :=
    HairpinRelative.hairpin_relative_derivative_bounds hf hfpos
  obtain ⟨D₁, hD₁, hD₁rel⟩ := hrel 1
  obtain ⟨D₂, hD₂, hD₂rel⟩ := hrel 2
  refine ⟨theta, x, D₁, D₂, htheta, hx, ?_, hD₁, hD₁rel, hD₂, hD₂rel⟩
  · intro s
    exact pulseField_le_inv_gap heps heps' hfl ⟨(htheta (x s)).1.le, (htheta (x s)).2.le⟩

end WideHairpinBounds
