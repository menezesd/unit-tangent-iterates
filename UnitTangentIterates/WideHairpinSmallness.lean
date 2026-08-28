import Mathlib
import UnitTangentIterates.WideHairpinBounds

/-!
# Small-curvature scale of the barrier hairpin

For the barrier parameter `eps <= 1/10`, the reciprocal lower-profile gap is
at most `2 eps`.  Combined with `WideHairpinBounds`, this gives the explicit
small-curvature scale used when choosing the selected-steering strip.
-/

noncomputable section

open Real Set

namespace WideHairpinSmallness

open HairpinRelative WideHairpinBounds

variable {eps : ℝ} {f : ℝ -> ℝ}

/-- The reciprocal barrier gap is on the order of the width parameter. -/
theorem inv_gap_le_two_mul (heps : 0 < eps) (heps' : eps <= 1 / 10) :
    1 / (eps⁻¹ - eps) <= 2 * eps := by
  have hepssq : eps ^ 2 <= (1 : ℝ) / 100 := by nlinarith
  have hden : (1 : ℝ) / 2 <= 1 - eps ^ 2 := by nlinarith
  have hdenpos : 0 < 1 - eps ^ 2 := by linarith
  have hgap : 0 < eps⁻¹ - eps := by
    rw [show eps⁻¹ - eps = (1 - eps ^ 2) / eps by field_simp]
    exact div_pos hdenpos heps
  have heq : 1 / (eps⁻¹ - eps) = eps / (1 - eps ^ 2) := by
    field_simp
  rw [heq, div_le_iff₀ hdenpos]
  have hmul : eps * ((1 : ℝ) / 2) <= eps * (1 - eps ^ 2) :=
    mul_le_mul_of_nonneg_left hden heps.le
  nlinarith

/-- A barrier profile with width parameter `eps` has intrinsic curvature at
most `2 eps` on the hairpin angle interval. -/
theorem curvField_le_two_mul (heps : 0 < eps) (heps' : eps <= 1 / 10)
    (hfl : forall theta, Barriers.fMinus eps theta <= f theta)
    {theta : ℝ} (htheta : theta ∈ Icc 0 Real.pi) :
    curvField f theta <= 2 * eps :=
  (curvField_le_inv_gap heps heps' hfl htheta).trans (inv_gap_le_two_mul heps heps')

/-- The selected steering pulse of a barrier profile is at most `2 eps`. -/
theorem pulseField_le_two_mul (heps : 0 < eps) (heps' : eps <= 1 / 10)
    (hfl : forall theta, Barriers.fMinus eps theta <= f theta)
    {theta : ℝ} (htheta : theta ∈ Icc 0 Real.pi) :
    pulseField f theta <= 2 * eps :=
  (pulseField_le_inv_gap heps heps' hfl htheta).trans (inv_gap_le_two_mul heps heps')

/-- A relative derivative estimate for the pulse becomes an absolute
`O(eps)` estimate on a barrier-wide hairpin.  The multiplier `D` remains the
fixed relative-derivative constant of the chosen translator profile; the
barrier construction alone does not make it uniform in `eps`. -/
theorem abs_iteratedDeriv_pulse_le_two_mul
    (heps : 0 < eps) (heps' : eps <= 1 / 10)
    (hfl : forall theta, Barriers.fMinus eps theta <= f theta)
    {theta x : ℝ -> ℝ} {j : ℕ} {D : ℝ}
    (htheta : forall s, theta (x s) ∈ Icc 0 Real.pi)
    (hD : 0 <= D)
    (hrel : forall s,
      |iteratedDeriv j (fun r => pulseField f (theta (x r))) s|
        <= D * pulseField f (theta (x s))) :
    forall s,
      |iteratedDeriv j (fun r => pulseField f (theta (x r))) s|
        <= (2 * D) * eps := by
  intro s
  calc
    |iteratedDeriv j (fun r => pulseField f (theta (x r))) s|
        <= D * pulseField f (theta (x s)) := hrel s
    _ <= D * (2 * eps) :=
      mul_le_mul_of_nonneg_left (pulseField_le_two_mul heps heps' hfl (htheta s)) hD
    _ = (2 * D) * eps := by ring

end WideHairpinSmallness
