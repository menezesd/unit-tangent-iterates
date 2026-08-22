import Mathlib
import UnitTangentIterates.HairpinRelativeDerivatives
import UnitTangentIterates.HairpinPulseDecay
import UnitTangentIterates.FrontPeriodizationHairpin

/-!
# The steering identity of the hairpin

The theorem *Curvature-measure matching* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* reads the isolated curvature `K_*` in the **own
arclength** `x` of the rear track, and consumes the *steering identity*

```
  y = √(1 - y²) · K_*(x),      x' = √(1 - y²),
```

which says that the steering pulse `y = sin δ` is the curvature measured
against the own speed of the track.  For the hairpin of a smooth positive
profile both clauses are exact, because the pulse field is
`G₂ = G/√(1+G²)` for the curvature field `G`:

* `one_sub_pulseField_sq` : `1 - G₂² = 1/(1+G²)`;
* `sqrt_one_sub_pulseField_sq` : `√(1 - G₂²) = 1/√(1+G²)`;
* `pulseField_eq_speed_mul_curvField` : `G₂ = √(1 - G₂²)·G`, the steering
  identity pointwise;
* `hasDerivAt_pulseInverse` : the inverse `x` of the front arclength has
  derivative `√(1 - y²)`, `y` being the pulse read in the front arclength;
* `pulseInverse_zero` : `x(0) = 0`;
* `hairpin_steering_identity` : the two clauses for the hairpin of the paper,
  packaged with the data of `FrontPeriodizationHairpin.exists_hairpin_pulse_data`.
-/

noncomputable section

open Real Set MeasureTheory

open scoped ContDiff

namespace HairpinPulseIdentity

open HairpinRelative

variable {f : ℝ → ℝ}

/-! ### The speed of the rear track -/

/-- `1 - G₂² = 1/(1+G²)`: the square of the own speed of the rear track. -/
theorem one_sub_pulseField_sq (f : ℝ → ℝ) (t : ℝ) :
    1 - pulseField f t ^ 2 = 1 / (1 + curvField f t ^ 2) := by
  have hpos : (0:ℝ) < 1 + curvField f t ^ 2 := by positivity
  have hs : Real.sqrt (1 + curvField f t ^ 2) ^ 2 = 1 + curvField f t ^ 2 :=
    Real.sq_sqrt hpos.le
  have hne : Real.sqrt (1 + curvField f t ^ 2) ≠ 0 := (sqrt_one_add_sq_pos _).ne'
  rw [pulseField, div_pow, hs]
  field_simp
  ring

/-- The own speed of the rear track is `1/√(1+G²)`. -/
theorem sqrt_one_sub_pulseField_sq (f : ℝ → ℝ) (t : ℝ) :
    Real.sqrt (1 - pulseField f t ^ 2) = 1 / Real.sqrt (1 + curvField f t ^ 2) := by
  rw [one_sub_pulseField_sq, one_div, one_div, Real.sqrt_inv]

/-- **The steering identity, pointwise.**  The steering pulse is the curvature
measured against the own speed of the rear track: `G₂ = √(1 - G₂²)·G`. -/
theorem pulseField_eq_speed_mul_curvField (f : ℝ → ℝ) (t : ℝ) :
    pulseField f t = Real.sqrt (1 - pulseField f t ^ 2) * curvField f t := by
  rw [sqrt_one_sub_pulseField_sq, pulseField]
  field_simp

/-! ### The inverse of the front arclength -/

section Inverse

variable {theta x : ℝ → ℝ}

/-- The front arclength has derivative `√(1+G²) ≥ 1`. -/
theorem hasDerivAt_frontArclength_sqrt (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u) (u : ℝ) :
    HasDerivAt (frontArclength f theta)
      (Real.sqrt (1 + curvField f (theta u) ^ 2)) u := by
  have hGc : Continuous (curvField f) := (contDiff_curvField hf hfpos).continuous
  have hthetac : Continuous theta :=
    Differentiable.continuous fun u => (hderiv u).differentiableAt
  have hgc : Continuous fun u => Real.sqrt (1 + curvField f (theta u) ^ 2) := by
    have : Continuous fun u => 1 + curvField f (theta u) ^ 2 :=
      continuous_const.add ((hGc.comp hthetac).pow 2)
    exact this.sqrt
  exact intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
    (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt

theorem one_le_sqrt_one_add_curv_sq (f : ℝ → ℝ) (u : ℝ) :
    (1:ℝ) ≤ Real.sqrt (1 + curvField f u ^ 2) := by
  have h1 : (1:ℝ) ≤ 1 + curvField f u ^ 2 := by nlinarith [sq_nonneg (curvField f u)]
  calc (1:ℝ) = Real.sqrt 1 := by simp
    _ ≤ _ := Real.sqrt_le_sqrt h1

/-- **The own speed as the derivative of the inverse front arclength.**  If `x`
inverts the front arclength, then `x' = √(1 - y²)` for the pulse
`y = G₂ ∘ θ ∘ x`. -/
theorem hasDerivAt_pulseInverse (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s) (s : ℝ) :
    HasDerivAt x (Real.sqrt (1 - pulseField f (theta (x s)) ^ 2)) s := by
  have h := ArclengthInverse.hasDerivAt_of_rightInverse (c := 1) one_pos
    (hasDerivAt_frontArclength_sqrt hf hfpos hderiv)
    (fun u => one_le_sqrt_one_add_curv_sq f (theta u)) hxinv s
  rwa [← sqrt_one_sub_pulseField_sq] at h

/-- The inverse of the front arclength fixes the origin. -/
theorem pulseInverse_zero (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s) : x 0 = 0 := by
  have hd := hasDerivAt_frontArclength_sqrt hf hfpos hderiv
  have hmono : StrictMono (frontArclength f theta) := by
    refine strictMono_of_deriv_pos fun u => ?_
    rw [(hd u).deriv]
    exact lt_of_lt_of_le one_pos (one_le_sqrt_one_add_curv_sq f (theta u))
  refine hmono.injective ?_
  rw [hxinv 0]
  exact (frontArclength_zero f theta).symm

end Inverse

/-! ### The steering identity for the hairpin of the paper -/

/-- **The steering identity of the hairpin.**  For a profile `f` smooth and
positive on the line, the hairpin has an arclength parametrization `θ` whose
curvature is `K_* = G ∘ θ`, and the inverse `x` of its front arclength carries
the steering pulse `y = G₂ ∘ θ ∘ x`, which obeys

`x(0) = 0`,  `x' = √(1 - y²)`,  `y = √(1 - y²)·K_*(x)`,

together with all the bounds of `exists_hairpin_pulse_data`. -/
theorem hairpin_steering_identity (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ (theta x : ℝ → ℝ) (alpha C b : ℝ),
      0 < alpha ∧ 0 ≤ C ∧ 0 ≤ b ∧ b < 1 ∧
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      Continuous (fun s => pulseField f (theta (x s))) ∧
      (∀ s, 0 ≤ pulseField f (theta (x s))) ∧
      (∀ s, pulseField f (theta (x s)) ≤ C * Real.exp (-alpha * |s|)) ∧
      (∀ s, pulseField f (theta (x s)) ≤ b) ∧
      x 0 = 0 ∧
      (∀ s, HasDerivAt x (Real.sqrt (1 - pulseField f (theta (x s)) ^ 2)) s) ∧
      (∀ s, pulseField f (theta (x s))
        = Real.sqrt (1 - pulseField f (theta (x s)) ^ 2)
          * curvField f (theta (x s))) := by
  obtain ⟨theta, x, -, alpha, C, -, b, halpha, hC0, -, hb0, hb1, -, -, -,
    hmem, hval, hderiv, hxinv, -, hycont, hy0, hyb, hsup, -, -, -, -⟩ :=
    FrontPeriodizationHairpin.exists_hairpin_pulse_data hf hfpos
  exact ⟨theta, x, alpha, C, b, halpha, hC0, hb0, hb1, hmem, hval, hderiv, hxinv,
    hycont, hy0, hyb, hsup,
    pulseInverse_zero hf hfpos hderiv hxinv,
    fun s => hasDerivAt_pulseInverse hf hfpos hderiv hxinv s,
    fun s => pulseField_eq_speed_mul_curvField f (theta (x s))⟩

end HairpinPulseIdentity
