import Mathlib
import UnitTangentIterates.WideHairpinSmallness
import UnitTangentIterates.PaperHairpinQuantitativeData

/-!
# The barrier smallness bounds, localized to the angle interval

`WideHairpinBounds` and `WideHairpinSmallness` state the wide-hairpin smallness
estimates with the barrier hypothesis quantified over the whole line,

```
  hfl : ∀ θ, Barriers.fMinus ε θ ≤ f θ,
```

but every proof uses it at a **single angle**, and that angle always lies in
`[0, π]`: `WideHairpinBounds.curvField_le_inv_gap` applies it only at its own
argument `θ ∈ Icc 0 π`, and `Data.wide_pulse_and_derivative_bounds` applies the
chain only at `θ(x s) ∈ Ioo 0 π`.

The global form is not merely wasteful, it is inconsistent with the profile
*extension* route: the smooth positive extension produced by
`ProfileExtension.exists_contDiff_pos_extension_pi` is identically `1` away from
a collar of `[0, π]`, whereas the barrier lower bound is `ε⁻¹ - ε > 1`.  So an
extended profile can never satisfy the global hypothesis, even though it
satisfies everything the proofs actually need.

This file restates the chain with the barrier hypothesis localized to
`Icc 0 π`, which is what the paper's "uniform barrier bounds" provide.

Main results: `curvField_le_two_mul_on`, `pulseField_le_two_mul_on`,
`wide_pulse_and_derivative_bounds_on`.
-/

noncomputable section

open Real Set HairpinRelative

namespace WideHairpinLocalBounds

variable {eps : ℝ} {f : ℝ → ℝ}

/-- Positivity of the profile at one angle, from the barrier there. -/
theorem profile_pos_at (heps : 0 < eps) (heps' : eps ≤ 1 / 10)
    {t : ℝ} (hfl : Barriers.fMinus eps t ≤ f t) :
    0 < eps⁻¹ - eps ∧ eps⁻¹ - eps ≤ f t := by
  have hm1 : 1 < eps⁻¹ - eps := BarrierEstimates.m_gt_one heps heps'
  exact ⟨by linarith, le_trans ((Barriers.fMinus_min heps).1 t) hfl⟩

/-- Nonnegativity of the curvature field at one angle of `[0, π]`. -/
theorem curvField_nonneg_at {t : ℝ} (ht : t ∈ Icc (0:ℝ) π) (hf : 0 < f t) :
    0 ≤ curvField f t :=
  div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2) hf.le

/-- The intrinsic curvature is uniformly small, from the barrier on `[0, π]`
only. -/
theorem curvField_le_inv_gap_on (heps : 0 < eps) (heps' : eps ≤ 1 / 10)
    (hfl : ∀ t ∈ Icc (0:ℝ) π, Barriers.fMinus eps t ≤ f t)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) π) :
    curvField f t ≤ 1 / (eps⁻¹ - eps) := by
  obtain ⟨hpos, hle⟩ := profile_pos_at heps heps' (hfl t ht)
  have hfpos : 0 < f t := lt_of_lt_of_le hpos hle
  calc curvField f t = Real.sin t / f t := rfl
    _ ≤ 1 / f t := div_le_div_of_nonneg_right (Real.sin_le_one t) hfpos.le
    _ ≤ 1 / (eps⁻¹ - eps) := one_div_le_one_div_of_le hpos hle

/-- The steering pulse obeys the same bound. -/
theorem pulseField_le_inv_gap_on (heps : 0 < eps) (heps' : eps ≤ 1 / 10)
    (hfl : ∀ t ∈ Icc (0:ℝ) π, Barriers.fMinus eps t ≤ f t)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) π) :
    pulseField f t ≤ 1 / (eps⁻¹ - eps) := by
  obtain ⟨hpos, hle⟩ := profile_pos_at heps heps' (hfl t ht)
  have hcurv : 0 ≤ curvField f t :=
    curvField_nonneg_at ht (lt_of_lt_of_le hpos hle)
  have hsqrt : 1 ≤ Real.sqrt (1 + curvField f t ^ 2) := by
    have h1 : (1:ℝ) ≤ 1 + curvField f t ^ 2 := by
      nlinarith [sq_nonneg (curvField f t)]
    calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt h1
  have hsqrtpos : 0 < Real.sqrt (1 + curvField f t ^ 2) := by positivity
  have hle' : pulseField f t ≤ curvField f t := by
    rw [pulseField, div_le_iff₀ hsqrtpos]
    exact le_mul_of_one_le_right hcurv hsqrt
  exact hle'.trans (curvField_le_inv_gap_on heps heps' hfl ht)

/-- `O(ε)` curvature, from the barrier on `[0, π]` only. -/
theorem curvField_le_two_mul_on (heps : 0 < eps) (heps' : eps ≤ 1 / 10)
    (hfl : ∀ t ∈ Icc (0:ℝ) π, Barriers.fMinus eps t ≤ f t)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) π) :
    curvField f t ≤ 2 * eps :=
  (curvField_le_inv_gap_on heps heps' hfl ht).trans
    (WideHairpinSmallness.inv_gap_le_two_mul heps heps')

/-- `O(ε)` steering pulse, from the barrier on `[0, π]` only. -/
theorem pulseField_le_two_mul_on (heps : 0 < eps) (heps' : eps ≤ 1 / 10)
    (hfl : ∀ t ∈ Icc (0:ℝ) π, Barriers.fMinus eps t ≤ f t)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) π) :
    pulseField f t ≤ 2 * eps :=
  (pulseField_le_inv_gap_on heps heps' hfl ht).trans
    (WideHairpinSmallness.inv_gap_le_two_mul heps heps')

/-- **The absolute `O(ε)` derivative bounds of the quantitative package, from
the barrier on `[0, π]` only.**  This is
`PaperHairpinQuantitativeData.Data.wide_pulse_and_derivative_bounds` with the
barrier hypothesis restricted to the angles at which it is actually used. -/
theorem wide_pulse_and_derivative_bounds_on
    {theta x : ℝ → ℝ} {M Delta beta C Ht : ℝ} {P Pp : ℝ → ℝ}
    (d : PaperHairpinQuantitativeData.Data f theta x M Delta beta C Ht P Pp)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 10)
    (hfl : ∀ t ∈ Icc (0:ℝ) π, Barriers.fMinus eps t ≤ f t) :
    (∀ s, pulseField f (theta (x s)) ≤ 2 * eps) ∧
      ∀ j ≤ 4, ∀ s,
        |iteratedDeriv j (fun r => pulseField f (theta (x r))) s|
          ≤ (2 * d.relativeConst j) * eps := by
  have hmem : ∀ s, theta (x s) ∈ Icc (0:ℝ) π := fun s =>
    ⟨(d.angle_mem (x s)).1.le, (d.angle_mem (x s)).2.le⟩
  refine ⟨fun s => pulseField_le_two_mul_on heps heps' hfl (hmem s), ?_⟩
  intro j hj s
  calc |iteratedDeriv j (fun r => pulseField f (theta (x r))) s|
      ≤ d.relativeConst j * pulseField f (theta (x s)) := d.relative j hj s
    _ ≤ d.relativeConst j * (2 * eps) :=
        mul_le_mul_of_nonneg_left
          (pulseField_le_two_mul_on heps heps' hfl (hmem s))
          (d.relativeConst_nonneg j)
    _ = (2 * d.relativeConst j) * eps := by ring

end WideHairpinLocalBounds
