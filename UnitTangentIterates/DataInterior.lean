import Mathlib
import UnitTangentIterates.HairpinMassInterior
import UnitTangentIterates.PaperHairpinQuantitativeData

/-!
# The profile-side package from interior data

`PaperHairpinQuantitativeData.exists_data` builds `Data` from a profile that is
smooth and positive on the **whole line**.  The paper builds its profile only on
`(0, π)`, and says so explicitly.

This file closes that gap.  Every field of `Data` is produced here from

* `ContDiffOn ℝ ∞ f (Ioo 0 π)` — the regularity the paper proves;
* a positive lower bound for `f` on `(0, π)` — the paper's barrier bound;
* the hairpin coordinates, as produced by
  `HairpinInteriorRegularity.exists_hairpin_coordinates_interior`;
* the order-zero curvature tail, from `HairpinArclength.curvature_decay_arclength`
  (which is already endpoint-free);
* and the relative derivative bounds at the orders `j ≤ 4` that `Data` records.

The last item is the one genuinely extra input, and that is faithful to the
paper: interior smoothness plus the barriers do **not** imply the relative
bounds (`f(t) = 2 + t³ sin(1/t²)` is a counterexample).  The paper derives them
from the *translator equation*, via the bounded-shift Harnack estimate — extra
structure, not extra regularity — and the endpoint-free Lean route to them is
`HairpinPulse.abs_curvatureDeriv_le_of_shift_harnack` (orders 1, 2) together
with `PulseIteratedDeriv` (orders 3, 4).

Given them, the exponential tails at those orders come for free, by
`HairpinTailsInterior.abs_iteratedDeriv_pulse_decay_of_relative`.

Main result: `data_of_interior`.
-/

noncomputable section

open Set Real MeasureTheory HairpinRelative
open scoped ContDiff

namespace PaperHairpinQuantitativeData

/-- **The profile-side quantitative package, from interior data.**  This is
`exists_data` with the global profile hypothesis `ContDiff ℝ ∞ f` replaced by
the regularity the paper actually proves, `f ∈ C^∞(0,π)`, together with the
barrier lower bound and the relative derivative bounds the paper obtains from
the translator equation. -/
def data_of_interior {f : ℝ → ℝ} {m A M : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hm : 0 < m)
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t)
    {theta x : ℝ → ℝ}
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hval : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s)
    (hw : ∀ s, HasDerivAt (fun r => theta (x r)) (pulseField f (theta (x s))) s)
    (hsm : StrictMono theta)
    (hsurj : ∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta u = z)
    (hA : 0 ≤ A) (hM : 0 < M)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (relativeConst : ℕ → ℝ) (hrc0 : ∀ j, 0 ≤ relativeConst j)
    (hrel : ∀ j ≤ 4, ∀ s,
      |iteratedDeriv j (fun r => pulseField f (theta (x r))) s|
        ≤ relativeConst j * pulseField f (theta (x s))) :
    Data f theta x M 0 0 0 0 (fun _ => 0) (fun _ => 0) := by
  have hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  have hthetac : Continuous theta :=
    Differentiable.continuous fun u => (hderiv u).differentiableAt
  have hcont : Continuous fun u => curvField f (theta u) :=
    (HairpinInteriorRegularity.contDiffOn_curvField hf hfpos).continuousOn.comp_continuous
      hthetac hmem
  have hnn : ∀ u, 0 ≤ curvField f (theta u) := fun u =>
    div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (hmem u).1.le (hmem u).2.le)
      (hfpos _ (hmem u)).le
  have hyC := (HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates hf hfpos
    hmem hderiv hw).2.2
  have hycont : Continuous fun s => pulseField f (theta (x s)) := (hyC 0).continuous
  have hle : ∀ u, pulseField f (theta u) ≤ curvField f (theta u) := fun u =>
    HairpinMassInterior.pulseField_le_curvField_at (hnn u)
  have hynn : ∀ s, 0 ≤ pulseField f (theta (x s)) := fun s => by
    rw [pulseField]
    exact div_nonneg (hnn (x s)) (Real.sqrt_nonneg _)
  -- the order-zero tail
  have hy0 : ∀ s, pulseField f (theta (x s))
      ≤ A * Real.exp (A ^ 2 / 2) * Real.exp (-|s| / M) := fun s =>
    HairpinTailsInterior.pulse_decay_of_comp hcont hnn hle hdecay hA hM hxinv s
  have hyabs : ∀ s, |pulseField f (theta (x s))|
      ≤ (A * Real.exp (A ^ 2 / 2)) * Real.exp (-(1 / M) * |s|) := by
    intro s
    rw [abs_of_nonneg (hynn s)]
    have h := hy0 s
    rwa [show -|s| / M = -(1 / M) * |s| by ring] at h
  have halpha : (0:ℝ) < 1 / M := by positivity
  have hA' : 0 ≤ A * Real.exp (A ^ 2 / 2) := by positivity
  exact
    { M_pos := hM
      angle_mem := hmem
      angle_value := hval
      angle_deriv := hderiv
      inverse_value := hxinv
      state_deriv := hw
      smooth_pulse := hyC
      decayConst := fun j => relativeConst j * (A * Real.exp (A ^ 2 / 2))
      decayConst_nonneg := fun j => mul_nonneg (hrc0 j) (by positivity)
      decay := fun j hj s =>
        HairpinTailsInterior.abs_iteratedDeriv_pulse_decay_of_relative
          hy0 (hrc0 j) (hrel j hj) s
      relativeConst := relativeConst
      relativeConst_nonneg := hrc0
      relative := hrel
      pulse_integrable :=
        FrontPeriodizationIntegral.integrable_of_exp_bound' halpha hycont hyabs
      firstMoment_integrable :=
        integrable_abs_mul_of_exp_bound halpha hA' hycont hyabs
      mass := HairpinMassInterior.pulse_mass_of_comp hcont hnn hmem hsm hsurj
        hderiv hdecay hA hM hxinv hycont }

/-- **The consecutive package itself, from interior data.**  The auxiliary
pulse derivative is not chosen: it is `y'` for the pulse the data already
carries.  `exists_consecutiveData_of_interior` is the existential form. -/
def consecutiveData_of_interior {f g gp : ℝ → ℝ} {m A M : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hm : 0 < m)
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t)
    {theta x : ℝ → ℝ}
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hval : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s)
    (hw : ∀ s, HasDerivAt (fun r => theta (x r)) (pulseField f (theta (x s))) s)
    (hsm : StrictMono theta)
    (hsurj : ∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta u = z)
    (hA : 0 ≤ A) (hM : 0 < M)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (relativeConst : ℕ → ℝ) (hrc0 : ∀ j, 0 ≤ relativeConst j)
    (hrel : ∀ j ≤ 4, ∀ s,
      |iteratedDeriv j (fun r => pulseField f (theta (x r))) s|
        ≤ relativeConst j * pulseField f (theta (x s)))
    (translator : TranslatorData f g gp) :
    ConsecutiveData f theta x g gp
      (iteratedDeriv 1 (fun r => pulseField f (theta (x r)))) M 0 0 0 0
      (fun _ => 0) (fun _ => 0) := by
  have hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  have hyC := (HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates hf hfpos
    hmem hderiv hw).2.2
  refine
    { quantitative := data_of_interior hf hm hlow hmem hval hderiv hxinv hw hsm
        hsurj hA hM hdecay relativeConst hrc0 hrel
      translator := translator
      pulse_deriv := ?_ }
  intro s
  have hd := (hyC 1).differentiable (by norm_num)
  simpa [iteratedDeriv_one] using (hd s).hasDerivAt

/-- **The consecutive quantitative package, from interior data.**  This is
`ConsecutiveData.exists_of_smooth_extension` with the extension step removed
entirely: no smoothness of the profile on a neighbourhood of `[0,π]`, and hence
no appeal to `ProfileExtension`.  The inputs are exactly what the paper's
theorem *Translating hairpin* and lemma *Hairpin pulse estimates* provide —
`f ∈ C^∞(0,π)`, the barrier lower bound, the hairpin coordinates, the
order-zero curvature tail, the relative bounds at `j ≤ 4` — together with the
translator relations, which the paper's operator supplies.

This is the constructor the model-orbit defect chain needs. -/
theorem exists_consecutiveData_of_interior {f g gp : ℝ → ℝ} {m A M : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hm : 0 < m)
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t)
    {theta x : ℝ → ℝ}
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hval : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s)
    (hw : ∀ s, HasDerivAt (fun r => theta (x r)) (pulseField f (theta (x s))) s)
    (hsm : StrictMono theta)
    (hsurj : ∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta u = z)
    (hA : 0 ≤ A) (hM : 0 < M)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (relativeConst : ℕ → ℝ) (hrc0 : ∀ j, 0 ≤ relativeConst j)
    (hrel : ∀ j ≤ 4, ∀ s,
      |iteratedDeriv j (fun r => pulseField f (theta (x r))) s|
        ≤ relativeConst j * pulseField f (theta (x s)))
    (translator : TranslatorData f g gp) :
    ∃ yp : ℝ → ℝ,
      Nonempty (ConsecutiveData f theta x g gp yp M 0 0 0 0
        (fun _ => 0) (fun _ => 0)) :=
  ⟨_, ⟨consecutiveData_of_interior hf hm hlow hmem hval hderiv hxinv hw hsm hsurj hA hM hdecay relativeConst hrc0 hrel translator⟩⟩

end PaperHairpinQuantitativeData
