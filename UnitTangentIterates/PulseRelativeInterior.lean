import UnitTangentIterates.RelativeDerivativesInterior
import UnitTangentIterates.HairpinInteriorRegularity
import UnitTangentIterates.HairpinPulseBarrier
import UnitTangentIterates.HairpinLowerComparisonInterior

/-!
# The relative pulse bounds, from interior data

`HairpinRelative.abs_iteratedDeriv_pulse_le` proves the paper's
`eq:relative-y-derivatives`

```
  |y^{(j)}(s)| ≤ D_j y(s)
```

from a profile smooth and positive on all of `ℝ`, by bounding the flow
coefficient of the pulse field over the **closed** interval `[0, π]`.

The paper assigns no endpoint values, so that bound is not available.  Using the
open-set flow machinery of `RelativeDerivativesInterior`, this file reduces the
relative bounds to exactly what compactness had been supplying, and nothing
more: a bound on the flow coefficient `L_j` of `pulseField f` over `(0, π)`.

The reduction matters because the resulting hypothesis is a statement about the
**profile alone** — no flow, no coordinates.  `coeff (pulseField f) j` is a
polynomial in `pulseField f` and its first `j` derivatives, so bounding it on
`(0, π)` is a question about `f, f', …, f^{(j)}` there, which the translator ODE
and the two-sided barriers are the natural source for.

Main results:

* `HairpinRelative.contDiffOn_pulseField`;
* `HairpinRelative.abs_iteratedDeriv_pulse_le_of_coeff_bound`.
-/

noncomputable section

open Set Real

open scoped ContDiff

namespace HairpinRelative

variable {f : ℝ → ℝ}

/-- The pulse field is smooth on the interior. -/
theorem contDiffOn_pulseField (hf : ContDiffOn ℝ ∞ f (Ioo 0 π))
    (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t) :
    ContDiffOn ℝ ∞ (pulseField f) (Ioo 0 π) := by
  have hG := HairpinInteriorRegularity.contDiffOn_curvField hf hfpos
  intro t ht
  have hGa : ContDiffAt ℝ ∞ (curvField f) t :=
    hG.contDiffAt (isOpen_Ioo.mem_nhds ht)
  have hden : ContDiffAt ℝ ∞ (fun r => Real.sqrt (1 + curvField f r ^ 2)) t := by
    refine ContDiffAt.sqrt ?_ ?_
    · exact contDiffAt_const.add (hGa.pow 2)
    · positivity
  exact (hGa.div hden (sqrt_one_add_sq_pos _).ne').contDiffWithinAt

/-- **The relative pulse bounds, from a bound on the flow coefficient.**  This
is `abs_iteratedDeriv_pulse_le` with the compactness extraction over `[0, π]`
replaced by the hypothesis it was producing, now over `(0, π)`. -/
theorem abs_iteratedDeriv_pulse_le_of_coeff_bound
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    {w : ℝ → ℝ} (hmem : ∀ s, w s ∈ Ioo 0 π)
    (hderiv : ∀ s, HasDerivAt w (pulseField f (w s)) s)
    {j : ℕ} {D : ℝ}
    (hbd : ∀ t ∈ Ioo (0:ℝ) π,
      |RelativeDerivatives.coeff (pulseField f) j t| ≤ D) :
    ∀ s, |iteratedDeriv j (fun s => pulseField f (w s)) s|
      ≤ D * pulseField f (w s) :=
  RelativeDerivatives.abs_iteratedDeriv_le_of_coeff_bound isOpen_Ioo
    (contDiffOn_pulseField hf hfpos) hmem hderiv
    (fun s => pulseField_nonneg_interior hfpos (hmem s)) hbd

/-- The package the interior route consumes: relative bounds at every order
`j ≤ 4`, from coefficient bounds at those orders. -/
theorem abs_iteratedDeriv_pulse_le_four
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    {theta x : ℝ → ℝ} (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hw : ∀ s, HasDerivAt (fun r => theta (x r)) (pulseField f (theta (x s))) s)
    {relativeConst : ℕ → ℝ}
    (hbd : ∀ j ≤ 4, ∀ t ∈ Ioo (0:ℝ) π,
      |RelativeDerivatives.coeff (pulseField f) j t| ≤ relativeConst j) :
    ∀ j ≤ 4, ∀ s,
      |iteratedDeriv j (fun r => pulseField f (theta (x r))) s|
        ≤ relativeConst j * pulseField f (theta (x s)) := by
  intro j hj
  exact abs_iteratedDeriv_pulse_le_of_coeff_bound hf hfpos
    (fun s => hmem (x s)) hw (hbd j hj)

end HairpinRelative
