import Mathlib
import UnitTangentIterates.CanonicalConsecutiveBasicAdapters
import UnitTangentIterates.HairpinLowerComparisonInterior

/-!
# Canonical consecutive adapters from interior data

`CanonicalConsecutiveBasicAdapters` supplies the three certificates that the
configured-model capstone consumes on top of `ConsecutiveData`:

* `currentPulse_nonneg`,
* `current_x_deriv`,
* `exists_previous_lower_comparison`,

and each of them asks for a profile that is smooth and positive on *all* of `ℝ`.
The paper assigns no endpoint values, so its profile is only `C^∞` on `(0, π)`.
This file redoes all three from interior data, so that the capstone can be fed
from `DataInterior.exists_consecutiveData_of_interior` without any appeal to a
smooth extension across the endpoints.

Where the original proofs extract `min f` and `max f` over the closed interval
`[0, π]` by compactness, these take the paper's own barrier bounds on `(0, π)`
as hypotheses — which is exactly what `DataInterior` already assumes.

Main results:

* `HairpinPulseIdentity.hasDerivAt_pulseInverse_of_comp`;
* `PaperHairpinQuantitativeData.ConsecutiveData.currentPulse_nonneg_interior`;
* `PaperHairpinQuantitativeData.ConsecutiveData.current_x_deriv_interior`;
* `PaperHairpinQuantitativeData.ConsecutiveData.exists_canonical_lower_comparison_interior`;
* `PaperHairpinQuantitativeData.ConsecutiveData.exists_previous_lower_comparison_interior`.
-/

noncomputable section

open Real Set

open scoped ContDiff

namespace HairpinRelative

/-- Continuity of the curvature along the angle map, from interior regularity
of the profile alone.  The angle map takes values in `(0, π)`, so only the
interior regularity of `curvField f` is ever evaluated. -/
theorem continuous_curv_along_theta {f theta : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u) :
    Continuous fun t => curvField f (theta t) :=
  (HairpinInteriorRegularity.contDiffOn_curvField hf hfpos).continuousOn.comp_continuous
    (Differentiable.continuous fun u => (hderiv u).differentiableAt) hmem

end HairpinRelative

namespace HairpinPulseIdentity

open HairpinRelative

/-- **The derivative of the front-arclength inverse, from interior data.**  This
is `hasDerivAt_pulseInverse` with global smoothness and positivity of the
profile replaced by continuity of the curvature along the angle. -/
theorem hasDerivAt_pulseInverse_of_comp {f theta x : ℝ → ℝ}
    (hkc : Continuous fun t => curvField f (theta t))
    (hxinv : ∀ s, frontArclength f theta (x s) = s) (s : ℝ) :
    HasDerivAt x (Real.sqrt (1 - pulseField f (theta (x s)) ^ 2)) s := by
  have h := ArclengthInverse.hasDerivAt_of_rightInverse (c := 1) one_pos
    (HairpinTailsInterior.hasDerivAt_frontArclength_of_comp hkc)
    (fun u => one_le_sqrt_one_add_curv_sq f (theta u)) hxinv s
  rwa [← sqrt_one_sub_pulseField_sq] at h

end HairpinPulseIdentity

namespace PaperHairpinQuantitativeData.ConsecutiveData

open HairpinRelative

variable {f theta x g gp yp : ℝ → ℝ} {M Delta beta C Ht : ℝ} {P Pp : ℝ → ℝ}

/-- The steering pulse is nonnegative, from interior positivity of the
profile. -/
theorem currentPulse_nonneg_interior
    (c : ConsecutiveData f theta x g gp yp M Delta beta C Ht P Pp)
    (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t) :
    ∀ s, 0 ≤ currentPulse f theta x s := fun s =>
  pulseField_nonneg_interior hfpos (c.quantitative.angle_mem (x s))

/-- The front coordinate solves `x' = √(1 − y²)`, from interior data. -/
theorem current_x_deriv_interior
    (c : ConsecutiveData f theta x g gp yp M Delta beta C Ht P Pp)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t) :
    ∀ s, HasDerivAt x (Real.sqrt (1 - currentPulse f theta x s ^ 2)) s := by
  intro s
  have hkc := continuous_curv_along_theta hf hfpos
    c.quantitative.angle_mem c.quantitative.angle_deriv
  simpa [currentPulse] using
    HairpinPulseIdentity.hasDerivAt_pulseInverse_of_comp hkc
      c.quantitative.inverse_value s

/-- **The lower comparison for the canonical coordinates, from interior data.**
Unlike `exists_canonical_lower_comparison`, the coordinates are not
reconstructed and then identified: they are the ones carried by the data. -/
theorem exists_canonical_lower_comparison_interior {A Mt D1 : ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta C Ht P Pp)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hMt : 0 < Mt) (hD1 : 0 ≤ D1)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / Mt))
    (hrelK : ∀ u,
      |deriv (fun r => curvField f (theta r)) u| ≤ D1 * curvField f (theta u)) :
    ∃ b0 : ℝ, 0 < b0 ∧ ∀ s,
      b0 * currentPulse f theta x s ≤ curvField f (theta s) :=
  hairpin_curv_ge_pulse_interior hf hfpos c.quantitative.angle_mem
    c.quantitative.angle_deriv c.quantitative.inverse_value hdecay hMt hD1 hrelK

/-- **The rear-coordinate lower comparison, from interior data.**  The
compactness extraction of `min f` and `max f` over `[0, π]` in
`exists_previous_lower_comparison` is replaced by the paper's barrier bounds
along the angle map. -/
theorem exists_previous_lower_comparison_interior {A Mt D1 m Am : ℝ}
    (c : ConsecutiveData f theta x g gp yp M Delta beta C Ht P Pp)
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hMt : 0 < Mt) (hD1 : 0 ≤ D1)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / Mt))
    (hrelK : ∀ u,
      |deriv (fun r => curvField f (theta r)) u| ≤ D1 * curvField f (theta u))
    (hm : 0 < m) (hmA : m ≤ Am)
    (hl : ∀ t, m ≤ f (theta t)) (hu : ∀ t, f (theta t) ≤ Am) :
    ∃ b1 : ℝ, 0 < b1 ∧ ∀ s,
      b1 * previousPulse f theta x g s ≤
        ModelOrbitDefect.hairpinCurvature (previousPulse f theta x g)
          (previousPulseDeriv f theta g yp) s := by
  obtain ⟨b0, hb0, hlower⟩ :=
    c.exists_canonical_lower_comparison_interior hf hfpos hMt hD1 hdecay hrelK
  set q := phase f theta g with hq
  set Ch := (Am / m) * Real.exp (|q| / m) with hCh_def
  have hA : 0 < Am := lt_of_lt_of_le hm hmA
  have hCh : 0 < Ch := mul_pos (div_pos hA hm) (Real.exp_pos _)
  have hKshift : ∀ s,
      curvField f (theta (s - q)) ≤ Ch * curvField f (theta s) := by
    intro s
    exact HairpinTails.curvField_shift_harnack_along_theta hm hmA
      c.quantitative.angle_mem c.quantitative.angle_deriv hl hu
      (abs_nonneg q) (by simp [hq])
  have hid : ∀ s, curvField f (theta s) =
      ModelOrbitDefect.hairpinCurvature (previousPulse f theta x g)
        (previousPulseDeriv f theta g yp) s := by
    intro s
    simpa [previousPulse, previousPulseDeriv, phase,
      ModelOrbitDefect.hairpinCurvature] using
        (CanonicalTranslatorLocalPhase.front_curvature_identity_shifted
          d d.x_zero c.pulse_deriv s)
  refine ⟨b0 / Ch, div_pos hb0 hCh, ?_⟩
  intro s
  have hlo := hlower (s - q)
  have hchain : b0 * previousPulse f theta x g s ≤ Ch * curvField f (theta s) :=
    hlo.trans (hKshift s)
  rw [← hid s, div_mul_eq_mul_div, div_le_iff₀ hCh]
  linarith [hchain]

end PaperHairpinQuantitativeData.ConsecutiveData
