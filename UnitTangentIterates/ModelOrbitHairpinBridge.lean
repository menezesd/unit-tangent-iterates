import Mathlib
import UnitTangentIterates.HairpinPulseSecondData
import UnitTangentIterates.HairpinPulseIdentity
import UnitTangentIterates.ModelOrbitDefect

/-!
# Hairpin data in the coordinates used by the model-orbit defect

`ModelOrbitDefect.Config` uses the steering pulse in front arclength and the
curvature of the isolated hairpin in its own arclength.  The two prior
hairpin packages supplied the necessary facts separately.  This file puts
them on the same witnesses: the pulse has two controlled derivatives, while
the inverse front arclength has the rear speed and the exact steering
identity.  It is the analytic/geometric core of `Config.hid`.

The remaining `Config` fields are genuinely quantitative: a phase alignment
with `hairpinCurvature yu yu'`, cell-period estimates, and smallness of the
relative derivative constants for a wide profile.
-/

noncomputable section

open Real Set MeasureTheory

open scoped ContDiff

namespace ModelOrbitHairpinBridge

open HairpinRelative HairpinPulseIdentity HairpinPulseSecondData

variable {f : ℝ → ℝ}

/-- The paper's hairpin supplies, on one common choice of coordinates, the
two-derivative steering-pulse data and the exact relation between that pulse
and the isolated curvature in rear own arclength. -/
theorem exists_second_steering_data (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ (theta x yp ypp : ℝ → ℝ) (alpha C D b : ℝ),
      0 < alpha ∧ 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ b ∧ b < 1 ∧
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      Continuous (fun s => pulseField f (theta (x s))) ∧
      (∀ s, 0 ≤ pulseField f (theta (x s))) ∧
      (∀ s, pulseField f (theta (x s)) ≤ C * Real.exp (-alpha * |s|)) ∧
      (∀ s, pulseField f (theta (x s)) ≤ b) ∧
      (∀ s, HasDerivAt (fun r => pulseField f (theta (x r))) (yp s) s) ∧
      Continuous yp ∧
      (∀ s, |yp s| ≤ C * Real.exp (-alpha * |s|)) ∧
      (∀ s, |yp s| ≤ D * pulseField f (theta (x s))) ∧
      (∀ s, HasDerivAt yp (ypp s) s) ∧
      Continuous ypp ∧
      (∀ s, |ypp s| ≤ C * Real.exp (-alpha * |s|)) ∧
      (∀ s, |ypp s| ≤ D * pulseField f (theta (x s))) ∧
      x 0 = 0 ∧
      (∀ s, HasDerivAt x (Real.sqrt (1 - pulseField f (theta (x s)) ^ 2)) s) ∧
      (∀ s, pulseField f (theta (x s)) =
        Real.sqrt (1 - pulseField f (theta (x s)) ^ 2) * curvField f (theta (x s))) := by
  obtain ⟨theta, x, yp, ypp, alpha, C, D, b, halpha, hC, hD, hb0, hb1, hmem, -, hderiv,
    hxinv, -, hycont, hy0, hyb, hsup, hy, hypc, hypb, hrel, hyppderiv, hyppc, hyppb, hrel2⟩ :=
    exists_hairpin_pulse_second_data hf hfpos
  exact ⟨theta, x, yp, ypp, alpha, C, D, b, halpha, hC, hD, hb0, hb1, hmem, hderiv, hxinv,
    hycont, hy0, hyb, hsup, hy, hypc, hypb, hrel, hyppderiv, hyppc, hyppb, hrel2,
    pulseInverse_zero hf hfpos hderiv hxinv,
    fun s => hasDerivAt_pulseInverse hf hfpos hderiv hxinv s,
    fun s => pulseField_eq_speed_mul_curvField f (theta (x s))⟩

/-- A horizontal coordinate with the rear-arclength speed is the model rear
arclength when both coordinates vanish at the origin. -/
theorem eq_modelRearArclength
    {y x : ℝ → ℝ}
    (hy : Continuous y)
    (hx0 : x 0 = 0)
    (hx : ∀ s, HasDerivAt x (Real.sqrt (1 - y s ^ 2)) s) :
    x = ModelOrbitDefect.modelRearArclength y := by
  have hrear : ∀ s, HasDerivAt (ModelOrbitDefect.modelRearArclength y)
      (Real.sqrt (1 - y s ^ 2)) s := by
    intro s
    have h := RearTrack.hasDerivAt_rearArclength
      (δ := ModelOrbitDefect.modelSteering y)
      (ModelOrbitDefect.continuous_modelSteering hy) s
    simpa [ModelOrbitDefect.modelRearArclength,
      ModelOrbitDefect.cos_modelSteering] using h
  have hdiff : Differentiable ℝ
      (fun s => x s - ModelOrbitDefect.modelRearArclength y s) :=
    fun t => ((hx t).sub (hrear t)).differentiableAt
  have hzero : ∀ s, HasDerivAt
      (fun s => x s - ModelOrbitDefect.modelRearArclength y s) 0 s := by
    intro s
    convert (hx s).sub (hrear s) using 1 <;> ring
  funext s
  have hconst := (is_const_of_deriv_eq_zero hdiff
    (fun t => (hzero t).deriv) 0 s).symm
  have hrear0 : ModelOrbitDefect.modelRearArclength y 0 = 0 := by
    simp [ModelOrbitDefect.modelRearArclength, RearTrack.rearArclength]
  rw [hx0, hrear0] at hconst
  linarith

/-- Transport a curvature identity from a normalized horizontal hairpin
coordinate to the model rear-arclength coordinate used by `ModelOrbitDefect`.
This is the coordinate part of the paper's common-phase convention. -/
theorem phase_identity_modelRear
    {y x K : ℝ → ℝ}
    (hy : Continuous y)
    (hx0 : x 0 = 0)
    (hx : ∀ s, HasDerivAt x (Real.sqrt (1 - y s ^ 2)) s)
    (hK : ∀ s, y s = Real.sqrt (1 - y s ^ 2) * K (x s)) :
    ∀ s, y s = Real.sqrt (1 - y s ^ 2) * K (ModelOrbitDefect.modelRearArclength y s) := by
  have hxeq := eq_modelRearArclength hy hx0 hx
  intro s
  rw [← hxeq]
  exact hK s

/-- The exact hairpin pulse/curvature identity from
`exists_second_steering_data`, expressed in the rear coordinate of the model
configuration. -/
theorem pulse_identity_modelRear
    {f theta x : ℝ → ℝ}
    (hy : Continuous (fun s => pulseField f (theta (x s))))
    (hx0 : x 0 = 0)
    (hx : ∀ s, HasDerivAt x
      (Real.sqrt (1 - pulseField f (theta (x s)) ^ 2)) s)
    (hid : ∀ s, pulseField f (theta (x s)) =
      Real.sqrt (1 - pulseField f (theta (x s)) ^ 2) * curvField f (theta (x s))) :
    ∀ s, pulseField f (theta (x s)) =
      Real.sqrt (1 - pulseField f (theta (x s)) ^ 2) *
        curvField f (theta (ModelOrbitDefect.modelRearArclength
          (fun r => pulseField f (theta (x r))) s)) := by
  exact phase_identity_modelRear (K := fun r => curvField f (theta r)) hy hx0 hx hid

end ModelOrbitHairpinBridge
