import Mathlib
import UnitTangentIterates.FrontPeriodizationHairpin

/-!
# The steering pulse of the hairpin with its second derivative

`FrontPeriodizationHairpin.exists_hairpin_pulse_data` packages the steering
pulse `y = sin δ` of the hairpin of *A Noncircular Oval with Convex
Unit-Tangent Iterates* with its first derivative and every bound the front
periodization error consumes.  The estimates for the *marked path
pseudodistance* need one derivative more: the periodized front curvature
`K_P = Y_P + G(Y_P)Y_P'` is `C¹` with a uniform derivative bound only when the
pulse is `C²` with `|y''| ≤ D₂ y` and `|y''| ≤ Ce^{−α|s|}`
(`PeriodizedCurvatureDeriv.lean`).

This file supplies that second-order data.  Nothing new is needed: the lemma
*Hairpin pulse estimates* already gives the exponential decay
(`HairpinPulseDecay.hairpin_pulse_exponential_decay`) and the relative bounds
(`HairpinRelativeDerivatives.abs_iteratedDeriv_pulse_le`) at **every** order,
and `RelativeDerivatives.iteratedDeriv_flow` exhibits each derivative of the
pulse as a function of the state, so that the second derivative is available as
an explicit function rather than as an iterated `deriv`.
-/

noncomputable section

open Real Set MeasureTheory

open scoped ContDiff

namespace HairpinPulseSecondData

open FrontPeriodization HairpinRelative PerimeterHairpinPulse FrontPeriodizationHairpin

variable {f : ℝ → ℝ}

/-- **The steering pulse of the hairpin, with two derivatives and all their
bounds.**  For a profile `f` smooth and positive on the line, the hairpin has a
tangent-angle parametrization `θ` and a front-arclength parametrization `x`
whose steering pulse `y = G₂(θ(x(·))) = sin δ` is nonnegative, bounded by
`b = 1/√(1+m²) < 1` and by `Ce^{−α|·|}`, and is twice differentiable with
continuous derivatives `y'`, `y''` obeying the same exponential bound and the
relative bounds `|y'| ≤ D y`, `|y''| ≤ D y`. -/
theorem exists_hairpin_pulse_second_data (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ (theta x yp ypp : ℝ → ℝ) (alpha C D b : ℝ),
      0 < alpha ∧ 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ b ∧ b < 1 ∧
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, HasDerivAt (fun r => theta (x r)) (pulseField f (theta (x s))) s) ∧
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
      (∀ s, |ypp s| ≤ D * pulseField f (theta (x s))) := by
  obtain ⟨M, theta, x, hM, hmem, hval, hderiv, hxinv, hxderiv, -, hdec⟩ :=
    hairpin_pulse_exponential_decay hf hfpos
  obtain ⟨C₀, hC₀0, hC₀b⟩ := hdec 0
  obtain ⟨C₁, hC₁0, hC₁b⟩ := hdec 1
  obtain ⟨C₂, hC₂0, hC₂b⟩ := hdec 2
  set C : ℝ := max (max C₀ C₁) C₂ with hCdef
  have hC0 : 0 ≤ C := le_trans hC₀0 (le_trans (le_max_left _ _) (le_max_left _ _))
  -- the sup bound of the pulse
  have hcontf : Continuous f := hf.continuous
  have hne : (Icc (0:ℝ) π).Nonempty := ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩
  obtain ⟨t₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Icc (0:ℝ) π) hne hcontf.continuousOn
  have hm : 0 < f t₀ := hfpos t₀
  have hlow : ∀ t ∈ Icc (0:ℝ) π, f t₀ ≤ f t := fun t ht => hmin ht
  set b : ℝ := 1 / Real.sqrt (1 + f t₀ ^ 2) with hb
  have hb0 : 0 ≤ b := by positivity
  have hb1 : b < 1 := inv_sqrt_one_add_sq_lt_one hm
  -- the state of the flow and the derivative functions
  have hmem' : ∀ u, theta u ∈ Icc (0:ℝ) π := fun u => ⟨(hmem u).1.le, (hmem u).2.le⟩
  set W : ℝ → ℝ := fun s => theta (x s) with hW
  have hpc : ContDiff ℝ ∞ (pulseField f) := contDiff_pulseField hf hfpos
  set yp : ℝ → ℝ :=
    fun s => pulseField f (W s) * RelativeDerivatives.coeff (pulseField f) 1 (W s) with hypdef
  set ypp : ℝ → ℝ :=
    fun s => pulseField f (W s) * RelativeDerivatives.coeff (pulseField f) 2 (W s) with hyppdef
  have hy0 : ∀ s, 0 ≤ pulseField f (W s) := fun s => pulseField_nonneg hfpos (hmem' (x s))
  have hsup : ∀ s, pulseField f (W s) ≤ b := fun s =>
    pulseField_le_of_lower_bound hm hfpos hlow (hmem' (x s))
  -- continuity
  have hWcont : Continuous W :=
    continuous_iff_continuousAt.2 fun s => (hxderiv s).continuousAt
  have hycont : Continuous fun s => pulseField f (W s) := hpc.continuous.comp hWcont
  have hypc : Continuous yp :=
    (hpc.continuous.mul (RelativeDerivatives.contDiff_coeff hpc 1).continuous).comp hWcont
  have hyppc : Continuous ypp :=
    (hpc.continuous.mul (RelativeDerivatives.contDiff_coeff hpc 2).continuous).comp hWcont
  -- the derivatives
  have hy : ∀ s, HasDerivAt (fun r => pulseField f (W r)) (yp s) s := by
    intro s
    have h := RelativeDerivatives.hasDerivAt_state hpc hxderiv 0 s
    simpa [hypdef, RelativeDerivatives.coeff] using h
  have hy2 : ∀ s, HasDerivAt yp (ypp s) s := fun s =>
    RelativeDerivatives.hasDerivAt_state hpc hxderiv 1 s
  -- the iterated derivatives, as functions of the state
  have hit1 : iteratedDeriv 1 (fun s => pulseField f (W s)) = yp :=
    RelativeDerivatives.iteratedDeriv_flow hpc hxderiv 1
  have hit2 : iteratedDeriv 2 (fun s => pulseField f (W s)) = ypp :=
    RelativeDerivatives.iteratedDeriv_flow hpc hxderiv 2
  -- the exponential bounds
  have hrw : ∀ s : ℝ, -|s| / M = -(1 / M) * |s| := fun s => by field_simp
  have halpha : 0 < 1 / M := by positivity
  have hyb : ∀ s, pulseField f (W s) ≤ C * Real.exp (-(1 / M) * |s|) := by
    intro s
    have h := hC₀b s
    rw [iteratedDeriv_zero, hrw s] at h
    have h2 : C₀ * Real.exp (-(1 / M) * |s|) ≤ C * Real.exp (-(1 / M) * |s|) :=
      mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _))
        (Real.exp_pos _).le
    exact le_trans (le_trans (le_abs_self _) h) h2
  have hypb : ∀ s, |yp s| ≤ C * Real.exp (-(1 / M) * |s|) := by
    intro s
    have h := hC₁b s
    rw [hit1, hrw s] at h
    have h2 : C₁ * Real.exp (-(1 / M) * |s|) ≤ C * Real.exp (-(1 / M) * |s|) :=
      mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _))
        (Real.exp_pos _).le
    exact le_trans h h2
  have hyppb : ∀ s, |ypp s| ≤ C * Real.exp (-(1 / M) * |s|) := by
    intro s
    have h := hC₂b s
    rw [hit2, hrw s] at h
    have h2 : C₂ * Real.exp (-(1 / M) * |s|) ≤ C * Real.exp (-(1 / M) * |s|) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
    exact le_trans h h2
  -- the relative bounds
  obtain ⟨D₁, hD₁0, hD₁b⟩ :=
    abs_iteratedDeriv_pulse_le hf hfpos (w := W) (fun s => hmem' (x s)) hxderiv 1
  obtain ⟨D₂, hD₂0, hD₂b⟩ :=
    abs_iteratedDeriv_pulse_le hf hfpos (w := W) (fun s => hmem' (x s)) hxderiv 2
  set D : ℝ := max D₁ D₂ with hDdef
  have hD0 : 0 ≤ D := le_trans hD₁0 (le_max_left _ _)
  have hrel1 : ∀ s, |yp s| ≤ D * pulseField f (W s) := by
    intro s
    have h := hD₁b s
    rw [hit1] at h
    exact le_trans h (mul_le_mul_of_nonneg_right (le_max_left _ _) (hy0 s))
  have hrel2 : ∀ s, |ypp s| ≤ D * pulseField f (W s) := by
    intro s
    have h := hD₂b s
    rw [hit2] at h
    exact le_trans h (mul_le_mul_of_nonneg_right (le_max_right _ _) (hy0 s))
  exact ⟨theta, x, yp, ypp, 1 / M, C, D, b, halpha, hC0, hD0, hb0, hb1, hmem, hval, hderiv,
    hxinv, hxderiv, hycont, hy0, hyb, hsup, hy, hypc, hypb, hrel1, hy2, hyppc, hyppb, hrel2⟩

end HairpinPulseSecondData
