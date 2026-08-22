import Mathlib
import UnitTangentIterates.PeriodizedTurning
import UnitTangentIterates.FrontPeriodizationHairpin
import UnitTangentIterates.HairpinPulseMass

/-!
# The total turning of the model front, for the hairpin of the paper

`PeriodizedTurning.integral_frontCurv_eq_pi` computes the total turning of the
periodized front curvature `K_P = Y_P + G(Y_P)Y_P'` over one period, from three
properties of the pulse: exponential decay of the pulse and of its derivative,
nonnegativity, and a periodization staying below `a < 1`; the answer is the
total mass `∫_ℝ y` of the pulse.

This file checks all of that for the **steering pulse of the paper's own
hairpin**, `y = sin δ = G₂(θ(x(·)))`, so that the model fronts of *A Noncircular
Oval with Convex Unit-Tangent Iterates* really do have total turning `π` over
one period — the hypothesis under which such a curvature is the curvature of a
closed convex curve, used throughout the two-cap and interpolation statements.

The pulse data and all its bounds come from
`FrontPeriodizationHairpin.exists_hairpin_pulse_data`, the periodization bound
from `PerimeterHairpinPulse.periodization_le_mid` (valid beyond an explicit
threshold in the period), and the mass `∫_ℝ y = π` from
`HairpinPulseMass.hairpin_pulse_mass`.  The last of these produces its own
parametrization, so it is first transferred to any parametrization satisfying
the same two characterizing equations (`hairpin_pulse_mass_of_data`): the
tangent-angle map is determined by `S(θ(u)) = u` because the hairpin arclength
is strictly monotone, and the front-arclength inverse is then determined too.

Main results:

* `theta_eq_of_arclength` — the tangent-angle parametrization of the hairpin is
  unique;
* `hairpin_pulse_mass_of_data` — hence the steering mass `∫_ℝ y = π` holds for
  any such parametrization;
* `hairpin_frontCurv_turning` — **for a profile smooth and positive on the
  line, and for every period beyond an explicit threshold, the periodized front
  curvature of the hairpin pulse has total turning `π` over one period**.
-/

noncomputable section

open Real Set MeasureTheory Function

open scoped ContDiff

namespace PeriodizedTurningHairpin

open FrontPeriodization HairpinRelative PerimeterHairpinPulse
  FrontPeriodizationHairpin

variable {f : ℝ → ℝ}

/-! ### Uniqueness of the parametrizations -/

/-- **The tangent-angle parametrization of the hairpin is unique.**  Two maps
with values in `(0, π)` inverting the hairpin arclength agree, the arclength
being strictly monotone. -/
theorem theta_eq_of_arclength (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {theta1 theta2 : ℝ → ℝ}
    (h1mem : ∀ u, theta1 u ∈ Ioo (0:ℝ) π)
    (h1val : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta1 u) = u)
    (h2mem : ∀ u, theta2 u ∈ Ioo (0:ℝ) π)
    (h2val : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta2 u) = u) :
    theta1 = theta2 := by
  have hcontf : Continuous f := hf.continuous
  have hne : (Icc (0:ℝ) π).Nonempty := ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩
  obtain ⟨t₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Icc (0:ℝ) π) hne hcontf.continuousOn
  have hm : 0 < f t₀ := hfpos t₀
  have hlow : ∀ t ∈ Ioo (0:ℝ) π, f t₀ ≤ f t := fun t ht => hmin ⟨ht.1.le, ht.2.le⟩
  have hmono := HairpinArclength.strictMonoOn_arclength (f := f) (m := f t₀)
    hcontf.continuousOn hm hlow
  funext u
  exact hmono.injOn (h1mem u) (h2mem u) (by rw [h1val u, h2val u])

/-- **The steering mass of the hairpin is `π`, for any parametrization.**
`HairpinPulseMass.hairpin_pulse_mass` produces one parametrization with this
property; since both the tangent-angle map and the inverse of the front
arclength are determined by their defining equations, the mass identity holds
for every such pair. -/
theorem hairpin_pulse_mass_of_data (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {theta x : ℝ → ℝ} (hmem : ∀ u, theta u ∈ Ioo (0:ℝ) π)
    (hval : ∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u)
    (hthetac : Continuous theta)
    (hxinv : ∀ s, frontArclength f theta (x s) = s) :
    (∫ s : ℝ, pulseField f (theta (x s))) = π := by
  obtain ⟨theta', x', hmem', hval', hxinv', hmass⟩ :=
    HairpinRelative.hairpin_pulse_mass hf hfpos
  have hthetaeq : theta = theta' := theta_eq_of_arclength hf hfpos hmem hval hmem' hval'
  subst hthetaeq
  -- the front arclength is strictly monotone, hence injective
  have hsigderiv : ∀ u, HasDerivAt (frontArclength f theta)
      (Real.sqrt (1 + curvField f (theta u) ^ 2)) u :=
    hasDerivAt_frontArclength hf hfpos hthetac
  have hge : ∀ u, (1:ℝ) ≤ Real.sqrt (1 + curvField f (theta u) ^ 2) := by
    intro u
    have h1 : (1:ℝ) ≤ 1 + curvField f (theta u) ^ 2 := by nlinarith [sq_nonneg (curvField f (theta u))]
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ _ := Real.sqrt_le_sqrt h1
  have hsigmono : StrictMono (frontArclength f theta) :=
    ArclengthInverse.strictMono_of_deriv_ge (c := 1) one_pos hsigderiv hge
  have hxeq : x = x' := by
    funext s
    exact hsigmono.injective (by rw [hxinv s, hxinv' s])
  rw [hxeq]
  exact hmass

/-! ### The total turning of the model front -/

/-- **The model front of the paper's hairpin has total turning `π` over one
period.**  For a profile `f` smooth and positive on the line there are a
tangent-angle parametrization `θ` of the hairpin, the inverse `x` of its front
arclength, the derivative `y'` of the steering pulse `y = G₂(θ(x(·)))` and
constants `α > 0`, `C ≥ 0`, `0 ≤ b < 1` such that, for every period `Q` beyond
the explicit threshold `2/α + 16C/(α(1−b)) + 1` and every base point `c`,

`∫_c^{c+Q} (Y_Q + G(Y_Q)Y_Q') = π`,   `Y_Q(u) = ∑_m y(u − mQ)`.

The two terms are computed separately: the periodization integrates to the mass
`∫_ℝ y = π` of the pulse, and `G(Y_Q)Y_Q'`, being the derivative of the
periodic function `arcsin ∘ Y_Q`, integrates to zero. -/
theorem hairpin_frontCurv_turning (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ (theta x yp : ℝ → ℝ) (alpha C b : ℝ),
      0 < alpha ∧ 0 ≤ C ∧ 0 ≤ b ∧ b < 1 ∧
      (∀ u, theta u ∈ Ioo (0:ℝ) π) ∧
      (∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, HasDerivAt (fun r => pulseField f (theta (x r))) (yp s) s) ∧
      ∀ Q : ℝ, threshold alpha C b ≤ Q → ∀ c : ℝ,
        (∫ u in c..(c + Q),
            ((∑' m : ℤ, pulseField f (theta (x (u - m * Q))))
              + G (∑' m : ℤ, pulseField f (theta (x (u - m * Q))))
                * ∑' m : ℤ, yp (u - m * Q))) = π := by
  obtain ⟨theta, x, yp, alpha, C, D, b, halpha, hC, -, hb0, hb1, -, -, -,
    hmem, hval, hthetaderiv, hxinv, -, hycont, hy0, hyb, hsup, hyderiv, hypc, hypb, -⟩ :=
    exists_hairpin_pulse_data hf hfpos
  refine ⟨theta, x, yp, alpha, C, b, halpha, hC, hb0, hb1, hmem, hval, hxinv, hyderiv, ?_⟩
  intro Q hQ c
  have hthetac : Continuous theta :=
    continuous_iff_continuousAt.2 fun u => (hthetaderiv u).continuousAt
  have hQpos : 0 < Q := lt_of_lt_of_le (threshold_pos halpha hC hb1) hQ
  have hyabs : ∀ s, |pulseField f (theta (x s))| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]; exact hyb s
  have hyint : Integrable fun s => pulseField f (theta (x s)) :=
    OverlapIntegral.integrable_of_exp_bound halpha hycont hy0 hyb
  have hmass : (∫ s : ℝ, pulseField f (theta (x s))) = π :=
    hairpin_pulse_mass_of_data hf hfpos hmem hval hthetac hxinv
  have hYnn : ∀ v : ℝ, 0 ≤ ∑' m : ℤ, pulseField f (theta (x (v - m * Q))) :=
    fun v => tsum_nonneg fun m => hy0 _
  have hYa : ∀ v : ℝ, |∑' m : ℤ, pulseField f (theta (x (v - m * Q)))| ≤ (1 + b) / 2 := by
    intro v
    rw [abs_of_nonneg (hYnn v)]
    exact periodization_le_mid (y := fun s => pulseField f (theta (x s)))
      halpha hb1 hy0 hyb hsup hQ v
  exact PeriodizedTurning.integral_frontCurv_eq_pi (y := fun s => pulseField f (theta (x s)))
    (y' := yp) (a := (1 + b) / 2) halpha hQpos hycont hypc hyderiv hyabs hypb hy0 hyint
    (by linarith) (by linarith) hYa hmass c

/-- **A sup bound for the model front of the paper's hairpin.**  The steering
pulse obeys a relative derivative bound `|y'| ≤ D y`, which survives the
periodization, so beyond the explicit threshold in the period the periodized
front curvature is bounded by `(1 + G(a)D)·a` with `a = (1+b)/2 < 1`. -/
theorem hairpin_frontCurv_sup_bound (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ (theta x yp : ℝ → ℝ) (alpha C D b : ℝ),
      0 < alpha ∧ 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ b ∧ b < 1 ∧
      (∀ u, theta u ∈ Ioo (0:ℝ) π) ∧
      (∀ s, HasDerivAt (fun r => pulseField f (theta (x r))) (yp s) s) ∧
      ∀ Q : ℝ, threshold alpha C b ≤ Q → ∀ u : ℝ,
        |(∑' m : ℤ, pulseField f (theta (x (u - m * Q))))
            + G (∑' m : ℤ, pulseField f (theta (x (u - m * Q))))
              * ∑' m : ℤ, yp (u - m * Q)|
          ≤ (1 + G ((1 + b) / 2) * D) * ((1 + b) / 2) := by
  obtain ⟨theta, x, yp, alpha, C, D, b, halpha, hC, hD, hb0, hb1, -, -, -,
    hmem, -, -, -, -, -, hy0, hyb, hsup, hyderiv, -, hypb, hrel⟩ :=
    exists_hairpin_pulse_data hf hfpos
  refine ⟨theta, x, yp, alpha, C, D, b, halpha, hC, hD, hb0, hb1, hmem, hyderiv, ?_⟩
  intro Q hQ u
  have hQpos : 0 < Q := lt_of_lt_of_le (threshold_pos halpha hC hb1) hQ
  have hyabs : ∀ s, |pulseField f (theta (x s))| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]; exact hyb s
  have hYle : ∀ v : ℝ, (∑' m : ℤ, pulseField f (theta (x (v - m * Q)))) ≤ (1 + b) / 2 :=
    fun v => periodization_le_mid (y := fun s => pulseField f (theta (x s)))
      halpha hb1 hy0 hyb hsup hQ v
  exact PeriodizedTurning.abs_frontCurv_le (y := fun s => pulseField f (theta (x s)))
    (y' := yp) (a := (1 + b) / 2) halpha hQpos hD hy0 hyabs hypb hrel (by linarith) hYle u

end PeriodizedTurningHairpin
