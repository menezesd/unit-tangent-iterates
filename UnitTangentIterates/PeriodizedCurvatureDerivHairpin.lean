import Mathlib
import UnitTangentIterates.PeriodizedCurvatureDeriv
import UnitTangentIterates.HairpinPulseSecondData
import UnitTangentIterates.PeriodizedTurningHairpin

/-!
# The model front of the paper's hairpin as a marked oval curvature

`PeriodizedCurvatureDeriv.frontCurv_marked_oval_data` shows that the periodized
front curvature `K_P = Y_P + G(Y_P)Y_P'` of a pulse satisfies every hypothesis
that the interpolation estimates for the marked path pseudodistance put on the
curvature of a marked oval of half perimeter `P`: continuity of the curvature
and of its derivative, periodicity, total turning `π`, a uniform derivative
bound and two-sided bounds.

This file checks the hypotheses of that theorem for the **steering pulse of the
paper's own hairpin**, using the second-order pulse data of
`HairpinPulseSecondData.lean`, the periodization bound
`PerimeterHairpinPulse.periodization_le_mid` and the steering mass
`∫_ℝ y = π` of `PeriodizedTurningHairpin.hairpin_pulse_mass_of_data`.

The one condition that does not come for free is the smallness `G(a)D ≤ 1`,
`a = (1+b)/2`, of the relative derivative constant against the periodization
bound; it is what makes the periodized curvature nonnegative, and it is
therefore carried as an explicit hypothesis of the conclusion.
-/

noncomputable section

open Real Set MeasureTheory Function

open scoped ContDiff

namespace PeriodizedCurvatureDerivHairpin

open FrontPeriodization HairpinRelative PerimeterHairpinPulse
  HairpinPulseSecondData PeriodizedCurvatureDeriv PeriodizedTurningHairpin

variable {f : ℝ → ℝ}

/-- **The model front of the paper's hairpin is an admissible marked-oval
curvature.**  For a profile `f` smooth and positive on the line there are a
tangent-angle parametrization `θ` of the hairpin, the inverse `x` of its front
arclength, the first two derivatives `y'`, `y''` of the steering pulse
`y = G₂(θ(x(·)))` and constants `α > 0`, `C, D ≥ 0`, `0 ≤ b < 1` such that,
beyond the explicit period threshold and under the smallness condition
`G(a)D ≤ 1` with `a = (1+b)/2`, the periodized front curvature `K_Q` is
continuous and `C¹`, `Q`-periodic, has total turning `π` over one period,
satisfies the uniform derivative bound
`|K_Q'| ≤ Da + G'(a)D²a² + G(a)Da` and the two-sided bounds
`0 ≤ K_Q ≤ (1 + G(a)D)a`. -/
theorem hairpin_frontCurv_marked_oval_data (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ (theta x yp ypp : ℝ → ℝ) (alpha C D b : ℝ),
      0 < alpha ∧ 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ b ∧ b < 1 ∧
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ s, HasDerivAt (fun r => pulseField f (theta (x r))) (yp s) s) ∧
      (∀ s, HasDerivAt yp (ypp s) s) ∧
      ∀ Q : ℝ, threshold alpha C b ≤ Q → G ((1 + b) / 2) * D ≤ 1 →
        ∃ K K' : ℝ → ℝ,
          (∀ u, K u = (∑' m : ℤ, pulseField f (theta (x (u - m * Q))))
            + G (∑' m : ℤ, pulseField f (theta (x (u - m * Q))))
              * ∑' m : ℤ, yp (u - m * Q)) ∧
          Continuous K ∧ Continuous K' ∧ Periodic K Q ∧
          (∫ r in (0:ℝ)..Q, K r) = π ∧
          (∀ r, HasDerivAt K (K' r) r) ∧
          (∀ r, |K' r| ≤ D * ((1 + b) / 2)
            + lipConst ((1 + b) / 2) * (D ^ 2 * ((1 + b) / 2) ^ 2)
            + G ((1 + b) / 2) * (D * ((1 + b) / 2))) ∧
          (∀ r, 0 ≤ K r) ∧ (∀ r, K r ≤ (1 + G ((1 + b) / 2) * D) * ((1 + b) / 2)) := by
  obtain ⟨theta, x, yp, ypp, alpha, C, D, b, halpha, hC, hD, hb0, hb1, hmem, hval, hthetaderiv,
    hxinv, hxderiv, hycont, hy0, hyb, hsup, hyderiv, hypc, hypb, hrel, hyppderiv, hyppc,
    hyppb, hrel2⟩ := exists_hairpin_pulse_second_data hf hfpos
  refine ⟨theta, x, yp, ypp, alpha, C, D, b, halpha, hC, hD, hb0, hb1, hmem, hyderiv,
    hyppderiv, ?_⟩
  intro Q hQ hsmall
  have hQpos : 0 < Q := lt_of_lt_of_le (threshold_pos halpha hC hb1) hQ
  have hthetac : Continuous theta :=
    continuous_iff_continuousAt.2 fun u => (hthetaderiv u).continuousAt
  have hyabs : ∀ s, |pulseField f (theta (x s))| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]; exact hyb s
  have hyint : Integrable fun s => pulseField f (theta (x s)) :=
    OverlapIntegral.integrable_of_exp_bound halpha hycont hy0 hyb
  have hmass : (∫ s : ℝ, pulseField f (theta (x s))) = π :=
    hairpin_pulse_mass_of_data hf hfpos hmem hval hthetac hxinv
  have hYa : ∀ v : ℝ, (∑' m : ℤ, pulseField f (theta (x (v - m * Q)))) ≤ (1 + b) / 2 :=
    fun v => periodization_le_mid (y := fun s => pulseField f (theta (x s)))
      halpha hb1 hy0 hyb hsup hQ v
  exact frontCurv_marked_oval_data (y := fun s => pulseField f (theta (x s)))
    (y' := yp) (y'' := ypp) (a := (1 + b) / 2) halpha hQpos hD hD hyderiv hyppderiv hyppc
    hyabs hypb hyppb hy0 hyint hmass hrel hrel2 (by linarith) (by linarith) hYa hsmall

end PeriodizedCurvatureDerivHairpin
