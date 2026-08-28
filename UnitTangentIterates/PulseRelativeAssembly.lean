import UnitTangentIterates.PulseRelativeOrderFour
import UnitTangentIterates.CurvatureFromPulse

/-!
# Assembling the relative pulse bounds into `hrelj`

The five order lemmas of `PulseRelativeFromIdentity`,
`PulseRelativeOrderTwo`, `PulseRelativeOrderThree` and `PulseRelativeOrderFour`
produce the bounds `|y^{(j)}| ≤ D_j y` for `j ≤ 4`.  This file assembles them
into the exact shape of the hypothesis `hrelj` that
`PaperHairpinQuantitativeData.data_of_interior` consumes, and supplies the three
bridges the assembly needs:

* `iteratedDeriv_one_bound` — the order-one conclusion, stated on
  `iteratedDeriv 1` rather than on a derivative witness;
* `shifted_curv_bound` — the curvature bounds of `CurvatureFromPulse` are stated
  along `theta`; the pulse orders consume them along `theta (· + s₀)`.
  `iteratedDeriv_comp_add_const` transports them;
* `ident_of_solved`, `harnack_pulse_form` — the identity and the Harnack
  comparison in the two forms the different orders use.

`rel_pulse_le_four_of_orders` is the assembly itself.
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Real HairpinRelative

namespace HairpinRelative


/-- Derive the unsolved identity from the solved one. -/
theorem ident_of_solved {f theta x yp : ℝ → ℝ} {s0 : ℝ}
    (hyp : ∀ r, yp r = Real.sqrt (1 - pulseField f (theta (x r)) ^ 2)
      * (curvField f (theta (r + s0)) - pulseField f (theta (x r)))) :
    ∀ s, curvField f (theta (s + s0))
      = pulseField f (theta (x s))
        + FrontPeriodization.G (pulseField f (theta (x s))) * yp s := by
  intro s
  have hsq := one_sub_pulseField_sq_pos f (theta (x s))
  have hs : 0 < Real.sqrt (1 - pulseField f (theta (x s)) ^ 2) :=
    Real.sqrt_pos.mpr hsq
  rw [hyp s, FrontPeriodization.G]
  field_simp [hs.ne']
  ring

/-- The Harnack comparison in the pulse-normalised form the higher orders use. -/
theorem harnack_pulse_form {f theta x : ℝ → ℝ} {s0 b Ch : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hCh : 0 ≤ Ch)
    (hy0 : ∀ s, 0 ≤ pulseField f (theta (x s)))
    (hsup : ∀ s, pulseField f (theta (x s)) ≤ b)
    (hharnack : ∀ s, curvField f (theta (s + s0))
      ≤ Ch * curvField f (theta (x s))) :
    ∀ s, curvField f (theta (s + s0))
      ≤ Ch * (pulseField f (theta (x s)) / Real.sqrt (1 - b ^ 2)) := by
  intro s
  refine le_trans (hharnack s) (mul_le_mul_of_nonneg_left ?_ hCh)
  exact curvField_le_pulse_div hb0 hb1 (hy0 s) (hsup s)

/-- **Assembling orders 0–4 into the `hrelj` shape** that `data_of_interior`
consumes.  The four inputs are exactly the conclusions of
`rel_pulse_one_of_identity`, `rel_pulse_two_of_identity`,
`rel_pulse_three_of_identity` and `rel_pulse_four_of_identity` (the first two
after the `iteratedDeriv` bridges). -/
theorem rel_pulse_le_four_of_orders {f theta x : ℝ → ℝ}
    {relativeConst : ℕ → ℝ}
    (hy0 : ∀ s, 0 ≤ pulseField f (theta (x s)))
    (h0 : 1 ≤ relativeConst 0)
    (h1 : ∀ s, |iteratedDeriv 1 (fun r => pulseField f (theta (x r))) s|
      ≤ relativeConst 1 * pulseField f (theta (x s)))
    (h2 : ∀ s, |iteratedDeriv 2 (fun r => pulseField f (theta (x r))) s|
      ≤ relativeConst 2 * pulseField f (theta (x s)))
    (h3 : ∀ s, |iteratedDeriv 3 (fun r => pulseField f (theta (x r))) s|
      ≤ relativeConst 3 * pulseField f (theta (x s)))
    (h4 : ∀ s, |iteratedDeriv 4 (fun r => pulseField f (theta (x r))) s|
      ≤ relativeConst 4 * pulseField f (theta (x s))) :
    ∀ j ≤ 4, ∀ s,
      |iteratedDeriv j (fun r => pulseField f (theta (x r))) s|
        ≤ relativeConst j * pulseField f (theta (x s)) := by
  intro j hj s
  interval_cases j
  · rw [iteratedDeriv_zero, abs_of_nonneg (hy0 s)]
    exact le_mul_of_one_le_left (hy0 s) h0
  · exact h1 s
  · exact h2 s
  · exact h3 s
  · exact h4 s

/-- The order-one conclusion in `iteratedDeriv` form. -/
theorem iteratedDeriv_one_bound {f theta x yp : ℝ → ℝ} {D1 : ℝ}
    (hYd : ∀ s, HasDerivAt (fun r => pulseField f (theta (x r))) (yp s) s)
    (hb : ∀ s, |yp s| ≤ D1 * pulseField f (theta (x s))) :
    ∀ s, |iteratedDeriv 1 (fun r => pulseField f (theta (x r))) s|
      ≤ D1 * pulseField f (theta (x s)) := by
  intro s
  have hd : deriv (fun r => pulseField f (theta (x r))) = yp :=
    funext fun r => (hYd r).deriv
  rw [iteratedDeriv_one, hd]
  exact hb s

/-- The curvature bounds in the shifted form the pulse orders consume. -/
theorem shifted_curv_bound {g : ℝ → ℝ} {s0 E : ℝ} {n : ℕ}
    (h : ∀ u, |iteratedDeriv n g u| ≤ E * g u) :
    ∀ s, |iteratedDeriv n (fun r => g (r + s0)) s| ≤ E * g (s + s0) := by
  intro s
  rw [iteratedDeriv_comp_add_const]
  exact h (s + s0)

end HairpinRelative
