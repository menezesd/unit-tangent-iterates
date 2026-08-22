import Mathlib
import UnitTangentIterates.PerimeterHairpinPulse
import UnitTangentIterates.FrontPeriodizationIntegral

/-!
# The front periodization error for the hairpin pulse of the paper

`FrontPeriodizationIntegral.front_periodization_error_exp` proves the lemma
*Front periodization error* of *A Noncircular Oval with Convex Unit-Tangent
Iterates* — over one period,

```
  ∫_q^{q+P} |K̄ - K_P| ≤ lipConst(a)·D·(8C²/(α-β))·e^{2βB}·e^{-βH},
```

`K̄` being the sum of the translates of the isolated curvature profile
`K_* = y + G(y)y'` and `K_P` its periodized form — for any pulse that is
continuous, nonnegative, exponentially localized, with a relative derivative
bound `|y'| ≤ D y` and a periodization staying below `a < 1`.

This file supplies those hypotheses for the **steering pulse of the paper's own
hairpin**.  All of them come from the lemma *Hairpin pulse estimates*, in the
form of `HairpinPulseDecay.lean` (exponential decay of the pulse and of its
derivative) and `HairpinRelativeDerivatives.lean` (the relative derivative
bounds), together with the sup bound `y ≤ 1/√(1+m²) < 1` of
`PerimeterHairpinPulse.lean`, which makes the periodization of the pulse stay
below `(1+b)/2 < 1` beyond an explicit period threshold.

Main results:

* `exists_hairpin_pulse_data` : the pulse of the hairpin, with its derivative,
  packaged with every bound the front periodization error consumes;
* `hairpin_front_periodization_error` : the front periodization error for the
  hairpin pulse.
-/

noncomputable section

open Real Set MeasureTheory

open scoped ContDiff

namespace FrontPeriodizationHairpin

open FrontPeriodization HairpinRelative PerimeterHairpinPulse

/-! ### The pulse of the hairpin with all its bounds -/

/-- **The steering pulse of the hairpin, with every bound it satisfies.**  For
a profile `f` smooth and positive on the line, the hairpin has an arclength
parametrization `θ` and a front-arclength parametrization `x` whose steering
pulse `y = G₂(θ(x(·))) = sin δ` is continuous, nonnegative, bounded by
`b = 1/√(1+m²) < 1` and by `Ce^{-α|·|}`, is differentiable with a continuous
derivative `y'` obeying the same exponential bound and the relative bound
`|y'| ≤ D y`. -/
theorem exists_hairpin_pulse_data {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfpos : ∀ t, 0 < f t) :
    ∃ (theta x yp : ℝ → ℝ) (alpha C D b : ℝ),
      0 < alpha ∧ 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ b ∧ b < 1 ∧
      (∀ u, 0 ≤ curvField f (theta u)) ∧
      Integrable (fun u => curvField f (theta u)) ∧
      (∀ u, |curvField f (theta u)| ≤ C * Real.exp (-alpha * |u|)) ∧
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s) ∧
      Continuous (fun s => pulseField f (theta (x s))) ∧
      (∀ s, 0 ≤ pulseField f (theta (x s))) ∧
      (∀ s, pulseField f (theta (x s)) ≤ C * Real.exp (-alpha * |s|)) ∧
      (∀ s, pulseField f (theta (x s)) ≤ b) ∧
      (∀ s, HasDerivAt (fun s => pulseField f (theta (x s))) (yp s) s) ∧
      Continuous yp ∧
      (∀ s, |yp s| ≤ C * Real.exp (-alpha * |s|)) ∧
      (∀ s, |yp s| ≤ D * pulseField f (theta (x s))) := by
  obtain ⟨M, theta, x, hM, hmem, hval, hderiv, hxinv, hxderiv, hcdec, hdec⟩ :=
    hairpin_pulse_exponential_decay hf hfpos
  obtain ⟨C₀, hC₀0, hC₀b⟩ := hdec 0
  obtain ⟨C₁, hC₁0, hC₁b⟩ := hdec 1
  obtain ⟨CK, hCK0, hCKb⟩ := hcdec 0
  set C : ℝ := max (max C₀ C₁) CK with hC
  have hC0 : 0 ≤ C := le_trans hC₀0 (le_trans (le_max_left _ _) (le_max_left _ _))
  -- the lower bound of the profile on `[0, π]`
  have hcontf : Continuous f := hf.continuous
  have hne : (Icc (0:ℝ) π).Nonempty := ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩
  obtain ⟨t₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Icc (0:ℝ) π) hne hcontf.continuousOn
  have hm : 0 < f t₀ := hfpos t₀
  have hlow : ∀ t ∈ Icc (0:ℝ) π, f t₀ ≤ f t := fun t ht => hmin ht
  set b : ℝ := 1 / Real.sqrt (1 + f t₀ ^ 2) with hb
  have hb0 : 0 ≤ b := by positivity
  have hb1 : b < 1 := inv_sqrt_one_add_sq_lt_one hm
  -- the pulse and its derivative
  set yy : ℝ → ℝ := fun s => pulseField f (theta (x s)) with hyy
  set yp : ℝ → ℝ := fun s => deriv (pulseField f) (theta (x s)) * yy s with hypdef
  have hmem' : ∀ u, theta u ∈ Icc (0:ℝ) π := fun u => ⟨(hmem u).1.le, (hmem u).2.le⟩
  have hy0 : ∀ s, 0 ≤ yy s := fun s => pulseField_nonneg hfpos (hmem' (x s))
  have hsup : ∀ s, yy s ≤ b := fun s =>
    pulseField_le_of_lower_bound hm hfpos hlow (hmem' (x s))
  have hpdiff : Differentiable ℝ (pulseField f) :=
    (contDiff_pulseField hf hfpos).differentiable (by simp)
  have hy : ∀ s, HasDerivAt yy (yp s) s := by
    intro s
    have h1 : HasDerivAt (pulseField f) (deriv (pulseField f) (theta (x s))) (theta (x s)) :=
      (hpdiff (theta (x s))).hasDerivAt
    simpa [hyy, hypdef, Function.comp, mul_comm] using h1.comp s (hxderiv s)
  have hw : Continuous (fun s => theta (x s)) :=
    continuous_iff_continuousAt.2 fun s => (hxderiv s).continuousAt
  have hycont : Continuous yy := ((contDiff_pulseField hf hfpos).continuous).comp hw
  have hypc : Continuous yp := by
    have hdc : Continuous (deriv (pulseField f)) :=
      (contDiff_pulseField hf hfpos).continuous_deriv (by simp)
    exact (hdc.comp hw).mul hycont
  have hyb : ∀ s, yy s ≤ C * Real.exp (-(1 / M) * |s|) := by
    intro s
    have h := hC₀b s
    rw [iteratedDeriv_zero] at h
    have h1 : yy s ≤ C₀ * Real.exp (-|s| / M) := le_trans (le_abs_self _) h
    have h2 : C₀ * Real.exp (-|s| / M) ≤ C * Real.exp (-|s| / M) :=
      mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _))
        (Real.exp_pos _).le
    have hrw : -|s| / M = -(1 / M) * |s| := by field_simp
    rw [hrw] at h1 h2
    linarith
  have hderivy : deriv yy = yp := funext fun t => (hy t).deriv
  have hypb : ∀ s, |yp s| ≤ C * Real.exp (-(1 / M) * |s|) := by
    intro s
    have h := hC₁b s
    rw [iteratedDeriv_one, hderivy] at h
    have h2 : C₁ * Real.exp (-|s| / M) ≤ C * Real.exp (-|s| / M) :=
      mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _))
        (Real.exp_pos _).le
    have hrw : -|s| / M = -(1 / M) * |s| := by field_simp
    rw [hrw] at h h2
    linarith
  -- the relative derivative bound `|y'| ≤ D y`
  obtain ⟨D, hD0, hDb⟩ :=
    abs_iteratedDeriv_pulse_le hf hfpos (w := fun s => theta (x s))
      (fun s => hmem' (x s)) hxderiv 1
  have hrel : ∀ s, |yp s| ≤ D * yy s := by
    intro s
    have h := hDb s
    rw [iteratedDeriv_one, hderivy] at h
    exact h
  have halpha : 0 < 1 / M := by positivity
  -- the curvature of the hairpin in its own arclength
  have hthetac : Continuous theta :=
    continuous_iff_continuousAt.2 fun u => (hderiv u).continuousAt
  have hKcont : Continuous (fun u => curvField f (theta u)) :=
    ((contDiff_curvField hf hfpos).continuous).comp hthetac
  have hK0 : ∀ u, 0 ≤ curvField f (theta u) := fun u => curvField_nonneg hfpos (hmem' u)
  have hKb : ∀ u, |curvField f (theta u)| ≤ C * Real.exp (-(1 / M) * |u|) := by
    intro u
    have h := hCKb u
    rw [iteratedDeriv_zero] at h
    have h2 : CK * Real.exp (-|u| / M) ≤ C * Real.exp (-|u| / M) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
    have hrw : -|u| / M = -(1 / M) * |u| := by field_simp
    rw [hrw] at h h2
    linarith
  have hKint : Integrable (fun u => curvField f (theta u)) :=
    OverlapIntegral.integrable_of_exp_bound halpha hKcont hK0
      (fun u => le_trans (le_abs_self _) (hKb u))
  exact ⟨theta, x, yp, 1 / M, C, D, b, halpha, hC0, hD0, hb0, hb1, hK0, hKint, hKb,
    hmem, hval, hderiv, hxinv, hxderiv, hycont, hy0, hyb, hsup, hy, hypc, hypb, hrel⟩

/-! ### The front periodization error for the hairpin -/

/-- **The lemma *Front periodization error* for the hairpin pulse of the
paper.**  For a profile `f` smooth and positive on the line, with `y` the
steering pulse of its hairpin, `K_* = y + G(y)y'` the isolated curvature
profile, `K̄` the sum of the translates of `K_*` of period `P` and `K_P` the
periodized form `Y_P + G(Y_P)Y_P'`, one has over one period

`∫_q^{q+P} |K̄ - K_P| ≤ lipConst(a)·D·(8C²/(α-β))·e^{2βB}·e^{-βH}`,  `a = (1+b)/2`,

for every period `P` beyond the explicit threshold, every `0 < β < α` with
`βP ≥ 2`, and every `H ≤ P + 2B`. -/
theorem hairpin_front_periodization_error {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfpos : ∀ t, 0 < f t) :
    ∃ (theta x yp : ℝ → ℝ) (alpha C D b : ℝ),
      0 < alpha ∧ 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ b ∧ b < 1 ∧
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s) ∧
      (∀ s, HasDerivAt (fun s => pulseField f (theta (x s))) (yp s) s) ∧
      (∀ s, pulseField f (theta (x s)) ≤ C * Real.exp (-alpha * |s|)) ∧
      (∀ s, |yp s| ≤ D * pulseField f (theta (x s))) ∧
      (∀ P beta H B q : ℝ, threshold alpha C b ≤ P → 0 < beta → beta < alpha →
        2 ≤ beta * P → H - 2 * B ≤ P →
        (∫ u in q..(q + P),
            |((pulseField f (theta (x u)) + G (pulseField f (theta (x u))) * yp u)
                + ∑' j : {j : ℤ // j ≠ 0},
                    (pulseField f (theta (x (u - (j : ℤ) * P)))
                      + G (pulseField f (theta (x (u - (j : ℤ) * P))))
                        * yp (u - (j : ℤ) * P)))
              - ((∑' m : ℤ, pulseField f (theta (x (u - m * P))))
                + G (∑' m : ℤ, pulseField f (theta (x (u - m * P))))
                  * (∑' m : ℤ, yp (u - m * P)))|)
          ≤ (lipConst ((1 + b) / 2) * D * (8 * C ^ 2 / (alpha - beta))
              * Real.exp (2 * beta * B)) * Real.exp (-(beta * H))) := by
  obtain ⟨theta, x, yp, alpha, C, D, b, halpha, hC0, hD0, hb0, hb1, -, -, -,
    hmem, hval, hderiv, hxinv, hxderiv, hycont, hy0, hyb, hsup, hy, hypc, -, hrel⟩ :=
    exists_hairpin_pulse_data hf hfpos
  refine ⟨theta, x, yp, alpha, C, D, b, halpha, hC0, hD0, hb0, hb1, hmem, hval, hderiv,
    hxinv, hxderiv, hy, hyb, hrel, ?_⟩
  intro P beta H B q hP hbeta0 hba hbP hPH
  have hPpos : 0 < P := lt_of_lt_of_le (threshold_pos halpha hC0 hb1) hP
  have hhalf : Real.exp (-(beta * P)) ≤ 1 / 2 := by
    have h := exp_neg_le_inv (t := beta * P) (by positivity)
    have hinv : (1:ℝ) / (beta * P) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hbP
    linarith
  have hYa : ∀ u : ℝ, (∑' m : ℤ, pulseField f (theta (x (u - m * P)))) ≤ (1 + b) / 2 :=
    periodization_le_mid halpha hb1 hy0 hyb hsup hP
  exact FrontPeriodizationIntegral.front_periodization_error_exp
    (y := fun s => pulseField f (theta (x s))) (yp := yp) (C := C) (alpha := alpha)
    (beta := beta) (a := (1 + b) / 2) (D := D) (P := P)
    (Kstar := fun s => pulseField f (theta (x s))
      + G (pulseField f (theta (x s))) * yp s)
    (Kbar := fun u => (pulseField f (theta (x u))
        + G (pulseField f (theta (x u))) * yp u)
      + ∑' j : {j : ℤ // j ≠ 0},
          (pulseField f (theta (x (u - (j : ℤ) * P)))
            + G (pulseField f (theta (x (u - (j : ℤ) * P)))) * yp (u - (j : ℤ) * P)))
    (KP := fun u => (∑' m : ℤ, pulseField f (theta (x (u - m * P))))
      + G (∑' m : ℤ, pulseField f (theta (x (u - m * P)))) * (∑' m : ℤ, yp (u - m * P)))
    (H := H) (B := B) (q := q)
    halpha hPpos hbeta0 hba hhalf hycont hypc hy0 hyb hD0 hrel
    (by linarith) (by linarith) hYa (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hPH

/-! ### The statement is not vacuous

The hypotheses are met by the constant profile `f ≡ 2`, which is smooth and
positive on the line. -/

example : ∃ alpha : ℝ, 0 < alpha := by
  obtain ⟨-, -, -, alpha, -, -, -, halpha, -⟩ :=
    hairpin_front_periodization_error (f := fun _ => (2 : ℝ)) contDiff_const fun _ => two_pos
  exact ⟨alpha, halpha⟩

end FrontPeriodizationHairpin
