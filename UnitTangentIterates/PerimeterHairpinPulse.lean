import Mathlib
import UnitTangentIterates.PerimeterValueProduced
import UnitTangentIterates.PeriodizationSup
import UnitTangentIterates.HairpinPulseDecay

/-!
# The value clause of *Exact two-cap pairs* for the hairpin pulse itself

`PerimeterValueProduced.abs_defect_sub_delta_le_pulse_full` proves the value
clause

```
  H - P(H) = Δ + O(e^{-β'H}),      Δ = ∫_ℝ Φ(y),   Φ(z) = 1 - √(1 - z²),
```

of the proposition *Exact two-cap pairs* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* for any pulse that is continuous, nonnegative,
exponentially localized, and whose periodization stays below a threshold
`a < 1`.  Until now those hypotheses had only been checked for stand-in pulses
(`PerimeterValueProducedInstance.lean`).  This file checks them for the
**steering pulse of the paper's own hairpin**

```
  y(s) = sin δ(s) = G₂(θ(x(s))),      G₂ = G/√(1+G²),   G(t) = sin t / f(t),
```

so that the value clause holds in the paper's configuration.

The two ingredients are

* `HairpinRelative.hairpin_pulse_exponential_decay`, which produces the
  arclength parametrization `θ` of the hairpin, the inverse `x` of its front
  arclength and the exponential bound `y ≤ C e^{-|s|/M}`, and
* the elementary sup bound `y ≤ 1/√(1+m²) < 1` proved here, `m` being a
  positive lower bound for the profile: the pulse is `G/√(1+G²)` with
  `0 ≤ G ≤ 1/m`, and `z ↦ z/√(1+z²)` is increasing.

With a sup bound `b < 1` the periodization stays below `(1+b)/2 < 1` once the
period is large (`PeriodizationSup.periodization_le_of_sup`), and the value
clause follows.

Main results:

* `pulseField_le_of_lower_bound` : `G₂(t) ≤ 1/√(1+m²)` for `t ∈ [0, π]`;
* `defect_value_clause_of_sup` : the value clause for any continuous,
  nonnegative, exponentially localized pulse with a sup bound `b < 1`, for
  every period `H` beyond an explicit threshold;
* `perimeter_derivative_clause_of_sup` : likewise the derivative clause
  `P'(H) = 1 + O(e^{-β'H})`, for every period beyond twice that threshold;
* `hairpin_perimeter_value_clause`, `hairpin_perimeter_derivative_clause` :
  the two clauses for the hairpin pulse of the paper.
-/

noncomputable section

open Real Set MeasureTheory

open scoped ContDiff

namespace PerimeterHairpinPulse

open PerimeterAsymptotics HairpinRelative

/-! ### Two elementary inequalities -/

/-- `e^{-t} ≤ 1/t` for `t > 0`. -/
theorem exp_neg_le_inv {t : ℝ} (ht : 0 < t) : Real.exp (-t) ≤ 1 / t := by
  have h1 : t < Real.exp t := by
    have := Real.add_one_le_exp t
    linarith
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos t)]
  have h2 : 1 / t * t = 1 := by field_simp
  nlinarith [one_div_pos.mpr ht]

/-- **The sup bound for the pulse field.**  If `m ≤ f` on `[0, π]` with
`m > 0`, then `G₂ = G/√(1+G²) ≤ 1/√(1+m²)` there. -/
theorem pulseField_le_of_lower_bound {f : ℝ → ℝ} {m : ℝ} (hm : 0 < m)
    (hfpos : ∀ t, 0 < f t) (hlow : ∀ t ∈ Icc (0:ℝ) π, m ≤ f t)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) π) :
    pulseField f t ≤ 1 / Real.sqrt (1 + m ^ 2) := by
  set G : ℝ := curvField f t with hG
  have hG0 : 0 ≤ G := curvField_nonneg hfpos ht
  have hGm : G * m ≤ 1 := by
    have hs : Real.sin t ≤ 1 := Real.sin_le_one t
    have hf : m ≤ f t := hlow t ht
    have hfp : 0 < f t := hfpos t
    have : G = Real.sin t / f t := rfl
    rw [this, div_mul_eq_mul_div, div_le_one hfp]
    nlinarith [Real.sin_nonneg_of_mem_Icc ht]
  set s1 : ℝ := Real.sqrt (1 + G ^ 2) with hs1
  set s2 : ℝ := Real.sqrt (1 + m ^ 2) with hs2
  have hs1p : 0 < s1 := sqrt_one_add_sq_pos G
  have hs2p : 0 < s2 := sqrt_one_add_sq_pos m
  have hs1sq : s1 ^ 2 = 1 + G ^ 2 := Real.sq_sqrt (by positivity)
  have hs2sq : s2 ^ 2 = 1 + m ^ 2 := Real.sq_sqrt (by positivity)
  have key : G * s2 ≤ s1 := by
    have hGm0 : 0 ≤ G * m := mul_nonneg hG0 hm.le
    have hsq2 : (G * m) ^ 2 ≤ 1 := by nlinarith
    have hexp : G ^ 2 * m ^ 2 = (G * m) ^ 2 := by ring
    have hsq : (G * s2) ^ 2 ≤ s1 ^ 2 := by
      rw [mul_pow, hs1sq, hs2sq]
      nlinarith [hsq2, hexp]
    nlinarith [mul_nonneg hG0 hs2p.le]
  show G / s1 ≤ 1 / s2
  rw [div_le_div_iff₀ hs1p hs2p]
  linarith

/-- `1/√(1+m²) < 1` for `m > 0`. -/
theorem inv_sqrt_one_add_sq_lt_one {m : ℝ} (hm : 0 < m) :
    1 / Real.sqrt (1 + m ^ 2) < 1 := by
  have h1 : (1:ℝ) < Real.sqrt (1 + m ^ 2) := by
    have : Real.sqrt 1 < Real.sqrt (1 + m ^ 2) := by
      apply Real.sqrt_lt_sqrt (by norm_num)
      nlinarith
    simpa using this
  rw [div_lt_one (by linarith)]
  exact h1

/-! ### The period threshold produced by a sup bound on the pulse -/

variable {y : ℝ → ℝ} {C alpha b H beta' : ℝ}

/-- The explicit period threshold `2/α + 16C/(α(1-b)) + 1` beyond which the
periodization of a pulse bounded by `b < 1` and by `Ce^{-α|·|}` stays below
`(1+b)/2 < 1`. -/
def threshold (alpha C b : ℝ) : ℝ := 2 / alpha + 16 * C / (alpha * (1 - b)) + 1

theorem threshold_pos (halpha : 0 < alpha) (hC : 0 ≤ C) (hb1 : b < 1) :
    0 < threshold alpha C b := by
  have h1 : 0 < 2 / alpha := by positivity
  have h1b : 0 < 1 - b := by linarith
  have h2 : 0 ≤ 16 * C / (alpha * (1 - b)) := by positivity
  unfold threshold
  linarith

/-- Beyond the threshold the smallness condition `e^{-αQ} ≤ ½` holds. -/
theorem exp_le_half_of_threshold (halpha : 0 < alpha) (hC : 0 ≤ C) (hb1 : b < 1)
    {Q : ℝ} (hQ : threshold alpha C b ≤ Q) : Real.exp (-alpha * Q) ≤ 1 / 2 := by
  have h1b : 0 < 1 - b := by linarith
  have h2 : 0 ≤ 16 * C / (alpha * (1 - b)) := by positivity
  have hQ2 : 2 / alpha ≤ Q := by unfold threshold at hQ; linarith
  have hah : 2 ≤ alpha * Q := by
    rw [div_le_iff₀ halpha] at hQ2
    linarith
  have h := exp_neg_le_inv (t := alpha * Q) (by linarith)
  have hinv : (1:ℝ) / (alpha * Q) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hah
  calc Real.exp (-alpha * Q) = Real.exp (-(alpha * Q)) := by ring_nf
    _ ≤ 1 / (alpha * Q) := h
    _ ≤ 1 / 2 := hinv

/-- Beyond the threshold the periodization error is at most `(1-b)/2`. -/
theorem tail_le_of_threshold (halpha : 0 < alpha) (hC : 0 ≤ C) (hb1 : b < 1)
    {Q : ℝ} (hQ : threshold alpha C b ≤ Q) :
    4 * C * Real.exp (-(alpha / 2) * Q) ≤ (1 - b) / 2 := by
  have h1b : 0 < 1 - b := by linarith
  have h1 : 0 < 2 / alpha := by positivity
  have h2 : 0 ≤ 16 * C / (alpha * (1 - b)) := by positivity
  have hQpos : 0 < Q := lt_of_lt_of_le (threshold_pos halpha hC hb1) hQ
  have hQ3 : 16 * C / (alpha * (1 - b)) ≤ Q := by unfold threshold at hQ; linarith
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · rw [← hC0]
    simp only [mul_zero, zero_mul]
    linarith
  · have hah : 0 < alpha / 2 * Q := by positivity
    have h := exp_neg_le_inv (t := alpha / 2 * Q) hah
    have hrw : Real.exp (-(alpha / 2) * Q) = Real.exp (-(alpha / 2 * Q)) := by ring_nf
    have hstep : 4 * C * Real.exp (-(alpha / 2) * Q) ≤ 4 * C * (1 / (alpha / 2 * Q)) := by
      rw [hrw]
      exact mul_le_mul_of_nonneg_left h (by positivity)
    have hkey : 4 * C * (1 / (alpha / 2 * Q)) ≤ (1 - b) / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have hmul : 16 * C ≤ alpha * (1 - b) * Q := by
        rw [div_le_iff₀ (by positivity)] at hQ3
        linarith
      nlinarith
    linarith

/-- **Beyond the threshold the periodization stays below `(1+b)/2 < 1`.** -/
theorem periodization_le_mid (halpha : 0 < alpha) (hb1 : b < 1)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) {Q : ℝ} (hQ : threshold alpha C b ≤ Q) (v : ℝ) :
    (∑' m : ℤ, y (v - m * Q)) ≤ (1 + b) / 2 := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hQpos : 0 < Q := lt_of_lt_of_le (threshold_pos halpha hC hb1) hQ
  have h := PeriodizationSup.periodization_le_of_sup (y := y) (C := C) (alpha := alpha)
    (P := Q) (b := b) halpha hQpos (exp_le_half_of_threshold halpha hC hb1 hQ)
    hy0 hyb hsup v
  have htail := tail_le_of_threshold halpha hC hb1 hQ
  linarith

/-! ### The value clause from a sup bound on the pulse -/

/-- **The value clause of the two-cap asymptotics, from a sup bound on the
pulse.**  For a continuous nonnegative pulse `y ≤ C e^{-α|·|}` with `y ≤ b < 1`
and every period `H` beyond the explicit threshold `2/α + 16C/(α(1-b)) + 1`,

`|(H - P(H)) - Δ| ≤ (a/√(1-a²)·4C/((α/2-β')e) + 2C²/α)e^{-β'H}`,  `a = (1+b)/2`,

for every `β' < α/2`; the periodization of `y` stays below `a < 1`. -/
theorem defect_value_clause_of_sup
    (halpha : 0 < alpha) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b)
    (hH : threshold alpha C b ≤ H)
    (hbeta : beta' < alpha / 2) :
    |(H - (∫ s in (0:ℝ)..H, Real.sqrt (1 - (∑' m : ℤ, y (s - m * H)) ^ 2)))
        - ∫ s : ℝ, Phi (y s)|
      ≤ ((1 + b) / 2 / Real.sqrt (1 - ((1 + b) / 2) ^ 2) * (4 * C)
            / ((alpha / 2 - beta') * Real.exp 1) + 2 * C ^ 2 / alpha)
          * Real.exp (-beta' * H) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hHpos : 0 < H := lt_of_lt_of_le (threshold_pos halpha hC hb1) hH
  have hq : Real.exp (-alpha * H) ≤ 1 / 2 := exp_le_half_of_threshold halpha hC hb1 hH
  have hYa : ∀ u : ℝ, (∑' m : ℤ, y (u - m * H)) ≤ (1 + b) / 2 :=
    periodization_le_mid halpha hb1 hy0 hyb hsup hH
  have ha0 : (0:ℝ) ≤ (1 + b) / 2 := by linarith
  have ha1 : (1 + b) / 2 < 1 := by linarith
  exact PerimeterValueProduced.abs_defect_sub_delta_le_pulse_full
    (y := y) (C := C) (a := (1 + b) / 2) (alpha := alpha) (H := H) (beta' := beta')
    halpha hHpos hbeta hq hy hy0 hyb ha0 ha1 hYa

/-! ### The derivative clause from a sup bound on the pulse -/

/-- **The derivative clause `P'(H) = 1 + O(e^{-β'H})`, from a sup bound on the
pulse.**  For a differentiable nonnegative pulse with `y, y' ≤ C e^{-α|·|}` and
`y ≤ b < 1`, and a rear half-perimeter `P` given by the centred cell integral
of the defect integrand, `P` is differentiable at every `H₀` beyond twice the
threshold, with

`|P'(H₀) - 1| ≤ (25C² + a/√(1-a²)·8C/((α/2-β')e))e^{-β'H₀}`,  `a = (1+b)/2`. -/
theorem perimeter_derivative_clause_of_sup {yp P : ℝ → ℝ} {H0 : ℝ}
    (halpha : 0 < alpha) (hb1 : b < 1)
    (hy : ∀ s, HasDerivAt y (yp s) s) (hypc : Continuous yp)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hypb : ∀ s, |yp s| ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b)
    (hH : 2 * threshold alpha C b ≤ H0)
    (hbeta : beta' < alpha / 2)
    (hid : ∀ H : ℝ, H - P H = ∫ u in (-(H / 2))..(H / 2),
      Phi (∑' m : ℤ, y (u - m * H))) :
    ∃ p : ℝ, HasDerivAt P p H0 ∧
      |p - 1| ≤ (25 * C ^ 2 + (1 + b) / 2 / Real.sqrt (1 - ((1 + b) / 2) ^ 2) * (8 * C)
          / ((alpha / 2 - beta') * Real.exp 1)) * Real.exp (-beta' * H0) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hthr0 : 0 < threshold alpha C b := threshold_pos halpha hC hb1
  have hhalf : threshold alpha C b ≤ H0 / 2 := by linarith
  have hH0 : 0 < H0 := by linarith
  have hb0 : 0 ≤ b := le_trans (hy0 0) (hsup 0)
  have hthr : Real.exp (-alpha * (H0 / 2)) ≤ 1 / 2 :=
    exp_le_half_of_threshold halpha hC hb1 hhalf
  have hyb' : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]; exact hyb s
  have hYa : ∀ Q : ℝ, H0 / 2 < Q → ∀ v : ℝ, |∑' m : ℤ, y (v - m * Q)| ≤ (1 + b) / 2 := by
    intro Q hQ v
    have hQ' : threshold alpha C b ≤ Q := le_trans hhalf hQ.le
    have hnn : 0 ≤ ∑' m : ℤ, y (v - m * Q) := tsum_nonneg fun _ => hy0 _
    rw [abs_of_nonneg hnn]
    exact periodization_le_mid halpha hb1 hy0 hyb hsup hQ' v
  exact PerimeterLeibnizProduced.hasDerivAt_perimeter_of_pulse_leibniz
    (y := y) (yp := yp) (C := C) (a := (1 + b) / 2) (alpha := alpha) (H0 := H0)
    (beta' := beta') (P := P)
    halpha hH0 hbeta hthr hy hypc hy0 hyb' hypb (by linarith) (by linarith) hYa hid

/-! ### The value clause for the hairpin pulse of the paper -/

/-- **The value clause of *Exact two-cap pairs* for the hairpin pulse.**  For a
profile `f` smooth and positive on the line, the hairpin has an arclength
parametrization `θ` and a front-arclength parametrization `x` whose steering
pulse `y = G₂(θ(x(·))) = sin δ` is continuous, nonnegative, exponentially
localized and bounded by `b < 1`; consequently, for every period `H` beyond an
explicit threshold and every `β' < α/2`, the perimeter defect of the periodized
profile differs from `Δ = ∫_ℝ Φ(y)` by at most an explicit multiple of
`e^{-β'H}`. -/
theorem hairpin_perimeter_value_clause {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfpos : ∀ t, 0 < f t) :
    ∃ (theta x : ℝ → ℝ) (alpha C b H₀ : ℝ),
      0 < alpha ∧ 0 ≤ C ∧ 0 ≤ b ∧ b < 1 ∧ 0 < H₀ ∧
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s) ∧
      (∀ s, pulseField f (theta (x s)) ≤ C * Real.exp (-alpha * |s|)) ∧
      (∀ s, pulseField f (theta (x s)) ≤ b) ∧
      (∀ H, H₀ ≤ H → ∀ beta' : ℝ, beta' < alpha / 2 →
        |(H - (∫ s in (0:ℝ)..H,
              Real.sqrt (1 - (∑' m : ℤ, pulseField f (theta (x (s - m * H)))) ^ 2)))
            - ∫ s : ℝ, Phi (pulseField f (theta (x s)))|
          ≤ ((1 + b) / 2 / Real.sqrt (1 - ((1 + b) / 2) ^ 2) * (4 * C)
                / ((alpha / 2 - beta') * Real.exp 1) + 2 * C ^ 2 / alpha)
              * Real.exp (-beta' * H)) := by
  obtain ⟨M, theta, x, hM, hmem, hval, hderiv, hxinv, hxderiv, -, hdec⟩ :=
    hairpin_pulse_exponential_decay hf hfpos
  obtain ⟨D, hD0, hDb⟩ := hdec 0
  -- the lower bound of the profile on `[0, π]`
  have hcontf : Continuous f := hf.continuous
  have hne : (Icc (0:ℝ) π).Nonempty := ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩
  obtain ⟨t₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Icc (0:ℝ) π) hne hcontf.continuousOn
  have hm : 0 < f t₀ := hfpos t₀
  have hlow : ∀ t ∈ Icc (0:ℝ) π, f t₀ ≤ f t := fun t ht => hmin ht
  set b : ℝ := 1 / Real.sqrt (1 + f t₀ ^ 2) with hb
  have hb0 : 0 ≤ b := by positivity
  have hb1 : b < 1 := inv_sqrt_one_add_sq_lt_one hm
  -- the pulse
  set yy : ℝ → ℝ := fun s => pulseField f (theta (x s)) with hyy
  have hmem' : ∀ u, theta u ∈ Icc (0:ℝ) π := fun u => ⟨(hmem u).1.le, (hmem u).2.le⟩
  have hy0 : ∀ s, 0 ≤ yy s := fun s => pulseField_nonneg hfpos (hmem' (x s))
  have hsup : ∀ s, yy s ≤ b := fun s =>
    pulseField_le_of_lower_bound hm hfpos hlow (hmem' (x s))
  have hyb : ∀ s, yy s ≤ D * Real.exp (-(1 / M) * |s|) := by
    intro s
    have h := hDb s
    rw [iteratedDeriv_zero] at h
    have h1 : yy s ≤ D * Real.exp (-|s| / M) := le_trans (le_abs_self _) h
    have hrw : -|s| / M = -(1 / M) * |s| := by field_simp
    rwa [hrw] at h1
  have hycont : Continuous yy := by
    have hw : Continuous (fun s => theta (x s)) := by
      refine continuous_iff_continuousAt.2 fun s => ?_
      exact (hxderiv s).continuousAt
    exact ((contDiff_pulseField hf hfpos).continuous).comp hw
  have halpha : 0 < 1 / M := by positivity
  refine ⟨theta, x, 1 / M, D, b, threshold (1 / M) D b,
    halpha, hD0, hb0, hb1, threshold_pos halpha hD0 hb1,
    hmem, hval, hderiv, hxinv, hxderiv, hyb, hsup, ?_⟩
  · intro H hH beta' hbeta
    exact defect_value_clause_of_sup (y := yy) (C := D) (alpha := 1 / M) (b := b)
      halpha hb0 hb1 hycont hy0 hyb hsup hH hbeta

/-! ### The derivative clause for the hairpin pulse of the paper -/

/-- **The derivative clause of *Exact two-cap pairs* for the hairpin pulse.**
For a profile `f` smooth and positive on the line, the rear half-perimeter of
the periodized hairpin pulse, `P(H) = H - ∫_{-H/2}^{H/2} Φ(Y_H)`, is
differentiable at every period `H₀` beyond an explicit threshold, with
`P'(H₀) = 1 + O(e^{-β'H₀})` for every `β' < α/2`. -/
theorem hairpin_perimeter_derivative_clause {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfpos : ∀ t, 0 < f t) :
    ∃ (theta x : ℝ → ℝ) (alpha C b H₀ : ℝ),
      0 < alpha ∧ 0 ≤ C ∧ 0 ≤ b ∧ b < 1 ∧ 0 < H₀ ∧
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s) ∧
      (∀ s, pulseField f (theta (x s)) ≤ C * Real.exp (-alpha * |s|)) ∧
      (∀ s, pulseField f (theta (x s)) ≤ b) ∧
      (∀ H0, H₀ ≤ H0 → ∀ beta' : ℝ, beta' < alpha / 2 →
        ∃ p : ℝ, HasDerivAt
            (fun H : ℝ => H - ∫ u in (-(H / 2))..(H / 2),
              Phi (∑' m : ℤ, pulseField f (theta (x (u - m * H))))) p H0 ∧
          |p - 1| ≤ (25 * C ^ 2
              + (1 + b) / 2 / Real.sqrt (1 - ((1 + b) / 2) ^ 2) * (8 * C)
                / ((alpha / 2 - beta') * Real.exp 1)) * Real.exp (-beta' * H0)) := by
  obtain ⟨M, theta, x, hM, hmem, hval, hderiv, hxinv, hxderiv, -, hdec⟩ :=
    hairpin_pulse_exponential_decay hf hfpos
  obtain ⟨D₀, hD₀0, hD₀b⟩ := hdec 0
  obtain ⟨D₁, hD₁0, hD₁b⟩ := hdec 1
  set D : ℝ := max D₀ D₁ with hD
  have hD0 : 0 ≤ D := le_trans hD₀0 (le_max_left _ _)
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
  set yp : ℝ → ℝ := fun s => deriv (pulseField f) (theta (x s)) * yy s with hyp
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
    simpa [hyy, hyp, Function.comp, mul_comm] using h1.comp s (hxderiv s)
  have hycont : Continuous yy := by
    have hw : Continuous (fun s => theta (x s)) := by
      refine continuous_iff_continuousAt.2 fun s => ?_
      exact (hxderiv s).continuousAt
    exact ((contDiff_pulseField hf hfpos).continuous).comp hw
  have hypc : Continuous yp := by
    have hw : Continuous (fun s => theta (x s)) := by
      refine continuous_iff_continuousAt.2 fun s => ?_
      exact (hxderiv s).continuousAt
    have hdc : Continuous (deriv (pulseField f)) :=
      (contDiff_pulseField hf hfpos).continuous_deriv (by simp)
    exact (hdc.comp hw).mul hycont
  have hyb : ∀ s, yy s ≤ D * Real.exp (-(1 / M) * |s|) := by
    intro s
    have h := hD₀b s
    rw [iteratedDeriv_zero] at h
    have h1 : yy s ≤ D₀ * Real.exp (-|s| / M) := le_trans (le_abs_self _) h
    have h2 : D₀ * Real.exp (-|s| / M) ≤ D * Real.exp (-|s| / M) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    have hrw : -|s| / M = -(1 / M) * |s| := by field_simp
    rw [hrw] at h1 h2
    linarith
  have hypb : ∀ s, |yp s| ≤ D * Real.exp (-(1 / M) * |s|) := by
    intro s
    have h := hD₁b s
    rw [iteratedDeriv_one] at h
    have hderivy : deriv yy = yp := funext fun t => (hy t).deriv
    rw [hderivy] at h
    have h2 : D₁ * Real.exp (-|s| / M) ≤ D * Real.exp (-|s| / M) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
    have hrw : -|s| / M = -(1 / M) * |s| := by field_simp
    rw [hrw] at h h2
    linarith
  have halpha : 0 < 1 / M := by positivity
  refine ⟨theta, x, 1 / M, D, b, 2 * threshold (1 / M) D b,
    halpha, hD0, hb0, hb1, by linarith [threshold_pos halpha hD0 hb1],
    hmem, hval, hderiv, hxinv, hxderiv, hyb, hsup, ?_⟩
  · intro H0 hH0 beta' hbeta
    exact perimeter_derivative_clause_of_sup (y := yy) (yp := yp) (C := D)
      (alpha := 1 / M) (b := b)
      (P := fun H : ℝ => H - ∫ u in (-(H / 2))..(H / 2),
        Phi (∑' m : ℤ, yy (u - m * H)))
      halpha hb1 hy hypc hy0 hyb hypb hsup hH0 hbeta (fun H => by ring)

/-! ### The statement is not vacuous

The hypotheses are met by the constant profile `f ≡ 2`, which is smooth and
positive on the line. -/

example : ∃ H₀ : ℝ, 0 < H₀ := by
  obtain ⟨-, -, -, -, -, H₀, -, -, -, -, hH₀, -⟩ :=
    hairpin_perimeter_value_clause (f := fun _ => (2 : ℝ)) contDiff_const fun _ => two_pos
  exact ⟨H₀, hH₀⟩

end PerimeterHairpinPulse
