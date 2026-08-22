import Mathlib
import UnitTangentIterates.RearTrack

/-!
# The derivative of an integral with a moving endpoint, and the rear period

`GaugeGeometryPathVariable.exists_normalPath_of_gauge_geometry_var` asks of the
rear arclength period `Q t = ∫₀^{P t} cos δ(t, ·)` only that it be
differentiable in the time.  This file supplies that derivative, through the
general Leibniz rule for an integral whose *upper endpoint* moves with the
parameter:

```
  d/dt ∫₀^{b(t)} g(t, s) ds = g(t₀, b(t₀)) b'(t₀) + ∫₀^{b(t₀)} ∂_t g(t₀, s) ds .
```

As in `LeibnizRule.lean` the fixed-endpoint parametric derivative is an input —
it is the standard differentiation under the integral sign — and what is proved
here is the endpoint term: the remainder

`∫_{b(t₀)}^{b(t)} (g(t, s) − g(t₀, s)) ds`

is `O(|t − t₀|²)`, because the integrand is `O(|t − t₀|)` uniformly in `s` while
the interval of integration is `O(|t − t₀|)` long.

Main results:

* `hasDerivAt_moving_endpoint_integral` — the Leibniz rule above;
* `hasDerivAt_rearPeriod` — its instance for the rear arclength period
  `Q t = rearArclength (δ t) (P t)`, whose derivative is
  `cos δ(t₀, P t₀) · P'(t₀) + ∫₀^{P t₀} ∂_t cos δ(t₀, s) ds`.
-/

noncomputable section

open Set MeasureTheory intervalIntegral

namespace RearPeriodDeriv

variable {g : ℝ → ℝ → ℝ} {gt : ℝ → ℝ} {b : ℝ → ℝ} {b' L t0 : ℝ}

/-- The remainder of the decomposition: the piece of the integral over the part
of the interval swept by the moving endpoint, with the value at the base point
subtracted. -/
private def rem (g : ℝ → ℝ → ℝ) (b : ℝ → ℝ) (t0 t : ℝ) : ℝ :=
  ∫ s in (b t0)..(b t), (g t s - g t0 s)

/-- The remainder is quadratically small: its integrand is `O(|t − t₀|)` and the
interval of integration is `O(|t − t₀|)` long. -/
private theorem abs_rem_le (hlip : ∀ r s, |g r s - g t0 s| ≤ L * |r - t0|) (t : ℝ) :
    |rem g b t0 t| ≤ L * |t - t0| * |b t - b t0| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s => g t s - g t0 s) (a := b t0) (b := b t) (C := L * |t - t0|)
    (fun s _ => by simpa [Real.norm_eq_abs] using hlip t s)
  simpa [rem, Real.norm_eq_abs] using h

/-- The remainder has vanishing derivative at the base point. -/
private theorem hasDerivAt_rem (hlip : ∀ r s, |g r s - g t0 s| ≤ L * |r - t0|)
    (hb : HasDerivAt b b' t0) : HasDerivAt (fun r => rem g b t0 r) 0 t0 := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ᶠ t in nhds t0, |b t - b t0| ≤ C * |t - t0| := by
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hb.hasFDerivAt.isBigO_sub
    exact ⟨C, by simpa [Real.norm_eq_abs] using hC⟩
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro eps heps
  have hd : (0:ℝ) < eps / (|L| * |C| + 1) := by positivity
  filter_upwards [hC, Metric.ball_mem_nhds t0 hd] with t hCt hball
  have hdist : |t - t0| < eps / (|L| * |C| + 1) := by
    rw [Metric.mem_ball, Real.dist_eq] at hball
    exact hball
  have hrem0 : rem g b t0 t0 = 0 := by simp [rem]
  have h1 : |rem g b t0 t| ≤ L * |t - t0| * |b t - b t0| := abs_rem_le hlip t
  have hLnn : 0 ≤ L * |t - t0| := le_trans (abs_nonneg _) (hlip t 0)
  have h2 : L * |t - t0| ≤ |L| * |t - t0| :=
    mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _)
  have h3 : |b t - b t0| ≤ |C| * |t - t0| :=
    le_trans hCt (mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _))
  have h4 : |rem g b t0 t| ≤ (|L| * |t - t0|) * (|C| * |t - t0|) := by
    calc |rem g b t0 t| ≤ L * |t - t0| * |b t - b t0| := h1
      _ ≤ (|L| * |t - t0|) * |b t - b t0| :=
          mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
      _ ≤ (|L| * |t - t0|) * (|C| * |t - t0|) := by
          refine mul_le_mul_of_nonneg_left h3 ?_
          positivity
  have h5 : |L| * |C| * |t - t0| ≤ eps := by
    have hden : (0:ℝ) < |L| * |C| + 1 := by positivity
    have hK : (0:ℝ) ≤ |L| * |C| := by positivity
    have hstep : |L| * |C| * |t - t0| ≤ |L| * |C| * (eps / (|L| * |C| + 1)) :=
      mul_le_mul_of_nonneg_left hdist.le hK
    refine hstep.trans ?_
    rw [mul_div_assoc', div_le_iff₀ hden]
    nlinarith [heps.le]
  have h6 : (|L| * |t - t0|) * (|C| * |t - t0|) ≤ eps * |t - t0| := by
    have : (|L| * |t - t0|) * (|C| * |t - t0|) = (|L| * |C| * |t - t0|) * |t - t0| := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right h5 (abs_nonneg _)
  simpa [hrem0, Real.norm_eq_abs] using le_trans h4 h6

/-- **The Leibniz rule for an integral with a moving endpoint.**  If `g` is
continuous in the space variable, Lipschitz in the parameter uniformly in the
space variable, the endpoint `b` is differentiable, and the fixed-endpoint
integral is differentiable with the expected derivative, then

`d/dt ∫₀^{b t} g t s ds = g t₀ (b t₀) · b'(t₀) + ∫₀^{b t₀} ∂_t g(t₀, s) ds`. -/
theorem hasDerivAt_moving_endpoint_integral (hcont : ∀ r, Continuous (g r))
    (hlip : ∀ r s, |g r s - g t0 s| ≤ L * |r - t0|)
    (hb : HasDerivAt b b' t0)
    (hparam : HasDerivAt (fun r => ∫ s in (0:ℝ)..(b t0), g r s)
      (∫ s in (0:ℝ)..(b t0), gt s) t0) :
    HasDerivAt (fun r => ∫ s in (0:ℝ)..(b r), g r s)
      (g t0 (b t0) * b' + ∫ s in (0:ℝ)..(b t0), gt s) t0 := by
  -- the moving endpoint, with the integrand frozen at the base point
  have hprim : ∀ x : ℝ, HasDerivAt (fun y => ∫ s in (0:ℝ)..y, g t0 s) (g t0 x) x := fun x =>
    ((hcont t0).integral_hasStrictDerivAt (0:ℝ) x).hasDerivAt
  have hA : HasDerivAt (fun r => ∫ s in (0:ℝ)..(b r), g t0 s) (g t0 (b t0) * b') t0 := by
    simpa [Function.comp] using (hprim (b t0)).comp t0 hb
  -- the remainder
  have hrem : HasDerivAt (fun r => rem g b t0 r) 0 t0 := hasDerivAt_rem hlip hb
  -- the algebraic decomposition
  have hdecomp : ∀ t : ℝ, (∫ s in (0:ℝ)..(b t), g t s)
      = (∫ s in (0:ℝ)..(b t), g t0 s) + (∫ s in (0:ℝ)..(b t0), g t s) + rem g b t0 t
        - ∫ s in (0:ℝ)..(b t0), g t0 s := by
    intro t
    have e1 : rem g b t0 t
        = (∫ s in (b t0)..(b t), g t s) - ∫ s in (b t0)..(b t), g t0 s :=
      intervalIntegral.integral_sub ((hcont t).intervalIntegrable _ _)
        ((hcont t0).intervalIntegrable _ _)
    have e2 : (∫ s in (0:ℝ)..(b t0), g t s) + (∫ s in (b t0)..(b t), g t s)
        = ∫ s in (0:ℝ)..(b t), g t s :=
      intervalIntegral.integral_add_adjacent_intervals ((hcont t).intervalIntegrable _ _)
        ((hcont t).intervalIntegrable _ _)
    have e3 : (∫ s in (0:ℝ)..(b t0), g t0 s) + (∫ s in (b t0)..(b t), g t0 s)
        = ∫ s in (0:ℝ)..(b t), g t0 s :=
      intervalIntegral.integral_add_adjacent_intervals ((hcont t0).intervalIntegrable _ _)
        ((hcont t0).intervalIntegrable _ _)
    rw [e1]
    linarith [e2, e3]
  rw [funext hdecomp]
  simpa using ((hA.add hparam).add hrem).sub_const (∫ s in (0:ℝ)..(b t0), g t0 s)

/-- **The derivative of the rear arclength period.**  For a family of steering
angles `δ` and a front period `P`, the rear period
`Q t = rearArclength (δ t) (P t) = ∫₀^{P t} cos δ(t, s) ds` is differentiable
wherever `P` is and the fixed-endpoint integral is, with

`Q'(t₀) = cos δ(t₀, P t₀) · P'(t₀) + ∫₀^{P t₀} ∂_t cos δ(t₀, s) ds`. -/
theorem hasDerivAt_rearPeriod {delta : ℝ → ℝ → ℝ} {dtc : ℝ → ℝ} {P : ℝ → ℝ} {P' : ℝ}
    (hcont : ∀ r, Continuous (delta r))
    (hlip : ∀ r s, |Real.cos (delta r s) - Real.cos (delta t0 s)| ≤ L * |r - t0|)
    (hP : HasDerivAt P P' t0)
    (hparam : HasDerivAt (fun r => ∫ s in (0:ℝ)..(P t0), Real.cos (delta r s))
      (∫ s in (0:ℝ)..(P t0), dtc s) t0) :
    HasDerivAt (fun r => RearTrack.rearArclength (delta r) (P r))
      (Real.cos (delta t0 (P t0)) * P' + ∫ s in (0:ℝ)..(P t0), dtc s) t0 :=
  hasDerivAt_moving_endpoint_integral
    (g := fun r s => Real.cos (delta r s))
    (fun r => Real.continuous_cos.comp (hcont r)) hlip hP hparam

/-! ### A local form of the Lipschitz hypothesis

When the family is written in a parameter in which the period moves, the
parameter Lipschitz bound holds only on a *bounded* range of the space
variable: two slices are compared at the points `s / P(a)` and `s / P(b)` of the
normalized circle, which drift apart as `|s|` grows.  Only the values near the
moving endpoint matter for the endpoint term, so the following variants ask for
the bound only on `[-R, R]`. -/

/-- The remainder bound with the Lipschitz hypothesis only on `[-R, R]`. -/
private theorem abs_rem_le_local {R t : ℝ}
    (hlip : ∀ r s, |s| ≤ R → |g r s - g t0 s| ≤ L * |r - t0|)
    (ht0R : |b t0| ≤ R) (htR : |b t| ≤ R) :
    |rem g b t0 t| ≤ L * |t - t0| * |b t - b t0| := by
  have hsub : ∀ s ∈ Set.uIoc (b t0) (b t), |s| ≤ R := by
    intro s hs
    rw [Set.uIoc] at hs
    have h1 : min (b t0) (b t) ≤ s := le_of_lt hs.1
    have h2 : s ≤ max (b t0) (b t) := hs.2
    rw [abs_le] at ht0R htR ⊢
    refine ⟨?_, ?_⟩
    · have hmin : -R ≤ min (b t0) (b t) := le_min ht0R.1 htR.1
      linarith
    · have hmax : max (b t0) (b t) ≤ R := max_le ht0R.2 htR.2
      linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s => g t s - g t0 s) (a := b t0) (b := b t) (C := L * |t - t0|)
    (fun s hs => by simpa [Real.norm_eq_abs] using hlip t s (hsub s hs))
  simpa [rem, Real.norm_eq_abs] using h

/-- The remainder has vanishing derivative at the base point, under the local
Lipschitz hypothesis. -/
private theorem hasDerivAt_rem_local {R : ℝ} (hbR : |b t0| < R)
    (hlip : ∀ r s, |s| ≤ R → |g r s - g t0 s| ≤ L * |r - t0|)
    (hb : HasDerivAt b b' t0) : HasDerivAt (fun r => rem g b t0 r) 0 t0 := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ᶠ t in nhds t0, |b t - b t0| ≤ C * |t - t0| := by
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hb.hasFDerivAt.isBigO_sub
    exact ⟨C, by simpa [Real.norm_eq_abs] using hC⟩
  have hopen : {x : ℝ | |x| < R} ∈ nhds (b t0) :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds hbR
  have hev : ∀ᶠ t in nhds t0, |b t| ≤ R := by
    have hmem : b ⁻¹' {x : ℝ | |x| < R} ∈ nhds t0 := hb.continuousAt hopen
    exact Filter.Eventually.mono hmem (fun t ht => le_of_lt ht)
  have ht0R : |b t0| ≤ R := le_of_lt hbR
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro eps heps
  have hd : (0:ℝ) < eps / (|L| * |C| + 1) := by positivity
  filter_upwards [hC, hev, Metric.ball_mem_nhds t0 hd] with t hCt htR hball
  have hdist : |t - t0| < eps / (|L| * |C| + 1) := by
    rw [Metric.mem_ball, Real.dist_eq] at hball
    exact hball
  have hrem0 : rem g b t0 t0 = 0 := by simp [rem]
  have h1 : |rem g b t0 t| ≤ L * |t - t0| * |b t - b t0| := abs_rem_le_local hlip ht0R htR
  have h2 : L * |t - t0| ≤ |L| * |t - t0| :=
    mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _)
  have h3 : |b t - b t0| ≤ |C| * |t - t0| :=
    le_trans hCt (mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _))
  have h4 : |rem g b t0 t| ≤ (|L| * |t - t0|) * (|C| * |t - t0|) := by
    calc |rem g b t0 t| ≤ L * |t - t0| * |b t - b t0| := h1
      _ ≤ (|L| * |t - t0|) * |b t - b t0| :=
          mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
      _ ≤ (|L| * |t - t0|) * (|C| * |t - t0|) := by
          refine mul_le_mul_of_nonneg_left h3 ?_
          positivity
  have h5 : |L| * |C| * |t - t0| ≤ eps := by
    have hden : (0:ℝ) < |L| * |C| + 1 := by positivity
    have hK : (0:ℝ) ≤ |L| * |C| := by positivity
    have hstep : |L| * |C| * |t - t0| ≤ |L| * |C| * (eps / (|L| * |C| + 1)) :=
      mul_le_mul_of_nonneg_left hdist.le hK
    refine hstep.trans ?_
    rw [mul_div_assoc', div_le_iff₀ hden]
    nlinarith [heps.le]
  have h6 : (|L| * |t - t0|) * (|C| * |t - t0|) ≤ eps * |t - t0| := by
    have hrw : (|L| * |t - t0|) * (|C| * |t - t0|) = (|L| * |C| * |t - t0|) * |t - t0| := by
      ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right h5 (abs_nonneg _)
  simpa [hrem0, Real.norm_eq_abs] using le_trans h4 h6

/-- **The Leibniz rule for an integral with a moving endpoint, with a local
Lipschitz hypothesis.**  The parameter Lipschitz bound is only needed for space
variables in `[-R, R]`, with the endpoint `b t₀` in the interior of that
range. -/
theorem hasDerivAt_moving_endpoint_integral_local {R : ℝ} (hcont : ∀ r, Continuous (g r))
    (hbR : |b t0| < R)
    (hlip : ∀ r s, |s| ≤ R → |g r s - g t0 s| ≤ L * |r - t0|)
    (hb : HasDerivAt b b' t0)
    (hparam : HasDerivAt (fun r => ∫ s in (0:ℝ)..(b t0), g r s)
      (∫ s in (0:ℝ)..(b t0), gt s) t0) :
    HasDerivAt (fun r => ∫ s in (0:ℝ)..(b r), g r s)
      (g t0 (b t0) * b' + ∫ s in (0:ℝ)..(b t0), gt s) t0 := by
  have hprim : ∀ x : ℝ, HasDerivAt (fun y => ∫ s in (0:ℝ)..y, g t0 s) (g t0 x) x := fun x =>
    ((hcont t0).integral_hasStrictDerivAt (0:ℝ) x).hasDerivAt
  have hA : HasDerivAt (fun r => ∫ s in (0:ℝ)..(b r), g t0 s) (g t0 (b t0) * b') t0 := by
    simpa [Function.comp] using (hprim (b t0)).comp t0 hb
  have hrem : HasDerivAt (fun r => rem g b t0 r) 0 t0 := hasDerivAt_rem_local hbR hlip hb
  have hdecomp : ∀ t : ℝ, (∫ s in (0:ℝ)..(b t), g t s)
      = (∫ s in (0:ℝ)..(b t), g t0 s) + (∫ s in (0:ℝ)..(b t0), g t s) + rem g b t0 t
        - ∫ s in (0:ℝ)..(b t0), g t0 s := by
    intro t
    have e1 : rem g b t0 t
        = (∫ s in (b t0)..(b t), g t s) - ∫ s in (b t0)..(b t), g t0 s :=
      intervalIntegral.integral_sub ((hcont t).intervalIntegrable _ _)
        ((hcont t0).intervalIntegrable _ _)
    have e2 : (∫ s in (0:ℝ)..(b t0), g t s) + (∫ s in (b t0)..(b t), g t s)
        = ∫ s in (0:ℝ)..(b t), g t s :=
      intervalIntegral.integral_add_adjacent_intervals ((hcont t).intervalIntegrable _ _)
        ((hcont t).intervalIntegrable _ _)
    have e3 : (∫ s in (0:ℝ)..(b t0), g t0 s) + (∫ s in (b t0)..(b t), g t0 s)
        = ∫ s in (0:ℝ)..(b t), g t0 s :=
      intervalIntegral.integral_add_adjacent_intervals ((hcont t0).intervalIntegrable _ _)
        ((hcont t0).intervalIntegrable _ _)
    rw [e1]
    linarith [e2, e3]
  rw [funext hdecomp]
  simpa using ((hA.add hparam).add hrem).sub_const (∫ s in (0:ℝ)..(b t0), g t0 s)

/-- **The derivative of the rear arclength period, with a local Lipschitz
hypothesis.** -/
theorem hasDerivAt_rearPeriod_local {delta : ℝ → ℝ → ℝ} {dtc : ℝ → ℝ} {P : ℝ → ℝ} {P' R : ℝ}
    (hcont : ∀ r, Continuous (delta r)) (hPR : |P t0| < R)
    (hlip : ∀ r s, |s| ≤ R → |Real.cos (delta r s) - Real.cos (delta t0 s)| ≤ L * |r - t0|)
    (hP : HasDerivAt P P' t0)
    (hparam : HasDerivAt (fun r => ∫ s in (0:ℝ)..(P t0), Real.cos (delta r s))
      (∫ s in (0:ℝ)..(P t0), dtc s) t0) :
    HasDerivAt (fun r => RearTrack.rearArclength (delta r) (P r))
      (Real.cos (delta t0 (P t0)) * P' + ∫ s in (0:ℝ)..(P t0), dtc s) t0 :=
  hasDerivAt_moving_endpoint_integral_local
    (g := fun r s => Real.cos (delta r s))
    (fun r => Real.continuous_cos.comp (hcont r)) hPR hlip hP hparam

/-- **The hypotheses are non-vacuous.**  For `g(t,s) = t` and `b(t) = t` the
rule gives `d/dt ∫₀^t t ds = d/dt t² = 2t`. -/
example (t0 : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ _s in (0:ℝ)..r, r) (t0 + t0) t0 := by
  have hparam : HasDerivAt (fun r : ℝ => ∫ _s in (0:ℝ)..(id t0), r)
      (∫ _s in (0:ℝ)..(id t0), (1:ℝ)) t0 := by
    simp only [intervalIntegral.integral_const, smul_eq_mul, id, sub_zero, mul_one]
    simpa using (hasDerivAt_id t0).const_mul t0
  have h := hasDerivAt_moving_endpoint_integral (g := fun r _ => r) (gt := fun _ => 1)
    (b := id) (b' := 1) (L := 1) (t0 := t0)
    (fun _ => continuous_const) (fun r s => by simp) (hasDerivAt_id t0) hparam
  simpa using h

end RearPeriodDeriv
