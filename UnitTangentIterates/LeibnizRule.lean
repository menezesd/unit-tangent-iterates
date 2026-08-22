import Mathlib

/-!
# Differentiating the centred cell integral in the period

The proposition *Exact two-cap pairs* of the paper *A Noncircular Oval with
Convex Unit-Tangent Iterates* differentiates the perimeter defect

```
   H - P(H) = ∫_{-H/2}^{H/2} Φ(Y_H(s)) ds
```

in the period `H`, "holding `s` fixed in the centred integral", and obtains

```
   d/dH (H - P(H)) = ½Φ(Y_H(H/2)) + ½Φ(Y_H(-H/2))
                      + ∫_{-H/2}^{H/2} ∂_H(Φ ∘ Y_H)(s) ds .
```

This file formalizes that Leibniz rule for a centred interval whose endpoints
move with the parameter.  The fixed-endpoint parametric derivative is taken as
a hypothesis (it is the standard differentiation under the integral sign); what
is proved here is that the two boundary terms are exactly the extra
contribution of the moving endpoints, the remainder being quadratic in the
increment.

Main result: `hasDerivAt_centred_integral`.
-/

noncomputable section

open Filter Topology Asymptotics

namespace LeibnizRule

variable {g : ℝ → ℝ → ℝ} {gH : ℝ → ℝ} {H0 L : ℝ}

/-- The remainder of the Leibniz decomposition. -/
private def rem (g : ℝ → ℝ → ℝ) (H0 H : ℝ) : ℝ :=
  (∫ s in (-(H / 2))..(H / 2), (g H s - g H0 s)) -
    ∫ s in (-(H0 / 2))..(H0 / 2), (g H s - g H0 s)

private lemma rem_le (hcont : ∀ H, Continuous (g H))
    (hlip : ∀ H s, |g H s - g H0 s| ≤ L * |H - H0|) (H : ℝ) :
    |rem g H0 H| ≤ L * |H - H0| * |H - H0| := by
  have hL : 0 ≤ L * |H0 - H0| := le_trans (abs_nonneg _) (hlip H0 0)
  have hLnn : 0 ≤ L * |H - H0| := le_trans (abs_nonneg _) (hlip H 0)
  set d : ℝ → ℝ := fun s => g H s - g H0 s with hd
  have hdcont : Continuous d := (hcont H).sub (hcont H0)
  have hsplit1 : (∫ s in (-(H / 2))..(H / 2), d s) =
      (∫ s in (-(H / 2))..(-(H0 / 2)), d s) + ∫ s in (-(H0 / 2))..(H / 2), d s :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hdcont.intervalIntegrable _ _) (hdcont.intervalIntegrable _ _)).symm
  have hsplit2 : (∫ s in (-(H0 / 2))..(H / 2), d s) =
      (∫ s in (-(H0 / 2))..(H0 / 2), d s) + ∫ s in (H0 / 2)..(H / 2), d s :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hdcont.intervalIntegrable _ _) (hdcont.intervalIntegrable _ _)).symm
  have hrem : rem g H0 H =
      (∫ s in (-(H / 2))..(-(H0 / 2)), d s) + ∫ s in (H0 / 2)..(H / 2), d s := by
    simp only [rem, hd] at *
    rw [hsplit1, hsplit2]
    ring
  have hbound1 : |∫ s in (-(H / 2))..(-(H0 / 2)), d s| ≤ L * |H - H0| * |H - H0| / 2 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -(H / 2)) (b := -(H0 / 2)) (C := L * |H - H0|) (f := d)
      (fun s _ => by simpa [Real.norm_eq_abs, hd] using hlip H s)
    have hlen : |(-(H0 / 2)) - (-(H / 2))| = |H - H0| / 2 := by
      rw [show (-(H0 / 2)) - (-(H / 2)) = (H - H0) / 2 by ring, abs_div]
      norm_num
    rw [Real.norm_eq_abs, hlen] at this
    calc |∫ s in (-(H / 2))..(-(H0 / 2)), d s| ≤ L * |H - H0| * (|H - H0| / 2) := this
      _ = L * |H - H0| * |H - H0| / 2 := by ring
  have hbound2 : |∫ s in (H0 / 2)..(H / 2), d s| ≤ L * |H - H0| * |H - H0| / 2 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := H0 / 2) (b := H / 2) (C := L * |H - H0|) (f := d)
      (fun s _ => by simpa [Real.norm_eq_abs, hd] using hlip H s)
    have hlen : |H / 2 - H0 / 2| = |H - H0| / 2 := by
      rw [show H / 2 - H0 / 2 = (H - H0) / 2 by ring, abs_div]
      norm_num
    rw [Real.norm_eq_abs, hlen] at this
    calc |∫ s in (H0 / 2)..(H / 2), d s| ≤ L * |H - H0| * (|H - H0| / 2) := this
      _ = L * |H - H0| * |H - H0| / 2 := by ring
  rw [hrem]
  calc |(∫ s in (-(H / 2))..(-(H0 / 2)), d s) + ∫ s in (H0 / 2)..(H / 2), d s|
      ≤ |∫ s in (-(H / 2))..(-(H0 / 2)), d s| + |∫ s in (H0 / 2)..(H / 2), d s| :=
        abs_add_le _ _
    _ ≤ L * |H - H0| * |H - H0| := by linarith

private lemma hasDerivAt_rem (hcont : ∀ H, Continuous (g H))
    (hlip : ∀ H s, |g H s - g H0 s| ≤ L * |H - H0|) :
    HasDerivAt (rem g H0) 0 H0 := by
  have hL : 0 ≤ L := by
    have h := hlip (H0 + 1) 0
    have : (0:ℝ) ≤ L * |H0 + 1 - H0| := le_trans (abs_nonneg _) h
    simpa using this
  have hzero : rem g H0 H0 = 0 := by simp [rem]
  rw [hasDerivAt_iff_isLittleO]
  rw [Asymptotics.isLittleO_iff]
  intro eps heps
  rw [Metric.eventually_nhds_iff]
  refine ⟨eps / (L + 1), by positivity, ?_⟩
  intro H hH
  have hdist : |H - H0| < eps / (L + 1) := by
    rwa [Real.dist_eq] at hH
  have hbd := rem_le hcont hlip H
  have habs : ‖rem g H0 H - rem g H0 H0 - (H - H0) • (0:ℝ)‖ = |rem g H0 H| := by
    simp [hzero]
  rw [habs, Real.norm_eq_abs]
  have hLH : L * |H - H0| ≤ eps := by
    have h1 : L * |H - H0| ≤ (L + 1) * |H - H0| := by nlinarith [abs_nonneg (H - H0)]
    have h2 : (L + 1) * |H - H0| < (L + 1) * (eps / (L + 1)) := by
      apply mul_lt_mul_of_pos_left hdist (by positivity)
    have h3 : (L + 1) * (eps / (L + 1)) = eps := by field_simp
    linarith
  calc |rem g H0 H| ≤ L * |H - H0| * |H - H0| := hbd
    _ ≤ eps * |H - H0| := mul_le_mul_of_nonneg_right hLH (abs_nonneg _)

/-- **The Leibniz rule for the centred cell integral.**  Let `g H s` be
continuous in `s` for each period `H`, Lipschitz in `H` uniformly in `s`, and
suppose the fixed-endpoint integral `H ↦ ∫_{-H₀/2}^{H₀/2} g H s ds` is
differentiable at `H₀` with derivative `∫_{-H₀/2}^{H₀/2} ∂_H g`.  Then the
centred integral with moving endpoints is differentiable at `H₀` and

```
  d/dH ∫_{-H/2}^{H/2} g H s ds
    = ½ g(H₀, H₀/2) + ½ g(H₀, -H₀/2) + ∫_{-H₀/2}^{H₀/2} ∂_H g(H₀, s) ds .
```
-/
theorem hasDerivAt_centred_integral (hcont : ∀ H, Continuous (g H))
    (hlip : ∀ H s, |g H s - g H0 s| ≤ L * |H - H0|)
    (hparam : HasDerivAt (fun H => ∫ s in (-(H0 / 2))..(H0 / 2), g H s)
      (∫ s in (-(H0 / 2))..(H0 / 2), gH s) H0) :
    HasDerivAt (fun H => ∫ s in (-(H / 2))..(H / 2), g H s)
      (g H0 (H0 / 2) / 2 + g H0 (-(H0 / 2)) / 2 +
        ∫ s in (-(H0 / 2))..(H0 / 2), gH s) H0 := by
  -- the moving-endpoint integral of the frozen integrand
  have hprim : ∀ x : ℝ, HasDerivAt (fun y => ∫ s in (0:ℝ)..y, g H0 s) (g H0 x) x := fun x =>
    ((hcont H0).integral_hasStrictDerivAt (0:ℝ) x).hasDerivAt
  have hu : HasDerivAt (fun H => ∫ s in (-(H / 2))..(H / 2), g H0 s)
      (g H0 (H0 / 2) / 2 + g H0 (-(H0 / 2)) / 2) H0 := by
    have h1 : HasDerivAt (fun H : ℝ => ∫ s in (0:ℝ)..(H / 2), g H0 s)
        (g H0 (H0 / 2) * (1 / 2)) H0 := by
      simpa [Function.comp] using (hprim (H0 / 2)).comp H0 ((hasDerivAt_id H0).div_const 2)
    have h2 : HasDerivAt (fun H : ℝ => ∫ s in (0:ℝ)..(-(H / 2)), g H0 s)
        (g H0 (-(H0 / 2)) * (-(1 / 2))) H0 := by
      have : HasDerivAt (fun H : ℝ => -(H / 2)) (-(1 / 2)) H0 := by
        simpa using ((hasDerivAt_id H0).div_const 2).neg
      simpa [Function.comp] using (hprim (-(H0 / 2))).comp H0 this
    have hsplit : ∀ H : ℝ, (∫ s in (-(H / 2))..(H / 2), g H0 s) =
        (∫ s in (0:ℝ)..(H / 2), g H0 s) - ∫ s in (0:ℝ)..(-(H / 2)), g H0 s := by
      intro H
      rw [← intervalIntegral.integral_interval_sub_left
        ((hcont H0).intervalIntegrable _ _) ((hcont H0).intervalIntegrable _ _)]
    have := h1.sub h2
    rw [funext hsplit]
    convert this using 1
    ring
  -- the algebraic decomposition
  have hdecomp : ∀ H : ℝ, (∫ s in (-(H / 2))..(H / 2), g H s) =
      (∫ s in (-(H / 2))..(H / 2), g H0 s) + (∫ s in (-(H0 / 2))..(H0 / 2), g H s) +
        rem g H0 H - ∫ s in (-(H0 / 2))..(H0 / 2), g H0 s := by
    intro H
    have e1 : (∫ s in (-(H / 2))..(H / 2), (g H s - g H0 s)) =
        (∫ s in (-(H / 2))..(H / 2), g H s) - ∫ s in (-(H / 2))..(H / 2), g H0 s :=
      intervalIntegral.integral_sub ((hcont H).intervalIntegrable _ _)
        ((hcont H0).intervalIntegrable _ _)
    have e2 : (∫ s in (-(H0 / 2))..(H0 / 2), (g H s - g H0 s)) =
        (∫ s in (-(H0 / 2))..(H0 / 2), g H s) - ∫ s in (-(H0 / 2))..(H0 / 2), g H0 s :=
      intervalIntegral.integral_sub ((hcont H).intervalIntegrable _ _)
        ((hcont H0).intervalIntegrable _ _)
    simp only [rem, e1, e2]
    ring
  have hR := hasDerivAt_rem hcont hlip (L := L)
  have hsum := ((hu.add hparam).add hR).sub_const
    (∫ s in (-(H0 / 2))..(H0 / 2), g H0 s)
  rw [funext hdecomp]
  convert hsum using 1
  ring

/-- A sanity check of the formula on the example `g(H, s) = H`, where the
centred integral is `H²` and the derivative is `2H₀ = ½H₀ + ½H₀ + H₀`. -/
example (H0 : ℝ) :
    HasDerivAt (fun H : ℝ => ∫ _s in (-(H / 2))..(H / 2), H) (2 * H0) H0 := by
  have hparam : HasDerivAt (fun H : ℝ => ∫ _s in (-(H0 / 2))..(H0 / 2), H)
      (∫ _s in (-(H0 / 2))..(H0 / 2), (1:ℝ)) H0 := by
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    have : (H0 / 2 - -(H0 / 2)) = H0 := by ring
    rw [this]
    simpa [mul_comm] using (hasDerivAt_id H0).mul_const H0
  have := hasDerivAt_centred_integral (g := fun H _s => H) (gH := fun _ => (1:ℝ)) (L := 1)
    (H0 := H0) (fun H => continuous_const) (fun H s => by simp) hparam
  simp only [intervalIntegral.integral_const, smul_eq_mul] at this ⊢
  convert this using 1
  ring

end LeibnizRule
