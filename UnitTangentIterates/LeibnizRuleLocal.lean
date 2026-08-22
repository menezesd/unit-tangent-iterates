import Mathlib
import UnitTangentIterates.LeibnizRule

/-!
# The Leibniz rule for the centred cell integral, with local hypotheses

`UnitTangentIterates/LeibnizRule.lean` proves the Leibniz rule for the centred cell
integral of the proposition *Exact two-cap pairs* under hypotheses required for
**every** period `H` and every point `s`: continuity of `g H` in `s`, and a
Lipschitz bound in the period valid on the whole line.  For the integrand the
paper differentiates, `g(H, s) = Φ(Y_H(s))` with `Y_H` the periodization of a
pulse, those hypotheses cannot hold globally: as the period shrinks to zero the
periodized profile blows up and `Φ` saturates at `1`, and the constant in the
Lipschitz bound degrades like `e^{α|s|}` as `|s|` grows.

This file restates the rule with hypotheses required only near the period at
which the derivative is taken, and only for `|s| ≤ H₀` — which is all the proof
uses, the two boundary strips being contained in that window once `H ≤ 2H₀`.

Main result: `hasDerivAt_centred_integral_local`.
-/

noncomputable section

open Filter Topology Asymptotics Set

namespace LeibnizRuleLocal

variable {g : ℝ → ℝ → ℝ} {gH : ℝ → ℝ} {H0 L : ℝ}

/-- The remainder of the Leibniz decomposition. -/
private def rem (g : ℝ → ℝ → ℝ) (H0 H : ℝ) : ℝ :=
  (∫ s in (-(H / 2))..(H / 2), (g H s - g H0 s)) -
    ∫ s in (-(H0 / 2))..(H0 / 2), (g H s - g H0 s)

private lemma rem_le (hH0 : 0 < H0) {H : ℝ} (hH : 0 < H) (hHb : H ≤ 2 * H0)
    (hcontH : Continuous (g H)) (hcont0 : Continuous (g H0))
    (hlip : ∀ s, |s| ≤ H0 → |g H s - g H0 s| ≤ L * |H - H0|) :
    |rem g H0 H| ≤ L * |H - H0| * |H - H0| := by
  set d : ℝ → ℝ := fun s => g H s - g H0 s with hd
  have hdcont : Continuous d := hcontH.sub hcont0
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
  -- both boundary strips lie in the window `|s| ≤ H₀`
  have hwin1 : ∀ s ∈ uIoc (-(H / 2)) (-(H0 / 2)), |s| ≤ H0 := by
    intro s hs
    have h1 : min (-(H / 2)) (-(H0 / 2)) < s := (Set.mem_uIoc.mp hs).elim (fun h => by
      simp only [uIoc, mem_Ioc] at *; exact lt_of_le_of_lt (min_le_left _ _) h.1) (fun h => by
      simp only [uIoc, mem_Ioc] at *; exact lt_of_le_of_lt (min_le_right _ _) h.1)
    have h2 : s ≤ max (-(H / 2)) (-(H0 / 2)) := (Set.mem_uIoc.mp hs).elim (fun h => by
      exact le_trans h.2 (le_max_right _ _)) (fun h => le_trans h.2 (le_max_left _ _))
    have hmin : -H0 ≤ min (-(H / 2)) (-(H0 / 2)) := by
      rw [le_min_iff]; constructor <;> linarith
    have hmax : max (-(H / 2)) (-(H0 / 2)) ≤ H0 := by
      rw [max_le_iff]; constructor <;> linarith
    rw [abs_le]
    constructor <;> linarith
  have hwin2 : ∀ s ∈ uIoc (H0 / 2) (H / 2), |s| ≤ H0 := by
    intro s hs
    have h1 : min (H0 / 2) (H / 2) < s := (Set.mem_uIoc.mp hs).elim (fun h => by
      simp only [uIoc, mem_Ioc] at *; exact lt_of_le_of_lt (min_le_left _ _) h.1) (fun h => by
      simp only [uIoc, mem_Ioc] at *; exact lt_of_le_of_lt (min_le_right _ _) h.1)
    have h2 : s ≤ max (H0 / 2) (H / 2) := (Set.mem_uIoc.mp hs).elim (fun h => by
      exact le_trans h.2 (le_max_right _ _)) (fun h => le_trans h.2 (le_max_left _ _))
    have hmin : -H0 ≤ min (H0 / 2) (H / 2) := by
      rw [le_min_iff]; constructor <;> linarith
    have hmax : max (H0 / 2) (H / 2) ≤ H0 := by
      rw [max_le_iff]; constructor <;> linarith
    rw [abs_le]
    constructor <;> linarith
  have hbound1 : |∫ s in (-(H / 2))..(-(H0 / 2)), d s| ≤ L * |H - H0| * |H - H0| / 2 := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -(H / 2)) (b := -(H0 / 2)) (C := L * |H - H0|) (f := d)
      (fun s hs => by simpa [Real.norm_eq_abs, hd] using hlip s (hwin1 s hs))
    have hlen : |(-(H0 / 2)) - (-(H / 2))| = |H - H0| / 2 := by
      rw [show (-(H0 / 2)) - (-(H / 2)) = (H - H0) / 2 by ring, abs_div]
      norm_num
    rw [Real.norm_eq_abs, hlen] at hb
    calc |∫ s in (-(H / 2))..(-(H0 / 2)), d s| ≤ L * |H - H0| * (|H - H0| / 2) := hb
      _ = L * |H - H0| * |H - H0| / 2 := by ring
  have hbound2 : |∫ s in (H0 / 2)..(H / 2), d s| ≤ L * |H - H0| * |H - H0| / 2 := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := H0 / 2) (b := H / 2) (C := L * |H - H0|) (f := d)
      (fun s hs => by simpa [Real.norm_eq_abs, hd] using hlip s (hwin2 s hs))
    have hlen : |H / 2 - H0 / 2| = |H - H0| / 2 := by
      rw [show H / 2 - H0 / 2 = (H - H0) / 2 by ring, abs_div]
      norm_num
    rw [Real.norm_eq_abs, hlen] at hb
    calc |∫ s in (H0 / 2)..(H / 2), d s| ≤ L * |H - H0| * (|H - H0| / 2) := hb
      _ = L * |H - H0| * |H - H0| / 2 := by ring
  rw [hrem]
  calc |(∫ s in (-(H / 2))..(-(H0 / 2)), d s) + ∫ s in (H0 / 2)..(H / 2), d s|
      ≤ |∫ s in (-(H / 2))..(-(H0 / 2)), d s| + |∫ s in (H0 / 2)..(H / 2), d s| :=
        abs_add_le _ _
    _ ≤ L * |H - H0| * |H - H0| := by linarith

private lemma hasDerivAt_rem (hH0 : 0 < H0) (hL : 0 ≤ L)
    (hcont0 : Continuous (g H0)) (hconts : ∀ᶠ H in 𝓝 H0, Continuous (g H))
    (hlip : ∀ᶠ H in 𝓝 H0, ∀ s, |s| ≤ H0 → |g H s - g H0 s| ≤ L * |H - H0|) :
    HasDerivAt (rem g H0) 0 H0 := by
  have hzero : rem g H0 H0 = 0 := by simp [rem]
  have hrange : ∀ᶠ H in 𝓝 H0, 0 < H ∧ H ≤ 2 * H0 := by
    have : Ioo (H0 / 2) (3 * H0 / 2) ∈ 𝓝 H0 := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [this] with H hH
    exact ⟨by linarith [hH.1], by linarith [hH.2]⟩
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro eps heps
  obtain ⟨delta, hdelta, hball⟩ := Metric.eventually_nhds_iff.mp (hlip.and (hconts.and hrange))
  rw [Metric.eventually_nhds_iff]
  refine ⟨min delta (eps / (L + 1)), by positivity, ?_⟩
  intro H hH
  have hH1 : dist H H0 < delta := lt_of_lt_of_le hH (min_le_left _ _)
  have hH2 : dist H H0 < eps / (L + 1) := lt_of_lt_of_le hH (min_le_right _ _)
  have hdist : |H - H0| < eps / (L + 1) := by rwa [Real.dist_eq] at hH2
  obtain ⟨hlipH, hcontH, hHr, hHb⟩ :
      (∀ s, |s| ≤ H0 → |g H s - g H0 s| ≤ L * |H - H0|) ∧ Continuous (g H) ∧
        0 < H ∧ H ≤ 2 * H0 := by
    obtain ⟨h1, h2, h3⟩ := hball hH1
    exact ⟨h1, h2, h3.1, h3.2⟩
  have hbd := rem_le hH0 hHr hHb hcontH hcont0 hlipH
  have habs : ‖rem g H0 H - rem g H0 H0 - (H - H0) • (0:ℝ)‖ = |rem g H0 H| := by
    simp [hzero]
  rw [habs, Real.norm_eq_abs]
  have hLH : L * |H - H0| ≤ eps := by
    have h1 : L * |H - H0| ≤ (L + 1) * |H - H0| := by nlinarith [abs_nonneg (H - H0)]
    have h2 : (L + 1) * |H - H0| < (L + 1) * (eps / (L + 1)) :=
      mul_lt_mul_of_pos_left hdist (by positivity)
    have h3 : (L + 1) * (eps / (L + 1)) = eps := by field_simp
    linarith
  calc |rem g H0 H| ≤ L * |H - H0| * |H - H0| := hbd
    _ ≤ eps * |H - H0| := mul_le_mul_of_nonneg_right hLH (abs_nonneg _)

/-- **The Leibniz rule for the centred cell integral, with local hypotheses.**
Let `g H₀` be continuous, let `g H` be continuous for every period `H` near
`H₀`, let `g` be Lipschitz in the period, uniformly for `|s| ≤ H₀`, for periods
near `H₀`, and suppose the fixed-endpoint integral
`H ↦ ∫_{-H₀/2}^{H₀/2} g H s ds` is differentiable at `H₀` with derivative
`∫_{-H₀/2}^{H₀/2} ∂_H g`.  Then

```
  d/dH ∫_{-H/2}^{H/2} g H s ds
    = ½ g(H₀, H₀/2) + ½ g(H₀, -H₀/2) + ∫_{-H₀/2}^{H₀/2} ∂_H g(H₀, s) ds .
```
-/
theorem hasDerivAt_centred_integral_local (hH0 : 0 < H0) (hL : 0 ≤ L)
    (hcont0 : Continuous (g H0)) (hconts : ∀ᶠ H in 𝓝 H0, Continuous (g H))
    (hlip : ∀ᶠ H in 𝓝 H0, ∀ s, |s| ≤ H0 → |g H s - g H0 s| ≤ L * |H - H0|)
    (hparam : HasDerivAt (fun H => ∫ s in (-(H0 / 2))..(H0 / 2), g H s)
      (∫ s in (-(H0 / 2))..(H0 / 2), gH s) H0) :
    HasDerivAt (fun H => ∫ s in (-(H / 2))..(H / 2), g H s)
      (g H0 (H0 / 2) / 2 + g H0 (-(H0 / 2)) / 2 +
        ∫ s in (-(H0 / 2))..(H0 / 2), gH s) H0 := by
  have hprim : ∀ x : ℝ, HasDerivAt (fun z => ∫ s in (0:ℝ)..z, g H0 s) (g H0 x) x := fun x =>
    (hcont0.integral_hasStrictDerivAt (0:ℝ) x).hasDerivAt
  have hu : HasDerivAt (fun H => ∫ s in (-(H / 2))..(H / 2), g H0 s)
      (g H0 (H0 / 2) / 2 + g H0 (-(H0 / 2)) / 2) H0 := by
    have h1 : HasDerivAt (fun H : ℝ => ∫ s in (0:ℝ)..(H / 2), g H0 s)
        (g H0 (H0 / 2) * (1 / 2)) H0 := by
      simpa [Function.comp] using (hprim (H0 / 2)).comp H0 ((hasDerivAt_id H0).div_const 2)
    have h2 : HasDerivAt (fun H : ℝ => ∫ s in (0:ℝ)..(-(H / 2)), g H0 s)
        (g H0 (-(H0 / 2)) * (-(1 / 2))) H0 := by
      have hneg : HasDerivAt (fun H : ℝ => -(H / 2)) (-(1 / 2)) H0 := by
        simpa using ((hasDerivAt_id H0).div_const 2).neg
      simpa [Function.comp] using (hprim (-(H0 / 2))).comp H0 hneg
    have hsplit : ∀ H : ℝ, (∫ s in (-(H / 2))..(H / 2), g H0 s) =
        (∫ s in (0:ℝ)..(H / 2), g H0 s) - ∫ s in (0:ℝ)..(-(H / 2)), g H0 s := by
      intro H
      rw [← intervalIntegral.integral_interval_sub_left
        (hcont0.intervalIntegrable _ _) (hcont0.intervalIntegrable _ _)]
    have hsub := h1.sub h2
    rw [funext hsplit]
    convert hsub using 1
    ring
  have hR := hasDerivAt_rem hH0 hL hcont0 hconts hlip
  have hsum := ((hu.add hparam).add hR).sub_const
    (∫ s in (-(H0 / 2))..(H0 / 2), g H0 s)
  rw [add_zero] at hsum
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hconts] with H hcontH
  have e1 : (∫ s in (-(H / 2))..(H / 2), (g H s - g H0 s)) =
      (∫ s in (-(H / 2))..(H / 2), g H s) - ∫ s in (-(H / 2))..(H / 2), g H0 s :=
    intervalIntegral.integral_sub (hcontH.intervalIntegrable _ _)
      (hcont0.intervalIntegrable _ _)
  have e2 : (∫ s in (-(H0 / 2))..(H0 / 2), (g H s - g H0 s)) =
      (∫ s in (-(H0 / 2))..(H0 / 2), g H s) - ∫ s in (-(H0 / 2))..(H0 / 2), g H0 s :=
    intervalIntegral.integral_sub (hcontH.intervalIntegrable _ _)
      (hcont0.intervalIntegrable _ _)
  simp only [Pi.add_apply, rem, e1, e2]
  ring

end LeibnizRuleLocal
