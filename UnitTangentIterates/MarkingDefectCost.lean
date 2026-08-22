import Mathlib
import UnitTangentIterates.MarkingDeviation
import UnitTangentIterates.GlobalODE
import UnitTangentIterates.GaugeRate

/-!
# The defect of a gauge marking is controlled by the cost of the path

`MarkingDeviation.lean` bounds the deviation of a gauge marking from the affine
marking by the displacement of the gauge flow plus the change of the period, and
`SelInvMarkingDefect.lean` turns such a bound `ε` into a uniform comparison of
the two marked selected inverses of the ends of a normal path.  Neither file
*produces* `ε`: the displacement of the gauge flow along an arbitrary normal
path was not estimated.

This file produces it, from the one structural fact the family of selected rears
supplies: the tangential component `ξ` of the motion **vanishes at the base
point** (`GaugeBaseFlow.lean`), and its arclength derivative is bounded by the
geometry (`RearOwnTangential.abs_partialX_frameTangential_le`).  Hence the field
of the gauge flow grows at most linearly,

```
  |R(t, x)| ≤ C t · |x| ,
```

with `C t` proportional to the normal velocity of the slice at time `t`, i.e. to
the cost density of the path.  A flow of such a field started from the affine
marking is *monotone* in the parameter — flow lines of a Lipschitz field cannot
cross — and, being quasi-periodic with the period `L t = Φ t 1`, it therefore
stays in `[0, L t]` over one period.  So the field is bounded by `C t · L_max`
along the lines that matter, the displacement over `[0, T]` is at most
`L_max ∫₀^T C`, the period itself moves by at most as much, and the total defect
is at most `2 L_max ∫₀^T C ≤ 2 L_max κ · cost Γ`.

Main results:

* `abs_le_mul_abs_of_deriv_bound` — a function vanishing at `0` with derivative
  bounded by `C` is bounded by `C|x|`;
* `abs_gaugeRate_le_mul_abs` — hence the linear growth of the tangential rate
  `−ξ/v` of a bundle whose tangential component vanishes at the base point;
* `lt_of_flow_lt` — flow lines of a globally Lipschitz field do not cross;
* `flow_mem_Icc_period` — a monotone quasi-periodic marking fixing the base
  point stays in `[0, L t]` over one period;
* `abs_marking_defect_le_linear` — the defect of such a marking is at most
  `L_max ∫₀^T C + |L 0 − L T|`;
* `abs_period_sub_le_linear` — the change of the period is at most
  `L_max ∫₀^T C`, so `abs_marking_defect_le_total` gives `2 L_max ∫₀^T C`;
* `abs_marking_defect_le_cost` — with `C t ≤ κ · m t` for the cost density `m`
  of a normal path, the defect is at most `2 L_max κ · cost Γ`.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
open scoped NNReal

namespace MarkingDefectCost

/-! ### Linear growth from a vanishing base value -/

/-- A function vanishing at the origin whose derivative is bounded by `C` is
bounded by `C|x|`. -/
theorem abs_le_mul_abs_of_deriv_bound {f g : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hb : ∀ x, |g x| ≤ C) (h0 : f 0 = 0) (x : ℝ) :
    |f x| ≤ C * |x| := by
  have h := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := g) (C := C) (fun y _ => (hf y).hasDerivWithinAt)
    (fun y _ => by simpa [Real.norm_eq_abs] using hb y) (mem_univ (0 : ℝ)) (mem_univ x)
  simpa [Real.norm_eq_abs, h0] using h

/-- **The tangential rate of a bundle whose tangential component vanishes at the
base point grows at most linearly.**  If `ξ(a, 0) = 0`, `|∂_xξ(a, ·)| ≤ C a` and
the speed is at least `v₀ > 0`, then `|−ξ/v| ≤ (C a / v₀)|x|`. -/
theorem abs_gaugeRate_le_mul_abs {xi xi1 v : ℝ → ℝ → ℝ} {C : ℝ → ℝ} {v0 : ℝ}
    (hxi : ∀ a x, HasDerivAt (xi a) (xi1 a x) x) (hxi0 : ∀ a, xi a 0 = 0)
    (hb : ∀ a x, |xi1 a x| ≤ C a) (hv0 : 0 < v0) (hv : ∀ a x, v0 ≤ |v a x|) (a x : ℝ) :
    |GaugeRate.gaugeRate xi v a x| ≤ (C a / v0) * |x| := by
  have hnum : |xi a x| ≤ C a * |x| :=
    abs_le_mul_abs_of_deriv_bound (fun y => hxi a y) (fun y => hb a y) (hxi0 a) x
  have hCnn : 0 ≤ C a := le_trans (abs_nonneg _) (hb a 0)
  have hvpos : 0 < |v a x| := lt_of_lt_of_le hv0 (hv a x)
  rw [GaugeRate.gaugeRate, abs_neg, abs_div]
  rw [div_le_iff₀ hvpos]
  have h3 : C a * |x| ≤ C a / v0 * |x| * |v a x| := by
    rw [show C a / v0 * |x| * |v a x| = C a * |x| * |v a x| / v0 by ring, le_div_iff₀ hv0]
    nlinarith [mul_nonneg hCnn (abs_nonneg x), hv a x]
  linarith

/-- **The tangential rate of a bundle whose tangential component is merely
bounded at the base point.**  If `|ξ(a, 0)| ≤ C₀ a`, `|∂_xξ(a, ·)| ≤ C a` and the
speed is at least `v₀ > 0`, then `|−ξ/v| ≤ (C₀ a + C a|x|)/v₀`.  This is the
form of the growth bound that survives when the marked point of the path is
allowed to move. -/
theorem abs_gaugeRate_le_of_base_bound {xi xi1 v : ℝ → ℝ → ℝ} {C C0 : ℝ → ℝ} {v0 : ℝ}
    (hxi : ∀ a x, HasDerivAt (xi a) (xi1 a x) x) (hxi0 : ∀ a, |xi a 0| ≤ C0 a)
    (hb : ∀ a x, |xi1 a x| ≤ C a) (hv0 : 0 < v0) (hv : ∀ a x, v0 ≤ |v a x|) (a x : ℝ) :
    |GaugeRate.gaugeRate xi v a x| ≤ (C0 a + C a * |x|) / v0 := by
  have hCnn : 0 ≤ C a := le_trans (abs_nonneg _) (hb a 0)
  have hC0nn : 0 ≤ C0 a := le_trans (abs_nonneg _) (hxi0 a)
  have hnum : |xi a x - xi a 0| ≤ C a * |x| := by
    have h := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := xi a) (f' := xi1 a) (C := C a) (fun y _ => (hxi a y).hasDerivWithinAt)
      (fun y _ => by simpa [Real.norm_eq_abs] using hb a y) (mem_univ (0 : ℝ)) (mem_univ x)
    simpa [Real.norm_eq_abs] using h
  have h2 : |xi a x| ≤ C0 a + C a * |x| := by
    have h3 := abs_sub_abs_le_abs_sub (xi a x) (xi a 0)
    linarith [hxi0 a]
  have hvpos : 0 < |v a x| := lt_of_lt_of_le hv0 (hv a x)
  have hMnn : 0 ≤ C0 a + C a * |x| := by positivity
  rw [GaugeRate.gaugeRate, abs_neg, abs_div, div_le_div_iff₀ hvpos hv0]
  nlinarith [hv a x, abs_nonneg (xi a x)]

/-! ### Flow lines do not cross -/

/-- **Flow lines of a globally Lipschitz field do not cross.**  Two global
solutions ordered at time `0` stay ordered at every time. -/
theorem lt_of_flow_lt {R : ℝ → ℝ → ℝ} {K : ℝ≥0} {a b : ℝ → ℝ}
    (hlip : ∀ t, LipschitzWith K (R t))
    (ha : ∀ t, HasDerivAt a (R t (a t)) t) (hb : ∀ t, HasDerivAt b (R t (b t)) t)
    (h0 : a 0 < b 0) (t : ℝ) : a t < b t := by
  by_contra hcon
  push_neg at hcon
  -- the difference is continuous and changes sign, so it vanishes somewhere
  have hca : Continuous a := continuous_iff_continuousAt.2 fun s => (ha s).continuousAt
  have hcb : Continuous b := continuous_iff_continuousAt.2 fun s => (hb s).continuousAt
  have hcont : Continuous fun s => b s - a s := hcb.sub hca
  have hzero : ∃ t₁, b t₁ - a t₁ = 0 := by
    rcases le_total (0 : ℝ) t with hle | hle
    · have := intermediate_value_Icc' (a := 0) (b := t) hle hcont.continuousOn
      have hmem : (0 : ℝ) ∈ Icc (b t - a t) (b 0 - a 0) :=
        ⟨by linarith, by linarith⟩
      obtain ⟨t₁, -, ht₁⟩ := this hmem
      exact ⟨t₁, ht₁⟩
    · have := intermediate_value_Icc (a := t) (b := 0) hle hcont.continuousOn
      have hmem : (0 : ℝ) ∈ Icc (b t - a t) (b 0 - a 0) :=
        ⟨by linarith, by linarith⟩
      obtain ⟨t₁, -, ht₁⟩ := this hmem
      exact ⟨t₁, ht₁⟩
  obtain ⟨t₁, ht₁⟩ := hzero
  have heq : a t₁ = b t₁ := by linarith [sub_eq_zero.1 ht₁]
  have hd := GlobalODE.dist_le_of_global_solutions (K := K) (f := R) hlip ha hb t₁ 0
  rw [heq, dist_self, zero_mul] at hd
  have : dist (a 0) (b 0) = 0 := le_antisymm hd dist_nonneg
  rw [dist_eq_zero] at this
  exact absurd this (ne_of_lt h0)

/-! ### A monotone quasi-periodic marking stays in one period -/

/-- **The range of a gauge marking over one period, measured from its own base
point.**  A flow of a globally Lipschitz field started from the affine marking
of positive period `L₀` is increasing in the parameter, so
`Φ t 0 ≤ Φ t u ≤ Φ t 1` for `u ∈ [0, 1]`.  No hypothesis is made on the motion
of the base point: the flow line through `0` is simply used as the lower fence
instead of the constant `0`. -/
theorem flow_mem_Icc_base {Phi : ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ} {K : ℝ≥0} {L0 : ℝ}
    (hlip : ∀ t, LipschitzWith K (R t))
    (hd : ∀ u t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t)
    (h0 : ∀ u, Phi 0 u = L0 * u) (hL0 : 0 < L0)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (t : ℝ) :
    Phi t u ∈ Icc (Phi t 0) (Phi t 1) := by
  constructor
  · rcases eq_or_lt_of_le hu0 with heq | hlt
    · rw [← heq]
    · have hstart : Phi 0 0 < Phi 0 u := by
        rw [h0 0, h0 u]
        simpa using mul_pos hL0 hlt
      exact (lt_of_flow_lt (K := K) hlip (fun s => hd 0 s) (fun s => hd u s) hstart t).le
  · rcases eq_or_lt_of_le hu1 with heq | hlt
    · rw [heq]
    · have hstart : Phi 0 u < Phi 0 1 := by
        rw [h0 u, h0 1]
        exact by nlinarith
      exact (lt_of_flow_lt (K := K) hlip (fun s => hd u s) (fun s => hd 1 s) hstart t).le

/-- **The range of a gauge marking over one period.**  A flow of a globally
Lipschitz field, started from the affine marking of positive period `L₀`, fixing
the base point and quasi-periodic with period `L t = Φ t 1`, satisfies
`0 ≤ Φ t u ≤ L t` for `u ∈ [0, 1]`. -/
theorem flow_mem_Icc_period {Phi : ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ} {K : ℝ≥0} {L0 : ℝ}
    (hlip : ∀ t, LipschitzWith K (R t))
    (hd : ∀ u t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t)
    (h0 : ∀ u, Phi 0 u = L0 * u) (hL0 : 0 < L0) (hbase : ∀ t, Phi t 0 = 0)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (t : ℝ) :
    Phi t u ∈ Icc (0 : ℝ) (Phi t 1) := by
  have h := flow_mem_Icc_base (K := K) hlip hd h0 hL0 hu0 hu1 t
  rwa [hbase t] at h

/-- **A marking whose base point stays within one period stays, over one
period, in a window of size `L_max`.** -/
theorem abs_flow_le_of_base_le {Phi : ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ} {K : ℝ≥0} {L0 Lmax : ℝ}
    (hlip : ∀ t, LipschitzWith K (R t))
    (hd : ∀ u t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t)
    (h0 : ∀ u, Phi 0 u = L0 * u) (hL0 : 0 < L0) {t : ℝ} (hbase : |Phi t 0| ≤ Lmax)
    (hLmax : Phi t 1 ≤ Lmax)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |Phi t u| ≤ Lmax := by
  obtain ⟨hl, hr⟩ := flow_mem_Icc_base (K := K) hlip hd h0 hL0 hu0 hu1 t
  have hb := abs_le.1 hbase
  rw [abs_le]
  exact ⟨le_trans hb.1 hl, le_trans hr hLmax⟩

/-- **The displacement of a flow line, from a bound on its field valid on the
time interval only.**  The companion of
`MarkingDeviation.abs_flow_displacement_le` whose bound is only required where
it is integrated. -/
theorem abs_flow_displacement_le_on {Phi : ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ} {rho : ℝ → ℝ}
    {T : ℝ} (u : ℝ)
    (hd : ∀ t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t)
    (hc : Continuous fun t => R t (Phi t u))
    (hb : ∀ t ∈ Ioc (0 : ℝ) T, |R t (Phi t u)| ≤ rho t) (hrho : Continuous rho)
    (hT : 0 ≤ T) :
    |Phi T u - Phi 0 u| ≤ ∫ t in (0:ℝ)..T, rho t := by
  have hint : (∫ t in (0:ℝ)..T, R t (Phi t u)) = Phi T u - Phi 0 u :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      (hc.intervalIntegrable 0 T)
  have hle : ‖∫ t in (0:ℝ)..T, R t (Phi t u)‖ ≤ ∫ t in (0:ℝ)..T, rho t :=
    intervalIntegral.norm_integral_le_of_norm_le hT
      (Filter.Eventually.of_forall fun t ht => by
        simpa [Real.norm_eq_abs] using hb t ht)
      (hrho.intervalIntegrable 0 T)
  rwa [hint, Real.norm_eq_abs] at hle

/-! ### The defect of a marking flowed by a field of linear growth -/

/-- **The defect of a gauge marking of linear growth.**  For a marking as in
`flow_mem_Icc_base`, whose field obeys `|R(t, x)| ≤ C t·L_max` on the window
`|x| ≤ L_max`, whose base point stays in that window and whose period never
exceeds `L_max`, the deviation from the affine marking of the terminal period is
at most `L_max ∫₀^T C` plus the change of the period. -/
theorem abs_marking_defect_le_linear {Phi : ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ} {C : ℝ → ℝ}
    {K : ℝ≥0} {L0 Lmax LT T : ℝ}
    (hlip : ∀ t, LipschitzWith K (R t))
    (hd : ∀ u t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t)
    (hc : ∀ u, Continuous fun t => R t (Phi t u)) (hCcont : Continuous C)
    (hgrow : ∀ t x, |x| ≤ Lmax → |R t x| ≤ C t * Lmax)
    (h0 : ∀ u, Phi 0 u = L0 * u) (hL0 : 0 < L0)
    (hbase : ∀ t ∈ Icc (0:ℝ) T, |Phi t 0| ≤ Lmax)
    (hper : ∀ u, Phi T (u + 1) = Phi T u + LT)
    (hLmax : ∀ t ∈ Icc (0:ℝ) T, Phi t 1 ≤ Lmax) (hT : 0 ≤ T) (u : ℝ) :
    |Phi T u - LT * u| ≤ Lmax * (∫ t in (0:ℝ)..T, C t) + |L0 - LT| := by
  -- reduce to the fractional part of `u`
  set g : ℝ → ℝ := fun x => Phi T x - LT * x with hg
  have hgper : Function.Periodic g 1 := by
    intro x
    simp only [hg, hper x]
    ring
  have hfract : g (Int.fract u) = g u := by
    have h2 := hgper.sub_int_mul_eq (x := u) ⌊u⌋
    rw [Int.fract, show u - (⌊u⌋ : ℝ) = u - (⌊u⌋ : ℝ) * 1 by ring]
    exact h2
  have hr0 : 0 ≤ Int.fract u := Int.fract_nonneg u
  have hr1 : Int.fract u ≤ 1 := (Int.fract_lt_one u).le
  -- along the line of the fractional part the field is bounded by `C t · L_max`
  have hbd : ∀ t ∈ Ioc (0:ℝ) T, |R t (Phi t (Int.fract u))| ≤ C t * Lmax := fun t ht =>
    hgrow t _ (abs_flow_le_of_base_le (K := K) hlip hd h0 hL0 (hbase t ⟨ht.1.le, ht.2⟩)
      (hLmax t ⟨ht.1.le, ht.2⟩) hr0 hr1)
  have hflow : |Phi T (Int.fract u) - Phi 0 (Int.fract u)| ≤ ∫ t in (0:ℝ)..T, C t * Lmax :=
    abs_flow_displacement_le_on (Int.fract u) (fun t => hd (Int.fract u) t)
      (hc _) hbd (hCcont.mul continuous_const) hT
  have hint : (∫ t in (0:ℝ)..T, C t * Lmax) = Lmax * ∫ t in (0:ℝ)..T, C t := by
    rw [intervalIntegral.integral_mul_const]
    ring
  rw [hint] at hflow
  have haff : |Phi 0 (Int.fract u) - LT * Int.fract u| ≤ |L0 - LT| := by
    rw [h0 (Int.fract u), show L0 * Int.fract u - LT * Int.fract u
      = (L0 - LT) * Int.fract u by ring, abs_mul, abs_of_nonneg hr0]
    exact mul_le_of_le_one_right (abs_nonneg _) hr1
  have hsplit : |g (Int.fract u)| ≤ Lmax * (∫ t in (0:ℝ)..T, C t) + |L0 - LT| := by
    have hdecomp : g (Int.fract u) = (Phi T (Int.fract u) - Phi 0 (Int.fract u))
        + (Phi 0 (Int.fract u) - LT * Int.fract u) := by simp [hg]
    rw [hdecomp]
    exact le_trans (abs_add_le _ _) (add_le_add hflow haff)
  have hgu : g u = Phi T u - LT * u := rfl
  rw [← hgu, ← hfract]
  exact hsplit

/-- **The change of the period is controlled by the same quantity.**  The period
`L t = Φ t 1` is itself a flow line, so it moves by at most `L_max ∫₀^T C`. -/
theorem abs_period_sub_le_linear {Phi : ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ} {C : ℝ → ℝ}
    {K : ℝ≥0} {L0 Lmax T : ℝ}
    (hlip : ∀ t, LipschitzWith K (R t))
    (hd : ∀ u t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t)
    (hc : ∀ u, Continuous fun t => R t (Phi t u)) (hCcont : Continuous C)
    (hgrow : ∀ t x, |x| ≤ Lmax → |R t x| ≤ C t * Lmax)
    (h0 : ∀ u, Phi 0 u = L0 * u) (hL0 : 0 < L0)
    (hbase : ∀ t ∈ Icc (0:ℝ) T, |Phi t 0| ≤ Lmax)
    (hLmax : ∀ t ∈ Icc (0:ℝ) T, Phi t 1 ≤ Lmax) (hT : 0 ≤ T) :
    |L0 - Phi T 1| ≤ Lmax * ∫ t in (0:ℝ)..T, C t := by
  have hbd : ∀ t ∈ Ioc (0:ℝ) T, |R t (Phi t 1)| ≤ C t * Lmax := fun t ht =>
    hgrow t _ (abs_flow_le_of_base_le (K := K) hlip hd h0 hL0 (hbase t ⟨ht.1.le, ht.2⟩)
      (hLmax t ⟨ht.1.le, ht.2⟩) (by norm_num : (0:ℝ) ≤ (1:ℝ)) le_rfl)
  have hflow : |Phi T 1 - Phi 0 1| ≤ ∫ t in (0:ℝ)..T, C t * Lmax :=
    abs_flow_displacement_le_on 1 (fun t => hd 1 t) (hc _) hbd
      (hCcont.mul continuous_const) hT
  have hint : (∫ t in (0:ℝ)..T, C t * Lmax) = Lmax * ∫ t in (0:ℝ)..T, C t := by
    rw [intervalIntegral.integral_mul_const]
    ring
  rw [hint, h0 1, mul_one] at hflow
  rw [abs_sub_comm]
  exact hflow

/-! ### The total defect, and its bound by the cost of a path -/

/-- **The total defect of a gauge marking of linear growth.**  Adding the two
previous bounds: the marking at the final time deviates from the affine marking
of its own period by at most `2 L_max ∫₀^T C`. -/
theorem abs_marking_defect_le_total {Phi : ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ} {C : ℝ → ℝ}
    {K : ℝ≥0} {L0 Lmax T : ℝ}
    (hlip : ∀ t, LipschitzWith K (R t))
    (hd : ∀ u t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t)
    (hc : ∀ u, Continuous fun t => R t (Phi t u)) (hCcont : Continuous C)
    (hgrow : ∀ t x, |x| ≤ Lmax → |R t x| ≤ C t * Lmax)
    (h0 : ∀ u, Phi 0 u = L0 * u) (hL0 : 0 < L0)
    (hbase : ∀ t ∈ Icc (0:ℝ) T, |Phi t 0| ≤ Lmax)
    (hper : ∀ t u, Phi t (u + 1) = Phi t u + Phi t 1)
    (hLmax : ∀ t ∈ Icc (0:ℝ) T, Phi t 1 ≤ Lmax) (hT : 0 ≤ T) (u : ℝ) :
    |Phi T u - Phi T 1 * u| ≤ 2 * Lmax * ∫ t in (0:ℝ)..T, C t := by
  have h1 := abs_marking_defect_le_linear (K := K) (Lmax := Lmax) (LT := Phi T 1)
    hlip hd hc hCcont hgrow h0 hL0 hbase (fun x => hper T x) hLmax hT u
  have h2 := abs_period_sub_le_linear (K := K) (Lmax := Lmax) hlip hd hc hCcont hgrow
    h0 hL0 hbase hLmax hT
  have : Lmax * (∫ t in (0:ℝ)..T, C t) + |L0 - Phi T 1|
      ≤ 2 * Lmax * ∫ t in (0:ℝ)..T, C t := by linarith
  exact le_trans h1 this

/-- **The total defect of a gauge marking of linear growth, measured against a
period that the marking reads only up to the drift of its base point.**  If the
marking is quasi-periodic with period `LT` at the final time, and `Φ T 1`
differs from `LT` by at most `dB`, then the deviation from the affine marking of
`LT` is at most `2 L_max ∫₀^T C + dB`. -/
theorem abs_marking_defect_le_total_drift {Phi : ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ} {C : ℝ → ℝ}
    {K : ℝ≥0} {L0 Lmax LT dB T : ℝ}
    (hlip : ∀ t, LipschitzWith K (R t))
    (hd : ∀ u t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t)
    (hc : ∀ u, Continuous fun t => R t (Phi t u)) (hCcont : Continuous C)
    (hgrow : ∀ t x, |x| ≤ Lmax → |R t x| ≤ C t * Lmax)
    (h0 : ∀ u, Phi 0 u = L0 * u) (hL0 : 0 < L0)
    (hbase : ∀ t ∈ Icc (0:ℝ) T, |Phi t 0| ≤ Lmax)
    (hper : ∀ u, Phi T (u + 1) = Phi T u + LT) (hLT : |Phi T 1 - LT| ≤ dB)
    (hLmax : ∀ t ∈ Icc (0:ℝ) T, Phi t 1 ≤ Lmax) (hT : 0 ≤ T) (u : ℝ) :
    |Phi T u - LT * u| ≤ 2 * Lmax * (∫ t in (0:ℝ)..T, C t) + dB := by
  have h1 := abs_marking_defect_le_linear (K := K) (Lmax := Lmax) (LT := LT)
    hlip hd hc hCcont hgrow h0 hL0 hbase hper hLmax hT u
  have h2 := abs_period_sub_le_linear (K := K) (Lmax := Lmax) hlip hd hc hCcont hgrow
    h0 hL0 hbase hLmax hT
  have h3 : |L0 - LT| ≤ |L0 - Phi T 1| + |Phi T 1 - LT| := by
    simpa using abs_sub_le L0 (Phi T 1) LT
  linarith

/-- **The defect of a gauge marking is at most twice the maximal period times
the cost of the path.**  If the growth coefficient of the field is at most `κ`
times the cost density of a normal path, then the deviation of the marking at
the final time from the affine marking of its own period is at most
`2 L_max κ · cost Γ`. -/
theorem abs_marking_defect_le_cost {p q : Data}
    (Γ : NormalPath p q) {Phi : ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ} {C : ℝ → ℝ}
    {K : ℝ≥0} {L0 Lmax kappa : ℝ}
    (hlip : ∀ t, LipschitzWith K (R t))
    (hd : ∀ u t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t)
    (hc : ∀ u, Continuous fun t => R t (Phi t u)) (hCcont : Continuous C)
    (hgrow : ∀ t x, |x| ≤ Lmax → |R t x| ≤ C t * Lmax)
    (h0 : ∀ u, Phi 0 u = L0 * u) (hL0 : 0 < L0)
    (hbase : ∀ t ∈ Icc (0:ℝ) Γ.T, |Phi t 0| ≤ Lmax)
    (hper : ∀ t u, Phi t (u + 1) = Phi t u + Phi t 1)
    (hLmax : ∀ t ∈ Icc (0:ℝ) Γ.T, Phi t 1 ≤ Lmax) (hcost : ∀ t, C t ≤ kappa * Γ.m t)
    (u : ℝ) :
    |Phi Γ.T u - Phi Γ.T 1 * u| ≤ 2 * Lmax * kappa * cost Γ := by
  have hT : (0 : ℝ) ≤ Γ.T := Γ.T_pos.le
  have hLmax0 : 0 ≤ Lmax := by
    refine le_trans ?_ (hLmax 0 ⟨le_rfl, hT⟩)
    rw [h0 1, mul_one]
    exact hL0.le
  have hmain := abs_marking_defect_le_total (K := K) (Lmax := Lmax) hlip hd hc hCcont hgrow
    h0 hL0 hbase hper hLmax hT u
  have hCint : IntervalIntegrable C volume 0 Γ.T := hCcont.intervalIntegrable 0 Γ.T
  have hmint : IntervalIntegrable (fun t => kappa * Γ.m t) volume 0 Γ.T := by
    have : Continuous fun t => kappa * Γ.m t := continuous_const.mul Γ.cont_m
    exact this.intervalIntegrable 0 Γ.T
  have hle : (∫ t in (0:ℝ)..Γ.T, C t) ≤ ∫ t in (0:ℝ)..Γ.T, kappa * Γ.m t :=
    intervalIntegral.integral_mono_on hT hCint hmint (fun t _ => hcost t)
  have heq : (∫ t in (0:ℝ)..Γ.T, kappa * Γ.m t) = kappa * cost Γ := by
    rw [intervalIntegral.integral_const_mul, cost]
  rw [heq] at hle
  refine le_trans hmain ?_
  have h2 : 0 ≤ 2 * Lmax := by linarith
  calc 2 * Lmax * (∫ t in (0:ℝ)..Γ.T, C t) ≤ 2 * Lmax * (kappa * cost Γ) :=
        mul_le_mul_of_nonneg_left hle h2
    _ = 2 * Lmax * kappa * cost Γ := by ring

/-- **The defect of a gauge marking with a drifting base point.**  As
`abs_marking_defect_le_cost`, but measured against the period `LT` that the
marking reads only up to the drift `dB` of its base point. -/
theorem abs_marking_defect_le_cost_drift {p q : Data}
    (Γ : NormalPath p q) {Phi : ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ} {C : ℝ → ℝ}
    {K : ℝ≥0} {L0 Lmax LT dB kappa : ℝ}
    (hlip : ∀ t, LipschitzWith K (R t))
    (hd : ∀ u t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t)
    (hc : ∀ u, Continuous fun t => R t (Phi t u)) (hCcont : Continuous C)
    (hgrow : ∀ t x, |x| ≤ Lmax → |R t x| ≤ C t * Lmax)
    (h0 : ∀ u, Phi 0 u = L0 * u) (hL0 : 0 < L0)
    (hbase : ∀ t ∈ Icc (0:ℝ) Γ.T, |Phi t 0| ≤ Lmax)
    (hper : ∀ u, Phi Γ.T (u + 1) = Phi Γ.T u + LT) (hLT : |Phi Γ.T 1 - LT| ≤ dB)
    (hLmax : ∀ t ∈ Icc (0:ℝ) Γ.T, Phi t 1 ≤ Lmax) (hcost : ∀ t, C t ≤ kappa * Γ.m t)
    (u : ℝ) :
    |Phi Γ.T u - LT * u| ≤ 2 * Lmax * kappa * cost Γ + dB := by
  have hT : (0 : ℝ) ≤ Γ.T := Γ.T_pos.le
  have hLmax0 : 0 ≤ Lmax := by
    refine le_trans ?_ (hLmax 0 ⟨le_rfl, hT⟩)
    rw [h0 1, mul_one]
    exact hL0.le
  have hmain := abs_marking_defect_le_total_drift (K := K) (Lmax := Lmax) (LT := LT)
    (dB := dB) hlip hd hc hCcont hgrow h0 hL0 hbase hper hLT hLmax hT u
  have hCint : IntervalIntegrable C volume 0 Γ.T := hCcont.intervalIntegrable 0 Γ.T
  have hmint : IntervalIntegrable (fun t => kappa * Γ.m t) volume 0 Γ.T := by
    have : Continuous fun t => kappa * Γ.m t := continuous_const.mul Γ.cont_m
    exact this.intervalIntegrable 0 Γ.T
  have hle : (∫ t in (0:ℝ)..Γ.T, C t) ≤ ∫ t in (0:ℝ)..Γ.T, kappa * Γ.m t :=
    intervalIntegral.integral_mono_on hT hCint hmint (fun t _ => hcost t)
  have heq : (∫ t in (0:ℝ)..Γ.T, kappa * Γ.m t) = kappa * cost Γ := by
    rw [intervalIntegral.integral_const_mul, cost]
  rw [heq] at hle
  have h2 : 0 ≤ 2 * Lmax := by linarith
  have hstep : 2 * Lmax * (∫ t in (0:ℝ)..Γ.T, C t) ≤ 2 * Lmax * kappa * cost Γ := by
    calc 2 * Lmax * (∫ t in (0:ℝ)..Γ.T, C t) ≤ 2 * Lmax * (kappa * cost Γ) :=
          mul_le_mul_of_nonneg_left hle h2
      _ = 2 * Lmax * kappa * cost Γ := by ring
  linarith

/-! ### Non-vacuity -/

/-- **The hypothesis block of `abs_marking_defect_le_total` is satisfiable.**
The dilated marking `Φ_t(u) = L₀ u e^{sin t}` is the flow of the linear field
`R(t, x) = (cos t) x`, which is globally Lipschitz with constant `1` and obeys
`|R(t, x)| ≤ 1·|x|`; it starts from the affine marking of period `L₀`, fixes the
base point, is quasi-periodic with period `Φ_t(1) = L₀e^{sin t} ≤ L₀e`, and its
defect — zero, the marking staying affine — obeys the bound. -/
theorem abs_marking_defect_le_total_dilation {L0 T : ℝ} (hL0 : 0 < L0) (hT : 0 ≤ T)
    (u : ℝ) :
    |L0 * u * Real.exp (Real.sin T) - L0 * 1 * Real.exp (Real.sin T) * u|
      ≤ 2 * (L0 * Real.exp 1) * ∫ _t in (0:ℝ)..T, (1 : ℝ) := by
  refine abs_marking_defect_le_total (Phi := fun t x => L0 * x * Real.exp (Real.sin t))
    (R := fun t x => Real.cos t * x) (C := fun _ => 1) (K := 1) (L0 := L0)
    (Lmax := L0 * Real.exp 1) (fun t => ?_) (fun x t => ?_) (fun x => ?_)
    continuous_const (fun t x hx => ?_) (fun x => by simp)
    hL0 (fun t _ => by simpa using mul_nonneg hL0.le (Real.exp_pos 1).le)
    (fun t x => by ring) (fun t _ => ?_) hT u
  · have hlip : LipschitzWith 1 fun x : ℝ => Real.cos t * x := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
      have h1 : |Real.cos t| ≤ 1 := Real.abs_cos_le_one t
      simpa using mul_le_mul_of_nonneg_right h1 (abs_nonneg (x - y))
    simpa using hlip
  · have hd : HasDerivAt (fun r : ℝ => Real.exp (Real.sin r))
        (Real.exp (Real.sin t) * Real.cos t) t := (Real.hasDerivAt_sin t).exp
    refine (hd.const_mul (L0 * x)).congr_deriv ?_
    ring
  · exact Real.continuous_cos.mul
      (continuous_const.mul (Real.continuous_exp.comp Real.continuous_sin))
  · rw [abs_mul, one_mul]
    exact le_trans (mul_le_of_le_one_left (abs_nonneg x) (Real.abs_cos_le_one t)) hx
  · have h1 : Real.exp (Real.sin t) ≤ Real.exp 1 := Real.exp_le_exp.2 (Real.sin_le_one t)
    have h2 := mul_le_mul_of_nonneg_left h1 hL0.le
    simpa using h2

end MarkingDefectCost
