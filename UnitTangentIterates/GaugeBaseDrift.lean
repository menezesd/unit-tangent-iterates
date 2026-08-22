import Mathlib
import UnitTangentIterates.GaugeBaseFlow

/-!
# The base point of the gauge flow moves at most the cost

`GaugeBaseFlow.gaugeFlow_base_fixed` shows that the gauge flow `Φ` of the family
of selected rears fixes the base point, `Φ(t,0) = 0`, as soon as the tangential
drift `ξ` of that family vanishes there — which, by `RearBaseDrift.lean`,
happens exactly when the marked point of the path of fronts is at rest.

`PinchedPathRigidity.lean` shows that this last hypothesis, together with the
constant speed of the slices, makes the admissible class of the `C²` estimate
empty.  Dropping it, the base point of the gauge flow is no longer fixed; but it
is *slow*: it moves at the rate `−ξ(t, Φ(t,0))`, and
`RearBaseDriftBound.abs_frameTangential_le_cost_on_period_free` bounds that rate
by a multiple of the cost density along any normal path.  Integrating in the
time, the base point of the gauge flow drifts by at most that multiple of the
cost of the path.

Main results:

* `abs_le_integral_of_hasDerivAt` — a function vanishing at `0` is bounded by
  the integral of any bound for its derivative;
* `abs_gaugeFlow_base_le` — the drift of the base point of the gauge flow;
* `abs_gaugeFlow_base_le_cost` — its cost form for a unit-speed family:
  `|Φ(t,0)| ≤ rr·∫₀ᵗ m`.
-/

noncomputable section

open Function MeasureTheory

namespace GaugeBaseDrift

open UniformFrameBounds

/-- **A function vanishing at the origin is bounded by the integral of a bound
for its derivative.** -/
theorem abs_le_integral_of_hasDerivAt {phi rate b : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hd : ∀ r, HasDerivAt phi (rate r) r) (hrc : Continuous rate) (hbc : Continuous b)
    (hbound : ∀ r, |rate r| ≤ b r) (h0 : phi 0 = 0) :
    |phi t| ≤ ∫ r in (0 : ℝ)..t, b r := by
  have hint : (∫ r in (0 : ℝ)..t, rate r) = phi t - phi 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
      (hrc.intervalIntegrable 0 t)
  have hle : ‖∫ r in (0 : ℝ)..t, rate r‖ ≤ ∫ r in (0 : ℝ)..t, b r :=
    intervalIntegral.norm_integral_le_of_norm_le ht
      (Filter.Eventually.of_forall fun r _ => by
        simpa [Real.norm_eq_abs] using hbound r)
      (hbc.intervalIntegrable 0 t)
  rw [hint, h0, sub_zero, Real.norm_eq_abs] at hle
  exact hle

/-- **A function vanishing at the origin, with its derivative bounded on an
interval, is bounded by the integral of that bound.** -/
theorem abs_le_integral_of_hasDerivAt_on {phi rate b : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hd : ∀ r, HasDerivAt phi (rate r) r) (hrc : Continuous rate) (hbc : Continuous b)
    (hbound : ∀ r ∈ Set.Ioc (0 : ℝ) s, |rate r| ≤ b r) (h0 : phi 0 = 0) :
    |phi s| ≤ ∫ r in (0 : ℝ)..s, b r := by
  have hint : (∫ r in (0 : ℝ)..s, rate r) = phi s - phi 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
      (hrc.intervalIntegrable 0 s)
  have hle : ‖∫ r in (0 : ℝ)..s, rate r‖ ≤ ∫ r in (0 : ℝ)..s, b r :=
    intervalIntegral.norm_integral_le_of_norm_le hs
      (Filter.Eventually.of_forall fun r hr => by
        simpa [Real.norm_eq_abs] using hbound r hr)
      (hbc.intervalIntegrable 0 s)
  rw [hint, h0, sub_zero, Real.norm_eq_abs] at hle
  exact hle

/-- **A trajectory that starts at the origin and is slow inside a window never
leaves the window.**  If `φ(0) = 0`, if `|φ'(t)| ≤ b t` at every time at which
`|φ(t)| ≤ A`, and if the whole budget `∫₀^T b` is smaller than the half-width
`A`, then `|φ(t)| ≤ ∫₀^t b` for every `t ∈ [0, T]`.

This is the bootstrap that replaces the vanishing of the base point of the gauge
flow: the drift rate of the base point can only be estimated while the base
point is still inside one period, and the estimate then shows that it is. -/
theorem abs_le_integral_of_window {phi rate b : ℝ → ℝ} {A T : ℝ}
    (hd : ∀ t, HasDerivAt phi (rate t) t) (hrc : Continuous rate)
    (hbc : Continuous b) (hbnn : ∀ t, 0 ≤ b t) (h0 : phi 0 = 0) (hA : 0 < A)
    (hbound : ∀ t, |phi t| ≤ A → |rate t| ≤ b t)
    (hsmall : (∫ r in (0 : ℝ)..T, b r) < A)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    |phi t| ≤ ∫ r in (0 : ℝ)..t, b r := by
  have hphic : Continuous phi :=
    (Differentiable.continuous (fun r => (hd r).differentiableAt))
  -- the integral of the budget is monotone in the endpoint
  have hmono : ∀ s, 0 ≤ s → s ≤ T → (∫ r in (0 : ℝ)..s, b r) ≤ ∫ r in (0 : ℝ)..T, b r := by
    intro s hs hsT
    have hsplit : (∫ r in (0 : ℝ)..T, b r)
        = (∫ r in (0 : ℝ)..s, b r) + ∫ r in s..T, b r :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hbc.intervalIntegrable 0 s) (hbc.intervalIntegrable s T)).symm
    have hnn : 0 ≤ ∫ r in s..T, b r :=
      intervalIntegral.integral_nonneg hsT fun r _ => hbnn r
    linarith
  -- no time in `[0, T]` leaves the window
  have hin : ∀ s ∈ Set.Icc (0 : ℝ) T, |phi s| < A := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨s0, hs0mem, hs0⟩ := hcon
    set E : Set ℝ := {s | s ∈ Set.Icc (0 : ℝ) T ∧ A ≤ |phi s|} with hEdef
    have hEne : E.Nonempty := ⟨s0, hs0mem, hs0⟩
    have hEclosed : IsClosed E := by
      have h1 : IsClosed (Set.Icc (0 : ℝ) T) := isClosed_Icc
      have h2 : IsClosed {s : ℝ | A ≤ |phi s|} :=
        isClosed_le continuous_const hphic.abs
      exact h1.inter h2
    have hEbdd : BddBelow E := ⟨0, fun s hs => hs.1.1⟩
    have ht1E : sInf E ∈ E := hEclosed.csInf_mem hEne hEbdd
    set t1 := sInf E with ht1def
    have ht1nn : 0 ≤ t1 := ht1E.1.1
    have ht1T : t1 ≤ T := ht1E.1.2
    have ht1pos : 0 < t1 := by
      rcases eq_or_lt_of_le ht1nn with heq | hlt
      · exfalso
        have := ht1E.2
        rw [← heq, h0] at this
        simp at this
        linarith
      · exact hlt
    have hlt : ∀ r, 0 ≤ r → r < t1 → |phi r| < A := by
      intro r hr0 hrt1
      by_contra hcon2
      push_neg at hcon2
      have hrmem : r ∈ E := ⟨⟨hr0, le_trans hrt1.le ht1T⟩, hcon2⟩
      exact absurd (csInf_le hEbdd hrmem) (not_le.2 hrt1)
    have hle1 : |phi t1| ≤ A := by
      have hcont : ContinuousWithinAt (fun r => |phi r|) (Set.Iio t1) t1 :=
        hphic.abs.continuousWithinAt
      have hmem : Set.Ioo 0 t1 ∈ nhdsWithin t1 (Set.Iio t1) := Ioo_mem_nhdsLT ht1pos
      exact le_of_tendsto hcont (Filter.eventually_of_mem hmem fun r hr =>
        (hlt r hr.1.le hr.2).le)
    have hbd : ∀ r ∈ Set.Ioc (0 : ℝ) t1, |rate r| ≤ b r := by
      intro r hr
      refine hbound r ?_
      rcases eq_or_lt_of_le hr.2 with heq | hrlt
      · rw [heq]; exact hle1
      · exact (hlt r hr.1.le hrlt).le
    have hfin : |phi t1| ≤ ∫ r in (0 : ℝ)..t1, b r :=
      abs_le_integral_of_hasDerivAt_on ht1nn hd hrc hbc hbd h0
    have := hmono t1 ht1nn ht1T
    linarith [ht1E.2]
  have hbd : ∀ r ∈ Set.Ioc (0 : ℝ) t, |rate r| ≤ b r := by
    intro r hr
    exact hbound r (hin r ⟨hr.1.le, le_trans hr.2 htT⟩).le
  exact abs_le_integral_of_hasDerivAt_on ht0 hd hrc hbc hbd h0

/-- The field of the gauge flow of a bundle of frame data is continuous. -/
theorem continuous_uncurry_gaugeRate (D : GaugeFrameData) :
    Continuous (uncurry (GaugeRate.gaugeRate D.xi D.v)) := by
  have h : uncurry (GaugeRate.gaugeRate D.xi D.v)
      = fun z : ℝ × ℝ => -(uncurry D.xi z / uncurry D.v z) := rfl
  rw [h]
  exact (D.hxic.div D.hvc (fun z => D.hvne z.1 z.2)).neg

/-- **The base point of the gauge flow drifts at most the integral of a bound
for the tangential rate.** -/
theorem abs_gaugeFlow_base_le (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hPhid : ∀ t, HasDerivAt (fun r => Phi r 0)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t 0)) t)
    (hPhi0 : Phi 0 0 = 0) (hbc : Continuous b)
    (hbound : ∀ r, |GaugeRate.gaugeRate D.xi D.v r (Phi r 0)| ≤ b r)
    {t : ℝ} (ht : 0 ≤ t) :
    |Phi t 0| ≤ ∫ r in (0 : ℝ)..t, b r := by
  have hPhidiff : Differentiable ℝ fun r => Phi r 0 := fun r => (hPhid r).differentiableAt
  have hPhicont : Continuous fun r => Phi r 0 := hPhidiff.continuous
  have hrc : Continuous fun r => GaugeRate.gaugeRate D.xi D.v r (Phi r 0) :=
    (continuous_uncurry_gaugeRate D).comp (continuous_id.prodMk hPhicont)
  exact abs_le_integral_of_hasDerivAt ht hPhid hrc hbc hbound hPhi0

/-- **The cost form of the drift of the base point.**  For a family written in
its own arclength — so that the speed of the bundle is one and the field of the
gauge flow is `−ξ` — with `|ξ|` dominated by `rr` times the cost density along
the flow line, the base point of the gauge flow moves at most `rr` times the
cost accumulated so far. -/
theorem abs_gaugeFlow_base_le_cost (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ}
    {m : ℝ → ℝ} {rr : ℝ}
    (hPhid : ∀ t, HasDerivAt (fun r => Phi r 0)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t 0)) t)
    (hPhi0 : Phi 0 0 = 0) (hv1 : ∀ a x, D.v a x = 1) (hmc : Continuous m)
    (hbound : ∀ r, |D.xi r (Phi r 0)| ≤ rr * m r)
    {t : ℝ} (ht : 0 ≤ t) :
    |Phi t 0| ≤ rr * ∫ r in (0 : ℝ)..t, m r := by
  have hrate : ∀ r, GaugeRate.gaugeRate D.xi D.v r (Phi r 0) = -D.xi r (Phi r 0) := by
    intro r
    rw [GaugeRate.gaugeRate, hv1 r (Phi r 0), div_one]
  have h := abs_gaugeFlow_base_le D (b := fun r => rr * m r) hPhid hPhi0
    (continuous_const.mul hmc) (fun r => by rw [hrate r, abs_neg]; exact hbound r) ht
  rwa [intervalIntegral.integral_const_mul] at h

/-- **The base point of the gauge flow drifts at most the cost, with no
hypothesis on the marked point of the path.**  For a family written in its own
arclength — so that the speed of the bundle is one and the field of the gauge
flow is `−ξ` — whose tangential component obeys `|ξ(t, x)| ≤ rr·m t` on the
window `|x| ≤ A`, and whose total budget `rr∫₀^T m` is smaller than `A`, the base
point of the gauge flow never leaves the window and moves at most `rr` times the
cost accumulated so far. -/
theorem abs_gaugeFlow_base_le_window (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ}
    {m : ℝ → ℝ} {rr A T : ℝ}
    (hPhid : ∀ t, HasDerivAt (fun r => Phi r 0)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t 0)) t)
    (hPhi0 : Phi 0 0 = 0) (hv1 : ∀ a x, D.v a x = 1) (hmc : Continuous m)
    (hmnn : ∀ t, 0 ≤ m t) (hrr : 0 ≤ rr) (hA : 0 < A)
    (hbound : ∀ t x, |x| ≤ A → |D.xi t x| ≤ rr * m t)
    (hsmall : rr * (∫ r in (0 : ℝ)..T, m r) < A)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    |Phi t 0| ≤ rr * ∫ r in (0 : ℝ)..t, m r := by
  have hrate : ∀ r, GaugeRate.gaugeRate D.xi D.v r (Phi r 0) = -D.xi r (Phi r 0) := by
    intro r
    rw [GaugeRate.gaugeRate, hv1 r (Phi r 0), div_one]
  have hPhicont : Continuous fun r => Phi r 0 :=
    Differentiable.continuous fun r => (hPhid r).differentiableAt
  have hrc : Continuous fun r => GaugeRate.gaugeRate D.xi D.v r (Phi r 0) :=
    (continuous_uncurry_gaugeRate D).comp (continuous_id.prodMk hPhicont)
  have hsmall' : (∫ r in (0 : ℝ)..T, rr * m r) < A := by
    rwa [intervalIntegral.integral_const_mul]
  have h := abs_le_integral_of_window (phi := fun r => Phi r 0)
    (rate := fun r => GaugeRate.gaugeRate D.xi D.v r (Phi r 0)) (b := fun r => rr * m r)
    (A := A) (T := T) hPhid hrc (continuous_const.mul hmc)
    (fun r => mul_nonneg hrr (hmnn r)) hPhi0 hA
    (fun r hr => by
      show |GaugeRate.gaugeRate D.xi D.v r (Phi r 0)| ≤ rr * m r
      rw [hrate r, abs_neg]
      exact hbound r (Phi r 0) hr) hsmall' ht0 htT
  rwa [intervalIntegral.integral_const_mul] at h

end GaugeBaseDrift
