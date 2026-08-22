import Mathlib
import UnitTangentIterates.MatchingPulseErrors

/-!
# The curvature-measure matching in exponential form

`MatchingPulseErrors.lean` supplies the two pulse errors of the theorem
*Curvature-measure matching* of *A Noncircular Oval with Convex Unit-Tangent
Iterates*, and `MatchingTheorem.rear_tail_interval_le` bounds the third error —
the mass of `K_*` omitted by the fundamental interval — by
`C(e^{αp} + e^{−α(p+P)})/α`, `p = x_H(−H/2)` its left endpoint.

This file turns that third bound into an exponential one, using the paper's
`x_H(s) = s + O(1)` and `P = H + O(1)`, and assembles the matching theorem in
the exponential form of the paper:

```
  ∫_{J_H} |k_H − K_P| ≤ Ce^{−βH} ,
```

for every `β < α/2`.  Only the front periodization error `e₄` — the content of
the lemma *Front periodization error*, whose overlap bound is in
`FrontPeriodization.lean` — is carried as a hypothesis, in the exponential form
in which the paper produces it.

* `rearTailConst`, `pulseConst` : the explicit constants;
* `rear_tail_exp` : the omitted mass is at most `rearTailConst · e^{−αH/2}`
  once the endpoints of the fundamental interval are `±H/2 + O(1)`;
* `curvature_measure_matching_exp_of_pulse` : the matching theorem with the
  three rear errors produced, in the form `≤ Ce^{−βH}`.
-/

noncomputable section

open MeasureTheory Set Function

namespace MatchingExponential

/-- The constant of the omitted-mass bound: with `|K_*| ≤ C e^{−α|·|}` and the
endpoints of the fundamental interval within `B` of `±H/2`, the omitted mass is
at most `(2Ce^{αB}/α) e^{−αH/2}`. -/
def rearTailConst (C alpha B : ℝ) : ℝ := 2 * C * Real.exp (alpha * B) / alpha

/-- The constant of the two pulse errors of
`MatchingPulseErrors.pulse_errors_periodization`. -/
def pulseConst (C Km Kd Lam alpha beta : ℝ) : ℝ :=
  4 * C * (1 + Km * Lam) * (1 / ((alpha / 2 - beta) * Real.exp 1))
    + 4 * C * Kd * Lam * (2 / ((alpha / 2 - beta) * Real.exp 1)) ^ 2

/-! ### The omitted mass, exponentially -/

/-- **The omitted mass is exponentially small.**  This is
`MatchingTheorem.rear_tail_interval_le` together with the paper's
`x_H(s) = s + O(1)` and `P = H + O(1)`: if the fundamental interval
`[p, p + P]` has `p ≤ −H/2 + B` and `p + P ≥ H/2 − B`, then

`∫_{−H/2}^{H/2} |c_H ∑_{j≠0} K_*(x_H − jP)| ≤ rearTailConst C α B · e^{−αH/2}`. -/
theorem rear_tail_exp {xH cH Kstar : ℝ → ℝ} {H P C alpha B : ℝ}
    (hH : 0 ≤ H)
    (hx : ∀ t, HasDerivAt xH (cH t) t) (hpos : ∀ t, 0 < cH t)
    (hP : xH (H / 2) = xH (-(H / 2)) + P) (hPpos : 0 < P) (halpha : 0 < alpha)
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ C * Real.exp (-alpha * |s|))
    (hp : xH (-(H / 2)) ≤ 0) (hq : 0 ≤ xH (-(H / 2)) + P)
    (hpB : xH (-(H / 2)) ≤ -(H / 2) + B) (hqB : H / 2 - B ≤ xH (-(H / 2)) + P) :
    (∫ s in (-(H / 2))..(H / 2),
        |cH s * ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)|)
      ≤ rearTailConst C alpha B * Real.exp (-(alpha / 2 * H)) := by
  have hab : -(H / 2) ≤ H / 2 := by linarith
  have hC : 0 ≤ C := by
    have h := hKbd 0
    have h0 := le_abs_self (Kstar 0)
    have h1 := hK0 0
    simp at h
    linarith
  have h := MatchingTheorem.rear_tail_interval_le (xH := xH) (cH := cH) (Kstar := Kstar)
    (a := -(H / 2)) (b := H / 2) (P := P) hab hx hpos hP hPpos halpha hKint hK0 hKbd hp hq
  refine h.trans ?_
  have hleft : Real.exp (alpha * xH (-(H / 2))) ≤ Real.exp (alpha * B) *
      Real.exp (-(alpha / 2 * H)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hright : Real.exp (-alpha * (xH (-(H / 2)) + P)) ≤ Real.exp (alpha * B) *
      Real.exp (-(alpha / 2 * H)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hCa : 0 ≤ C / alpha := by positivity
  have h1 : C * Real.exp (alpha * xH (-(H / 2))) / alpha
      ≤ C / alpha * (Real.exp (alpha * B) * Real.exp (-(alpha / 2 * H))) := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left hleft hCa
  have h2 : C * Real.exp (-alpha * (xH (-(H / 2)) + P)) / alpha
      ≤ C / alpha * (Real.exp (alpha * B) * Real.exp (-(alpha / 2 * H))) := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left hright hCa
  have hsum : C / alpha * (Real.exp (alpha * B) * Real.exp (-(alpha / 2 * H)))
      + C / alpha * (Real.exp (alpha * B) * Real.exp (-(alpha / 2 * H)))
      = rearTailConst C alpha B * Real.exp (-(alpha / 2 * H)) := by
    unfold rearTailConst
    field_simp
    ring
  linarith

/-! ### The theorem -/

/-- **Curvature-measure matching, exponentially, with the rear errors
produced.**  The steering mass `y` of the isolated pulse decays like
`Ce^{−α|s|}`, `Y_H` is its `H`-periodization, both are bounded by `a < 1`, the
rear arclengths `x`, `x_H` are their primitives with a common origin, the
isolated relation `y = √(1−y²)K_*(x)` holds, and the curvature profile `K_*`
and its derivative are bounded by `Km`, `Kd`; the fundamental interval
`[x_H(−H/2), x_H(−H/2) + P]` has its endpoints within `B` of `±H/2`, and the
front periodization error is at most `C₄e^{−βH}`.  Then, for every
`β < α/2`,

`∫_{J_H} |k_H − K_P| ≤ (pulseConst + rearTailConst + C₄) e^{−βH}`.

The three rear terms are the two pulse errors and the omitted mass; only the
front periodization error is assumed. -/
theorem curvature_measure_matching_exp_of_pulse
    {Y y xH x Kstar Kstar' kH Kbar KP : ℝ → ℝ}
    {a C CK alpha beta H P B Km Kd C4 : ℝ}
    (ha : 0 < alpha) (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hH : 0 < H) (hq2 : Real.exp (-alpha * H) ≤ 1 / 2)
    (hYdef : ∀ s, Y s = ∑' m : ℤ, y (s - m * H))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hY : Continuous Y) (hy : Continuous y)
    (hYa : ∀ s, |Y s| ≤ a) (hya : ∀ s, |y s| ≤ a)
    (hxH : ∀ t, HasDerivAt xH (Real.sqrt (1 - (Y t) ^ 2)) t)
    (hx : ∀ t, HasDerivAt x (Real.sqrt (1 - (y t) ^ 2)) t)
    (h0 : xH 0 = x 0)
    (hid : ∀ t, y t = Real.sqrt (1 - (y t) ^ 2) * Kstar (x t))
    (hK : ∀ u, |Kstar u| ≤ Km) (hKderiv : ∀ u, HasDerivAt Kstar (Kstar' u) u)
    (hKd' : ∀ u, |Kstar' u| ≤ Kd) (hKcont : Continuous Kstar)
    (hbeta : beta < alpha / 2)
    (hk : ∀ t, kH (xH t) * Real.sqrt (1 - (Y t) ^ 2) = Y t)
    (hkcont : Continuous fun u => |kH u - Kbar u|)
    (hKbar : ∀ u, Kbar u = Kstar u + ∑' j : {j : ℤ // j ≠ 0}, Kstar (u - (j : ℤ) * P))
    (hD : IntervalIntegrable
      (fun s => Real.sqrt (1 - (Y s) ^ 2) *
        ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)) volume (-(H / 2)) (H / 2))
    (hi0 : IntervalIntegrable (fun u => |kH u - KP u|) volume (xH (-(H / 2))) (xH (H / 2)))
    (hi2 : IntervalIntegrable (fun u => |Kbar u - KP u|) volume (xH (-(H / 2))) (xH (H / 2)))
    (hP : xH (H / 2) = xH (-(H / 2)) + P) (hPpos : 0 < P)
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ CK * Real.exp (-alpha * |s|))
    (hp : xH (-(H / 2)) ≤ 0) (hqe : 0 ≤ xH (-(H / 2)) + P)
    (hpB : xH (-(H / 2)) ≤ -(H / 2) + B) (hqB : H / 2 - B ≤ xH (-(H / 2)) + P)
    (h4 : (∫ u in (xH (-(H / 2)))..(xH (H / 2)), |Kbar u - KP u|)
      ≤ C4 * Real.exp (-(beta * H))) :
    (∫ u in (xH (-(H / 2)))..(xH (H / 2)), |kH u - KP u|)
      ≤ (pulseConst C Km Kd (a / Real.sqrt (1 - a ^ 2)) alpha beta
          + rearTailConst CK alpha B + C4) * Real.exp (-(beta * H)) := by
  -- the speed of the closed rear is positive
  have hposY : ∀ t, 0 < Real.sqrt (1 - (Y t) ^ 2) := by
    intro t
    refine Real.sqrt_pos.mpr ?_
    have h := hYa t
    have h2 : (Y t) ^ 2 ≤ a ^ 2 := by
      have := abs_le.mp h; nlinarith [this.1, this.2]
    nlinarith [ha0, ha1]
  -- the omitted mass
  have htail := rear_tail_exp (xH := xH) (cH := fun t => Real.sqrt (1 - (Y t) ^ 2))
    (Kstar := Kstar) (H := H) (P := P) (C := CK) (alpha := alpha) (B := B) hH.le hxH hposY
    hP hPpos ha hKint hK0 hKbd hp hqe hpB hqB
  -- the omitted mass in the exponential of the exponent `β`
  have hmono : Real.exp (-(alpha / 2 * H)) ≤ Real.exp (-(beta * H)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hCK : 0 ≤ CK := by
    have h := hKbd 0
    have h0 := le_abs_self (Kstar 0)
    have h1 := hK0 0
    simp at h
    linarith
  have htailconst : 0 ≤ rearTailConst CK alpha B := by
    unfold rearTailConst; positivity
  have htail' : (∫ s in (-(H / 2))..(H / 2),
      |Real.sqrt (1 - (Y s) ^ 2) * ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)|)
      ≤ rearTailConst CK alpha B * Real.exp (-(beta * H)) :=
    htail.trans (mul_le_mul_of_nonneg_left hmono htailconst)
  -- assemble
  have hmain := MatchingPulseErrors.curvature_measure_matching_of_pulse
    (Y := Y) (y := y) (xH := xH) (x := x) (Kstar := Kstar) (Kstar' := Kstar')
    (kH := kH) (Kbar := Kbar) (KP := KP) (a := a) (T := H / 2)
    (eps := 4 * C * Real.exp (-(alpha / 2 * H))) (Km := Km) (Kd := Kd) (P := P)
    (e3 := rearTailConst CK alpha B * Real.exp (-(beta * H)))
    (e4 := C4 * Real.exp (-(beta * H)))
    ha0 ha1 (by linarith) hY hy hYa hya
    (fun s hs => MatchingPulseErrors.abs_periodization_sub_le ha hy0 hyb hH hq2 hYdef hs)
    hxH hx h0 hid hK hKderiv hKd' hKcont hk hkcont hKbar hD hi0 hi2 htail' h4
  refine hmain.trans ?_
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hLam : (0 : ℝ) ≤ a / Real.sqrt (1 - a ^ 2) := by positivity
  have hKm : 0 ≤ Km := le_trans (abs_nonneg _) (hK 0)
  have hKd0 : 0 ≤ Kd := le_trans (abs_nonneg _) (hKd' 0)
  have hexp := MatchingPulseErrors.pulse_errors_exp (C0 := 4 * C) (alpha := alpha)
    (beta := beta) (Lam := a / Real.sqrt (1 - a ^ 2)) (Km := Km) (Kd := Kd) (H := H)
    hH.le (by linarith) hLam hKm hKd0 hbeta
  unfold pulseConst
  linarith

end MatchingExponential
