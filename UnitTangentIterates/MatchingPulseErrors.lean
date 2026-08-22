import Mathlib
import UnitTangentIterates.MatchingEstimates
import UnitTangentIterates.MatchingTheorem
import UnitTangentIterates.ExpDecay
import UnitTangentIterates.Periodization

/-!
# The two pulse errors of the curvature-measure matching

`MatchingTheorem.curvature_measure_matching` assembles the theorem
*Curvature-measure matching* of *A Noncircular Oval with Convex Unit-Tangent
Iterates* from four error terms.  Two of them are the *pulse errors* over the
cell `I_H = [−H/2, H/2]`,

```
  e₁ = ∫_{I_H} |Y_H − y| ,        e₂ = ∫_{I_H} |y − c_H K_*(x_H)| ,
```

and the paper bounds them by `Ce^{−αH/2}` and `CHe^{−αH/2}` respectively,
from the sup bound on `Y_H − y` supplied by the exponential periodization.
This file supplies both bounds, so that the matching theorem no longer has to
assume them.

The chain is the paper's:

* `integral_abs_le_of_sup` : an `L∞` bound on the cell gives the `L¹` bound
  `2T · ε`;
* `integral_abs_speed_le_of_sup` : hence `‖c_H − c‖_{L¹(I_H)} ≤ Λ · 2Tε`, with
  `Λ = a/√(1−a²)` the Lipschitz constant of `z ↦ √(1−z²)` on `[−a, a]`;
* `abs_arclength_sub_le_of_sup` : hence `‖x_H − x‖_{L^∞(I_H)} ≤ Λ · 2Tε`;
* `abs_second_pulse_le` : the pointwise split
  `y − c_H K_*(x_H) = (c − c_H)K_*(x) + c_H(K_*(x) − K_*(x_H))`, bounded by
  `Km · Λε + Kd · Λ · 2Tε` using `|K_*| ≤ Km`, `|K_*'| ≤ Kd` and `c_H ≤ 1`;
* `integral_second_pulse_le` : the second pulse error, `e₂`;
* `curvature_measure_matching_of_pulse` : the matching theorem with `e₁` and
  `e₂` produced rather than assumed;
* `pulse_errors_exp` : with the cell `T = H/2` and the periodization error
  `ε = C₀e^{−αH/2}`, the two pulse errors together are `O(e^{−βH})` for every
  `β < α/2` (the quadratic factor `H²` is absorbed by `sq_exp_decay`).
-/

noncomputable section

open MeasureTheory Set Function

namespace MatchingPulseErrors

/-! ### From a sup bound on the cell to an `L¹` bound -/

/-- **`L¹ ≤ 2T · L∞` on the cell `[−T, T]`.** -/
theorem integral_abs_le_of_sup {f : ℝ → ℝ} {T eps : ℝ} (hT : 0 ≤ T)
    (hf : Continuous f) (hbd : ∀ s ∈ Icc (-T) T, |f s| ≤ eps) :
    (∫ s in (-T)..T, |f s|) ≤ 2 * T * eps := by
  have hTT : -T ≤ T := by linarith
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (a := -T) (b := T)
    (f := fun s => |f s|) (g := fun _ => eps) hTT
    (hf.abs.intervalIntegrable _ _) (intervalIntegrable_const) hbd
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-! ### The speeds and the arclength functions -/

variable {Y y xH x Kstar Kstar' : ℝ → ℝ} {a T eps Km Kd : ℝ}

/-- **The `L¹` distance of the speeds from the sup distance of the steering
masses**: with `Λ = a/√(1−a²)`,
`‖√(1−Y²) − √(1−y²)‖_{L¹(I)} ≤ Λ · 2Tε`. -/
theorem integral_abs_speed_le_of_sup (ha0 : 0 ≤ a) (ha1 : a < 1) (hT : 0 ≤ T)
    (hY : Continuous Y) (hy : Continuous y)
    (hYa : ∀ s, |Y s| ≤ a) (hya : ∀ s, |y s| ≤ a)
    (heps : ∀ s ∈ Icc (-T) T, |Y s - y s| ≤ eps) :
    (∫ s in (-T)..T, |Real.sqrt (1 - (Y s) ^ 2) - Real.sqrt (1 - (y s) ^ 2)|)
      ≤ a / Real.sqrt (1 - a ^ 2) * (2 * T * eps) := by
  have hTT : -T ≤ T := by linarith
  have hlip : (0 : ℝ) ≤ a / Real.sqrt (1 - a ^ 2) := by positivity
  have h1 := MatchingEstimates.integral_abs_speed_sub_le (Y := Y) (y := y) (a := a)
    (p := -T) (q := T) ha0 ha1 hY hy hTT (fun s _ => hYa s) (fun s _ => hya s)
  have h2 : (∫ s in (-T)..T, |Y s - y s|) ≤ 2 * T * eps :=
    integral_abs_le_of_sup hT (hY.sub hy) heps
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hlip)

/-- **The rear arclength functions stay uniformly close on the cell**:
`|x_H − x| ≤ Λ · 2Tε` on `[−T, T]`. -/
theorem abs_arclength_sub_le_of_sup (ha0 : 0 ≤ a) (ha1 : a < 1) (hT : 0 ≤ T)
    (hY : Continuous Y) (hy : Continuous y)
    (hYa : ∀ s, |Y s| ≤ a) (hya : ∀ s, |y s| ≤ a)
    (heps : ∀ s ∈ Icc (-T) T, |Y s - y s| ≤ eps)
    (hxH : ∀ t, HasDerivAt xH (Real.sqrt (1 - (Y t) ^ 2)) t)
    (hx : ∀ t, HasDerivAt x (Real.sqrt (1 - (y t) ^ 2)) t)
    (h0 : xH 0 = x 0) {s : ℝ} (hs : s ∈ Icc (-T) T) :
    |xH s - x s| ≤ a / Real.sqrt (1 - a ^ 2) * (2 * T * eps) := by
  have hcY : Continuous fun t => Real.sqrt (1 - (Y t) ^ 2) :=
    Real.continuous_sqrt.comp (continuous_const.sub (hY.pow 2))
  have hcy : Continuous fun t => Real.sqrt (1 - (y t) ^ 2) :=
    Real.continuous_sqrt.comp (continuous_const.sub (hy.pow 2))
  exact (MatchingEstimates.abs_arclength_sub_le hxH hx hcY hcy h0 hT hs).trans
    (integral_abs_speed_le_of_sup ha0 ha1 hT hY hy hYa hya heps)

/-! ### The second pulse error -/

/-- A bound for the increment of the curvature profile from a bound on its
derivative. -/
theorem abs_Kstar_sub_le (hKd : ∀ u, HasDerivAt Kstar (Kstar' u) u)
    (hKd' : ∀ u, |Kstar' u| ≤ Kd) (u v : ℝ) :
    |Kstar u - Kstar v| ≤ Kd * |u - v| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Kstar) (f' := Kstar') (s := (univ : Set ℝ)) (C := Kd)
    (fun z _ => (hKd z).hasDerivWithinAt) (fun z _ => by simpa using hKd' z)
    convex_univ (mem_univ v) (mem_univ u)
  simpa [Real.norm_eq_abs] using h

/-- **The pointwise bound for the second pulse error.**  With
`y = c K_*(x)`, `c = √(1−y²)`, `c_H = √(1−Y²)`,

```
  |y − c_H K_*(x_H)| ≤ |c − c_H| |K_*(x)| + c_H |K_*(x) − K_*(x_H)|
                     ≤ Km |c − c_H| + Kd |x − x_H| .
```
-/
theorem abs_second_pulse_le {s : ℝ}
    (hid : ∀ t, y t = Real.sqrt (1 - (y t) ^ 2) * Kstar (x t))
    (hK : ∀ u, |Kstar u| ≤ Km) (hKd : ∀ u, HasDerivAt Kstar (Kstar' u) u)
    (hKd' : ∀ u, |Kstar' u| ≤ Kd) {Lc Lx : ℝ}
    (h1 : |Real.sqrt (1 - (y s) ^ 2) - Real.sqrt (1 - (Y s) ^ 2)| ≤ Lc)
    (h2 : |x s - xH s| ≤ Lx) :
    |y s - Real.sqrt (1 - (Y s) ^ 2) * Kstar (xH s)| ≤ Km * Lc + Kd * Lx := by
  have hcH1 : Real.sqrt (1 - (Y s) ^ 2) ≤ 1 := by
    have : Real.sqrt (1 - (Y s) ^ 2) ≤ Real.sqrt 1 :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Y s)])
    simpa using this
  have hcH0 : 0 ≤ Real.sqrt (1 - (Y s) ^ 2) := Real.sqrt_nonneg _
  have hsplit : y s - Real.sqrt (1 - (Y s) ^ 2) * Kstar (xH s)
      = (Real.sqrt (1 - (y s) ^ 2) - Real.sqrt (1 - (Y s) ^ 2)) * Kstar (x s)
        + Real.sqrt (1 - (Y s) ^ 2) * (Kstar (x s) - Kstar (xH s)) := by
    have h := hid s
    set cy := Real.sqrt (1 - y s ^ 2) with hcydef
    rw [h]; ring
  have hKdiff : |Kstar (x s) - Kstar (xH s)| ≤ Kd * Lx := by
    refine (abs_Kstar_sub_le hKd hKd' _ _).trans ?_
    have hKd0 : 0 ≤ Kd := le_trans (abs_nonneg _) (hKd' 0)
    exact mul_le_mul_of_nonneg_left h2 hKd0
  have hKd0 : 0 ≤ Kd * Lx := le_trans (abs_nonneg _) hKdiff
  calc |y s - Real.sqrt (1 - (Y s) ^ 2) * Kstar (xH s)|
      = |(Real.sqrt (1 - (y s) ^ 2) - Real.sqrt (1 - (Y s) ^ 2)) * Kstar (x s)
          + Real.sqrt (1 - (Y s) ^ 2) * (Kstar (x s) - Kstar (xH s))| := by rw [hsplit]
    _ ≤ |(Real.sqrt (1 - (y s) ^ 2) - Real.sqrt (1 - (Y s) ^ 2)) * Kstar (x s)|
          + |Real.sqrt (1 - (Y s) ^ 2) * (Kstar (x s) - Kstar (xH s))| := abs_add_le _ _
    _ ≤ Km * Lc + Kd * Lx := by
        have hA : |(Real.sqrt (1 - (y s) ^ 2) - Real.sqrt (1 - (Y s) ^ 2)) * Kstar (x s)|
            ≤ Km * Lc := by
          rw [abs_mul]
          calc |Real.sqrt (1 - (y s) ^ 2) - Real.sqrt (1 - (Y s) ^ 2)| * |Kstar (x s)|
              ≤ Lc * Km := by
                exact mul_le_mul h1 (hK _) (abs_nonneg _) (le_trans (abs_nonneg _) h1)
            _ = Km * Lc := by ring
        have hB : |Real.sqrt (1 - (Y s) ^ 2) * (Kstar (x s) - Kstar (xH s))| ≤ Kd * Lx := by
          rw [abs_mul, abs_of_nonneg hcH0]
          calc Real.sqrt (1 - (Y s) ^ 2) * |Kstar (x s) - Kstar (xH s)|
              ≤ 1 * (Kd * Lx) :=
                mul_le_mul hcH1 hKdiff (abs_nonneg _) zero_le_one
            _ = Kd * Lx := by ring
        linarith

/-- **The second pulse error over the cell.**  With `Λ = a/√(1−a²)`,

`∫_{−T}^{T} |y − c_H K_*(x_H)| ≤ 2T (Km Λε + Kd Λ 2Tε)`. -/
theorem integral_second_pulse_le (ha0 : 0 ≤ a) (ha1 : a < 1) (hT : 0 ≤ T)
    (hY : Continuous Y) (hy : Continuous y)
    (hYa : ∀ s, |Y s| ≤ a) (hya : ∀ s, |y s| ≤ a)
    (heps : ∀ s ∈ Icc (-T) T, |Y s - y s| ≤ eps)
    (hxH : ∀ t, HasDerivAt xH (Real.sqrt (1 - (Y t) ^ 2)) t)
    (hx : ∀ t, HasDerivAt x (Real.sqrt (1 - (y t) ^ 2)) t)
    (h0 : xH 0 = x 0)
    (hid : ∀ t, y t = Real.sqrt (1 - (y t) ^ 2) * Kstar (x t))
    (hK : ∀ u, |Kstar u| ≤ Km) (hKd : ∀ u, HasDerivAt Kstar (Kstar' u) u)
    (hKd' : ∀ u, |Kstar' u| ≤ Kd) (hKcont : Continuous Kstar) :
    (∫ s in (-T)..T, |y s - Real.sqrt (1 - (Y s) ^ 2) * Kstar (xH s)|)
      ≤ 2 * T * (Km * (a / Real.sqrt (1 - a ^ 2) * eps)
          + Kd * (a / Real.sqrt (1 - a ^ 2) * (2 * T * eps))) := by
  have hlip : (0 : ℝ) ≤ a / Real.sqrt (1 - a ^ 2) := by positivity
  have hxHc : Continuous xH :=
    continuous_iff_continuousAt.2 fun t => (hxH t).differentiableAt.continuousAt
  have hcYc : Continuous fun t => Real.sqrt (1 - (Y t) ^ 2) :=
    Real.continuous_sqrt.comp (continuous_const.sub (hY.pow 2))
  have hcont : Continuous fun s => y s - Real.sqrt (1 - (Y s) ^ 2) * Kstar (xH s) :=
    hy.sub (hcYc.mul (hKcont.comp hxHc))
  refine integral_abs_le_of_sup hT hcont (fun s hs => ?_)
  have h1 : |Real.sqrt (1 - (y s) ^ 2) - Real.sqrt (1 - (Y s) ^ 2)|
      ≤ a / Real.sqrt (1 - a ^ 2) * eps := by
    refine (MatchingEstimates.abs_sqrt_one_sub_sq_sub_le ha0 ha1 (hya s) (hYa s)).trans ?_
    have : |y s - Y s| ≤ eps := by
      rw [abs_sub_comm]; exact heps s hs
    exact mul_le_mul_of_nonneg_left this hlip
  have h2 : |x s - xH s| ≤ a / Real.sqrt (1 - a ^ 2) * (2 * T * eps) := by
    rw [abs_sub_comm]
    exact abs_arclength_sub_le_of_sup ha0 ha1 hT hY hy hYa hya heps hxH hx h0 hs
  exact abs_second_pulse_le hid hK hKd hKd' h1 h2

/-! ### The matching theorem with the pulse errors produced -/

/-- **Curvature-measure matching with the two pulse errors produced.**  The
hypotheses on the steering masses are the geometric ones — `|Y_H|, |y| ≤ a < 1`,
the identity `y = c K_*(x)`, the sup bound `|Y_H − y| ≤ ε` on the cell supplied
by the exponential periodization, and bounds `Km`, `Kd` for the profile and its
derivative — and the two pulse errors are the explicit quantities they give.
Only the omitted mass `e₃` and the front periodization error `e₄` remain as
hypotheses; those are supplied by `MatchingTheorem.rear_tail_interval_le` and
`FrontPeriodization.lean`. -/
theorem curvature_measure_matching_of_pulse
    {kH Kbar KP : ℝ → ℝ} {P e3 e4 : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hT : 0 ≤ T)
    (hY : Continuous Y) (hy : Continuous y)
    (hYa : ∀ s, |Y s| ≤ a) (hya : ∀ s, |y s| ≤ a)
    (heps : ∀ s ∈ Icc (-T) T, |Y s - y s| ≤ eps)
    (hxH : ∀ t, HasDerivAt xH (Real.sqrt (1 - (Y t) ^ 2)) t)
    (hx : ∀ t, HasDerivAt x (Real.sqrt (1 - (y t) ^ 2)) t)
    (h0 : xH 0 = x 0)
    (hid : ∀ t, y t = Real.sqrt (1 - (y t) ^ 2) * Kstar (x t))
    (hK : ∀ u, |Kstar u| ≤ Km) (hKd : ∀ u, HasDerivAt Kstar (Kstar' u) u)
    (hKd' : ∀ u, |Kstar' u| ≤ Kd) (hKcont : Continuous Kstar)
    (hk : ∀ t, kH (xH t) * Real.sqrt (1 - (Y t) ^ 2) = Y t)
    (hkcont : Continuous fun u => |kH u - Kbar u|)
    (hKbar : ∀ u, Kbar u = Kstar u + ∑' j : {j : ℤ // j ≠ 0}, Kstar (u - (j : ℤ) * P))
    (hD : IntervalIntegrable
      (fun s => Real.sqrt (1 - (Y s) ^ 2) *
        ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)) volume (-T) T)
    (hi0 : IntervalIntegrable (fun u => |kH u - KP u|) volume (xH (-T)) (xH T))
    (hi2 : IntervalIntegrable (fun u => |Kbar u - KP u|) volume (xH (-T)) (xH T))
    (h3 : (∫ s in (-T)..T, |Real.sqrt (1 - (Y s) ^ 2) *
      ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)|) ≤ e3)
    (h4 : (∫ u in (xH (-T))..(xH T), |Kbar u - KP u|) ≤ e4) :
    (∫ u in (xH (-T))..(xH T), |kH u - KP u|)
      ≤ 2 * T * eps
        + 2 * T * (Km * (a / Real.sqrt (1 - a ^ 2) * eps)
            + Kd * (a / Real.sqrt (1 - a ^ 2) * (2 * T * eps)))
        + e3 + e4 := by
  have hTT : -T ≤ T := by linarith
  have hcYc : Continuous fun t => Real.sqrt (1 - (Y t) ^ 2) :=
    Real.continuous_sqrt.comp (continuous_const.sub (hY.pow 2))
  have hxHc : Continuous xH :=
    continuous_iff_continuousAt.2 fun t => (hxH t).differentiableAt.continuousAt
  have hpos : ∀ t, 0 < Real.sqrt (1 - (Y t) ^ 2) := by
    intro t
    refine Real.sqrt_pos.mpr ?_
    have h := hYa t
    have h2 : (Y t) ^ 2 ≤ a ^ 2 := by
      have := abs_le.mp h; nlinarith [this.1, this.2]
    nlinarith [ha0, ha1]
  refine MatchingTheorem.curvature_measure_matching hTT hxH hcYc hpos hk hkcont hKbar
    ((hY.sub hy).intervalIntegrable _ _)
    ((hy.sub (hcYc.mul (hKcont.comp hxHc))).intervalIntegrable _ _)
    hD hi0 hi2 ?_ ?_ h3 h4
  · exact integral_abs_le_of_sup hT (hY.sub hy) heps
  · exact integral_second_pulse_le ha0 ha1 hT hY hy hYa hya heps hxH hx h0 hid hK hKd hKd'
      hKcont

/-! ### The exponential form -/

/-- **Absorbing a quadratic factor into the exponential**: for `b' < b` and
`x ≥ 0`, `x²e^{−bx} ≤ (2/((b−b')e))² e^{−b'x}`. -/
theorem sq_exp_decay {b b' x : ℝ} (hb : b' < b) (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-(b * x)) ≤ (2 / ((b - b') * Real.exp 1)) ^ 2 * Real.exp (-(b' * x)) := by
  set m : ℝ := (b + b') / 2 with hm
  have hmb : m < b := by rw [hm]; linarith
  have hbm : b' < m := by rw [hm]; linarith
  have hK : (0 : ℝ) < 2 / ((b - b') * Real.exp 1) := by
    have : (0 : ℝ) < b - b' := by linarith
    positivity
  have h1 : x * Real.exp (-(b * x)) ≤ (2 / ((b - b') * Real.exp 1)) * Real.exp (-(m * x)) := by
    have := ExpDecay.linear_exp_decay (b := b) (b' := m) (x := x) hmb
    have hbm2 : b - m = (b - b') / 2 := by rw [hm]; ring
    have heq : 1 / ((b - m) * Real.exp 1) = 2 / ((b - b') * Real.exp 1) := by
      rw [hbm2]
      have hne : b - b' ≠ 0 := ne_of_gt (by linarith)
      have hexp : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
      field_simp
    rwa [heq] at this
  have h2 : x * Real.exp (-(m * x)) ≤ (2 / ((b - b') * Real.exp 1)) * Real.exp (-(b' * x)) := by
    have := ExpDecay.linear_exp_decay (b := m) (b' := b') (x := x) hbm
    have hbm2 : m - b' = (b - b') / 2 := by rw [hm]; ring
    have heq : 1 / ((m - b') * Real.exp 1) = 2 / ((b - b') * Real.exp 1) := by
      rw [hbm2]
      have hne : b - b' ≠ 0 := ne_of_gt (by linarith)
      have hexp : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
      field_simp
    rwa [heq] at this
  calc x ^ 2 * Real.exp (-(b * x)) = x * (x * Real.exp (-(b * x))) := by ring
    _ ≤ x * ((2 / ((b - b') * Real.exp 1)) * Real.exp (-(m * x))) :=
        mul_le_mul_of_nonneg_left h1 hx
    _ = (2 / ((b - b') * Real.exp 1)) * (x * Real.exp (-(m * x))) := by ring
    _ ≤ (2 / ((b - b') * Real.exp 1)) *
          ((2 / ((b - b') * Real.exp 1)) * Real.exp (-(b' * x))) :=
        mul_le_mul_of_nonneg_left h2 hK.le
    _ = (2 / ((b - b') * Real.exp 1)) ^ 2 * Real.exp (-(b' * x)) := by ring

/-- **The two pulse errors are exponentially small.**  On the cell `T = H/2`,
with the periodization error `ε = C₀e^{−αH/2}` of `Periodization.lean`, the sum
of the two pulse errors is at most `Ce^{−βH}` for every `β < α/2`, the constant
being explicit in `C₀`, `Km`, `Kd`, `Λ = a/√(1−a²)` and `α/2 − β`. -/
theorem pulse_errors_exp {C0 alpha beta Lam H : ℝ} (hH : 0 ≤ H) (hC0 : 0 ≤ C0)
    (hLam : 0 ≤ Lam) (hKm : 0 ≤ Km) (hKd : 0 ≤ Kd) (hbeta : beta < alpha / 2) :
    2 * (H / 2) * (C0 * Real.exp (-(alpha / 2 * H)))
        + 2 * (H / 2) * (Km * (Lam * (C0 * Real.exp (-(alpha / 2 * H))))
          + Kd * (Lam * (2 * (H / 2) * (C0 * Real.exp (-(alpha / 2 * H))))))
      ≤ (C0 * (1 + Km * Lam) * (1 / ((alpha / 2 - beta) * Real.exp 1))
          + C0 * Kd * Lam * (2 / ((alpha / 2 - beta) * Real.exp 1)) ^ 2)
        * Real.exp (-(beta * H)) := by
  have hlin := ExpDecay.linear_exp_decay (b := alpha / 2) (b' := beta) (x := H) hbeta
  have hsq := sq_exp_decay (b := alpha / 2) (b' := beta) (x := H) hbeta hH
  have hc1 : 0 ≤ C0 * (1 + Km * Lam) := by positivity
  have hc2 : 0 ≤ C0 * Kd * Lam := by positivity
  have hlhs : 2 * (H / 2) * (C0 * Real.exp (-(alpha / 2 * H)))
      + 2 * (H / 2) * (Km * (Lam * (C0 * Real.exp (-(alpha / 2 * H))))
        + Kd * (Lam * (2 * (H / 2) * (C0 * Real.exp (-(alpha / 2 * H))))))
      = C0 * (1 + Km * Lam) * (H * Real.exp (-(alpha / 2 * H)))
        + C0 * Kd * Lam * (H ^ 2 * Real.exp (-(alpha / 2 * H))) := by ring
  rw [hlhs]
  have h1 := mul_le_mul_of_nonneg_left hlin hc1
  have h2 := mul_le_mul_of_nonneg_left hsq hc2
  nlinarith [h1, h2]

/-! ### The pulse errors from the exponential periodization -/

/-- **The sup bound on the cell supplied by the exponential periodization.**
If `y ≥ 0` decays like `Ce^{−a|s|}` and `Y` is its `H`-periodization, then
`|Y − y| ≤ 4Ce^{−aH/2}` on `[−H/2, H/2]`. -/
theorem abs_periodization_sub_le {C alpha H : ℝ} (ha : 0 < alpha)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hH : 0 < H) (hq : Real.exp (-alpha * H) ≤ 1 / 2)
    (hYdef : ∀ s, Y s = ∑' m : ℤ, y (s - m * H))
    {s : ℝ} (hs : s ∈ Icc (-(H / 2)) (H / 2)) :
    |Y s - y s| ≤ 4 * C * Real.exp (-(alpha / 2 * H)) := by
  have habs : |s| ≤ H / 2 := abs_le.mpr ⟨hs.1, hs.2⟩
  have h := Periodization.periodization_error_le (z := y) (C := C) (a := alpha) (H := H)
    (s := s) ha hy0 hyb hH hq habs
  rw [hYdef s]
  have hform : Real.exp (-(alpha / 2) * H) = Real.exp (-(alpha / 2 * H)) := by ring_nf
  rwa [hform] at h

/-- **The two pulse errors of the matching theorem are exponentially small.**
This is the paper's estimate

```
  ‖Y_H − y‖_{L¹(I_H)} + ‖y − c_H K_*(x_H)‖_{L¹(I_H)} ≤ Ce^{−βH} ,
```

with every ingredient supplied: the sup bound on the cell comes from the
exponential periodization of the pulse `y`, the `L¹` bounds from
`integral_abs_le_of_sup` and `integral_second_pulse_le`, and the polynomial
factors `H` and `H²` are absorbed into the exponential for any `β < α/2`. -/
theorem pulse_errors_periodization {C alpha H beta : ℝ}
    (ha : 0 < alpha) (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hH : 0 < H) (hq : Real.exp (-alpha * H) ≤ 1 / 2)
    (hYdef : ∀ s, Y s = ∑' m : ℤ, y (s - m * H))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hY : Continuous Y) (hy : Continuous y)
    (hYa : ∀ s, |Y s| ≤ a) (hya : ∀ s, |y s| ≤ a)
    (hxH : ∀ t, HasDerivAt xH (Real.sqrt (1 - (Y t) ^ 2)) t)
    (hx : ∀ t, HasDerivAt x (Real.sqrt (1 - (y t) ^ 2)) t)
    (h0 : xH 0 = x 0)
    (hid : ∀ t, y t = Real.sqrt (1 - (y t) ^ 2) * Kstar (x t))
    (hK : ∀ u, |Kstar u| ≤ Km) (hKd : ∀ u, HasDerivAt Kstar (Kstar' u) u)
    (hKd' : ∀ u, |Kstar' u| ≤ Kd) (hKcont : Continuous Kstar)
    (hbeta : beta < alpha / 2) :
    (∫ s in (-(H / 2))..(H / 2), |Y s - y s|)
        + (∫ s in (-(H / 2))..(H / 2),
            |y s - Real.sqrt (1 - (Y s) ^ 2) * Kstar (xH s)|)
      ≤ (4 * C * (1 + Km * (a / Real.sqrt (1 - a ^ 2)))
              * (1 / ((alpha / 2 - beta) * Real.exp 1))
            + 4 * C * Kd * (a / Real.sqrt (1 - a ^ 2))
              * (2 / ((alpha / 2 - beta) * Real.exp 1)) ^ 2)
        * Real.exp (-(beta * H)) := by
  have hT : (0 : ℝ) ≤ H / 2 := by linarith
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hLam : (0 : ℝ) ≤ a / Real.sqrt (1 - a ^ 2) := by positivity
  have hKm : 0 ≤ Km := le_trans (abs_nonneg _) (hK 0)
  have hKd0 : 0 ≤ Kd := le_trans (abs_nonneg _) (hKd' 0)
  have hsup : ∀ s ∈ Icc (-(H / 2)) (H / 2),
      |Y s - y s| ≤ 4 * C * Real.exp (-(alpha / 2 * H)) :=
    fun s hs => abs_periodization_sub_le ha hy0 hyb hH hq hYdef hs
  have h1 := integral_abs_le_of_sup (T := H / 2) hT (hY.sub hy) hsup
  have h2 := integral_second_pulse_le (a := a) (T := H / 2)
    (eps := 4 * C * Real.exp (-(alpha / 2 * H)))
    ha0 ha1 hT hY hy hYa hya hsup hxH hx h0 hid hK hKd hKd' hKcont
  have h3 := pulse_errors_exp (C0 := 4 * C) (alpha := alpha) (beta := beta)
    (Lam := a / Real.sqrt (1 - a ^ 2)) (Km := Km) (Kd := Kd) (H := H)
    (by linarith) (by linarith) hLam hKm hKd0 hbeta
  linarith

end MatchingPulseErrors
