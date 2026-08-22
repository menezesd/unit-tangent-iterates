import Mathlib
import UnitTangentIterates.CellAsymptotics

/-!
# Comparison estimates for the curvature-measure matching

This file formalizes three quantitative steps in the proof of the theorem
*Curvature-measure matching* of *A Noncircular Oval with Convex Unit-Tangent
Iterates*:

> Since `c_H = √(1 − Y_H²)` and `c = √(1 − y²)` stay uniformly positive,
> `‖c_H − c‖_{L¹(I_H)} ≤ Ce^{−αH/2}` and `‖x_H − x‖_{L^∞(I_H)} ≤ Ce^{−αH/2}`.
> ... The endpoints of `J_H` are `±H/2 + O(1)`, and the exponential tails of
> `K_*` make `∫_{ℝ∖J_H} K_*` exponentially small.

Main results:

* `abs_sqrt_one_sub_sq_sub_le` : `z ↦ √(1 − z²)` is Lipschitz on `[−a, a]`
  with constant `a/√(1 − a²)` for `0 ≤ a < 1`;
* `integral_abs_speed_sub_le` : hence the `L¹` distance of the speeds `c_H`
  and `c` is controlled by that of the steering masses `Y_H` and `y`;
* `abs_arclength_sub_le` : the sup distance of the rear arclength functions is
  controlled by the same `L¹` distance;
* `abs_integral_compl_le` : the integral of an exponentially localized
  function outside an interval `[p, q]` (with `p ≤ 0 ≤ q`) is at most
  `C(e^{αp} + e^{−αq})/α`.
-/

noncomputable section

open MeasureTheory Set Real

namespace MatchingEstimates

/-! ### The speed is a Lipschitz function of the steering mass -/

/-- **`z ↦ √(1 − z²)` is Lipschitz on `[−a, a]`** with constant
`a / √(1 − a²)`, for `0 ≤ a < 1`. -/
theorem abs_sqrt_one_sub_sq_sub_le {a z w : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hz : |z| ≤ a) (hw : |w| ≤ a) :
    |Real.sqrt (1 - z ^ 2) - Real.sqrt (1 - w ^ 2)| ≤ a / Real.sqrt (1 - a ^ 2) * |z - w| := by
  have ha2 : a ^ 2 < 1 := by nlinarith [abs_nonneg z]
  have hden : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hz2 : z ^ 2 ≤ a ^ 2 := by
    have := abs_le.mp hz
    nlinarith [this.1, this.2]
  have hw2 : w ^ 2 ≤ a ^ 2 := by
    have := abs_le.mp hw
    nlinarith [this.1, this.2]
  have hzs : Real.sqrt (1 - a ^ 2) ≤ Real.sqrt (1 - z ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have hws : Real.sqrt (1 - a ^ 2) ≤ Real.sqrt (1 - w ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have hzsq : Real.sqrt (1 - z ^ 2) ^ 2 = 1 - z ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  have hwsq : Real.sqrt (1 - w ^ 2) ^ 2 = 1 - w ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  have hsum : 0 < Real.sqrt (1 - z ^ 2) + Real.sqrt (1 - w ^ 2) := by linarith
  have hfac : (Real.sqrt (1 - z ^ 2) - Real.sqrt (1 - w ^ 2))
      * (Real.sqrt (1 - z ^ 2) + Real.sqrt (1 - w ^ 2)) = (w - z) * (w + z) := by
    have : Real.sqrt (1 - z ^ 2) * Real.sqrt (1 - z ^ 2) = 1 - z ^ 2 := by
      nlinarith [hzsq]
    have h2 : Real.sqrt (1 - w ^ 2) * Real.sqrt (1 - w ^ 2) = 1 - w ^ 2 := by
      nlinarith [hwsq]
    nlinarith [this, h2]
  have habs : |Real.sqrt (1 - z ^ 2) - Real.sqrt (1 - w ^ 2)|
      * (Real.sqrt (1 - z ^ 2) + Real.sqrt (1 - w ^ 2)) = |w - z| * |w + z| := by
    have hmul : |(Real.sqrt (1 - z ^ 2) - Real.sqrt (1 - w ^ 2))
        * (Real.sqrt (1 - z ^ 2) + Real.sqrt (1 - w ^ 2))|
        = |Real.sqrt (1 - z ^ 2) - Real.sqrt (1 - w ^ 2)|
          * (Real.sqrt (1 - z ^ 2) + Real.sqrt (1 - w ^ 2)) := by
      rw [abs_mul, abs_of_pos hsum]
    rw [← hmul, hfac, abs_mul]
  have hwz : |w + z| ≤ 2 * a := by
    calc |w + z| ≤ |w| + |z| := abs_add_le _ _
      _ ≤ 2 * a := by linarith
  have hkey : |Real.sqrt (1 - z ^ 2) - Real.sqrt (1 - w ^ 2)| * (2 * Real.sqrt (1 - a ^ 2))
      ≤ 2 * a * |z - w| := by
    calc |Real.sqrt (1 - z ^ 2) - Real.sqrt (1 - w ^ 2)| * (2 * Real.sqrt (1 - a ^ 2))
        ≤ |Real.sqrt (1 - z ^ 2) - Real.sqrt (1 - w ^ 2)|
            * (Real.sqrt (1 - z ^ 2) + Real.sqrt (1 - w ^ 2)) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = |w - z| * |w + z| := habs
      _ ≤ |z - w| * (2 * a) := by
          rw [abs_sub_comm w z]
          exact mul_le_mul_of_nonneg_left hwz (abs_nonneg _)
      _ = 2 * a * |z - w| := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith [hkey, abs_nonneg (Real.sqrt (1 - z ^ 2) - Real.sqrt (1 - w ^ 2))]

/-- **The `L¹` distance of the speeds is controlled by that of the steering
masses**: if `|Y|, |y| ≤ a < 1` on `[p, q]`, then

`∫_p^q |√(1−Y²) − √(1−y²)| ≤ (a/√(1−a²)) ∫_p^q |Y − y|`. -/
theorem integral_abs_speed_sub_le {Y y : ℝ → ℝ} {a p q : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hY : Continuous Y) (hy : Continuous y) (hpq : p ≤ q)
    (hYa : ∀ s ∈ Icc p q, |Y s| ≤ a) (hya : ∀ s ∈ Icc p q, |y s| ≤ a) :
    (∫ s in p..q, |Real.sqrt (1 - (Y s) ^ 2) - Real.sqrt (1 - (y s) ^ 2)|)
      ≤ a / Real.sqrt (1 - a ^ 2) * ∫ s in p..q, |Y s - y s| := by
  have hcY : Continuous fun s => Real.sqrt (1 - (Y s) ^ 2) :=
    Real.continuous_sqrt.comp (by continuity)
  have hcy : Continuous fun s => Real.sqrt (1 - (y s) ^ 2) :=
    Real.continuous_sqrt.comp (by continuity)
  have hL : Continuous fun s => |Real.sqrt (1 - (Y s) ^ 2) - Real.sqrt (1 - (y s) ^ 2)| :=
    (hcY.sub hcy).abs
  have hR : Continuous fun s => a / Real.sqrt (1 - a ^ 2) * |Y s - y s| :=
    continuous_const.mul ((hY.sub hy).abs)
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (a := p) (b := q)
    (f := fun s => |Real.sqrt (1 - (Y s) ^ 2) - Real.sqrt (1 - (y s) ^ 2)|)
    (g := fun s => a / Real.sqrt (1 - a ^ 2) * |Y s - y s|) hpq
    (hL.intervalIntegrable _ _) (hR.intervalIntegrable _ _)
    (fun s hs => abs_sqrt_one_sub_sq_sub_le ha0 ha1 (hYa s hs) (hya s hs))
  rwa [intervalIntegral.integral_const_mul] at hmono

/-! ### The arclength functions -/

/-- **The rear arclength functions stay uniformly close**: if `x_H` and `x`
have derivatives `c_H` and `c` and agree at `0`, then on `[-T, T]` their
difference is bounded by the `L¹` distance of the speeds. -/
theorem abs_arclength_sub_le {xH x cH c : ℝ → ℝ} {T s : ℝ}
    (hxH : ∀ t, HasDerivAt xH (cH t) t) (hx : ∀ t, HasDerivAt x (c t) t)
    (hcH : Continuous cH) (hc : Continuous c) (h0 : xH 0 = x 0)
    (hT : 0 ≤ T) (hs : s ∈ Icc (-T) T) :
    |xH s - x s| ≤ ∫ t in (-T)..T, |cH t - c t| := by
  have hdiff : ∀ t, HasDerivAt (fun u => xH u - x u) (cH t - c t) t :=
    fun t => (hxH t).sub (hx t)
  have hfund : xH s - x s = ∫ t in (0:ℝ)..s, (cH t - c t) := by
    have hthis := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => xH u - x u)
      (f' := fun t => cH t - c t) (a := 0) (b := s)
      (fun t _ => hdiff t) ((hcH.sub hc).intervalIntegrable _ _)
    have hbeta : (∫ t in (0:ℝ)..s, (cH t - c t)) = (xH s - x s) - (xH 0 - x 0) := hthis
    rw [hbeta, h0]
    ring
  have hnn : ∀ t, 0 ≤ |cH t - c t| := fun t => abs_nonneg _
  rw [hfund]
  rcases le_total (0:ℝ) s with h | h
  · have h1 : |∫ t in (0:ℝ)..s, (cH t - c t)| ≤ ∫ t in (0:ℝ)..s, |cH t - c t| :=
      intervalIntegral.abs_integral_le_integral_abs h
    have h2 : (∫ t in (0:ℝ)..s, |cH t - c t|) ≤ ∫ t in (-T)..T, |cH t - c t| := by
      refine intervalIntegral.integral_mono_interval (by linarith [hs.1]) h hs.2
        (Filter.Eventually.of_forall (fun t => hnn t))
        (((hcH.sub hc).abs).intervalIntegrable _ _)
    linarith
  · have h1 : |∫ t in (0:ℝ)..s, (cH t - c t)| ≤ ∫ t in s..(0:ℝ), |cH t - c t| := by
      have hsym : (∫ t in (0:ℝ)..s, (cH t - c t)) = -∫ t in s..(0:ℝ), (cH t - c t) :=
        intervalIntegral.integral_symm s 0
      rw [hsym, abs_neg]
      exact intervalIntegral.abs_integral_le_integral_abs h
    have h2 : (∫ t in s..(0:ℝ), |cH t - c t|) ≤ ∫ t in (-T)..T, |cH t - c t| := by
      refine intervalIntegral.integral_mono_interval hs.1 h (by linarith [hs.2])
        (Filter.Eventually.of_forall (fun t => hnn t))
        (((hcH.sub hc).abs).intervalIntegrable _ _)
    linarith

/-! ### The tail outside a fundamental interval -/

/-- **The mass of an exponentially localized function outside an interval**
`[p, q]` with `p ≤ 0 ≤ q` is at most `C(e^{αp} + e^{−αq})/α`.  This is the
estimate `∫_{ℝ∖J_H} K_*` of the matching proof, with `J_H = [p, q]` an
interval whose endpoints are `±H/2 + O(1)`. -/
theorem abs_integral_compl_le {g : ℝ → ℝ} {C alpha p q : ℝ} (ha : 0 < alpha)
    (hp : p ≤ 0) (hq : 0 ≤ q) (hg : Integrable g)
    (hbd : ∀ s, |g s| ≤ C * Real.exp (-alpha * |s|)) :
    |(∫ s : ℝ, g s) - ∫ s in p..q, g s|
      ≤ C * Real.exp (alpha * p) / alpha + C * Real.exp (-alpha * q) / alpha := by
  have hsplit1 : (∫ s in Iic p, g s) + (∫ s in Ioi p, g s) = ∫ s : ℝ, g s :=
    intervalIntegral.integral_Iic_add_Ioi hg.integrableOn hg.integrableOn
  have hsplit2 : (∫ s in p..q, g s) + (∫ s in Ioi q, g s) = ∫ s in Ioi p, g s :=
    intervalIntegral.integral_interval_add_Ioi hg.integrableOn hg.integrableOn
  have hkey : (∫ s : ℝ, g s) - ∫ s in p..q, g s
      = (∫ s in Iic p, g s) + ∫ s in Ioi q, g s := by linarith [hsplit1, hsplit2]
  have hleft := CellAsymptotics.abs_integral_Iic_le (g := g) ha hp hg hbd
  have hright := CellAsymptotics.abs_integral_Ioi_le (g := g) ha hq hg hbd
  calc |(∫ s : ℝ, g s) - ∫ s in p..q, g s|
      = |(∫ s in Iic p, g s) + ∫ s in Ioi q, g s| := by rw [hkey]
    _ ≤ |∫ s in Iic p, g s| + |∫ s in Ioi q, g s| := abs_add_le _ _
    _ ≤ C * Real.exp (alpha * p) / alpha + C * Real.exp (-alpha * q) / alpha :=
        add_le_add hleft hright

end MatchingEstimates
