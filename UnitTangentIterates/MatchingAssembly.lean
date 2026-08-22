import Mathlib
import UnitTangentIterates.L1Matching

/-!
# Assembling the curvature-measure matching estimate

The theorem *Curvature-measure matching* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* compares the rear curvature measure of `R_H` with the
front curvature of `F_{P(H)}` by comparing both with the same periodization
`K̄_P` of the isolated hairpin curvature:

`‖k_H − K_P‖_{L¹(ℝ/PℤZ)} ≤ ‖k_H − K̄_P‖_{L¹} + ‖K̄_P − K_P‖_{L¹} ≤ Ce^{-βH}`.

`UnitTangentIterates/L1Matching.lean` contains the ingredients (the convolution
estimate, the overlap summation, the rear curvature measure identity, the
change of variables and the three-term split).  This file supplies the two
steps that turn them into the theorem's statement:

* `abs_rear_integrand`, `rear_L1_change_of_variables` : the rear `L¹` distance
  over the fundamental interval `J_H = x_H(I_H)` equals the cell integral
  `∫_{I_H}|Y_H − c_H K̄_P(x_H)|` which the paper estimates;
* `matching_triangle`, `matching_conclusion` : the triangle inequality that
  combines the rear and front comparisons into the matching estimate
  `∫ |k_H − K_P| ≤ Ce^{-βH}`.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral

namespace MatchingAssembly

variable {x cc k Kbar : ℝ → ℝ} {Y : ℝ → ℝ}

/-! ### The rear `L¹` distance as a cell integral -/

/-- **The rear matching integrand.**  Where the rear speed `c` is positive and
the rear curvature measure identity `k(x(s))·c(s) = Y(s)` holds, one has
`|Y − c K̄(x)| = c·|k(x) − K̄(x)|`. -/
theorem abs_rear_integrand {s : ℝ} (hc : 0 < cc s) (hk : k (x s) * cc s = Y s) :
    |Y s - cc s * Kbar (x s)| = cc s * |k (x s) - Kbar (x s)| := by
  have h : Y s - cc s * Kbar (x s) = cc s * (k (x s) - Kbar (x s)) := by
    rw [← hk]; ring
  rw [h, abs_mul, abs_of_pos hc]

/-- **The rear `L¹` distance over the fundamental interval.**  With
`x' = c > 0` and the rear curvature measure identity, the `L¹` distance of the
rear curvature from the periodized model over the fundamental interval
`[x a, x b]` equals the cell integral of `|Y − c K̄(x)|`. -/
theorem rear_L1_change_of_variables {a b : ℝ}
    (hx : ∀ t ∈ uIcc a b, HasDerivAt x (cc t) t) (hcc : ContinuousOn cc (uIcc a b))
    (hpos : ∀ t, 0 < cc t) (hk : ∀ t, k (x t) * cc t = Y t)
    (hcont : Continuous fun u => |k u - Kbar u|) :
    (∫ s in a..b, |Y s - cc s * Kbar (x s)|) = ∫ u in (x a)..(x b), |k u - Kbar u| := by
  have hcongr : (∫ s in a..b, |Y s - cc s * Kbar (x s)|)
      = ∫ s in a..b, cc s * |k (x s) - Kbar (x s)| :=
    intervalIntegral.integral_congr (fun s _ => abs_rear_integrand (hpos s) (hk s))
  rw [hcongr]
  exact L1Matching.integral_comp_rear hx hcc hcont

/-! ### The triangle inequality -/

/-- **The triangle inequality for the matching integrals.** -/
theorem matching_triangle {f g h : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (h0 : IntervalIntegrable (fun u => |f u - h u|) volume p q)
    (h1 : IntervalIntegrable (fun u => |f u - g u|) volume p q)
    (h2 : IntervalIntegrable (fun u => |g u - h u|) volume p q) :
    (∫ u in p..q, |f u - h u|) ≤ (∫ u in p..q, |f u - g u|) + ∫ u in p..q, |g u - h u| := by
  have hsum : (∫ u in p..q, |f u - g u|) + (∫ u in p..q, |g u - h u|)
      = ∫ u in p..q, (|f u - g u| + |g u - h u|) :=
    (intervalIntegral.integral_add h1 h2).symm
  rw [hsum]
  refine intervalIntegral.integral_mono_on hpq h0 (h1.add h2) (fun u _ => ?_)
  calc |f u - h u| = |(f u - g u) + (g u - h u)| := by ring_nf
    _ ≤ |f u - g u| + |g u - h u| := abs_add_le _ _

/-- **The matching estimate.**  If the rear curvature is `L¹`-close to the
common periodized model `K̄_P` and the front curvature of period `P` is too,
then the two curvatures are `L¹`-close over a period. -/
theorem matching_conclusion {kH KP Kbar : ℝ → ℝ} {p q e1 e2 : ℝ} (hpq : p ≤ q)
    (hi0 : IntervalIntegrable (fun u => |kH u - KP u|) volume p q)
    (hi1 : IntervalIntegrable (fun u => |kH u - Kbar u|) volume p q)
    (hi2 : IntervalIntegrable (fun u => |Kbar u - KP u|) volume p q)
    (h1 : (∫ u in p..q, |kH u - Kbar u|) ≤ e1)
    (h2 : (∫ u in p..q, |Kbar u - KP u|) ≤ e2) :
    (∫ u in p..q, |kH u - KP u|) ≤ e1 + e2 :=
  le_trans (matching_triangle hpq hi0 hi1 hi2) (by linarith)

end MatchingAssembly
