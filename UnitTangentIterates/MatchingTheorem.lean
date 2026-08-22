import Mathlib
import UnitTangentIterates.L1Matching
import UnitTangentIterates.MatchingAssembly
import UnitTangentIterates.PeriodizedTail

/-!
# The theorem *Curvature-measure matching*, assembled

This file assembles the theorem *Curvature-measure matching* of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates* into a single estimate
about the two curvatures.

The paper compares the rear curvature `k_H` and the front curvature `K_P` of
period `P = P(H)` with the common periodized model
`K̄_P(u) = ∑_{j ∈ ℤ} K_*(u − jP)`, over the fundamental interval
`J_H = x_H([−H/2, H/2])`.  The rear comparison is the three-term split

```
  Y_H − c_H K̄_P(x_H)
     = (Y_H − y) + (y − c_H K_*(x_H)) − c_H ∑_{j ≠ 0} K_*(x_H − jP),
```

whose first two terms are exponentially small by the pulse estimates, and whose
third term is, after the change of variables `u = x_H(s)`, the mass of `K_*`
outside `J_H`, again exponentially small.  Adding the front comparison
`‖K_P − K̄_P‖_{L¹}` gives the theorem.

The ingredients are in `L1Matching.lean`, `MatchingEstimates.lean`,
`PeriodizedTail.lean` and `MatchingAssembly.lean`.  What is added here is the
change of variables for the omitted mass and the assembly itself:

* `setIntegral_comp_rear` : the change of variables `∫_{J} g = ∫_{I} c_H g(x_H)`
  for an arbitrary integrand (the periodized tail is not assumed continuous);
* `rear_tail_le` : the third term is at most `C(e^{αp} + e^{−α(p+P)})/α`;
* `rear_cell_bound` : the three-term split, giving the cell bound
  `∫_I |Y_H − c_H K̄_P(x_H)| ≤ e₁ + e₂ + e₃`;
* `curvature_measure_matching` : **the theorem**, in the form
  `∫_{J_H} |k_H − K_P| ≤ e₁ + e₂ + e₃ + e₄`, where the four terms are the two
  pulse errors, the omitted mass and the front periodization error;
* `curvature_measure_matching_exp` : the same conclusion in the paper's form
  `≤ Ce^{−βH}` when the four terms are exponentially small.
-/

noncomputable section

open Set MeasureTheory intervalIntegral

namespace MatchingTheorem

/-! ### The change of variables to the fundamental interval -/

/-- **The change of variables `u = x_H(s)` for an arbitrary integrand.**  If
`x_H' = c_H > 0` then, for every `g`, the integral of `g` over the fundamental
interval `x_H([a,b])` equals the integral of `c_H · g(x_H)` over the cell
`[a,b]`.  Unlike `L1Matching.integral_comp_rear` this does not require `g` to be
continuous, which is what the periodized tail `∑_{j≠0} K_*(· − jP)` needs. -/
theorem setIntegral_comp_rear {xH cH : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hx : ∀ t, HasDerivAt xH (cH t) t) (hpos : ∀ t, 0 < cH t) (g : ℝ → ℝ) :
    (∫ u in Icc (xH a) (xH b), g u) = ∫ s in Icc a b, cH s * g (xH s) := by
  have hmono : StrictMono xH :=
    strictMono_of_deriv_pos (fun x => by rw [(hx x).deriv]; exact hpos x)
  have hcontinuous : Continuous xH :=
    continuous_iff_continuousAt.2 (fun x => (hx x).differentiableAt.continuousAt)
  have himg : xH '' Icc a b = Icc (xH a) (xH b) :=
    ContinuousOn.image_Icc_of_monotoneOn hab hcontinuous.continuousOn (hmono.monotone.monotoneOn _)
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
    (fun x _ => (hx x).hasDerivWithinAt) hmono.injective.injOn g]
  refine setIntegral_congr_fun measurableSet_Icc (fun x _ => ?_)
  simp [abs_of_pos (hpos x)]

/-! ### The omitted mass -/

/-- **The third term of the split is the mass of `K_*` outside the fundamental
interval**, hence exponentially small.  Here `p = x_H(a)` is the left endpoint
of the fundamental interval and `P` its length. -/
theorem rear_tail_le {xH cH Kstar : ℝ → ℝ} {a b P C alpha : ℝ} (hab : a ≤ b)
    (hx : ∀ t, HasDerivAt xH (cH t) t) (hpos : ∀ t, 0 < cH t)
    (hP : xH b = xH a + P) (hPpos : 0 < P) (halpha : 0 < alpha)
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ C * Real.exp (-alpha * |s|))
    (hp : xH a ≤ 0) (hq : 0 ≤ xH a + P) :
    (∫ s in Icc a b, cH s * ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P))
      ≤ C * Real.exp (alpha * xH a) / alpha
        + C * Real.exp (-alpha * (xH a + P)) / alpha := by
  rw [← setIntegral_comp_rear hab hx hpos
    (fun u => ∑' j : {j : ℤ // j ≠ 0}, Kstar (u - (j : ℤ) * P)), hP,
    integral_Icc_eq_integral_Ico]
  exact PeriodizedTail.integral_tsum_translates_le hPpos halpha hKint hK0 hKbd hp hq

/-- **The third term in the form used by the split.**  Since the speed and the
omitted translates are nonnegative, the absolute value is harmless and the
interval integral over the cell obeys the same exponential bound. -/
theorem rear_tail_interval_le {xH cH Kstar : ℝ → ℝ} {a b P C alpha : ℝ} (hab : a ≤ b)
    (hx : ∀ t, HasDerivAt xH (cH t) t) (hpos : ∀ t, 0 < cH t)
    (hP : xH b = xH a + P) (hPpos : 0 < P) (halpha : 0 < alpha)
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ C * Real.exp (-alpha * |s|))
    (hp : xH a ≤ 0) (hq : 0 ≤ xH a + P) :
    (∫ s in a..b, |cH s * ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)|)
      ≤ C * Real.exp (alpha * xH a) / alpha
        + C * Real.exp (-alpha * (xH a + P)) / alpha := by
  have habs : ∀ s : ℝ, |cH s * ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)|
      = cH s * ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P) := by
    intro s
    exact abs_of_nonneg (mul_nonneg (hpos s).le (tsum_nonneg (fun _ => hK0 _)))
  rw [intervalIntegral.integral_congr (g := fun s =>
      cH s * ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)) (fun s _ => habs s),
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact rear_tail_le hab hx hpos hP hPpos halpha hKint hK0 hKbd hp hq

/-! ### The three-term split over the cell -/

/-- **The rear cell bound.**  With the periodized model split as
`K̄_P = K_* + ∑_{j≠0} K_*(· − jP)`, and with `L¹` bounds `e₁, e₂, e₃` for the
three terms of the paper's split, the matching integrand over the cell is
bounded by `e₁ + e₂ + e₃`. -/
theorem rear_cell_bound {xH cH YH y Kstar Kbar : ℝ → ℝ} {a b P e1 e2 e3 : ℝ} (hab : a ≤ b)
    (hKbar : ∀ u, Kbar u = Kstar u + ∑' j : {j : ℤ // j ≠ 0}, Kstar (u - (j : ℤ) * P))
    (hA : IntervalIntegrable (fun s => YH s - y s) volume a b)
    (hB : IntervalIntegrable (fun s => y s - cH s * Kstar (xH s)) volume a b)
    (hD : IntervalIntegrable
      (fun s => cH s * ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)) volume a b)
    (h1 : (∫ s in a..b, |YH s - y s|) ≤ e1)
    (h2 : (∫ s in a..b, |y s - cH s * Kstar (xH s)|) ≤ e2)
    (h3 : (∫ s in a..b, |cH s * ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)|) ≤ e3) :
    (∫ s in a..b, |YH s - cH s * Kbar (xH s)|) ≤ e1 + e2 + e3 := by
  have hcongr : (∫ s in a..b, |YH s - cH s * Kbar (xH s)|)
      = ∫ s in a..b, |(YH s - y s) + (y s - cH s * Kstar (xH s))
          - cH s * ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)| := by
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    congr 1
    rw [hKbar (xH s)]
    ring
  rw [hcongr]
  exact L1Matching.matching_split hab hA hB hD h1 h2 h3

/-! ### The theorem -/

/-- **Curvature-measure matching.**  Let the closed rear be parametrized by the
cell `[a,b]` through its arclength `x_H` (with `x_H' = c_H > 0`), let `k_H` be
its curvature, related to the steering mass by the measure identity
`k_H(x_H(s))c_H(s) = Y_H(s)`, and let `K_P` be the front curvature of period
`P`.  Compare both with the periodized model `K̄_P = ∑_j K_*(· − jP)`.

If the pulse errors `‖Y_H − y‖_{L¹}` and `‖y − c_H K_*(x_H)‖_{L¹}` over the cell
are at most `e₁` and `e₂`, the omitted mass is at most `e₃`, and the front
periodization error over the fundamental interval is at most `e₄`, then the two
curvatures are `L¹`-close over the fundamental interval:

`∫_{J_H} |k_H − K_P| ≤ e₁ + e₂ + e₃ + e₄`.

In the paper all four terms are `O(e^{−βH})`; see
`curvature_measure_matching_exp`. -/
theorem curvature_measure_matching
    {xH cH YH y kH Kstar Kbar KP : ℝ → ℝ} {a b P e1 e2 e3 e4 : ℝ} (hab : a ≤ b)
    (hx : ∀ t, HasDerivAt xH (cH t) t) (hcH : Continuous cH) (hpos : ∀ t, 0 < cH t)
    (hk : ∀ t, kH (xH t) * cH t = YH t)
    (hkcont : Continuous fun u => |kH u - Kbar u|)
    (hKbar : ∀ u, Kbar u = Kstar u + ∑' j : {j : ℤ // j ≠ 0}, Kstar (u - (j : ℤ) * P))
    (hA : IntervalIntegrable (fun s => YH s - y s) volume a b)
    (hB : IntervalIntegrable (fun s => y s - cH s * Kstar (xH s)) volume a b)
    (hD : IntervalIntegrable
      (fun s => cH s * ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)) volume a b)
    (hi0 : IntervalIntegrable (fun u => |kH u - KP u|) volume (xH a) (xH b))
    (hi2 : IntervalIntegrable (fun u => |Kbar u - KP u|) volume (xH a) (xH b))
    (h1 : (∫ s in a..b, |YH s - y s|) ≤ e1)
    (h2 : (∫ s in a..b, |y s - cH s * Kstar (xH s)|) ≤ e2)
    (h3 : (∫ s in a..b, |cH s * ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)|) ≤ e3)
    (h4 : (∫ u in (xH a)..(xH b), |Kbar u - KP u|) ≤ e4) :
    (∫ u in (xH a)..(xH b), |kH u - KP u|) ≤ e1 + e2 + e3 + e4 := by
  have hmono : StrictMono xH :=
    strictMono_of_deriv_pos (fun x => by rw [(hx x).deriv]; exact hpos x)
  have hxab : xH a ≤ xH b := hmono.monotone hab
  -- the rear comparison over the fundamental interval
  have hrear : (∫ u in (xH a)..(xH b), |kH u - Kbar u|) ≤ e1 + e2 + e3 := by
    rw [← MatchingAssembly.rear_L1_change_of_variables (Y := YH)
      (fun t _ => hx t) hcH.continuousOn hpos hk hkcont]
    exact rear_cell_bound hab hKbar hA hB hD h1 h2 h3
  -- add the front comparison
  have hi1 : IntervalIntegrable (fun u => |kH u - Kbar u|) volume (xH a) (xH b) :=
    (hkcont.intervalIntegrable _ _)
  exact le_trans (MatchingAssembly.matching_conclusion hxab hi0 hi1 hi2 hrear h4)
    (by linarith)

/-- **Curvature-measure matching, in the paper's exponential form.**  If each of
the four error terms is at most `(C/4)e^{−βH}`, the conclusion is the estimate
`∫_{J_H}|k_H − K_P| ≤ Ce^{−βH}` of the paper. -/
theorem curvature_measure_matching_exp
    {xH cH YH y kH Kstar Kbar KP : ℝ → ℝ} {a b P C beta H : ℝ} (hab : a ≤ b)
    (hx : ∀ t, HasDerivAt xH (cH t) t) (hcH : Continuous cH) (hpos : ∀ t, 0 < cH t)
    (hk : ∀ t, kH (xH t) * cH t = YH t)
    (hkcont : Continuous fun u => |kH u - Kbar u|)
    (hKbar : ∀ u, Kbar u = Kstar u + ∑' j : {j : ℤ // j ≠ 0}, Kstar (u - (j : ℤ) * P))
    (hA : IntervalIntegrable (fun s => YH s - y s) volume a b)
    (hB : IntervalIntegrable (fun s => y s - cH s * Kstar (xH s)) volume a b)
    (hD : IntervalIntegrable
      (fun s => cH s * ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)) volume a b)
    (hi0 : IntervalIntegrable (fun u => |kH u - KP u|) volume (xH a) (xH b))
    (hi2 : IntervalIntegrable (fun u => |Kbar u - KP u|) volume (xH a) (xH b))
    (h1 : (∫ s in a..b, |YH s - y s|) ≤ C / 4 * Real.exp (-beta * H))
    (h2 : (∫ s in a..b, |y s - cH s * Kstar (xH s)|) ≤ C / 4 * Real.exp (-beta * H))
    (h3 : (∫ s in a..b, |cH s * ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)|)
      ≤ C / 4 * Real.exp (-beta * H))
    (h4 : (∫ u in (xH a)..(xH b), |Kbar u - KP u|) ≤ C / 4 * Real.exp (-beta * H)) :
    (∫ u in (xH a)..(xH b), |kH u - KP u|) ≤ C * Real.exp (-beta * H) := by
  have h := curvature_measure_matching hab hx hcH hpos hk hkcont hKbar hA hB hD hi0 hi2
    h1 h2 h3 h4
  linarith

end MatchingTheorem
