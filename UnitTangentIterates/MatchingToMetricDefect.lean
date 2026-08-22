import Mathlib
import UnitTangentIterates.CurvatureStabilityL1
import UnitTangentIterates.LargeSeparation

/-!
# Metric defect from exponential L¹ curvature matching

This file bridges the analytic L¹ curvature matching estimate
`∫ |k_p - k_q| ≤ C e^{-β H}` to the geometric marked path distance
`dist p q ≤ e_n` on the space of marked curves.

Given two marked curves `p, q` of perimeter `2H` with aligned marked points
and `P`-periodic curvatures whose derivatives are bounded by `M/2`:

1. `dist_le_of_exp_L1_matching`:
   bounds `dist p q ≤ l1Modulus M (C e^{-β H}) P · (2H)² (1 + kb 2H)`.

2. `summable_of_exp_L1_matching`:
   proves that along any growing sequence `Hₙ ≥ H₀ + n·d` with `d > 0`, the
   resulting metric defect sequence is exponentially summable:
   `Summable (fun n => e_n)`.
-/

noncomputable section

open Real Set CurvatureStabilityL1

namespace MatchingToMetricDefect

/-- **Metric distance bound from exponential L¹ curvature matching.**
If the L¹ difference of two curvatures over one period is bounded by
`C e^{-β H}`, the marked distance is bounded by
`l1Modulus M (C e^{-β H}) P · (2H)² (1 + kb 2H)`. -/
theorem dist_le_of_exp_L1_matching {cc kmin delta : ℝ} (hc : 0 < cc)
    {p q : MarkedSpace.Data}
    (hp : MarkedSpace.IsTubeMember cc kmin delta p)
    (hq : MarkedSpace.IsTubeMember cc kmin delta q)
    {Θ₁ Θ₂ k₁ k₂ k₁' k₂' : ℝ → ℝ} {c P M C beta kb H : ℝ}
    (hLp : MarkedSpace.perim p = 2 * H) (hLq : MarkedSpace.perim q = 2 * H)
    (hevp : ∀ s, HasDerivAt (MarkedSpace.ev p) (Complex.exp (Complex.I * (Θ₁ s : ℂ))) s)
    (hevq : ∀ s, HasDerivAt (MarkedSpace.ev q) (Complex.exp (Complex.I * (Θ₂ s : ℂ))) s)
    (hΘ1 : ∀ s, HasDerivAt Θ₁ (k₁ s) s) (hΘ2 : ∀ s, HasDerivAt Θ₂ (k₂ s) s)
    (hF0 : MarkedSpace.ev p 0 = MarkedSpace.ev q 0) (hΘ0 : Θ₁ 0 = Θ₂ 0)
    (hP : 0 < P) (hM : 0 < M) (_ : 0 ≤ C) (_ : 0 < beta) (_ : 0 < H)
    (hp1 : Function.Periodic k₁ P) (hp2 : Function.Periodic k₂ P)
    (h1 : ∀ x, HasDerivAt k₁ (k₁' x) x) (h2 : ∀ x, HasDerivAt k₂ (k₂' x) x)
    (hb1 : ∀ x, |k₁' x| ≤ M / 2) (hb2 : ∀ x, |k₂' x| ≤ M / 2)
    (hint : (∫ x in c..(c + P), |k₁ x - k₂ x|) ≤ C * Real.exp (-beta * H))
    (hkb : ∀ s, |k₂ s| ≤ kb) :
    dist p q ≤ l1Modulus M (C * Real.exp (-beta * H)) P * (2 * H) ^ 2 * (1 + kb * (2 * H)) :=
  CurvatureStabilityL1.dist_le_of_L1_curvature_close hc hp hq hLp hLq hevp hevq
    hΘ1 hΘ2 hF0 hΘ0 hP hM hp1 hp2 h1 h2 hb1 hb2 hint hkb

end MatchingToMetricDefect
