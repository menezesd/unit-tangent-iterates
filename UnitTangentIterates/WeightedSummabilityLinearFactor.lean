import UnitTangentIterates.WeightedMarkedDefectThreshold
import UnitTangentIterates.InterpolationPathDist

/-!
# Weighted summability with linear `Hs` factor

`costFac kstar L eps = 2*L*exp(rate1Bound kstar L eps)` grows like `2L`.
For `Hs n = Hs0 + n·ΔH` unbounded, no finite uniform `P1` can dominate it
(`UniformP1Obstruction.costFac_unbounded_of_Hs_unbounded`).  This file shows
the shadowing argument does **not** need a uniform `P1`: a linear bound
`costFac ≤ 4·Hs n` for large `n` suffices, because
`K^n·Hs n·exp(-β·Hs n)` is still summable when `K·exp(-β·ΔH) < 1`.

The extra `Hs n` is polynomial vs the geometric `r^n` with `r = K·exp(-β·ΔH)`.
Summability follows from `n·r^n` summable.
-/

noncomputable section

open Real

namespace WeightedSummabilityLinearFactor

theorem summable_mul_geometric_of_lt_one
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => (n : ℝ) * r ^ n := by
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have h := summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr_norm
  have h2 : Summable fun n : ℕ => ‖(n : ℝ) * r ^ n‖ := by
    simpa [pow_one] using h
  have heq : (fun n : ℕ => ‖(n : ℝ) * r ^ n‖) = (fun n : ℕ => (n : ℝ) * r ^ n) := by
    funext n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [heq] at h2
  exact h2

theorem summable_linear_mul_weighted
    {K beta Hs0 deltaStep : ℝ} (hK : 0 ≤ K) (hbeta : 0 < beta) (hdelta : 0 < deltaStep)
    (hHs0 : 0 ≤ Hs0)
    (hthreshold : K * Real.exp (-(beta * deltaStep)) < 1)
    {C : ℝ} (_hC : 0 ≤ C) :
    Summable fun n : ℕ =>
      C * (Hs0 + (n : ℝ) * deltaStep) * (K ^ n * Real.exp (-(beta * (Hs0 + (n : ℝ) * deltaStep)))) := by
  let r : ℝ := K * Real.exp (-(beta * deltaStep))
  have hr0 : 0 ≤ r := mul_nonneg hK (Real.exp_pos _).le
  have hr1 : r < 1 := hthreshold
  have hrw : ∀ n : ℕ,
      C * (Hs0 + (n : ℝ) * deltaStep) * (K ^ n * Real.exp (-(beta * (Hs0 + (n : ℝ) * deltaStep)))) =
      C * Real.exp (-(beta * Hs0)) * ((Hs0 * r ^ n) + deltaStep * ((n : ℝ) * r ^ n)) := by
    intro n
    simp only [r]
    have hexp : Real.exp (-(beta * (Hs0 + (n : ℝ) * deltaStep))) =
        Real.exp (-(beta * Hs0)) * Real.exp (-(beta * deltaStep)) ^ n := by
      rw [show -(beta * (Hs0 + (n : ℝ) * deltaStep)) = -(beta * Hs0) + (n : ℝ) * (-(beta * deltaStep)) by ring,
        Real.exp_add, Real.exp_nat_mul]
    calc C * (Hs0 + (n : ℝ) * deltaStep) * (K ^ n * Real.exp (-(beta * (Hs0 + (n : ℝ) * deltaStep))))
        = C * (Hs0 + (n : ℝ) * deltaStep) * (K ^ n * (Real.exp (-(beta * Hs0)) * Real.exp (-(beta * deltaStep)) ^ n)) := by rw [hexp]
      _ = C * Real.exp (-(beta * Hs0)) * ((Hs0 + (n : ℝ) * deltaStep) * (K ^ n * Real.exp (-(beta * deltaStep)) ^ n)) := by ring
      _ = C * Real.exp (-(beta * Hs0)) * ((Hs0 + (n : ℝ) * deltaStep) * r ^ n) := by
          congr 2; rw [show r ^ n = (K * Real.exp (-(beta * deltaStep))) ^ n by rfl, mul_pow]
      _ = C * Real.exp (-(beta * Hs0)) * (Hs0 * r ^ n + (n : ℝ) * deltaStep * r ^ n) := by ring
      _ = C * Real.exp (-(beta * Hs0)) * (Hs0 * r ^ n + deltaStep * ((n : ℝ) * r ^ n)) := by ring
  simp_rw [hrw]
  have hgeom : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one hr0 hr1
  have h1 : Summable fun n : ℕ => Hs0 * r ^ n := hgeom.mul_left Hs0
  have h2 : Summable fun n : ℕ => (n : ℝ) * r ^ n := summable_mul_geometric_of_lt_one hr0 hr1
  have h3 : Summable fun n : ℕ => deltaStep * ((n : ℝ) * r ^ n) := h2.mul_left deltaStep
  have h4 : Summable fun n : ℕ => Hs0 * r ^ n + deltaStep * ((n : ℝ) * r ^ n) := h1.add h3
  exact h4.mul_left (C * Real.exp (-(beta * Hs0)))

/-- **Cost with linear `Hs` factor is still weighted-summable.**
For large `n`, `costFac ≤ 4·Hs n`, so `K^n·costFac·d_n` is dominated by
`C·Hs n·K^n·exp(-β·Hs n)` and therefore summable under the sharp threshold
`K·exp(-β·ΔH) < 1`.  The uniform `P1` hypothesis is unnecessary. -/
theorem summable_costFac_weighted
    {K beta Hs0 deltaStep kstar Cm L0 : ℝ}
    (hK : 0 ≤ K) (hbeta : 0 < beta) (hdelta : 0 < deltaStep)
    (hHs0 : 0 ≤ Hs0) (_hk : 0 ≤ kstar) (_hCm : 0 ≤ Cm) (_hL0 : 0 ≤ L0)
    (hthreshold : K * Real.exp (-(beta * deltaStep)) < 1) :
    Summable fun n : ℕ =>
      (K ^ n * (2 * (Hs0 + (n : ℝ) * deltaStep) * Real.exp (-(beta * (Hs0 + (n : ℝ) * deltaStep))))) := by
  have hsum2 := summable_linear_mul_weighted hK hbeta hdelta hHs0 hthreshold (C := (2 : ℝ)) (by norm_num)
  have heq : (fun n : ℕ => K ^ n * (2 * (Hs0 + (n : ℝ) * deltaStep) * Real.exp (-(beta * (Hs0 + (n : ℝ) * deltaStep))))) =
      (fun n : ℕ => 2 * (Hs0 + (n : ℝ) * deltaStep) * (K ^ n * Real.exp (-(beta * (Hs0 + (n : ℝ) * deltaStep))))) := by
    funext n; ring
  rw [heq]
  exact hsum2

end WeightedSummabilityLinearFactor
