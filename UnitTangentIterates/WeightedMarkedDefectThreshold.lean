import Mathlib
import UnitTangentIterates.ModelOrbitDefectMarked
import UnitTangentIterates.WeightedRecursiveDefect

/-!
# The weighted marked-defect threshold

The marked-distance modulus contains a square-root branch.  Thus curvature
matching at rate `exp (-2 * beta * H)` gives a marked defect at rate
`exp (-beta * H)`.  After `n` recursive transports with cost `K ^ n`, the
sharp geometric ratio is therefore

`K * exp (-(beta * deltaStep))`.

This file records that implication for the canonical marked defect used by the
model pseudo-orbit.  Its remaining factors are fixed in `n`, so no polynomial
loss in the separation has to be absorbed.
-/

noncomputable section

open Real CurvatureStabilityL1

namespace PathMetric

namespace WeightedMarkedDefectThreshold

/-- The canonical marked defect produced from curvature matching with exponent
`2 * beta`.  The factor two is exactly what compensates for the square-root
branch of `l1Modulus`. -/
def canonicalMarkedDefect
    (Cm L kstar kd beta : ℝ) (Hs : ℕ → ℝ) (n : ℕ) : ℝ :=
  l1Modulus (2 * kd)
      (Cm * Real.exp (-((2 * beta) * Hs (n + 1)))) (Hs n)
    * L ^ 2 * (1 + kstar * L)

/-- **Weighted marked defects are summable at the exact transport threshold.**

If separations grow by at least `deltaStep`, curvature matching decays like
`exp (-2 * beta * H)`, and one recursive transport costs `K`, then
`K ^ n` times the canonical marked defect is summable whenever
`K * exp (-(beta * deltaStep)) < 1`.  In particular, no assumption `K ≤ 1`
is made. -/
theorem summable_weighted_canonicalMarkedDefect
    {K Cm L kstar kd P0 H0 deltaStep beta : ℝ} {Hs : ℕ → ℝ}
    (hK : 0 ≤ K) (hbeta : 0 < beta) (hdelta : 0 < deltaStep)
    (hCm : 0 ≤ Cm) (hL : 0 ≤ L) (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd)
    (hP0 : 0 < P0) (hPle : ∀ n, P0 ≤ Hs n)
    (hgrow : ∀ n : ℕ, H0 + n * deltaStep ≤ Hs n)
    (hthreshold : K * Real.exp (-(beta * deltaStep)) < 1) :
    Summable
      (WeightedRecursiveDefect.weightedDefect K
        (canonicalMarkedDefect Cm L kstar kd beta Hs)) := by
  let q : ℝ := Real.exp (-(beta * deltaStep))
  let A : ℝ := Real.sqrt (4 * kd * Cm) + 4 * Cm / P0
  let D : ℝ := A * Real.exp (-(beta * H0)) * L ^ 2 * (1 + kstar * L)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg (Real.sqrt_nonneg _) (div_nonneg (by positivity) hP0.le)
  have hfixed : 0 ≤ L ^ 2 * (1 + kstar * L) := by positivity
  have hD0 : 0 ≤ D := by
    dsimp [D]
    positivity
  have hHs0 : ∀ n, 0 ≤ Hs n := fun n => le_trans hP0.le (hPle n)
  have hexp : ∀ n : ℕ,
      Real.exp (-(beta * Hs (n + 1)))
        ≤ Real.exp (-(beta * H0)) * q ^ n := by
    intro n
    have hstep : Real.exp (-(beta * Hs (n + 1)))
        ≤ Real.exp (-(beta * (H0 + ((n : ℝ) + 1) * deltaStep))) := by
      apply Real.exp_le_exp.mpr
      have hn := hgrow (n + 1)
      push_cast at hn
      nlinarith
    have hval : Real.exp (-(beta * (H0 + ((n : ℝ) + 1) * deltaStep)))
        = Real.exp (-(beta * H0)) * q ^ (n + 1) := by
      dsimp [q]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      push_cast
      ring_nf
    have hq1 : q < 1 := by
      dsimp [q]
      exact Real.exp_lt_one_iff.mpr (by nlinarith)
    have hpow : q ^ (n + 1) ≤ q ^ n := by
      rw [pow_succ]
      nlinarith [pow_nonneg hq0 n]
    calc
      Real.exp (-(beta * Hs (n + 1)))
          ≤ Real.exp (-(beta * (H0 + ((n : ℝ) + 1) * deltaStep))) := hstep
      _ = Real.exp (-(beta * H0)) * q ^ (n + 1) := hval
      _ ≤ Real.exp (-(beta * H0)) * q ^ n :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
  have hd0 : ∀ n, 0 ≤ canonicalMarkedDefect Cm L kstar kd beta Hs n := by
    intro n
    exact mul_nonneg
      (mul_nonneg (l1Modulus_nonneg _ _ _) (sq_nonneg L))
      (by positivity)
  have hdgeo : ∀ n,
      canonicalMarkedDefect Cm L kstar kd beta Hs n ≤ D * q ^ n := by
    intro n
    have hmod := ModelOrbitDefectMarked.l1Modulus_le_exp
      (Cm := Cm) (kd := kd) (P0 := P0) (beta := 2 * beta)
      (Pp := Hs n) (H := Hs (n + 1))
      (by positivity) hCm hkd hP0 (hPle n) (hHs0 (n + 1))
    have hmod' : l1Modulus (2 * kd)
        (Cm * Real.exp (-((2 * beta) * Hs (n + 1)))) (Hs n)
        ≤ A * Real.exp (-(beta * Hs (n + 1))) := by
      simpa [A] using hmod
    have hmarked : canonicalMarkedDefect Cm L kstar kd beta Hs n
        ≤ (A * Real.exp (-(beta * Hs (n + 1))))
          * (L ^ 2 * (1 + kstar * L)) := by
      dsimp [canonicalMarkedDefect]
      calc
        l1Modulus (2 * kd)
              (Cm * Real.exp (-((2 * beta) * Hs (n + 1)))) (Hs n)
            * L ^ 2 * (1 + kstar * L)
            = l1Modulus (2 * kd)
                (Cm * Real.exp (-((2 * beta) * Hs (n + 1)))) (Hs n)
              * (L ^ 2 * (1 + kstar * L)) := by ring
        _ ≤ (A * Real.exp (-(beta * Hs (n + 1))))
              * (L ^ 2 * (1 + kstar * L)) :=
          mul_le_mul_of_nonneg_right hmod' hfixed
    calc
      canonicalMarkedDefect Cm L kstar kd beta Hs n
          ≤ (A * Real.exp (-(beta * Hs (n + 1))))
              * (L ^ 2 * (1 + kstar * L)) := hmarked
      _ ≤ (A * (Real.exp (-(beta * H0)) * q ^ n))
              * (L ^ 2 * (1 + kstar * L)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hexp n) hA0) hfixed
      _ = D * q ^ n := by
          dsimp [D]
          ring
  exact WeightedRecursiveDefect.summable_weightedDefect_of_geometric
    hK hD0 hq0 (by simpa [q] using hthreshold) hd0 hdgeo

end WeightedMarkedDefectThreshold

end PathMetric
