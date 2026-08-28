import UnitTangentIterates.MarkedUnitTangentRangeClosure
import UnitTangentIterates.TubeHarnackStrictness
import UnitTangentIterates.NormalPathC2IncrementVariableSpeed
import UnitTangentIterates.ShadowingTails
import UnitTangentIterates.MarkedCurveHausdorff

/-!
# Fixed-map-free triangular marked shadowing

This is the paper-faithful replacement for iteration of one marked map.  Each
finite rear may choose its own terminal marking.  The construction retains
actual normal paths between consecutive choices and exact range-level
unit-tangent identities, but assumes no function `B` and no continuity of one.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed

namespace TriangularMarkedPathScheme

/-- A triangular family of independently marked finite rear choices.
`stepPath` is the datum used for completeness.  `basePath` records the actual
paper path from the row model to each positive-depth terminal choice. -/
structure Scheme
    (Q : ℕ → Data) (P : ℕ → ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 kh G1 Cg c dlt : ℝ) where
  base : ∀ n, P n 0 = Q n
  error_nonnegative : ∀ n k, 0 ≤ e n k
  error_summable : ∀ n, Summable (e n)
  tube : ∀ n k, IsTubeMember c 0 dlt (P n k)
  stepPath : ∀ n k, NormalPath (P n k) (P n (k + 1))
  stepGeometry : ∀ n k,
    IsVariableSpeedNormalPath P0 P1 kh G1 Cg (stepPath n k)
  stepCost : ∀ n k, cost (stepPath n k) ≤ e n k
  basePath : ∀ n k, NormalPath (Q n) (P n (k + 1))
  basePathGeometry : ∀ n k,
    IsVariableSpeedNormalPath P0 P1 kh G1 Cg (basePath n k)
  basePathCost : ∀ n k,
    cost (basePath n k) ≤ ∑ j ∈ Finset.range (k + 1), e n j
  finiteEdge : ∀ n k,
    range (ev (P (n + 1) k)) =
      range (UnitTangent.unitTangentMap (ev (P n (k + 1))))
  finiteHarnack : ∀ n k, ∀ a b : ℝ, a ≤ b →
    Real.exp (a - b) *
        (UnconditionalAssembly.arcCurv (P n k) a /
          Real.sqrt (1 + UnconditionalAssembly.arcCurv (P n k) a ^ 2)) ≤
      UnconditionalAssembly.arcCurv (P n k) b /
        Real.sqrt (1 + UnconditionalAssembly.arcCurv (P n k) b ^ 2)

/-- All limit conclusions of the triangular scheme, including the exact
range orbit and the finite-Harnack-to-oval passage. -/
structure LimitOutput
    (Q : ℕ → Data) (P : ℕ → ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 kh G1 Cg c dlt : ℝ) where
  X : ℕ → Data
  row_cauchy : ∀ n, CauchySeq (P n)
  row_limit : ∀ n, Tendsto (P n) atTop (nhds (X n))
  limit_tube : ∀ n, IsTubeMember c 0 dlt (X n)
  shadow_dist : ∀ n,
    dist (Q n) (X n) ≤ c2ConstVar P0 P1 kh G1 Cg * ShadowingTails.tail (e n) 0
  shadow_perimeter : ∀ n,
    |perim (X n) - perim (Q n)| ≤
      c2ConstVar P0 P1 kh G1 Cg * ShadowingTails.tail (e n) 0
  shadow_range : ∀ n,
    Metric.hausdorffDist (range (ev (X n))) (range (ev (Q n))) ≤
      c2ConstVar P0 P1 kh G1 Cg * ShadowingTails.tail (e n) 0
  range_orbit : ∀ n,
    range (ev (X (n + 1))) =
      range (UnitTangent.unitTangentMap (ev (X n)))
  oval : ∀ n, MainTheoremConditional.IsOval (ev (X n))

/-- Summable weighted path costs close the triangular marked scheme without a
fixed inverse map or a continuity hypothesis for one. -/
theorem exists_limitOutput
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 kh G1 Cg c dlt : ℝ}
    (S : Scheme Q P e P0 P1 kh G1 Cg c dlt)
    (hC : 0 ≤ c2ConstVar P0 P1 kh G1 Cg)
    (hc : 0 < c) (hdlt : 0 < dlt) :
    Nonempty (LimitOutput Q P e P0 P1 kh G1 Cg c dlt) := by
  let C := c2ConstVar P0 P1 kh G1 Cg
  have hstep : ∀ n k, dist (P n k) (P n (k + 1)) ≤ C * e n k := by
    intro n k
    exact (dist_le_cost_variableSpeed (S.stepPath n k)
      (S.tube n k).hasDerivAt_curve (S.tube n (k + 1)).hasDerivAt_curve
      (S.tube n k).hasDerivAt_vel (S.tube n (k + 1)).hasDerivAt_vel
      (S.stepGeometry n k)).trans
        (mul_le_mul_of_nonneg_left (S.stepCost n k) (by simpa [C] using hC))
  have hrowCauchy : ∀ n, CauchySeq (P n) := by
    intro n
    apply cauchySeq_of_summable_dist
    exact Summable.of_nonneg_of_le (fun k => dist_nonneg)
      (hstep n) ((S.error_summable n).mul_left C)
  have hlim : ∀ n, ∃ x : Data,
      Tendsto (P n) atTop (nhds x) ∧
      ∀ k, dist (P n k) x ≤ C * ShadowingTails.tail (e n) k := by
    intro n
    exact ShadowingTails.exists_limit_of_summable_increments
      (C := C) (S.error_summable n) (hstep n)
  choose X hXlim hXdist using hlim
  have hXmem : ∀ n, IsTubeMember c 0 dlt (X n) := by
    intro n
    exact (isClosed_tube c 0 dlt).mem_of_tendsto (hXlim n)
      (Eventually.of_forall (S.tube n))
  have hshadow : ∀ n,
      dist (Q n) (X n) ≤ C * ShadowingTails.tail (e n) 0 := by
    intro n
    rw [← S.base n]
    exact hXdist n 0
  have hperim : ∀ n, |perim (X n) - perim (Q n)| ≤
      C * ShadowingTails.tail (e n) 0 := by
    intro n
    exact (abs_perim_sub_le_dist (X n) (Q n)).trans
      (by simpa [dist_comm] using hshadow n)
  have htail0 : ∀ n, 0 ≤ C * ShadowingTails.tail (e n) 0 := by
    intro n
    exact mul_nonneg (by simpa [C] using hC)
      (ShadowingTails.tail_nonneg (S.error_nonnegative n) 0)
  have hhaus : ∀ n,
      Metric.hausdorffDist (range (ev (X n))) (range (ev (Q n))) ≤
        C * ShadowingTails.tail (e n) 0 := by
    intro n
    have hQmem : IsTubeMember c 0 dlt (Q n) := by
      rw [← S.base n]
      exact S.tube n 0
    exact hausdorffDist_range_ev_le_of_tube hc (hXmem n) hQmem
      (htail0 n) (by simpa [dist_comm] using hshadow n)
  have horbit : ∀ n,
      range (ev (X (n + 1))) =
        range (UnitTangent.unitTangentMap (ev (X n))) := by
    intro n
    apply range_unitTangentMap_closed_under_marked_limits hc
      (fun k => S.tube (n + 1) k) (fun k => S.tube n (k + 1))
      (hXmem (n + 1)) (hXmem n) (hXlim (n + 1))
      ((hXlim n).comp (tendsto_add_atTop_nat 1))
    exact S.finiteEdge n
  have hoval : ∀ n, MainTheoremConditional.IsOval (ev (X n)) := by
    intro n
    let D := UnconditionalAssembly.limitStrictnessDataH_of_limit' hc
      (hXmem n) (hXlim n) (S.finiteHarnack n)
    exact UnconditionalAssembly.isOval_ev_of_limitStrictnessDataH
      hc hdlt (hXmem n) D
  exact ⟨⟨X, hrowCauchy, hXlim, hXmem, hshadow, hperim, hhaus, horbit, hoval⟩⟩

end TriangularMarkedPathScheme
