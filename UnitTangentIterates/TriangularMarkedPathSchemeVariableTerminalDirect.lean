import UnitTangentIterates.TriangularMarkedPathSchemeVariableTerminal

/-!
# Direct limit-Harnack triangular scheme

This variant does not require Harnack certificates at the finite marked
columns.  The only geometric closing datum is a certificate for the actual
row limit.  This is the natural interface for aligned physical rear rows:
finite physical kinematics and terminal-base convergence prove the limit
certificate directly, without imposing a Harnack estimate on the initial
configured marking.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed

namespace TriangularMarkedPathSchemeVariableTerminalDirect

open VariableMarkedTube
open TriangularMarkedPathSchemeVariableTerminal

structure Scheme
    (Q : ℕ → Data) (P : ℕ → ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ) where
  base : ∀ n, P n 0 = Q n
  error_nonnegative : ∀ n k, 0 ≤ e n k
  error_summable : ∀ n, Summable (e n)
  tube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (P n k)
  stepPath : ∀ n k, NormalPath (P n k) (P n (k + 1))
  stepGeometry : ∀ n k,
    IsVariableSpeedNormalPath (P0 n) (P1 n) (khat n) (G1 n) (Cg n)
      (stepPath n k)
  stepCost : ∀ n k, cost (stepPath n k) ≤ e n k
  finiteEdge : ∀ n k,
    GeometricUnitTangentRangeEdge (P (n + 1) k) (P n (k + 1))
  limitHarnack : ∀ n x, Tendsto (P n) atTop (nhds x) →
    ArclengthHarnackCertificate x

theorem exists_limitOutput
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (S : Scheme Q P e P0 P1 khat G1 Cg C c dlt)
    (hc : 0 < c) :
    Nonempty (LimitOutput Q P e P0 P1 khat G1 Cg C c dlt) := by
  let A : ℕ → ℝ := rowC P0 P1 khat G1 Cg
  have hA : ∀ n, 0 ≤ A n := fun n => by
    simpa [A, rowC] using
      c2ConstVar_nonneg (P0 n) (P1 n) (khat n) (G1 n) (Cg n)
  have hstep : ∀ n k, dist (P n k) (P n (k + 1)) ≤ A n * e n k := by
    intro n k
    exact (dist_le_cost_variableSpeed (S.stepPath n k)
      (S.tube n k).hasDerivAt_curve (S.tube n (k + 1)).hasDerivAt_curve
      (S.tube n k).hasDerivAt_vel (S.tube n (k + 1)).hasDerivAt_vel
      (S.stepGeometry n k)).trans
        (mul_le_mul_of_nonneg_left (S.stepCost n k) (hA n))
  have hrowCauchy : ∀ n, CauchySeq (P n) := by
    intro n
    apply cauchySeq_of_summable_dist
    exact Summable.of_nonneg_of_le (fun k => dist_nonneg)
      (hstep n) ((S.error_summable n).mul_left (A n))
  have hlim : ∀ n, ∃ x : Data,
      Tendsto (P n) atTop (nhds x) ∧
      ∀ k, dist (P n k) x ≤ A n * ShadowingTails.tail (e n) k := by
    intro n
    exact ShadowingTails.exists_limit_of_summable_increments
      (C := A n) (S.error_summable n) (hstep n)
  choose X hXlim hXdist using hlim
  have hXmem : ∀ n, IsVariableTubeMember c (C n) 0 dlt (X n) := by
    intro n
    exact (isClosed_variableTube c (C n) 0 dlt).mem_of_tendsto (hXlim n)
      (Eventually.of_forall (S.tube n))
  have hshadow : ∀ n,
      dist (Q n) (X n) ≤ A n * ShadowingTails.tail (e n) 0 := by
    intro n
    rw [← S.base n]
    exact hXdist n 0
  have hhaus : ∀ n,
      Metric.hausdorffDist (range (⇑(X n).1)) (range (⇑(Q n).1)) ≤
        A n * ShadowingTails.tail (e n) 0 := by
    intro n
    apply CurveDistance.hausdorffDist_range_le
      (mul_nonneg (hA n) (ShadowingTails.tail_nonneg (S.error_nonnegative n) 0))
    intro u
    exact (dist_apply_le (X n) (Q n) u).trans
      (by simpa [dist_comm] using hshadow n)
  have hlength : ∀ n,
      |MarkedReparam.totalLength (fun u => (X n).2.1 u) -
          MarkedReparam.totalLength (fun u => (Q n).2.1 u)| ≤
        A n * ShadowingTails.tail (e n) 0 := by
    intro n
    exact (VariableMarkedPhysicalLength.abs_totalLength_sub_le_dist (X n) (Q n)).trans
      (by simpa [dist_comm] using hshadow n)
  have horbit : ∀ n, GeometricUnitTangentRangeEdge (X (n + 1)) (X n) := by
    intro n
    let Cedge := max (C n) (C (n + 1))
    have hfrontN : ∀ k, IsVariableTubeMember c Cedge 0 dlt (P (n + 1) k) :=
      fun k => variableTube_mono_upper (S.tube (n + 1) k) (le_max_right _ _)
    have hrearN : ∀ k, IsVariableTubeMember c Cedge 0 dlt (P n (k + 1)) :=
      fun k => variableTube_mono_upper (S.tube n (k + 1)) (le_max_left _ _)
    have hfront : IsVariableTubeMember c Cedge 0 dlt (X (n + 1)) :=
      variableTube_mono_upper (hXmem (n + 1)) (le_max_right _ _)
    have hrear : IsVariableTubeMember c Cedge 0 dlt (X n) :=
      variableTube_mono_upper (hXmem n) (le_max_left _ _)
    exact range_geometricUnitTangent_closed_under_marked_limits hc
      hfrontN hrearN hfront hrear (hXlim (n + 1))
      ((hXlim n).comp (tendsto_add_atTop_nat 1)) (S.finiteEdge n)
  have hoval : ∀ n, IsGeometricOval (X n) := fun n =>
    isGeometricOval_of_arclengthHarnack (S.limitHarnack n (X n) (hXlim n))
  exact ⟨⟨X, hrowCauchy, hXlim, hXmem, hshadow, hlength, hhaus, horbit, hoval⟩⟩

/-- Distance-driven variant for presented rows whose chosen normal path ends
at a selected rear and is followed by a small terminal marking defect. -/
structure DistanceScheme
    (Q : ℕ → Data) (P : ℕ → ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ) where
  base : ∀ n, P n 0 = Q n
  error_nonnegative : ∀ n k, 0 ≤ e n k
  error_summable : ∀ n, Summable (e n)
  tube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (P n k)
  stepDistance : ∀ n k,
    dist (P n k) (P n (k + 1)) ≤ rowC P0 P1 khat G1 Cg n * e n k
  finiteEdge : ∀ n k,
    GeometricUnitTangentRangeEdge (P (n + 1) k) (P n (k + 1))
  limitHarnack : ∀ n x, Tendsto (P n) atTop (nhds x) →
    ArclengthHarnackCertificate x

/-- Compactness from genuine consecutive marked-distance estimates. -/
theorem exists_limitOutput_of_distance
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (S : DistanceScheme Q P e P0 P1 khat G1 Cg C c dlt)
    (hc : 0 < c) :
    Nonempty (LimitOutput Q P e P0 P1 khat G1 Cg C c dlt) := by
  let A : ℕ → ℝ := rowC P0 P1 khat G1 Cg
  have hA : ∀ n, 0 ≤ A n := fun n => by
    simpa [A, rowC] using
      c2ConstVar_nonneg (P0 n) (P1 n) (khat n) (G1 n) (Cg n)
  have hrowCauchy : ∀ n, CauchySeq (P n) := fun n =>
    cauchySeq_of_summable_dist (Summable.of_nonneg_of_le (fun _ => dist_nonneg)
      (S.stepDistance n) ((S.error_summable n).mul_left (A n)))
  have hlim : ∀ n, ∃ x : Data,
      Tendsto (P n) atTop (nhds x) ∧
      ∀ k, dist (P n k) x ≤ A n * ShadowingTails.tail (e n) k := by
    intro n
    exact ShadowingTails.exists_limit_of_summable_increments
      (C := A n) (S.error_summable n) (S.stepDistance n)
  choose X hXlim hXdist using hlim
  have hXmem : ∀ n, IsVariableTubeMember c (C n) 0 dlt (X n) := fun n =>
    (isClosed_variableTube c (C n) 0 dlt).mem_of_tendsto (hXlim n)
      (Eventually.of_forall (S.tube n))
  have hshadow : ∀ n,
      dist (Q n) (X n) ≤ A n * ShadowingTails.tail (e n) 0 := fun n => by
    rw [← S.base n]
    exact hXdist n 0
  have hhaus : ∀ n,
      Metric.hausdorffDist (range (⇑(X n).1)) (range (⇑(Q n).1)) ≤
        A n * ShadowingTails.tail (e n) 0 := by
    intro n
    apply CurveDistance.hausdorffDist_range_le
      (mul_nonneg (hA n) (ShadowingTails.tail_nonneg (S.error_nonnegative n) 0))
    intro u
    exact (dist_apply_le (X n) (Q n) u).trans
      (by simpa [dist_comm] using hshadow n)
  have hlength : ∀ n,
      |MarkedReparam.totalLength (fun u => (X n).2.1 u) -
          MarkedReparam.totalLength (fun u => (Q n).2.1 u)| ≤
        A n * ShadowingTails.tail (e n) 0 := fun n =>
    (VariableMarkedPhysicalLength.abs_totalLength_sub_le_dist (X n) (Q n)).trans
      (by simpa [dist_comm] using hshadow n)
  have horbit : ∀ n, GeometricUnitTangentRangeEdge (X (n + 1)) (X n) := by
    intro n
    let Cedge := max (C n) (C (n + 1))
    exact range_geometricUnitTangent_closed_under_marked_limits hc
      (fun k => variableTube_mono_upper (S.tube (n + 1) k) (le_max_right _ _))
      (fun k => variableTube_mono_upper (S.tube n (k + 1)) (le_max_left _ _))
      (variableTube_mono_upper (hXmem (n + 1)) (le_max_right _ _))
      (variableTube_mono_upper (hXmem n) (le_max_left _ _))
      (hXlim (n + 1)) ((hXlim n).comp (tendsto_add_atTop_nat 1))
      (S.finiteEdge n)
  have hoval : ∀ n, IsGeometricOval (X n) := fun n =>
    isGeometricOval_of_arclengthHarnack (S.limitHarnack n (X n) (hXlim n))
  exact ⟨⟨X, hrowCauchy, hXlim, hXmem, hshadow, hlength, hhaus, horbit, hoval⟩⟩

end TriangularMarkedPathSchemeVariableTerminalDirect
