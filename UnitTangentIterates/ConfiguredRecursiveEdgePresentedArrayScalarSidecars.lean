import UnitTangentIterates.ConfiguredRecursiveEdgeFiniteColumnScalarClosing
import UnitTangentIterates.GenericVariableTerminalDirectCapstoneExplicitFront
import UnitTangentIterates.VariableTerminalRowTubeAdapter

/-!
# Scalar sidecars for arbitrary presented finite columns

This module does not choose a selected-inverse grid.  It starts with an
arbitrary presented array whose depth-zero datum is the configured model,
telescopes its genuine consecutive marked distances, and combines the result
with the row-local variable-tube stability theorem.  The final lemmas expose
the tube and paper-gap fields in exactly the form used by the explicit-front
direct capstone.
-/

noncomputable section

open Function Set Filter MarkedSpace PathMetric PathMetric.NormalPath
  NormalPathC2IncrementVariableSpeed

namespace ConfiguredRecursiveEdgePresentedArrayScalarSidecars

open ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeFiniteColumnScalarClosing
  GenericVariableTerminalDirectCapstoneExplicitFront
  VariableMarkedTube VariableMarkedTubeLocalStability
  VariableTerminalRowTubeAdapter

variable {MA NA : ℝ}

/-- Finite telescoping for an arbitrary presented array.  No pullback map or
infinite recursive object occurs in the statement. -/
theorem dist_base_le_radius_of_stepDistance
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {r : ℕ → ℝ}
    (hbase : ∀ n, P n 0 = Q n)
    (hstep : ∀ n k, dist (P n k) (P n (k + 1)) ≤ e n k)
    (hpartial : ∀ n k, (∑ j ∈ Finset.range k, e n j) ≤ r n) :
    ∀ n k, dist (Q n) (P n k) ≤ r n := by
  intro n k
  have hchain := dist_le_range_sum_dist (P n) k
  calc
    dist (Q n) (P n k) = dist (P n 0) (P n k) := by rw [hbase n]
    _ ≤ ∑ j ∈ Finset.range k, dist (P n j) (P n (j + 1)) := hchain
    _ ≤ ∑ j ∈ Finset.range k, e n j :=
      Finset.sum_le_sum fun j _ ↦ hstep n j
    _ ≤ r n := hpartial n k

/-- Summability and nonnegativity replace every finite prefix by the complete
row error mass. -/
theorem partial_le_tsum
    {e : ℕ → ℕ → ℝ}
    (he0 : ∀ n k, 0 ≤ e n k) (hes : ∀ n, Summable (e n)) :
    ∀ n k, (∑ j ∈ Finset.range k, e n j) ≤ ∑' j, e n j := by
  intro n k
  exact (hes n).sum_le_tsum (Finset.range k) (fun j _ ↦ he0 n j)

/-- The exact variable-tube field for the presented array.  Compared with
`schemeTube_of_basePath_tail`, the geometric input is only the genuine
consecutive marked-distance estimate. -/
theorem tube_of_stepDistance_and_rowBudget
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg : ℕ → ℝ}
    {c0 d0 A0 r rho C : ℕ → ℝ} {c dlt : ℝ}
    (B : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0 r rho C c dlt)
    (hbaseEq : ∀ n, P n 0 = Q n)
    (hbase : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hbase_acc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n)
    (hPcurve : ∀ n k u, HasDerivAt (⇑(P n k).1) ((P n k).2.1 u) u)
    (hPvel : ∀ n k u, HasDerivAt (⇑(P n k).2.1) ((P n k).2.2 u) u)
    (hPperiodic : ∀ n k, Periodic (⇑(P n k).1) 1)
    (horiented : ∀ n k u, 0 ≤
      ((starRingEnd ℂ) ((P n k).2.1 u) * (P n k).2.2 u).im)
    (hstep : ∀ n k, dist (P n k) (P n (k + 1)) ≤ e n k)
    (hpartial : ∀ n k, (∑ j ∈ Finset.range k, e n j) ≤ r n) :
    ∀ n k, IsVariableTubeMember c (C n) 0 dlt (P n k) := by
  have hdist := dist_base_le_radius_of_stepDistance hbaseEq hstep hpartial
  intro n k
  have hlocal := variableTube_of_dist_le (hbase n) (hPcurve n k)
    (hPvel n k) (hPperiodic n k) (hdist n k) (hbase_acc n)
    (horiented n k) (B.radius_nonnegative n) (B.local_speed_positive n)
    (B.acceleration_nonnegative n) (B.rho_positive n) (B.rho_half n)
    (B.acceleration_radius n) B.chord_nonnegative (B.chord_speed n)
    (B.chord_margin n)
  exact
    { hasDerivAt_curve := hlocal.hasDerivAt_curve
      hasDerivAt_vel := hlocal.hasDerivAt_vel
      periodic := hlocal.periodic
      speed_lb := fun u ↦ (B.target_speed n).trans (hlocal.speed_lb u)
      speed_ub := fun u ↦ (hlocal.speed_ub u).trans (B.upper_speed n)
      curv_lb := hlocal.curv_lb
      chord := hlocal.chord }

/-- Assemble the exact geometric scheme consumed by the explicit-front
capstone, using the scalar radius only through a row budget. -/
def geometricSchemeOfStepDistance
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {c0 d0 A0 r rho : ℕ → ℝ}
    (B : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0 r rho C c dlt)
    (hbaseEq : ∀ n, P n 0 = Q n)
    (he0 : ∀ n k, 0 ≤ e n k) (hes : ∀ n, Summable (e n))
    (hbase : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hbase_acc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n)
    (hPcurve : ∀ n k u, HasDerivAt (⇑(P n k).1) ((P n k).2.1 u) u)
    (hPvel : ∀ n k u, HasDerivAt (⇑(P n k).2.1) ((P n k).2.2 u) u)
    (hPperiodic : ∀ n k, Periodic (⇑(P n k).1) 1)
    (horiented : ∀ n k u, 0 ≤
      ((starRingEnd ℂ) ((P n k).2.1 u) * (P n k).2.2 u).im)
    (hstepDist : ∀ n k, dist (P n k) (P n (k + 1)) ≤ e n k)
    (hpartial : ∀ n k, (∑ j ∈ Finset.range k, e n j) ≤ r n)
    (stepPath : ∀ n k, NormalPath (P n k) (P n (k + 1)))
    (stepGeometry : ∀ n k,
      IsVariableSpeedNormalPath (P0 n) (P1 n) (khat n) (G1 n) (Cg n)
        (stepPath n k))
    (stepCost : ∀ n k, cost (stepPath n k) ≤ e n k)
    (finiteEdge : ∀ n k,
      GeometricUnitTangentRangeEdge (P (n + 1) k) (P n (k + 1))) :
    GeometricScheme Q P e P0 P1 khat G1 Cg C c dlt where
  base := hbaseEq
  error_nonnegative := he0
  error_summable := hes
  tube := tube_of_stepDistance_and_rowBudget B hbaseEq hbase hbase_acc
    hPcurve hPvel hPperiodic horiented hstepDist hpartial
  stepPath := stepPath
  stepGeometry := stepGeometry
  stepCost := stepCost
  finiteEdge := finiteEdge

namespace ScalarClosing

variable
  {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  {G : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output J E0
      (configuredSourceMassTarget E0 C0 C1 C2)}

/-- The scalar closing radius is exactly a pullback tail, for consumers whose
budget is phrased with `PullbackTubeTailBudget.radius`. -/
theorem radius_eq_pullback
    (O : ConfiguredRecursiveEdgeFiniteColumnScalarClosing.ClosingOutput
      J G E0 C0 C1 C2) (n : ℕ) :
    O.radius n = PullbackTubeTailBudget.radius 1 1 O.defect n :=
  ConfiguredRecursiveEdgeFiniteColumnScalarClosing.ClosingOutput.radius_eq_pullback O n

/-- Monotonicity of the paper shadow inequality.  This is the exact `hgap`
conclusion required by the explicit-front capstone. -/
theorem paperGap_of_shadow_le_radius
    (O : ConfiguredRecursiveEdgeFiniteColumnScalarClosing.ClosingOutput
      J G E0 C0 C1 C2)
    {shadow : ℝ} (hshadow : shadow ≤ O.radius 0) :
    J.scalar.Cw + 2 * shadow <
      (2 * O.data.Hs 0 - shadow) / Real.pi := by
  have hleft : J.scalar.Cw + 2 * shadow ≤
      J.scalar.Cw + 2 * O.radius 0 := by linarith
  have hright :
      (2 * O.data.Hs 0 - O.radius 0) / Real.pi ≤
        (2 * O.data.Hs 0 - shadow) / Real.pi :=
    div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
  exact hleft.trans_lt (O.width_gap.trans_le hright)

/-- Universal paper gap from one row-zero shadow bound.  The result can be
passed directly as the `hgap` argument of
`GenericVariableTerminalDirectCapstoneExplicitFront.exists_paperFacingOutput`. -/
theorem universalPaperGap
    (O : ConfiguredRecursiveEdgeFiniteColumnScalarClosing.ClosingOutput
      J G E0 C0 C1 C2)
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (hshadow : ∀ X : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt,
      PaperFacingVariableTerminalOutput.shadowSize X ≤ O.radius 0) :
    ∀ X : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt,
      J.scalar.Cw + 2 * PaperFacingVariableTerminalOutput.shadowSize X <
        (2 * O.data.Hs 0 -
          PaperFacingVariableTerminalOutput.shadowSize X) / Real.pi := by
  intro X
  exact paperGap_of_shadow_le_radius O (hshadow X)

/-- The definition of `shadowSize` reduces the universal shadow obligation to
one scalar row-error-tail inequality, independent of the chosen limit. -/
theorem universalPaperGap_of_rowError
    (O : ConfiguredRecursiveEdgeFiniteColumnScalarClosing.ClosingOutput
      J G E0 C0 C1 C2)
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (hrow : c2ConstVar (P0 0) (P1 0) (khat 0) (G1 0) (Cg 0) *
      (∑' k, e 0 k) ≤ O.radius 0) :
    ∀ X : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt,
      J.scalar.Cw + 2 * PaperFacingVariableTerminalOutput.shadowSize X <
        (2 * O.data.Hs 0 -
          PaperFacingVariableTerminalOutput.shadowSize X) / Real.pi := by
  apply universalPaperGap O
  intro X
  simpa [PaperFacingVariableTerminalOutput.shadowSize,
    TriangularMarkedPathSchemeVariableTerminal.rowC,
    ShadowingTails.tail] using hrow

end ScalarClosing

end ConfiguredRecursiveEdgePresentedArrayScalarSidecars
