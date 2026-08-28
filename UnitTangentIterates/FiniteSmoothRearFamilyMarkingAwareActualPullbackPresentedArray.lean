import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
import UnitTangentIterates.GenericVariableTerminalDirectCapstoneExplicitFront
import UnitTangentIterates.WeightedRecursiveDefectCapAwareActualPullbackStages

/-!
# Two-dimensional displayed array of actual pullback stages

Rows are independent one-dimensional actual-source recursions.  Every cell
exposes the intermediate selected rear and its recosted path, while diagonal
range coherence and tube membership are stated only for the displayed grid.
-/

noncomputable section

open MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareActualPullbackPresentedArray

open FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  NormalPathC2IncrementVariableSpeed VariableMarkedTube

/-- A row-indexed family of actual pullback providers. -/
structure Rows
    (P0 kh khat Qmax : ℕ → ℕ → ℝ)
    (E C0 C1 C2 : ℕ → ℝ) (d : ℕ → ℕ → ℝ) where
  base : ∀ n, Stage (P0 n) (kh n) (khat n) (Qmax n) 0
  provider : ∀ n, Provider (base n) (E n) (C0 n) (C1 n) (C2 n) (d n)

namespace Rows

variable {P0 kh khat Qmax : ℕ → ℕ → ℝ}
  {E C0 C1 C2 : ℕ → ℝ} {d : ℕ → ℕ → ℝ}

/-- The canonical displayed grid. -/
def P (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) : Data :=
  (R.provider n).displayed k

/-- The complete theorem-selected input at a displayed cell. -/
def input (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) :=
  (R.provider n).step k ((R.provider n).stages k)

/-- The intermediate actual selected rear, before the outgoing endpoint cap. -/
def intermediateRear (R : Rows P0 kh khat Qmax E C0 C1 C2 d)
    (n k : ℕ) : Data :=
  (R.input n k).geometric.output.jets.rear

/-- The raw selected path used by the successor source. -/
def rawPath (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) :
    NormalPath (R.P n k) (R.intermediateRear n k) :=
  (R.input n k).geometric.rawPath

/-- The canonical physical recost, used only for the metric estimate. -/
def recostPath (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) :
    NormalPath (R.P n k) (R.intermediateRear n k) :=
  let I := R.input n k
  I.geometric.recost I.metric.c2 I.metric.eta_continuous
    I.metric.eta1_continuous I.metric.eta2_continuous

/-- The outgoing nonaffine cap from the intermediate rear to displayed `P`. -/
def endpointCap (R : Rows P0 kh khat Qmax E C0 C1 C2 d)
    (n k : ℕ) : ℝ :=
  (R.input n k).geometric.endpointCap

/-- The intrinsic path-to-metric conversion at a cell. -/
def pathConversion (R : Rows P0 kh khat Qmax E C0 C1 C2 d)
    (n k : ℕ) : ℝ :=
  let M := (R.input n k).metric
  c2ConstVar M.pathP0 M.pathP1 M.pathKhat M.pathG1 M.pathCg

/-- The sharp physical-path-plus-endpoint-cap budget. -/
def error (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) : ℝ :=
  (R.provider n).error k

/-- Stable-component contribution before the outgoing endpoint cap. -/
def pathError (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) : ℝ :=
  R.pathConversion n k *
    (4 * ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
      (E n) (C0 n) (C1 n) (C2 n) * d n k)

theorem path_dist_le_pathError
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) :
    dist (R.P n k) (R.intermediateRear n k) ≤ R.pathError n k := by
  let M := (R.input n k).metric
  have hK0 : 0 ≤ R.pathConversion n k := by
    exact c2ConstVar_nonneg _ _ _ _ _
  have hcost :=
    FiniteSmoothRearFamilyMarkingAwareNonaffineFiniteStability.recost_cost_le_four_configuredTarget_mul
      M.c2 M.eta_continuous M.eta1_continuous M.eta2_continuous M.stable
  exact M.dist_start_rear_le_recost.trans
    (mul_le_mul_of_nonneg_left hcost hK0)

theorem endpointCap_nonnegative
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) :
    0 ≤ R.endpointCap n k :=
  (R.input n k).geometric.endpointCap_nonnegative

theorem intermediateRear_dist_next_le
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) :
    dist (R.intermediateRear n k) (R.P n (k + 1)) ≤
      R.endpointCap n k :=
  (R.input n k).geometric.rear_dist_base_le_endpointCap

theorem displayed_step_dist_le_error
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) :
    dist (R.P n k) (R.P n (k + 1)) ≤ R.error n k :=
  (R.provider n).step_dist k

/-- Construct the common cap-aware stage interface used by the final direct
capstone. -/
def toCapAwareActualPullbackStages
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d)
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (hbase : ∀ n, R.P n 0 = Q n)
    (hcombined : ∀ n k,
      R.pathError n k + R.endpointCap n k ≤ e n k)
    (hrange : ∀ n k,
      GeometricUnitTangentRangeEdge (R.P (n + 1) k) (R.P n (k + 1))) :
    WeightedRecursiveDefect.CapAwareActualPullbackStages
      Q R.P R.intermediateRear R.pathError R.endpointCap e where
  base := hbase
  path := R.recostPath
  path_dist_le := R.path_dist_le_pathError
  cap_dist_le := R.intermediateRear_dist_next_le
  combined_le := hcombined
  range_edge := hrange

/-- The two independent configured ceilings needed by direct-diagonal
domination.  The endpoint cap is not multiplied by `pathCeiling`. -/
structure Ceilings
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d)
    (pathCeiling endpointCeiling q : ℕ → ℕ → ℝ) : Prop where
  path : ∀ n k, R.pathConversion n k ≤ pathCeiling n k
  endpoint : ∀ n k,
    R.endpointCap n k ≤ endpointCeiling n k * q n k

/-- Configured scalar closure of the two separate ceilings. -/
theorem configured_combined_le
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d)
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C00 C10 C20 M : ℝ) (idx : ℕ → ℕ → ℕ)
    (H : Ceilings R
      (fun n k => ConfiguredRecursiveEdgeSourceP0Growth.edgeConversion D
        (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D) MA NA (idx n k))
      (fun n k => ConfiguredRecursiveEdgeSourceP0Growth.edgeEndpointConversion
        D ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh M (idx n k))
      (fun n k => ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
        D (idx n k + 1)))
    (hE : ∀ n, E n = E0) (hC0 : ∀ n, C0 n = C00)
    (hC1 : ∀ n, C1 n = C10) (hC2 : ∀ n, C2 n = C20)
    (hd : ∀ n k, d n k =
      ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
        D (idx n k + 1)) :
    ∀ n k, R.pathError n k + R.endpointCap n k ≤
      ConfiguredRecursiveEdgeFiniteColumnScalarClosing.directDiagonal
        D MA NA E0 C00 C10 C20 M (idx n k) := by
  intro n k
  rw [pathError, hE n, hC0 n, hC1 n, hC2 n, hd n k]
  exact ConfiguredRecursiveEdgeFiniteColumnScalarClosing.capAwareBudget_le_directDiagonal
    D (c2ConstVar_nonneg _ _ _ _ _) (H.path n k) (H.endpoint n k)

/-- The configured ceilings directly produce the common cap-aware stage
interface with `directDiagonal` as displayed error. -/
def toConfiguredCapAwareActualPullbackStages
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d)
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C00 C10 C20 M : ℝ) (idx : ℕ → ℕ → ℕ)
    (H : Ceilings R
      (fun n k => ConfiguredRecursiveEdgeSourceP0Growth.edgeConversion D
        (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D) MA NA (idx n k))
      (fun n k => ConfiguredRecursiveEdgeSourceP0Growth.edgeEndpointConversion
        D ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh M (idx n k))
      (fun n k => ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
        D (idx n k + 1)))
    (hE : ∀ n, E n = E0) (hC0 : ∀ n, C0 n = C00)
    (hC1 : ∀ n, C1 n = C10) (hC2 : ∀ n, C2 n = C20)
    (hd : ∀ n k, d n k =
      ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
        D (idx n k + 1))
    (Q : ℕ → Data) (hbase : ∀ n, R.P n 0 = Q n)
    (hrange : ∀ n k,
      GeometricUnitTangentRangeEdge (R.P (n + 1) k) (R.P n (k + 1))) :
    WeightedRecursiveDefect.CapAwareActualPullbackStages
      Q R.P R.intermediateRear R.pathError R.endpointCap
      (fun n k => ConfiguredRecursiveEdgeFiniteColumnScalarClosing.directDiagonal
        D MA NA E0 C00 C10 C20 M (idx n k)) :=
  R.toCapAwareActualPullbackStages Q _ hbase
    (R.configured_combined_le D MA NA E0 C00 C10 C20 M idx H
      hE hC0 hC1 hC2 hd) hrange

/-- Displayed-grid data needed by the direct capstone.  Range edges and tubes
belong to `P`; the intermediate rear never appears in either statement. -/
structure PresentedData
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d)
    (Q : ℕ → Data) (err : ℕ → ℕ → ℝ)
    (rowP0 rowP1 rowKhat rowG1 rowCg rowC : ℕ → ℝ)
    (c dlt : ℝ) : Prop where
  base : ∀ n, R.P n 0 = Q n
  error_nonnegative : ∀ n k, 0 ≤ err n k
  error_summable : ∀ n, Summable (err n)
  tube : ∀ n k, IsVariableTubeMember c (rowC n) 0 dlt (R.P n k)
  range_edge : ∀ n k,
    GeometricUnitTangentRangeEdge (R.P (n + 1) k) (R.P n (k + 1))
  metric : ∀ n k,
    dist (R.P n k) (R.P n (k + 1)) ≤ err n k

/-- Forget the analytic source recursion and feed the displayed array to the
generic direct capstone. -/
def PresentedData.toGeometricDistanceScheme
    {R : Rows P0 kh khat Qmax E C0 C1 C2 d}
    {Q : ℕ → Data} {err : ℕ → ℕ → ℝ}
    {rowP0 rowP1 rowKhat rowG1 rowCg rowC : ℕ → ℝ}
    {c dlt : ℝ}
    (A : PresentedData R Q err rowP0 rowP1 rowKhat rowG1 rowCg rowC c dlt) :
    GenericVariableTerminalDirectCapstoneExplicitFront.GeometricDistanceScheme
      Q R.P err rowP0 rowP1 rowKhat rowG1 rowCg rowC c dlt where
  base := A.base
  error_nonnegative := A.error_nonnegative
  error_summable := A.error_summable
  tube := A.tube
  stepDistance := by
    intro n k
    have hrow : 1 ≤
        TriangularMarkedPathSchemeVariableTerminal.rowC
          rowP0 rowP1 rowKhat rowG1 rowCg n := by
      simpa [TriangularMarkedPathSchemeVariableTerminal.rowC] using
        one_le_c2ConstVar (rowP0 n) (rowP1 n) (rowKhat n)
          (rowG1 n) (rowCg n)
    exact (A.metric n k).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hrow (A.error_nonnegative n k))
  finiteEdge := A.range_edge

end Rows

end FiniteSmoothRearFamilyMarkingAwareActualPullbackPresentedArray
