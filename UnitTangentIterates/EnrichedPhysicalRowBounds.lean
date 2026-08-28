import UnitTangentIterates.EnrichedPhysicalChosenRichFamily
import UnitTangentIterates.RichFamilyRetainedPhysicalRows
import UnitTangentIterates.RichFamilyPhysicalMarkingIntegration

/-!
# Physical row bounds retained by an enriched chosen family

This is a nonbreaking extension of the chosen-column API.  It records the
fixed-tube, perimeter, acceleration, and endpoint-distance data on each
terminal base before `RichStageData` erases them, and assembles the exact
`PhysicalRowBounds` used downstream.
-/

noncomputable section

open MarkedSpace PathMetric

namespace EnrichedPhysicalRowBounds

open EnrichedPhysicalChosenRichFamily
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- Rowwise constants shared by all retained physical depths. -/
structure Parameters (cb db : ℝ) where
  Lmin : ℕ → ℝ
  Lmax : ℕ → ℝ
  Ab : ℕ → ℝ
  r : ℕ → ℝ
  Lmin_pos : ∀ n, 0 < Lmin n
  Ab_nonneg : ∀ n, 0 ≤ Ab n
  r_nonneg : ∀ n, 0 ≤ r n

/-- Exact geometric data on one retained physical terminal base. -/
structure TerminalBounds {cb db : ℝ} (R : Parameters cb db)
    (n : ℕ) (physical endpoint : Data) : Prop where
  tube : IsTubeMember cb 0 db physical
  perim_lower : R.Lmin n ≤ perim physical
  perim_upper : perim physical ≤ R.Lmax n
  acceleration : ∀ u, ‖physical.2.2 u‖ ≤ R.Ab n
  endpoint_dist : dist physical endpoint ≤ R.r n

/-- A chosen enriched construction with all physical row geometry retained.
The terminal field is indexed only over the stages actually selected by `E`.
-/
structure BoundedConstruction
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (E : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      GaugeCertificate a MA NA K0 K1 K2)
    (cb db : ℝ) where
  params : Parameters cb db
  base_tube : ∀ n, IsTubeMember cb 0 db (Q n)
  base_perim_lower : ∀ n, params.Lmin n ≤ perim (Q n)
  base_perim_upper : ∀ n, perim (Q n) ≤ params.Lmax n
  base_acceleration : ∀ n u, ‖(Q n).2.2 u‖ ≤ params.Ab n
  terminal : ∀ k n, TerminalBounds params n
    ((E.chosenColumn k).step.richStage n).terminalBase
    ((E.chosenColumn k).step.next n)

/-- Assemble the downstream row package with no alignment hypothesis: at
successor depth both the retained physical row and the marked endpoint are
definitionally the entries stored in the chosen stage. -/
def BoundedConstruction.physicalRowBounds
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 cb db : ℝ}
    {E : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      GaugeCertificate a MA NA K0 K1 K2}
    (B : BoundedConstruction E cb db) :
    RichFamilyPhysicalMarkingIntegration.PhysicalRowBounds
      (RichFamilyRetainedPhysicalRows.rows E.toRichFamily)
      E.toRichFamily.P cb db where
  Lmin := B.params.Lmin
  Lmax := B.params.Lmax
  Ab := B.params.Ab
  r := B.params.r
  Lmin_pos := B.params.Lmin_pos
  Ab_nonneg := B.params.Ab_nonneg
  r_nonneg := B.params.r_nonneg
  physical_tube := by
    intro n k
    cases k with
    | zero => simpa [Construction.toRichFamily,
        EnrichedPhysicalChosenRichFamily.columns_zero] using B.base_tube n
    | succ k => exact (B.terminal k n).tube
  physical_perim_lower := by
    intro n k
    cases k with
    | zero => simpa [Construction.toRichFamily,
        EnrichedPhysicalChosenRichFamily.columns_zero] using
        B.base_perim_lower n
    | succ k => exact (B.terminal k n).perim_lower
  physical_perim_upper := by
    intro n k
    cases k with
    | zero => simpa [Construction.toRichFamily,
        EnrichedPhysicalChosenRichFamily.columns_zero] using
        B.base_perim_upper n
    | succ k => exact (B.terminal k n).perim_upper
  physical_acc := by
    intro n k u
    cases k with
    | zero => simpa [Construction.toRichFamily,
        EnrichedPhysicalChosenRichFamily.columns_zero] using
        B.base_acceleration n u
    | succ k => exact (B.terminal k n).acceleration u
  endpoint_dist := by
    intro n k
    cases k with
    | zero =>
        simpa [Construction.toRichFamily,
          EnrichedPhysicalChosenRichFamily.columns_zero] using B.params.r_nonneg n
    | succ k =>
        simpa [Construction.toRichFamily,
          EnrichedPhysicalChosenRichFamily.columns_succ] using
          (B.terminal k n).endpoint_dist

end EnrichedPhysicalRowBounds
