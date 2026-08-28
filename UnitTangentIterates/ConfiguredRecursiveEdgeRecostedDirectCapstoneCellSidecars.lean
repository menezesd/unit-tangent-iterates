import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedConcreteCapstoneInput

/-!
# Cell sidecars for truthful recosted diagonal rows

Every positive-depth source is the exact source constructed by the preceding
diagonal step.  Its analytic slice therefore supplies the full nonaffine
facts automatically.  Only depth-zero source facts and the terminal-front
common-tube facts remain external to the current diagonal-row API.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedDirectCapstoneCellSidecars

open ConfiguredCanonicalPairSource
  ConfiguredRecursiveEdgeRecostedConcreteCapstoneInput
  ConfiguredRecursiveEdgeRecostedDirectCapstoneAdapter
  ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  VariableMarkedTube

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
  ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
  ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}

/-- Source facts needed only at depth zero.  At positive depth they are
reconstructed from the exact analytic slice stored by the preceding step. -/
structure BaseFacts (H : Grid J) where
  P1 : ℕ → ℝ
  markingLower : ℕ → ℝ
  markingUpper : ℕ → ℝ
  facts : ∀ n, Nonaffine.Facts (H.stage n 0).source
    (P1 n) (markingLower n) (markingUpper n)
  baseTube : ∀ n,
    IsTubeMember (commonC (rowData J)) 0 (commonDlt (rowData J)) (H.P n 0)

/-- The two canonical-front facts not retained by the abstract `Rows`
structure.  A configured canonical-row provider can fill these directly
from its composition invariant and common tube. -/
structure FrontFacts (H : Grid J) where
  frontData_eq : ∀ n k,
    (H.row n k).geometric.terminal.frontData =
      FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
        (H.stage n k).source
  frontTube : ∀ n k,
    IsTubeMember (commonC (rowData J)) 0 (commonDlt (rowData J))
      (H.row n k).geometric.terminal.frontData

namespace Grid

/-- The exact slice installed in the source of cell `(n,k+1)`. -/
def positiveSlice (H : Grid J) (n k : ℕ) :=
  ((H.rows.step k (H.rows.stages k)).analytic n).slice

/-- Positive-depth nonaffine facts are theorem-produced, rather than a
cellwise callback. -/
def positiveFacts (H : Grid J) (n k : ℕ) :
    Nonaffine.Facts (H.stage n (k + 1)).source
      (positiveSlice H n k).periodUpper
      (positiveSlice H n k).markingLower
      (positiveSlice H n k).markingUpper := by
  change Nonaffine.Facts
    ((H.rows.step k (H.rows.stages k)).analytic n).source
      (positiveSlice H n k).periodUpper
      (positiveSlice H n k).markingLower
      (positiveSlice H n k).markingUpper
  exact Nonaffine.Facts.ofAnalytic (positiveSlice H n k) le_rfl

/-- Assemble every exact geometric cell.  The only source-side input is the
depth-zero family; all successor source facts come from `Input.slice`. -/
def cellFamily (H : Grid J) (B : BaseFacts H) (F : FrontFacts H) :
    CellFamily H where
  input := by
    intro n k
    cases k with
    | zero =>
        exact
          { P1 := B.P1 n
            markingLower := B.markingLower n
            markingUpper := B.markingUpper n
            facts := B.facts n
            frontData_eq := F.frontData_eq n 0
            frontTube := F.frontTube n 0 }
    | succ k =>
        exact
          { P1 := (positiveSlice H n k).periodUpper
            markingLower := (positiveSlice H n k).markingLower
            markingUpper := (positiveSlice H n k).markingUpper
            facts := positiveFacts H n k
            frontData_eq := F.frontData_eq n (k + 1)
            frontTube := F.frontTube n (k + 1) }
  baseTube := B.baseTube

end Grid

/-- Build the complete geometric assembly from truthful diagonal rows and
their reduced sidecar package. -/
def assembly
    (H : Grid J) (B : BaseFacts H) (F : FrontFacts H)
    (C : ℕ → ℝ)
    (htube : ∀ n k, IsVariableTubeMember
      (commonC (rowData J)) (C n) 0 (commonDlt (rowData J)) (H.P n k)) :
    Assembly J where
  grid := H
  cells := Grid.cellFamily H B F
  C := C
  tube := htube

/-- The final concrete capstone input.  The complete `GeometricArray.Package`
is generated internally by `Assembly.physicalPackage`; the closing input is
stated directly on the actual displayed base. -/
def concreteInput
    (H : Grid J) (B : BaseFacts H) (F : FrontFacts H)
    (C : ℕ → ℝ)
    (htube : ∀ n k, IsVariableTubeMember
      (commonC (rowData J)) (C n) 0 (commonDlt (rowData J)) (H.P n k))
    (baseFacts :
      ConfiguredRecursiveEdgeRecostScaledPaperCapstoneBaseFacts.BaseFacts
        (assembly H B F C htube).core) :
    ConfiguredRecursiveEdgeRecostedConcreteCapstoneInput.Input J where
  assembly := assembly H B F C htube
  baseFacts := baseFacts

end ConfiguredRecursiveEdgeRecostedDirectCapstoneCellSidecars
