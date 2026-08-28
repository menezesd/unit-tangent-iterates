import UnitTangentIterates.TriangularMarkedRecursiveChoiceVariableTerminal
import UnitTangentIterates.GaugeRearFamilyRichTerminalStage
import UnitTangentIterates.NormalizedTerminalMarkingComposition

/-!
# Dependent construction of variable-terminal triangular families

One recursive step acts on a whole column: the rear in row `n` uses both
entries `n` and `n+1` of the current column.  This module packages that
dependence once, applies countable choice column by column, and retains the
base-to-depth path and normalized terminal marking produced by the rich gauge
stage.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed

namespace TriangularMarkedRecursiveChoiceVariableTerminalConstructor

open VariableMarkedTube GaugeRearFamilyVariableTerminal
  NormalizedTerminalMarkingComposition

/-- The defect facts are independent of the recursive choices. -/
structure RowDefectProvider (e : ℕ → ℕ → ℝ) : Prop where
  nonnegative : ∀ n k, 0 ≤ e n k
  summable : ∀ n, Summable (e n)

/-- A gauge stage together with the normalized marking which relates its
physical arclength representative to the actual terminal marked datum. -/
structure RichStageData
    (p front rear : Data) (bound P0 P1 khat G1 Cg c C dlt : ℝ) where
  stage : RawStageOutput p front rear bound P0 P1 khat G1 Cg
  terminalBase : Data
  lambda : ℝ
  Lambda : ℝ
  marking : NormalizedC2Marking terminalBase rear lambda Lambda

/-- Forget the additional terminal-marking information. -/
def RichStageData.toRawStageOutput
    {p front rear : Data} {bound P0 P1 khat G1 Cg c C dlt : ℝ}
    (S : RichStageData p front rear bound P0 P1 khat G1 Cg c C dlt) :
    RawStageOutput p front rear bound P0 P1 khat G1 Cg :=
  S.stage

/-- The existing analytic rich gauge output is an instance of the generic
rich-stage datum used by the recursive constructor. -/
def RichStageData.ofGaugeRich
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {ell L T : ℝ} {base : Data}
    {J : GaugeFlowMarkedTerminalJets.TerminalJets xi xiX xiXX Phi ell L T base}
    {p front : Data} {bound P0 kh khat M c C dlt : ℝ}
    (S : GaugeRearFamilyRichTerminalStage.RichStageOutput
      J p front bound P0 kh khat M c C dlt) :
    RichStageData p front J.rear bound P0
      (GaugeFlowDerivCost.costP1 ell khat M) khat
      (GaugeFlowDerivCost.costG1 ell khat
        (GaugeMarkedDataOfRearFamily.rearKappa2 kh) M)
      (khat * GaugeFlowDerivCost.costG1 ell khat
          (GaugeMarkedDataOfRearFamily.rearKappa2 kh) M +
        GaugeMarkedDataOfRearFamily.rearKappa2 kh *
          GaugeFlowDerivCost.costP1 ell khat M ^ 2) c C dlt where
  stage := S.stage
  terminalBase := base
  lambda := S.lambda
  Lambda := S.Lambda
  marking := NormalizedC2Marking.ofRichStage S

/-- One simultaneous recursive choice from a current column to the next. -/
structure ColumnStep
    (Q current : ℕ → Data) (e : ℕ → ℕ → ℝ) (k : ℕ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ) where
  next : ℕ → Data
  richStage : ∀ n,
    RichStageData (current n) (current (n + 1)) (next n) (e n k)
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n) c (C n) dlt

/-- The depth-zero rich stages start from the configured base column. -/
structure BaseStageProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ) where
  base : Nonempty (ColumnStep Q Q e 0 P0 P1 khat G1 Cg C c dlt)

/-- A mapped stage receives the complete previously chosen rich stage column.
In particular it retains the path and terminal marking needed to propagate
that path, rather than receiving only the previous endpoint data. -/
structure MapStageProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ) where
  map : ∀ k {current}
    (S : ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt),
      Nonempty (ColumnStep Q S.next e (k + 1) P0 P1 khat G1 Cg C c dlt)

/-- The dependent sequence of chosen rich stage columns.  The current column
of stage `k+1` is definitionally the terminal column of stage `k`. -/
def stageColumns
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (B : BaseStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    (M : MapStageProvider Q e P0 P1 khat G1 Cg C c dlt) :
    ∀ k, (current : ℕ → Data) ×
      ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt
  | 0 => ⟨Q, Classical.choice B.base⟩
  | k + 1 =>
      let S := stageColumns B M k
      ⟨S.2.next, Classical.choice (M.map k S.2)⟩

/-- The endpoint columns selected by the dependent stage recursion. -/
def columns
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (B : BaseStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    (M : MapStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    (k : ℕ) : ℕ → Data :=
  (stageColumns B M k).1

/-- The chosen rich transition at depth `k`. -/
def chosenStep
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (B : BaseStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    (M : MapStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    (k : ℕ) :
    ColumnStep Q (columns B M k) e k P0 P1 khat G1 Cg C c dlt :=
  by
    change ColumnStep Q (stageColumns B M k).1 e k P0 P1 khat G1 Cg C c dlt
    exact (stageColumns B M k).2

theorem columns_zero
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (B : BaseStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    (M : MapStageProvider Q e P0 P1 khat G1 Cg C c dlt) :
    columns B M 0 = Q := rfl

theorem columns_succ
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (B : BaseStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    (M : MapStageProvider Q e P0 P1 khat G1 Cg C c dlt) (k : ℕ) :
    columns B M (k + 1) = (chosenStep B M k).next := rfl

/-- A variable-terminal family retaining all rich finite-stage markings. -/
structure RichFamily
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ) where
  P : ℕ → ℕ → Data
  base : ∀ n, P n 0 = Q n
  defect : RowDefectProvider e
  base_harnack : ∀ n, ArclengthHarnackCertificate (Q n)
  richStage : ∀ n k,
    RichStageData (P n k) (P (n + 1) k) (P n (k + 1)) (e n k)
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n) c (C n) dlt
  harnackClosed : ∀ n x, Tendsto (P n) atTop (nhds x) →
    (∀ k, ArclengthHarnackCertificate (P n k)) → ArclengthHarnackCertificate x

/-- Forget rich markings down to the existing limit-facing family. -/
def RichFamily.toFamily
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (F : RichFamily Q e P0 P1 khat G1 Cg C c dlt)
    (htube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (F.P n k)) :
    TriangularMarkedRecursiveChoiceVariableTerminal.Family
      Q e P0 P1 khat G1 Cg C c dlt where
  P := F.P
  base := F.base
  error_nonnegative := F.defect.nonnegative
  error_summable := F.defect.summable
  tube := htube
  base_harnack := F.base_harnack
  stage := fun n k => (F.richStage n k).stage
  harnackClosed := F.harnackClosed

/-- Countable dependent choice assembles the complete rich triangular family. -/
def construct
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (D : RowDefectProvider e)
    (B : BaseStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    (M : MapStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    (hbaseHarnack : ∀ n, ArclengthHarnackCertificate (Q n))
    (hclosed : ∀ n x, Tendsto (fun k => columns B M k n) atTop (nhds x) →
      (∀ k, ArclengthHarnackCertificate (columns B M k n)) →
        ArclengthHarnackCertificate x) :
    RichFamily Q e P0 P1 khat G1 Cg C c dlt where
  P n k := columns B M k n
  base := fun _ => rfl
  defect := D
  base_harnack := hbaseHarnack
  richStage := by
    intro n k
    simpa only [columns_succ] using (chosenStep B M k).richStage n
  harnackClosed := hclosed

end TriangularMarkedRecursiveChoiceVariableTerminalConstructor
