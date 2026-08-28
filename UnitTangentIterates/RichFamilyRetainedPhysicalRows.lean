import UnitTangentIterates.RichFamilyDirectPhysicalMarking

/-!
# Physical rows retained by a rich recursive family

Each rich stage already stores the physical terminal base whose normalized
marking produces the actual variable terminal.  This module makes those
stored bases into the physical row family used by the limit argument.  No
identification with a canonically marked selected inverse is required.
-/

noncomputable section

open MarkedSpace

namespace RichFamilyRetainedPhysicalRows

open NormalizedTerminalMarkingComposition
  RichFamilyPhysicalMarkingIntegration
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- The physical row represented directly by the rich stages. -/
def rows
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (F : RichFamily Q e P0 P1 khat G1 Cg C c dlt) : ℕ → ℕ → Data
  | n, 0 => F.P n 0
  | n, k + 1 => (F.richStage n k).terminalBase

@[simp] theorem rows_zero
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (F : RichFamily Q e P0 P1 khat G1 Cg C c dlt) (n : ℕ) :
    rows F n 0 = F.P n 0 := rfl

@[simp] theorem rows_succ
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (F : RichFamily Q e P0 P1 khat G1 Cg C c dlt) (n k : ℕ) :
    rows F n (k + 1) = (F.richStage n k).terminalBase := rfl

/-- The normalized physical-to-terminal markings are intrinsic to the rich
family once its retained physical rows are used. -/
def directMarkings
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (F : RichFamily Q e P0 P1 khat G1 Cg C c dlt) :
    DirectPhysicalTerminalMarkingFamily (rows F) F.P where
  lambda n
    | 0 => 1
    | k + 1 => (F.richStage n k).lambda
  Lambda n
    | 0 => 1
    | k + 1 => (F.richStage n k).Lambda
  marking n
    | 0 => NormalizedC2Marking.refl (F.P n 0)
    | k + 1 => (F.richStage n k).marking

end RichFamilyRetainedPhysicalRows
