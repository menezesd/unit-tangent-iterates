import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalBaseCell
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainVariableTube

/-!
# The physical array of a chosen prepared chain

The depth-zero cell comes from the retained physical base presentation, while
every successor cell comes from the prepared positive-depth construction.
Together with coherent step distance and the final row budget, these cells
form the exact geometric array consumed by the multiplier paper capstone.
-/

noncomputable section

open Function Set MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed VariableMarkedTube

namespace ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray

open CoherentPhaseReachableMetricRange
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFinitePresentedPaperCapstone
  ConfiguredRecursiveEdgeRecostFinitePreparedChosenChain
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  {H : Output R}

/-- The unconditional physical cell at every depth. -/
def cell (C : ChosenChain H) (n k : ℕ) : Cell C.system.P n k :=
  match k with
  | 0 =>
      ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalBaseCell.cell
        C n
  | k + 1 =>
      ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell.cell
        C n k

@[simp] theorem cell_zero (C : ChosenChain H) (n : ℕ) :
    cell C n 0 =
      ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalBaseCell.cell
        C n := rfl

@[simp] theorem cell_succ (C : ChosenChain H) (n k : ℕ) :
    cell C n (k + 1) =
      ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell.cell
        C n k := rfl

@[simp] theorem cell_state_kh (C : ChosenChain H) (n k : ℕ) :
    (cell C n k).state.kh = sourceKh := by
  cases k <;> rfl

/-- The coherent system metric with the exact row coefficient required by
the paper-facing geometric array. -/
theorem stepDistance (C : ChosenChain H) (n k : ℕ) :
    dist (C.system.P n k) (C.system.P n (k + 1)) ≤
      TriangularMarkedPathSchemeVariableTerminal.rowC
          ActualStageProvider.paperP0 ActualStageProvider.paperP1
          ActualStageProvider.paperKhat ActualStageProvider.paperG1
          ActualStageProvider.paperCg n * H.error n k := by
  have hrow : 1 ≤
      TriangularMarkedPathSchemeVariableTerminal.rowC
        ActualStageProvider.paperP0 ActualStageProvider.paperP1
        ActualStageProvider.paperKhat ActualStageProvider.paperG1
        ActualStageProvider.paperCg n := by
    simpa [TriangularMarkedPathSchemeVariableTerminal.rowC] using
      (NormalPathC2IncrementVariableSpeed.one_le_c2ConstVar
        (ActualStageProvider.paperP0 n) (ActualStageProvider.paperP1 n)
        (ActualStageProvider.paperKhat n) (ActualStageProvider.paperG1 n)
        (ActualStageProvider.paperCg n))
  calc
    dist (C.system.P n k) (C.system.P n (k + 1)) ≤ H.error n k :=
      C.system.stepDistance n k
    _ = 1 * H.error n k := by simp
    _ ≤ TriangularMarkedPathSchemeVariableTerminal.rowC
          ActualStageProvider.paperP0 ActualStageProvider.paperP1
          ActualStageProvider.paperKhat ActualStageProvider.paperG1
          ActualStageProvider.paperCg n * H.error n k :=
      mul_le_mul_of_nonneg_right hrow (H.error_nonnegative n k)

/-- The complete paper-constant geometric array of the chosen chain. -/
noncomputable def array (C : ChosenChain H) :
    FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray.Array
      (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing)
      C.system.P H.error
      ActualStageProvider.paperP0 ActualStageProvider.paperP1
      ActualStageProvider.paperKhat ActualStageProvider.paperG1
      ActualStageProvider.paperCg
      (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.upper H.toClosing)
      (H.toClosing.data.Hs 0)
      (ConfiguredInductiveTubeBudget.chordBase H.toClosing.data.model / 2) where
  cell := cell C
  base := fun n => C.system.P_zero n
  error_nonnegative := H.error_nonnegative
  error_summable := H.error_summable
  tube :=
    ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainVariableTube.variableTube
      H C
  stepDistance := stepDistance C

@[simp] theorem array_cell (C : ChosenChain H) (n k : ℕ) :
    (array C).cell n k = cell C n k := rfl

/-- The exact geometric core expected by the multiplier paper capstone.  Its
presented grid is definitionally the coherent grid of `C.system`. -/
noncomputable def core (C : ChosenChain H) :
    ConfiguredRecursiveEdgeRecostMultiplierPaperCapstone.GeometricCore
      H.toClosing where
  Q := ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing
  P := C.system.P
  B0 := ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing
  C := ConfiguredRecursiveEdgeRecostMultiplierRowBudget.upper H.toClosing
  c := H.toClosing.data.Hs 0
  dlt := ConfiguredInductiveTubeBudget.chordBase H.toClosing.data.model / 2
  cell := cell C
  base := fun n => C.system.P_zero n
  tube :=
    ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainVariableTube.variableTube
      H C
  stepDistance := fun n k => C.system.stepDistance n k

@[simp] theorem core_Q (C : ChosenChain H) :
    (core C).Q =
      ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing := rfl

@[simp] theorem core_P (C : ChosenChain H) :
    (core C).P = C.system.P := rfl

@[simp] theorem core_B0 (C : ChosenChain H) :
    (core C).B0 =
      ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing := rfl

@[simp] theorem core_C (C : ChosenChain H) :
    (core C).C =
      ConfiguredRecursiveEdgeRecostMultiplierRowBudget.upper H.toClosing := rfl

@[simp] theorem core_c (C : ChosenChain H) :
    (core C).c = H.toClosing.data.Hs 0 := rfl

@[simp] theorem core_dlt (C : ChosenChain H) :
    (core C).dlt =
      ConfiguredInductiveTubeBudget.chordBase H.toClosing.data.model / 2 := rfl

@[simp] theorem core_cell (C : ChosenChain H) (n k : ℕ) :
    (core C).cell n k = cell C n k := rfl

end ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray
