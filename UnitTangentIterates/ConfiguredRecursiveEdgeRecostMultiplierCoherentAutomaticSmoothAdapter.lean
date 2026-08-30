import UnitTangentIterates.CoherentPhaseReachableMetricRangeAutomaticClosure
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPaperSmoothCapstone

/-!
# Coherent automatic rows as a configured smooth capstone input

`CoherentPhaseReachableMetricRange.System.P` is a two-index finite grid, while
the canonical capstone representative is limiting marked data.  Thus the
honest compatibility assertion identifies the row limit `X n` used by the
automatic-closure adapter with the canonical representative datum, rather
than identifying every finite `P n k` with that limit.
-/

noncomputable section

open MarkedSpace

namespace ConfiguredRecursiveEdgeRecostMultiplierCoherentAutomaticSmoothAdapter

open CoherentPhaseReachableMetricRange
  CoherentPhaseReachableMetricRangeAutomaticClosure
  ConfiguredRecursiveEdgeFinitePresentedPaperCapstone
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierPaperCapstone
  ConfiguredRecursiveEdgeRecostMultiplierPaperSmoothCapstone
  ConfiguredRecursiveEdgeRecostMultiplierRowBudget
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}
  {GO : GaugeOutput J} (R : RecostClosingOutput J GO)

/-- When the automatic coherent-grid input already uses the canonical
representative data as its row limits, assembly is definitionally direct. -/
def toSmoothPhysicalBaseInputExact
    (baseInput : PhysicalBaseInput R)
    (F : System (base R) R.error)
    (automatic :
      CoherentPhaseReachableMetricRangeAutomaticClosure.Input R baseInput F
        (fun n ↦ (representatives R baseInput n).q)) :
    SmoothPhysicalBaseInput R where
  base := baseInput
  fixedRows := automatic.toFixedRowInput

/-- Extensional version of `toSmoothPhysicalBaseInputExact`.  The equality
transport is stated explicitly because `FixedRowInput` is indexed by its two
limiting marked data. -/
def ofExtensionalLimits
    (baseInput : PhysicalBaseInput R)
    (F : System (base R) R.error)
    {X : ℕ → Data}
    (automatic :
      CoherentPhaseReachableMetricRangeAutomaticClosure.Input R baseInput F X)
    (limit_eq : ∀ n, X n = (representatives R baseInput n).q) :
    SmoothPhysicalBaseInput R where
  base := baseInput
  fixedRows := fun n ↦ by
    simpa only [limit_eq n, limit_eq (n + 1)] using
      automatic.toFixedRowInput n

/-- A single record packaging the final direct-branch constructor target. -/
structure Input where
  baseInput : PhysicalBaseInput R
  system : System (base R) R.error
  rowLimit : ℕ → Data
  automatic :
    CoherentPhaseReachableMetricRangeAutomaticClosure.Input R baseInput system
      rowLimit
  rowLimit_eq_representative : ∀ n,
    rowLimit n = (representatives R baseInput n).q

/-- Mechanical projection from coherent physical row data to the existing
smooth configured capstone input. -/
def Input.toSmoothPhysicalBaseInput (I : Input R) :
    SmoothPhysicalBaseInput R :=
  ofExtensionalLimits R I.baseInput I.system I.automatic
    I.rowLimit_eq_representative

/-- The strongest configured paper conclusion follows immediately after the
single coherent automatic input record has been built. -/
theorem Input.paperSmooth (I : Input R) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      Set.InjOn (Gamma 0) (Set.Ico 0 L) ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (Gamma n)) ∧
      (∀ n, Set.range (Gamma (n + 1)) =
        Set.range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (Set.range (Gamma 0)) L :=
  ConfiguredRecursiveEdgeRecostMultiplierPaperSmoothCapstone.paperSmooth R
    I.toSmoothPhysicalBaseInput

end ConfiguredRecursiveEdgeRecostMultiplierCoherentAutomaticSmoothAdapter
