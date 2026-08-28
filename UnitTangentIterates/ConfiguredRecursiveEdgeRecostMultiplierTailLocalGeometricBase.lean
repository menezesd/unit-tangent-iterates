import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalGeometricBase
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierClosing
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedGeometricState

/-!
# Tail-local physical geometric base

The final multiplier construction only has estimates after `R.totalShift`.
This module therefore rebuilds the physical geometric column on the public
tail itself.  No theorem or successor input is requested on the discarded
rows.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase

open ConfiguredRecursiveEdgePhysicalGeometricBase
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostedGeometricState
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeSourceP0
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {K0 K1 K2 : ℝ}

abbrev MA := ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
abbrev NA := ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0

def row (R : RecostClosingOutput J O) (n : ℕ) : ℕ := R.totalShift + n

abbrev Q (R : RecostClosingOutput J O) (n : ℕ) : Data :=
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction.Q J.scalar (row R n)

abbrev current (R : RecostClosingOutput J O) (n : ℕ) : Data :=
  baseCurrent J (K0 := K0) (K1 := K1) (K2 := K2) (row R n)

abbrev error (R : RecostClosingOutput J O) (n k : ℕ) : ℝ :=
  ConfiguredRecursiveEdgePhysicalCompositionBase.compositionError J (row R n) k

abbrev P0 (R : RecostClosingOutput J O) (n : ℕ) : ℝ :=
  edgeSourceP0 (D J.scalar) (row R n)

abbrev P1 (R : RecostClosingOutput J O) (n : ℕ) : ℝ :=
  edgeP1 (D J.scalar) MA (row R n)

abbrev G1 (R : RecostClosingOutput J O) (n : ℕ) : ℝ :=
  edgeG1 (D J.scalar) MA NA (row R n)

abbrev Cg (R : RecostClosingOutput J O) (n : ℕ) : ℝ :=
  edgeCgWithKhat (D J.scalar) (pathKhat J.scalar) MA NA (row R n)

abbrev C (R : RecostClosingOutput J O) (n : ℕ) : ℝ :=
  rowC J.scalar (row R n)

abbrev Qmax (R : RecostClosingOutput J O) (n : ℕ) : ℝ :=
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction.Qmax J.scalar (row R n)

noncomputable def column (R : RecostClosingOutput J O) :
    GeometricCorrelatedColumn (Q R)
      (current (K0 := K0) (K1 := K1) (K2 := K2) R) (error R) 0
      (P0 R) (P1 R) (fun _ => pathKhat J.scalar) (G1 R) (Cg R) (C R)
      (ConfiguredCanonicalPairSource.commonC (D J.scalar))
      (ConfiguredCanonicalPairSource.commonDlt (D J.scalar))
      (fun n => ConfiguredRecursiveEdgeSourceP0CappedRowProduction.khRow (row R n))
      (Qmax R) := by
  let B := base J (K0 := K0) (K1 := K1) (K2 := K2)
  refine
    { pathStart := fun n => B.pathStart (row R n)
      pathEnd := fun n => B.pathEnd (row R n)
      path := fun n => B.path (row R n)
      source := fun n => B.source (row R n)
      initial := fun n => B.initial (row R n)
      initial_eq := ?_
      initial_range := ?_
      pathEndRange := ?_ }
  · intro n u
    simpa [B, row, khRow,
      Nat.add_assoc] using B.initial_eq (row R n) u
  · intro n
    simpa [B, row, khRow]
      using B.initial_range (row R n)
  · intro n
    simpa [B, row, khRow,
      Nat.add_assoc] using B.pathEndRange (row R n)

noncomputable def invariant (R : RecostClosingOutput J O) :
    GeometricCompositionInvariant (column (K0 := K0) (K1 := K1) (K2 := K2) R) := by
  let H := ConfiguredRecursiveEdgePhysicalGeometricBase.invariant J
    (K0 := K0) (K1 := K1) (K2 := K2)
  refine
    { slice := fun n => H.slice (row R n)
      periodUpper_le := fun n => H.periodUpper_le (row R n)
      rearCurvature_le := fun n t s => H.rearCurvature_le (row R n) t s
      frontPeriodScaleOne := fun n t => H.frontPeriodScaleOne (row R n) t
      spatial := fun n => by
        simpa [column, row] using H.spatial (row R n)
      sidecars := fun n => H.sidecars (row R n)
      terminalCurvature_nonnegative := fun n s =>
        H.terminalCurvature_nonnegative (row R n) s
      terminalRange := fun n => H.terminalRange (row R n)
      terminalFront_phase := fun n => H.terminalFront_phase (row R n)
      terminalFront_eq_phase := fun n => by
        simpa [column, row, Nat.add_assoc] using H.terminalFront_eq_phase (row R n)
      nextFront_zero := fun n => by
        simpa [column, row, Nat.add_assoc] using H.nextFront_zero (row R n)
      nextPeriod_zero := fun n => by
        simpa [column, row, Nat.add_assoc] using H.nextPeriod_zero (row R n)
      initialTube := fun n => H.initialTube (row R n)
      initialOrdinaryTube := fun n => H.initialOrdinaryTube (row R n)
      rearPeriod_zero_eq_initial_perim := fun n =>
        H.rearPeriod_zero_eq_initial_perim (row R n)
      initialRange := fun n => H.initialRange (row R n)
      pathEndRange := fun n => by
        simpa [column, row, Nat.add_assoc] using H.pathEndRange (row R n)
      source_cost_le := fun n => H.source_cost_le (row R n)
      composition_d1 := fun n t => H.composition_d1 (row R n) t
      composition_d2 := fun n t => H.composition_d2 (row R n) t }

noncomputable def state (R : RecostClosingOutput J O) :
    State (Q R) (error R) (P0 R) (P1 R) (G1 R) (Cg R) (C R) (Qmax R)
      (pathKhat J.scalar)
      (ConfiguredCanonicalPairSource.commonC (D J.scalar))
      (ConfiguredCanonicalPairSource.commonDlt (D J.scalar))
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh where
  current := current (K0 := K0) (K1 := K1) (K2 := K2) R
  depth := 0
  column := column (K0 := K0) (K1 := K1) (K2 := K2) R
  invariant := invariant (K0 := K0) (K1 := K1) (K2 := K2) R

@[simp] theorem state_displayed (R : RecostClosingOutput J O) (n : ℕ) :
    ((state (K0 := K0) (K1 := K1) (K2 := K2) R).stage n).displayed =
      ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar
        (R.totalShift + n) := rfl

end ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase
