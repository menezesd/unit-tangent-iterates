import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalCompositionBase

/-!
# Configured base physical-component initial bound

The ordinary configured base column already carries the unamplified physical
component diagonal.  This file exposes that certificate in the conjunction
shape consumed by finite stable-component chains.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeBasePhysicalComponentInitial

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgePhysicalCompositionBase
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  EnrichedPhysicalChosenRichFamily
  PhysicalArclengthJacobiTransition

variable {MA NA K0 K1 K2 : ℝ}

/-- The base path at diagonal `q` starts the physical chain inside the exact
public defect `edgePhysicalDefect D q`.  In a synchronized cell this is used
with `q = n + k + 1`. -/
theorem base_components_le_edgePhysicalDefect
    (J : RowJetScalarOutput MA NA) (q : ℕ) :
    let B := baseCorrelated J (K0 := K0) (K1 := K1) (K2 := K2)
    let V := components (period J.scalar q 0)
      (B.column.step.richStage q).stage.increment.eta
    V.w ≤ edgePhysicalDefect (D J.scalar) q ∧
      V.s0 ≤ edgePhysicalDefect (D J.scalar) q ∧
      V.s1 ≤ edgePhysicalDefect (D J.scalar) q ∧
      V.s2 ≤ edgePhysicalDefect (D J.scalar) q := by
  dsimp only
  have H := (baseCorrelated J (K0 := K0) (K1 := K1)
    (K2 := K2)).column.components_bound q
  simpa [edgePhysicalDefect,
    ConfiguredEnrichedConstructionCoreProvider.diagonal] using
    And.intro H.w (And.intro H.s0 (And.intro H.s1 H.s2))

end ConfiguredRecursiveEdgeBasePhysicalComponentInitial
