import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierClosing

/-!
# Unconditional multiplier-recost scalar closing package

This module packages the scalar choices that precede the recursive grid.  It
contains no geometric or recursive input: the configured model epsilon gives
the row-jet output, the fixed distortion budget and physical transition
ceilings give the gauge output, and the multiplier closing theorem supplies
the final displayed-metric tail.
-/

noncomputable section

namespace ConfiguredRecursiveEdgeRecostMultiplierClosingExistence

open ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion

/-- The complete callback-free scalar/gauge/closing chain used by the final
recost construction. -/
structure ConcreteClosingPackage where
  jet : RowJetScalarOutput choice.MA0 choice.NA0
  gauge : GaugeOutput jet
  closing : RecostClosingOutput jet gauge

/-- All scalar choices, gauge tails, source-mass smallness, and the final full
displayed-metric closing tail exist without any recursive-grid input. -/
theorem exists_concreteClosingPackage :
    Nonempty ConcreteClosingPackage := by
  obtain ⟨J⟩ := exists_fixed_rowJetScalarOutput_of_eps
    modelEpsilon_pos modelEpsilon_le_tenth
  obtain ⟨O⟩ := exists_configuredOutput J
    (C0 := physicalTransitionCeilings.C0)
    (C1 := physicalTransitionCeilings.C1)
    (C2 := physicalTransitionCeilings.C2)
    distortionTotal_pos distortionTotal_le_eighth
  obtain ⟨R⟩ := exists_recostClosingOutput J O
  exact ⟨{
    jet := J
    gauge := O
    closing := R }⟩

/-- Canonical choice of the unconditional scalar closing package. -/
noncomputable def concreteClosingPackage : ConcreteClosingPackage :=
  Classical.choice exists_concreteClosingPackage

end ConfiguredRecursiveEdgeRecostMultiplierClosingExistence
