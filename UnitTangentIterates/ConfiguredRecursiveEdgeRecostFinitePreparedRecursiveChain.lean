import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedBaseGeometry
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedChosenChain

/-! # Unconditional recursive prepared chain

The theorem-produced base step starts an enriched positive-depth recursion.
For each depth, that recursion supplies both the reached layer and the prepared
step used to reach its successor.
-/

noncomputable section

namespace ConfiguredRecursiveEdgeRecostFinitePreparedRecursiveChain

open ConfiguredRecursiveEdgeRecostFiniteBasePreparedProvenance
  ConfiguredRecursiveEdgeRecostFiniteBasePreparedStep
  ConfiguredRecursiveEdgeRecostFiniteIntrinsicBaseLayer
  ConfiguredRecursiveEdgeRecostFinitePreparedBaseGeometry
  ConfiguredRecursiveEdgeRecostFinitePreparedChosenChain
  ConfiguredRecursiveEdgeRecostFinitePreparedGeometrySchema
  ConfiguredRecursiveEdgeRecostFinitePreparedProvenance
  ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}

/-- The enriched reachable layer at each strictly positive depth. -/
noncomputable def positive (H : Output R) {K0 K1 K2 : ℝ} :
    (r : ℕ) → EnrichedReachable H (r + 1)
  | 0 =>
      firstEnrichedReachable (K0 := K0) (K1 := K1) (K2 := K2) H
  | r + 1 =>
      (positive (K0 := K0) (K1 := K1) (K2 := K2) H r).stepData.next H

/-- The prepared reachable layer at every depth, including the physical base. -/
noncomputable def reachable (H : Output R) {K0 K1 K2 : ℝ} :
    (k : ℕ) → PreparedReachable H k
  | 0 => preparedBase (K0 := K0) (K1 := K1) (K2 := K2) H
  | k + 1 =>
      (positive (K0 := K0) (K1 := K1) (K2 := K2) H k).reachable

/-- The prepared step based at each recursively reached layer. -/
noncomputable def stepData (H : Output R) {K0 K1 K2 : ℝ} :
    (k : ℕ) → PreparedStepData H
      (reachable (K0 := K0) (K1 := K1) (K2 := K2) H k)
  | 0 => preparedStep (K0 := K0) (K1 := K1) (K2 := K2) H
  | k + 1 =>
      ((positive (K0 := K0) (K1 := K1) (K2 := K2) H k).stepData).data

/-- Geometric provenance at every recursively reached prepared layer. -/
noncomputable def geometry (H : Output R) {K0 K1 K2 : ℝ} :
    (k : ℕ) → PreparedGeometryProvenance H k
      (reachable (K0 := K0) (K1 := K1) (K2 := K2) H k)
  | 0 => preparedBaseGeometry (K0 := K0) (K1 := K1) (K2 := K2) H
  | k + 1 =>
      (positive (K0 := K0) (K1 := K1) (K2 := K2) H k).geometry

/-- Each recursively stored reachable layer is exactly the successor selected
by the preceding stored prepared step. -/
theorem successorReachable (H : Output R) {K0 K1 K2 : ℝ} :
    ∀ k,
      reachable (K0 := K0) (K1 := K1) (K2 := K2) H (k + 1) =
        (stepData (K0 := K0) (K1 := K1) (K2 := K2) H k).next H
  | 0 => rfl
  | k + 1 => rfl

/-- The unconditional arbitrary-depth chain generated from the prepared base. -/
noncomputable def chosenChain (H : Output R) {K0 K1 K2 : ℝ} : ChosenChain H where
  reachable := reachable (K0 := K0) (K1 := K1) (K2 := K2) H
  stepData := stepData (K0 := K0) (K1 := K1) (K2 := K2) H
  geometry := geometry (K0 := K0) (K1 := K1) (K2 := K2) H
  baseDisplayed :=
    preparedBase_displayed (K0 := K0) (K1 := K1) (K2 := K2) H
  successorReachable :=
    successorReachable (K0 := K0) (K1 := K1) (K2 := K2) H

theorem exists_chosenChain (H : Output R) {K0 K1 K2 : ℝ} :
    Nonempty (ChosenChain H) :=
  ⟨chosenChain (K0 := K0) (K1 := K1) (K2 := K2) H⟩

end ConfiguredRecursiveEdgeRecostFinitePreparedRecursiveChain
