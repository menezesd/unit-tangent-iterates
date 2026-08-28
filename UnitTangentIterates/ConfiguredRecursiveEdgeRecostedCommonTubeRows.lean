import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedDirectCapstoneCellSidecars

/-!
# Common-tube coherence for truthful recosted diagonal rows

The erased diagonal `Rows` interface does not retain the common variable tube
of its displayed representatives.  A reachable geometric composition
invariant does: its `initialTube` field is transported at every recursive
depth.  This module records an identification with that reachable grid and
derives the global tube family used by the capstone.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedCommonTubeRows

open ConfiguredCanonicalPairSource
  ConfiguredRecursiveEdgeRecostScaledPaperCapstone
  ConfiguredRecursiveEdgeRecostedConcreteCapstoneInput
  ConfiguredRecursiveEdgeRecostedDirectCapstoneAdapter
  ConfiguredRecursiveEdgeRecostedDirectCapstoneCellSidecars
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
  VariableMarkedTube

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}

/-- The common-tube and exact-base facts erased by the structural diagonal
row interface.  Use `ofGeometricConstructionCore` below rather than filling
the tube family cellwise. -/
structure CommonTubeRows (H : Grid J) where
  C : ℕ → ℝ
  tube : ∀ n k, IsVariableTubeMember
    (commonC (rowData J)) (C n) 0 (commonDlt (rowData J)) (H.P n k)

/-- A reachable geometric composition core supplies the full common tube at
every depth.  The only additional identification is equality of the erased
recost grid with its reachable `markedGrid`; no tube estimate is repeated. -/
def CommonTubeRows.ofGeometricConstructionCore
    {H : Grid J}
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ}
    (F : GeometricPresentedConstructionCore Q e P0 P1 khat G1 Cg C kh Qmax
      (commonC (rowData J)) (commonDlt (rowData J)))
    (hP : ∀ n k, H.P n k = F.markedGrid n k) :
    CommonTubeRows H where
  C := C
  tube := by
    intro n k
    rw [hP n k]
    exact (F.state k).invariant.initialTube n

namespace CommonTubeRows

/-- Construct the geometric assembly with its displayed variable tube
supplied by reachable invariant propagation. -/
def assembly
    {H : Grid J} (R : CommonTubeRows H)
    (B : BaseFacts H) (F : FrontFacts H) : Assembly J :=
  ConfiguredRecursiveEdgeRecostedDirectCapstoneCellSidecars.assembly
    H B F R.C R.tube

/-- Callback-free capstone input from reachable common-tube rows and the
already reduced cell sidecars. -/
def concreteInput
    {H : Grid J} (R : CommonTubeRows H)
    (B : BaseFacts H) (F : FrontFacts H)
    (closing : ConfiguredRecursiveEdgeRecostScaledPaperCapstoneBaseFacts.BaseFacts
      (R.assembly B F).core) :
    ConfiguredRecursiveEdgeRecostedConcreteCapstoneInput.Input J := by
  exact ConfiguredRecursiveEdgeRecostedDirectCapstoneCellSidecars.concreteInput
    H B F R.C R.tube closing

/-- The paper theorem after common-tube invariant propagation. -/
theorem paper
    {H : Grid J} (R : CommonTubeRows H)
    (B : BaseFacts H) (F : FrontFacts H)
    (closing : ConfiguredRecursiveEdgeRecostScaledPaperCapstoneBaseFacts.BaseFacts
      (R.assembly B F).core) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L :=
  (R.concreteInput B F closing).paper

end CommonTubeRows

end ConfiguredRecursiveEdgeRecostedCommonTubeRows
