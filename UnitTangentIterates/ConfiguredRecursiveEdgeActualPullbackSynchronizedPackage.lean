import UnitTangentIterates.ConfiguredRecursiveEdgeFinitePresentedPaperCapstone
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedCellAdapter

/-!
# Configured package for synchronized actual pullback rows

This is the final local adapter between the reachable synchronized recurrence
and the direct-stage paper capstone.  The caller supplies one synchronized
cell family; its cells and all configured physical `CellFacts` are then
derived together.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeFinitePresentedPaperCapstone

open ConfiguredCanonicalPairSource
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows
  VariableMarkedTube

namespace DirectStagePackage

variable {X : ScalarPackage physicalTransitionCeilings}
  {P0 kh khat Qmax : ℕ → ℕ → ℝ}
  {E C0 C1 C2 : ℕ → ℝ} {d : ℕ → ℕ → ℝ}

/-- Package configured synchronized rows and their local physical cell family
into the single input consumed by `paper_of_actual_stages`. -/
def ofConfiguredSynchronizedFamily
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d)
    (H : R.Ceilings
      (fun n k => ConfiguredRecursiveEdgeSourceP0Growth.edgeConversion X.gauge.data
        (analyticKhat X.gauge.data)
        ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
        ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0
        (publicIndex X n k))
      (fun n k => ConfiguredRecursiveEdgeSourceP0Growth.edgeEndpointConversion X.gauge.data
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
        X.jet.scalar.Mend
        (publicIndex X n k))
      (fun n k => ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect X.gauge.data
        (publicIndex X n k + 1)))
    (hE : ∀ n, E n = distortionTotal)
    (hC0 : ∀ n, C0 n = physicalTransitionCeilings.C0)
    (hC1 : ∀ n, C1 n = physicalTransitionCeilings.C1)
    (hC2 : ∀ n, C2 n = physicalTransitionCeilings.C2)
    (hd : ∀ n k, d n k = ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect X.gauge.data
      (publicIndex X n k + 1))
    (Q : ℕ → Data) (C : ℕ → ℝ)
    (hbase : ∀ n, R.P n 0 = Q n)
    (L :
      FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedCellAdapter.Family
        X.data R)
    (tube : ∀ n k, IsVariableTubeMember
      (commonC X.data) (C n) 0 (commonDlt X.data) (R.P n k))
    (hQ0 : Q 0 = X.jet.scalar.Q X.totalRowShift) :
    DirectStagePackage X := by
  let F := ActualStageProvider.ofConfiguredSynchronizedRows
    R H hE hC0 hC1 hC2 hd Q C hbase L.cell tube
  exact ofConfiguredSynchronizedRows R H hE hC0 hC1 hC2 hd Q C hbase
    L.cell tube
    (L.cellFacts F.array (by
      intro n k
      rfl))
    (by simpa [F] using hQ0)

end DirectStagePackage

end ConfiguredRecursiveEdgeFinitePresentedPaperCapstone
