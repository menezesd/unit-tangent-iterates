import UnitTangentIterates.ConfiguredRecursiveEdgeChosenMajorConfiguredPhysicalRow

/-! # Structural extension of exact chosen ancestry -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeChosenMajorAncestryExtension

open AnchoredJacobiStableTransition
  ConfiguredRecursiveEdgeChosenMajorSplitHistory
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareAppliedSource

variable {MA NA Etotal Dtarget K0 K1 K2 : ℝ}
  {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  {O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output RJ Etotal Dtarget}
  {p q p' q' : Data} {Gamma : NormalPath p q} {Gamma' : NormalPath p' q'}
  {n depth : ℕ}

/-- Append one exact chosen transition.  The terminal path parameter of an
ancestry is used only by its eventual terminal comparison, so it may change
to the newly reached row while the common component chain is retained. -/
def Ancestry.snoc
    (H : Ancestry (K0 := K0) (K1 := K1) (K2 := K2)
      O Gamma n depth)
    (L : ChosenLink O H.V depth) :
    Ancestry (K0 := K0) (K1 := K1) (K2 := K2)
      O Gamma' n (depth + 1) where
  V := H.V
  base_eq := H.base_eq
  links := by
    intro j hj
    by_cases hlt : j < depth
    · exact H.links j hlt
    · have hle : j ≤ depth := by omega
      have hge : depth ≤ j := Nat.le_of_not_gt hlt
      have : j = depth := Nat.le_antisymm hle hge
      subst j
      exact L

variable {j : ℕ}
  {S : Stage
    (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar))
    (fun _ ↦ ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
    (fun _ ↦ ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar))
    (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar)) j}
  {G : GeometricInput S}

variable
  {Ophys : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output RJ
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal Dtarget}

/-- Package the appended ancestry as the concrete terminal ancestry of a
new geometric row once the two structural endpoint identities are known. -/
def ConcreteAncestry.snoc
    (H : Ancestry (K0 := K0) (K1 := K1) (K2 := K2)
      Ophys Gamma n depth)
    (L : ChosenLink Ophys H.V depth)
    (hperiod : FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod L.source =
      FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod S.source)
    (heta : L.chosen.Delta.eta = G.output.chosen.Delta.eta) :
    ConfiguredRecursiveEdgeChosenMajorConfiguredPhysicalRow.ConcreteAncestry
      (K0 := K0) (K1 := K1) (K2 := K2) Ophys G n depth where
  ancestry := Ancestry.snoc H L
  last_period_eq := by
    change FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
      (if hlt : depth < depth then H.links depth hlt else L).source = _
    rw [dif_neg (Nat.lt_irrefl depth)]
    exact hperiod
  last_chosen_eta_eq := by
    change (if hlt : depth < depth then H.links depth hlt else L).chosen.Delta.eta = _
    rw [dif_neg (Nat.lt_irrefl depth)]
    exact heta

end ConfiguredRecursiveEdgeChosenMajorAncestryExtension
