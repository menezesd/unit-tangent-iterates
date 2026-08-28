import UnitTangentIterates.ConfiguredRecursiveEdgeActualPhysicalSplitHistory
import UnitTangentIterates.ConfiguredRecursiveEdgeBaseFullyPhysicalComponentInitial
import UnitTangentIterates.ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTerminalScaling

/-! # Configured split history from exact chosen rows -/

noncomputable section

open Function Set MeasureTheory MarkedSpace MarkedTopology PathMetric

namespace ConfiguredRecursiveEdgeChosenMajorSplitHistory

open AnchoredJacobiStableTransition
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ControlledJunctionPathFunctionalBounds
  ConfiguredRecursiveEdgeActualPhysicalHistory
  ConfiguredRecursiveEdgeActualPhysicalSplitHistory
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeSourceP0Growth
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTerminalScaling
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
  FiniteSmoothRearFamilyMarkingAwareSource

variable {MA NA Etotal Dtarget K0 K1 K2 : ℝ}
  {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  (O : Output RJ Etotal Dtarget)

/-- One exact chosen row, identified with two consecutive members of the
common fully-physical component chain. -/
structure ChosenLink
    (V : ℕ → Components) (j : ℕ) where
  p : Data
  q : Data
  a : Data
  b : Data
  Gamma : NormalPath p q
  P0 : ℝ
  khat : ℝ
  Qmax : ℝ
  P1 : ℝ
  source : MarkingAwareSource Gamma P0 sourceKh khat Qmax
  applied : Applied Gamma source
  chosen : ChosenPath Gamma source applied.Phi a b
  separated :
    FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.SeparatedFacts
      source P1
  integrable :
    ControlledJunctionPathFunctionalBounds.FunctionalIntegrable Gamma.eta
  eps : ℝ
  jets : NormalizedJetBounds chosen eps
  periodFloor_one : 1 ≤ rearPeriodFloor P0 sourceKh
  eps_le_major : eps ≤ O.major (j + 1)
  source_eq : V j =
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
      source.P Gamma.eta
  target_eq : V (j + 1) =
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
      (rearPeriod source) chosen.Delta.eta

/-- A finite configured ancestry rooted at the actual fully-physical base
source.  Its endpoint comparison is kept explicit because it belongs to the
particular raw path whose recost is being bounded. -/
structure Ancestry
    {p q : Data} (Gamma : NormalPath p q)
    (n depth : ℕ) where
  V : ℕ → Components
  base_eq : V 0 =
    let B := ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated RJ
      (K0 := K0) (K1 := K1) (K2 := K2)
    let A := B.source n
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
      A.P (B.column.step.richStage (n + 1)).stage.increment.eta
  links : ∀ j, j < depth → ChosenLink O V j

namespace Ancestry

variable {p q : Data} {Gamma : NormalPath p q} {n depth : ℕ}

private theorem adjacent_le (hE : Etotal ≤ 1 / 8) (j : ℕ) :
    O.major j + O.major (j + 1) ≤ 1 / 4 := by
  have hcur : O.major j ≤ ∑' i, O.major i :=
    O.major_summable'.le_tsum j (fun i _ => O.major_nonnegative' i)
  have hnext : O.major (j + 1) ≤ ∑' i, O.major i :=
    O.major_summable'.le_tsum (j + 1) (fun i _ => O.major_nonnegative' i)
  nlinarith [O.major_tsum_le']

/-- Every exact row in the ancestry is nonnegative: the root uses the
configured source period, and each positive row is the fully physical rear
of its preceding exact chosen link. -/
theorem components_nonnegative
    (H : Ancestry (K0 := K0) (K1 := K1) (K2 := K2) O Gamma n depth) :
    ∀ j, j ≤ depth → (H.V j).Nonnegative := by
  intro j hj
  cases j with
  | zero =>
      let B := ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated RJ
        (K0 := K0) (K1 := K1) (K2 := K2)
      rw [H.base_eq]
      exact
        FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents_nonnegative
          (fun t _ => ((B.source n).period_pos t).le)
          (B.column.step.richStage (n + 1)).stage.increment.eta
  | succ j =>
      have hjlt : j < depth := Nat.lt_of_succ_le hj
      let A := H.links j hjlt
      rw [A.target_eq]
      exact
        FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents_nonnegative
          (fun t _ => (A.source.rear_period_pos t).le) A.chosen.Delta.eta

/-- Assemble the split history required by the canonical physical recost. -/
def toSplitHistory
    (H : Ancestry (K0 := K0) (K1 := K1) (K2 := K2) O Gamma n depth)
    (hE : Etotal ≤ 1 / 8)
    (hterminal :
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).w ≤
          (H.V depth).w ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s0 ≤
          (H.V depth).s0 ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s1 ≤
          (H.V depth).s1 ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s2 ≤
          (H.V depth).s2) :
    SplitHistory Gamma H.V O.major depth Etotal
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2
      (edgePhysicalDefect
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar)
        (n + 1)) where
  major_nonnegative := O.major_nonnegative'
  major_summable := O.major_summable'
  major_tsum_le := O.major_tsum_le'
  E_le := hE
  C0_nonnegative :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0_nonnegative
  C1_nonnegative :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1_nonnegative
  C2_nonnegative :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2_nonnegative
  d_nonnegative := edgePhysicalDefect_nonnegative
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) (n + 1)
  components_nonnegative := components_nonnegative O H
  initial_le := by
    rw [H.base_eq]
    exact
      ConfiguredRecursiveEdgeBaseFullyPhysicalComponentInitial.base_fullyPhysical_components_le_edgePhysicalDefect
        (K0 := K0) (K1 := K1) (K2 := K2) RJ n
  link := by
    intro j hj
    let L := H.links j hj
    have hterm : O.major (j + 1) ≤ ∑' i, O.major i :=
      O.major_summable'.le_tsum (j + 1) (fun i _ => O.major_nonnegative' i)
    have heps : L.eps < 1 := by
      have := L.eps_le_major.trans hterm
      linarith [O.major_tsum_le', hE]
    have hkh : 0 < sourceKh := by rw [sourceKh_eq]; norm_num
    have HT := pairedTransitionOfChosenMajor L.chosen hkh
      L.separated L.integrable L.jets heps L.periodFloor_one
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1_nonnegative
        hkh sourceKh_lt_one)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2_nonnegative
        hkh sourceKh_lt_one)
      O.major_nonnegative' L.eps_le_major (adjacent_le O hE j)
    simpa [L.source_eq, L.target_eq,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2] using HT
  terminal_le := hterminal

/-- Assemble a split history after uniformly scaling every component by
`L²`.  Transition constants remain unchanged, while the initial defect is
multiplied by exactly `L²`; the terminal comparison follows from
`1 ≤ P ≤ L`. -/
def toScaledSplitHistory
    (H : Ancestry (K0 := K0) (K1 := K1) (K2 := K2) O Gamma n depth)
    (hE : Etotal ≤ 1 / 8)
    (P : ℝ → ℝ) (L : ℝ)
    (hterminal : H.V depth =
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        P Gamma.eta)
    (hL : 1 ≤ L)
    (hP1 : ∀ t ∈ Icc (0 : ℝ) 1, 1 ≤ P t)
    (hPL : ∀ t ∈ Icc (0 : ℝ) 1, P t ≤ L)
    (hW : IntervalIntegrable
      (fun t ↦ ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) volume 0 1)
    (hPW : IntervalIntegrable
      (fun t ↦ P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) volume 0 1)
    (hS1 : IntervalIntegrable
      (fun t ↦ supNorm (iteratedDeriv 1 (Gamma.eta t))) volume 0 1)
    (hS1P : IntervalIntegrable
      (fun t ↦ supNorm (iteratedDeriv 1 (Gamma.eta t)) / P t) volume 0 1)
    (hS2 : IntervalIntegrable
      (fun t ↦ supNorm (iteratedDeriv 2 (Gamma.eta t))) volume 0 1)
    (hS2P : IntervalIntegrable
      (fun t ↦ supNorm (iteratedDeriv 2 (Gamma.eta t)) / P t ^ 2) volume 0 1) :
    SplitHistory Gamma (fun j ↦ scaleAll (L ^ 2) (H.V j)) O.major depth Etotal
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2
      (L ^ 2 * edgePhysicalDefect
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar)
        (n + 1)) where
  major_nonnegative := O.major_nonnegative'
  major_summable := O.major_summable'
  major_tsum_le := O.major_tsum_le'
  E_le := hE
  C0_nonnegative :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0_nonnegative
  C1_nonnegative :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1_nonnegative
  C2_nonnegative :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2_nonnegative
  d_nonnegative := mul_nonneg (sq_nonneg L)
    (edgePhysicalDefect_nonnegative
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) (n + 1))
  components_nonnegative := fun j hj =>
    scaleAll_nonnegative (sq_nonneg L) (components_nonnegative O H j hj)
  initial_le := by
    change
      (scaleAll (L ^ 2) (H.V 0)).w ≤
          L ^ 2 * edgePhysicalDefect
            (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) (n + 1) ∧
      (scaleAll (L ^ 2) (H.V 0)).s0 ≤
          L ^ 2 * edgePhysicalDefect
            (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) (n + 1) ∧
      (scaleAll (L ^ 2) (H.V 0)).s1 ≤
          L ^ 2 * edgePhysicalDefect
            (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) (n + 1) ∧
      (scaleAll (L ^ 2) (H.V 0)).s2 ≤
          L ^ 2 * edgePhysicalDefect
            (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) (n + 1)
    rw [H.base_eq]
    have HB :=
      ConfiguredRecursiveEdgeBaseFullyPhysicalComponentInitial.base_fullyPhysical_components_le_edgePhysicalDefect
        (K0 := K0) (K1 := K1) (K2 := K2) RJ n
    dsimp only at HB ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact mul_le_mul_of_nonneg_left HB.1 (sq_nonneg L)
    · exact mul_le_mul_of_nonneg_left HB.2.1 (sq_nonneg L)
    · exact mul_le_mul_of_nonneg_left HB.2.2.1 (sq_nonneg L)
    · exact mul_le_mul_of_nonneg_left HB.2.2.2 (sq_nonneg L)
  link := by
    intro j hj
    let A := H.links j hj
    have hterm : O.major (j + 1) ≤ ∑' i, O.major i :=
      O.major_summable'.le_tsum (j + 1) (fun i _ => O.major_nonnegative' i)
    have heps : A.eps < 1 := by
      have := A.eps_le_major.trans hterm
      linarith [O.major_tsum_le', hE]
    have hkh : 0 < sourceKh := by rw [sourceKh_eq]; norm_num
    have HT := pairedTransitionOfChosenMajor A.chosen hkh
      A.separated A.integrable A.jets heps A.periodFloor_one
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1_nonnegative
        hkh sourceKh_lt_one)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2_nonnegative
        hkh sourceKh_lt_one)
      O.major_nonnegative' A.eps_le_major (adjacent_le O hE j)
    apply transition_scaleAll (c := L ^ 2) _ (sq_nonneg L)
    simpa [A.source_eq, A.target_eq,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC0,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC1,
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.configuredC2] using HT
  terminal_le := by
    rw [hterminal]
    exact terminal_le_scaleAll hL hP1 hPL hW hPW hS1 hS1P hS2 hS2P

end Ancestry

end ConfiguredRecursiveEdgeChosenMajorSplitHistory
