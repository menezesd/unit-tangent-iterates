import UnitTangentIterates.ConfiguredRecursiveEdgeChosenMajorSplitHistory
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink

/-!
# Nonaffine chosen-row split histories

This is the marking-aware replacement for `ChosenMajorSplitHistory.ChosenLink`.
Successive rows are measured by `jacobianComponents source.phi1 Gamma.eta`;
no affine `SeparatedFacts` occurs.  The concrete row constructor proves the
stored transition using `transition_of_intrinsic_and_markingComparisons` and
the exact successor `P/phi1` identities retained by the two slices.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace MarkedTopology PathMetric

namespace ConfiguredRecursiveEdgeNonaffineChosenMajorSplitHistory

open AnchoredJacobiStableTransition
  ConfiguredRecursiveEdgeActualPhysicalSplitHistory
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTerminalScaling
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
  FiniteSmoothRearFamilyMarkingAwareSource

variable {MA NA Etotal Dtarget K0 K1 K2 : ℝ}
  {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  (O : Output RJ Etotal Dtarget)

/-- One exact nonaffine chosen row.  `rawTransition` is precisely the output
of the intrinsic transition sandwiched between the source and target marking
comparisons; retaining it here avoids any affine source assertion. -/
structure NonaffineChosenLink
    (V : ℕ → Components) (j : ℕ) where
  p : Data
  q : Data
  a : Data
  b : Data
  Gamma : NormalPath p q
  P0 : ℝ
  khat : ℝ
  Qmax : ℝ
  source : MarkingAwareSource Gamma P0
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khat Qmax
  applied : Applied Gamma source
  chosen : ChosenPath Gamma source applied.Phi a b
  sourceSlice : AnalyticSuccessorSliceFacts source
  P0Next : ℝ
  khatNext : ℝ
  QmaxNext : ℝ
  targetPath : NormalPath a b
  target : MarkingAwareSource targetPath P0Next
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh khatNext QmaxNext
  targetSlice : AnalyticSuccessorSliceFacts target
  target_eta_eq : targetPath.eta = chosen.Delta.eta
  target_period_eq : target.P = rearPeriod source
  target_phi1_eq : target.phi1 = chosen.phi1
  epsPrev : ℝ
  epsCur : ℝ
  sourceJets : SourceNormalizedJetBounds source epsPrev
  chosenJets : NormalizedJetBounds chosen epsCur
  epsPrev_le : epsPrev ≤ O.major j
  epsCur_le : epsCur ≤ O.major (j + 1)
  source_eq : V j = markedPhysicalComponents source.phi1 source.P Gamma.eta
  target_eq : V (j + 1) =
    markedPhysicalComponents target.phi1 target.P targetPath.eta
  rawTransition : Transition
    (markedPhysicalComponents source.phi1 source.P Gamma.eta)
    (markedPhysicalComponents target.phi1 target.P targetPath.eta)
    1 ((1 + epsCur) / (1 - epsPrev)) epsCur
    configuredC0 configuredC1 configuredC2

/-- A finite Jacobian-component ancestry.  The initial estimate is stated on
the actual nonaffine base component; it can be discharged from the configured
base slice without converting its marking to an affine one. -/
structure Ancestry
    {p q : Data} (Gamma : NormalPath p q) (depth : ℕ) (d : ℝ) where
  V : ℕ → Components
  baseJ : ℝ → ℝ → ℝ
  baseP : ℝ → ℝ
  baseEta : ℝ → ℝ → ℝ
  base_eq : V 0 = markedPhysicalComponents baseJ baseP baseEta
  d_nonnegative : 0 ≤ d
  components_nonnegative : ∀ j, j ≤ depth → (V j).Nonnegative
  initial_le : (V 0).w ≤ d ∧ (V 0).s0 ≤ d ∧
    (V 0).s1 ≤ d ∧ (V 0).s2 ≤ d
  links : ∀ j, j < depth → NonaffineChosenLink O V j

namespace Ancestry

variable {p q : Data} {Gamma : NormalPath p q} {depth : ℕ} {d : ℝ}

private theorem adjacent_le (hE : Etotal ≤ 1 / 8) (j : ℕ) :
    O.major j + O.major (j + 1) ≤ 1 / 4 := by
  have hcur : O.major j ≤ ∑' i, O.major i :=
    O.major_summable'.le_tsum j (fun i _ ↦ O.major_nonnegative' i)
  have hnext : O.major (j + 1) ≤ ∑' i, O.major i :=
    O.major_summable'.le_tsum (j + 1)
      (fun i _ ↦ O.major_nonnegative' i)
  nlinarith [O.major_tsum_le']

/-- Uniform scaling preserves every nonaffine transition.  It absorbs both
the normalized-to-unweighted base comparison and the terminal inverse-
Jacobian comparison in one scalar `L²`; those two endpoint comparisons are
the explicit `initial_le` and `terminal_le` premises. -/
def toScaledSplitHistory
    (H : Ancestry O Gamma depth d)
    (hE : Etotal ≤ 1 / 8) (L : ℝ)
    (terminal_le :
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).w ≤
          (scaleAll (L ^ 2) (H.V depth)).w ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s0 ≤
          (scaleAll (L ^ 2) (H.V depth)).s0 ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s1 ≤
          (scaleAll (L ^ 2) (H.V depth)).s1 ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s2 ≤
          (scaleAll (L ^ 2) (H.V depth)).s2) :
    SplitHistory Gamma (fun j ↦ scaleAll (L ^ 2) (H.V j)) O.major depth Etotal
      configuredC0 configuredC1 configuredC2 (L ^ 2 * d) where
  major_nonnegative := O.major_nonnegative'
  major_summable := O.major_summable'
  major_tsum_le := O.major_tsum_le'
  E_le := hE
  C0_nonnegative := configuredC0_nonnegative
  C1_nonnegative := configuredC1_nonnegative
  C2_nonnegative := configuredC2_nonnegative
  d_nonnegative := mul_nonneg (sq_nonneg L) H.d_nonnegative
  components_nonnegative := fun j hj ↦
    scaleAll_nonnegative (sq_nonneg L) (H.components_nonnegative j hj)
  initial_le := by
    change
      L ^ 2 * (H.V 0).w ≤ L ^ 2 * d ∧
      L ^ 2 * (H.V 0).s0 ≤ L ^ 2 * d ∧
      L ^ 2 * (H.V 0).s1 ≤ L ^ 2 * d ∧
      L ^ 2 * (H.V 0).s2 ≤ L ^ 2 * d
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact mul_le_mul_of_nonneg_left H.initial_le.1 (sq_nonneg L)
    · exact mul_le_mul_of_nonneg_left H.initial_le.2.1 (sq_nonneg L)
    · exact mul_le_mul_of_nonneg_left H.initial_le.2.2.1 (sq_nonneg L)
    · exact mul_le_mul_of_nonneg_left H.initial_le.2.2.2 (sq_nonneg L)
  link := by
    intro j hj
    let A := H.links j hj
    have hsource :
        (markedPhysicalComponents A.source.phi1 A.source.P
          A.Gamma.eta).Nonnegative := by
      rw [← A.source_eq]
      exact H.components_nonnegative j (Nat.le_of_lt hj)
    have HT := transition_to_pairedMajor
      hsource
      configuredC1_nonnegative configuredC2_nonnegative
      A.sourceJets.eps_nonnegative A.chosenJets.eps_nonnegative
      O.major_nonnegative' A.epsPrev_le A.epsCur_le (adjacent_le O hE j)
      A.rawTransition
    apply transition_scaleAll (c := L ^ 2) _ (sq_nonneg L)
    simpa [A.source_eq, A.target_eq] using HT
  terminal_le := terminal_le

end Ancestry

end ConfiguredRecursiveEdgeNonaffineChosenMajorSplitHistory
