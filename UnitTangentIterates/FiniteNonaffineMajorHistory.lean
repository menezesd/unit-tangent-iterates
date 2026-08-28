import UnitTangentIterates.FiniteHistoryMajorBudget
import UnitTangentIterates.ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints

/-! # Nonaffine histories over an explicit scalar major -/

noncomputable section

open Function Set MeasureTheory MarkedSpace MarkedTopology PathMetric

namespace FiniteNonaffineMajorHistory

open AnchoredJacobiStableTransition
  ConfiguredRecursiveEdgeActualPhysicalSplitHistory
  ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints
  FiniteHistoryMajorBudget
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTerminalScaling
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
  FiniteSmoothRearFamilyMarkingAwareSource

variable {Etotal : ℝ} (B : MajorBudget Etotal)

/-- One normalized nonaffine transition charged to an explicit major. -/
structure ChosenLink (V : ℕ → Components) (j : ℕ) where
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
  epsPrev_le : epsPrev ≤ B.major j
  epsCur_le : epsCur ≤ B.major (j + 1)
  source_eq : V j = markedPhysicalComponents source.phi1 source.P Gamma.eta
  target_eq : V (j + 1) =
    markedPhysicalComponents target.phi1 target.P targetPath.eta
  rawTransition : Transition
    (markedPhysicalComponents source.phi1 source.P Gamma.eta)
    (markedPhysicalComponents target.phi1 target.P targetPath.eta)
    1 ((1 + epsCur) / (1 - epsPrev)) epsCur
    configuredC0 configuredC1 configuredC2

/-- Finite forward ancestry over an arbitrary explicit major budget. -/
structure Ancestry {p q : Data} (Gamma : NormalPath p q)
    (depth : ℕ) (d : ℝ) where
  V : ℕ → Components
  baseJ : ℝ → ℝ → ℝ
  baseP : ℝ → ℝ
  baseEta : ℝ → ℝ → ℝ
  base_eq : V 0 = markedPhysicalComponents baseJ baseP baseEta
  d_nonnegative : 0 ≤ d
  components_nonnegative : ∀ j, j ≤ depth → (V j).Nonnegative
  initial_le : (V 0).w ≤ d ∧ (V 0).s0 ≤ d ∧
    (V 0).s1 ≤ d ∧ (V 0).s2 ≤ d
  links : ∀ j, j < depth → ChosenLink B V j

namespace Ancestry

variable {p q p' q' : Data} {Gamma : NormalPath p q}
  {Gamma' : NormalPath p' q'} {depth : ℕ} {d : ℝ}

def extendV (H : Ancestry B Gamma depth d) (target : Components) :
    ℕ → Components := fun i => if i ≤ depth then H.V i else target

@[simp] theorem extendV_of_le (H : Ancestry B Gamma depth d)
    (target : Components) {i : ℕ} (hi : i ≤ depth) :
    extendV B H target i = H.V i := by simp [extendV, hi]

@[simp] theorem extendV_succ (H : Ancestry B Gamma depth d)
    (target : Components) : extendV B H target (depth + 1) = target := by
  simp [extendV]

/-- Append the theorem-produced current-source to new-target link. -/
def snoc (H : Ancestry B Gamma depth d) (target : Components)
    (htarget : target.Nonnegative)
    (L : ChosenLink B (extendV B H target) depth) :
    Ancestry B Gamma' (depth + 1) d where
  V := extendV B H target
  baseJ := H.baseJ
  baseP := H.baseP
  baseEta := H.baseEta
  base_eq := by simpa using H.base_eq
  d_nonnegative := H.d_nonnegative
  components_nonnegative := by
    intro i hi
    by_cases hle : i ≤ depth
    · rw [extendV_of_le B H target hle]
      exact H.components_nonnegative i hle
    · have : i = depth + 1 := by omega
      subst i
      simpa using htarget
  initial_le := by simpa using H.initial_le
  links := by
    intro i hi
    by_cases hlt : i < depth
    · let A := H.links i hlt
      exact
        { A with
          source_eq := by
            rw [extendV_of_le B H target (Nat.le_of_lt hlt)]
            exact A.source_eq
          target_eq := by
            rw [extendV_of_le B H target (Nat.succ_le_of_lt hlt)]
            exact A.target_eq }
    · have : i = depth := by omega
      subst i
      exact L

private theorem adjacent_le (hE : Etotal ≤ 1 / 8) (j : ℕ) :
    B.major j + B.major (j + 1) ≤ 1 / 4 := by
  have hcur : B.major j ≤ ∑' i, B.major i :=
    B.summable.le_tsum j (fun i _ => B.nonnegative i)
  have hnext : B.major (j + 1) ≤ ∑' i, B.major i :=
    B.summable.le_tsum (j + 1) (fun i _ => B.nonnegative i)
  nlinarith [B.tsum_le]

/-- Project the explicit-major ancestry to the existing scaled split-history
compactness interface. -/
def toScaledSplitHistory
    (H : Ancestry B Gamma depth d) (hE : Etotal ≤ 1 / 8) (L : ℝ)
    (terminal_le :
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).w ≤
          (scaleAll (L ^ 2) (H.V depth)).w ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s0 ≤
          (scaleAll (L ^ 2) (H.V depth)).s0 ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s1 ≤
          (scaleAll (L ^ 2) (H.V depth)).s1 ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s2 ≤
          (scaleAll (L ^ 2) (H.V depth)).s2) :
    SplitHistory Gamma (fun j => scaleAll (L ^ 2) (H.V j)) B.major depth
      Etotal configuredC0 configuredC1 configuredC2 (L ^ 2 * d) where
  major_nonnegative := B.nonnegative
  major_summable := B.summable
  major_tsum_le := B.tsum_le
  E_le := hE
  C0_nonnegative := configuredC0_nonnegative
  C1_nonnegative := configuredC1_nonnegative
  C2_nonnegative := configuredC2_nonnegative
  d_nonnegative := mul_nonneg (sq_nonneg L) H.d_nonnegative
  components_nonnegative := fun j hj =>
    scaleAll_nonnegative (sq_nonneg L) (H.components_nonnegative j hj)
  initial_le := by
    change
      L ^ 2 * (H.V 0).w ≤ L ^ 2 * d ∧
      L ^ 2 * (H.V 0).s0 ≤ L ^ 2 * d ∧
      L ^ 2 * (H.V 0).s1 ≤ L ^ 2 * d ∧
      L ^ 2 * (H.V 0).s2 ≤ L ^ 2 * d
    exact ⟨mul_le_mul_of_nonneg_left H.initial_le.1 (sq_nonneg L),
      mul_le_mul_of_nonneg_left H.initial_le.2.1 (sq_nonneg L),
      mul_le_mul_of_nonneg_left H.initial_le.2.2.1 (sq_nonneg L),
      mul_le_mul_of_nonneg_left H.initial_le.2.2.2 (sq_nonneg L)⟩
  link := by
    intro j hj
    let A := H.links j hj
    have hsource : (markedPhysicalComponents A.source.phi1 A.source.P
        A.Gamma.eta).Nonnegative := by
      rw [← A.source_eq]
      exact H.components_nonnegative j (Nat.le_of_lt hj)
    have HT := transition_to_pairedMajor hsource configuredC1_nonnegative
      configuredC2_nonnegative A.sourceJets.eps_nonnegative
      A.chosenJets.eps_nonnegative B.nonnegative A.epsPrev_le A.epsCur_le
      (adjacent_le B hE j) A.rawTransition
    apply transition_scaleAll (c := L ^ 2) _ (sq_nonneg L)
    simpa [A.source_eq, A.target_eq] using HT
  terminal_le := terminal_le

end Ancestry

/-- Endpoint-identified explicit-major ancestry. -/
structure ConcreteAncestry {p q : Data} (Gamma : NormalPath p q)
    (depth : ℕ) (edgeDefect : ℝ) where
  ancestry : Ancestry B Gamma depth (2 * edgeDefect)
  terminalJ : ℝ → ℝ → ℝ
  terminalP : ℝ → ℝ
  terminal_eq : ancestry.V depth =
    markedPhysicalComponents terminalJ terminalP Gamma.eta

namespace ConcreteAncestry

variable {p q p' q' : Data} {Gamma : NormalPath p q}
  {Gamma' : NormalPath p' q'} {depth : ℕ} {edgeDefect : ℝ}

def snoc (H : ConcreteAncestry B Gamma depth edgeDefect)
    (J : ℝ → ℝ → ℝ) (P : ℝ → ℝ)
    (htarget : (markedPhysicalComponents J P Gamma'.eta).Nonnegative)
    (L : ChosenLink B
      (H.ancestry.extendV B (markedPhysicalComponents J P Gamma'.eta)) depth) :
    ConcreteAncestry B Gamma' (depth + 1) edgeDefect where
  ancestry := Ancestry.snoc B H.ancestry _ htarget L
  terminalJ := J
  terminalP := P
  terminal_eq := Ancestry.extendV_succ B H.ancestry _

def toScaledSplitHistory
    (H : ConcreteAncestry B Gamma depth edgeDefect)
    (hE : Etotal ≤ 1 / 8) (L : ℝ) (terminal_le :
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).w ≤
          (scaleAll (L ^ 2) (H.ancestry.V depth)).w ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s0 ≤
          (scaleAll (L ^ 2) (H.ancestry.V depth)).s0 ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s1 ≤
          (scaleAll (L ^ 2) (H.ancestry.V depth)).s1 ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s2 ≤
          (scaleAll (L ^ 2) (H.ancestry.V depth)).s2) :
    SplitHistory Gamma (fun j => scaleAll (L ^ 2) (H.ancestry.V j))
      B.major depth Etotal configuredC0 configuredC1 configuredC2
      (2 * L ^ 2 * edgeDefect) := by
  convert Ancestry.toScaledSplitHistory B H.ancestry hE L terminal_le using 1 <;>
    ring

/-- Chosen-path terminal comparison specialized to an explicit major. -/
def toScaledSplitHistoryOfChosen
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax eps : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    (H : ConcreteAncestry B W.Delta depth edgeDefect)
    (hJ : H.terminalJ = W.phi1)
    (hP : H.terminalP = rearPeriod A)
    (jets : NormalizedJetBounds W eps) (heps : eps ≤ 1 / 2)
    (hEtotal : Etotal ≤ 1 / 8) (L : ℝ)
    (hL : 1 ≤ L) (hL2 : 2 ≤ L ^ 2)
    (hP1 : ∀ t ∈ Icc (0 : ℝ) 1, 1 ≤ rearPeriod A t)
    (hPL : ∀ t ∈ Icc (0 : ℝ) 1, rearPeriod A t ≤ L)
    (F : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable W.Delta.eta)
    (heta : ∀ t, Continuous (W.Delta.eta t))
    (hjac : IntervalIntegrable
      (fun t => ∫ u in (0 : ℝ)..1,
        W.phi1 t u * |W.Delta.eta t u|) volume 0 1)
    (hPW : IntervalIntegrable
      (fun t => rearPeriod A t *
        ∫ u in (0 : ℝ)..1, |W.Delta.eta t u|) volume 0 1)
    (hS1P : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (W.Delta.eta t)) /
        rearPeriod A t) volume 0 1)
    (hS2P : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 2 (W.Delta.eta t)) /
        rearPeriod A t ^ 2) volume 0 1) :
    SplitHistory W.Delta (fun j => scaleAll (L ^ 2) (H.ancestry.V j))
      B.major depth Etotal configuredC0 configuredC1 configuredC2
      (L ^ 2 * (2 * edgeDefect)) := by
  have hterm :
      (ArclengthScaledJacobiTransition.physicalComponents 1 W.Delta.eta).w ≤
          (scaleAll (L ^ 2) (H.ancestry.V depth)).w ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 W.Delta.eta).s0 ≤
          (scaleAll (L ^ 2) (H.ancestry.V depth)).s0 ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 W.Delta.eta).s1 ≤
          (scaleAll (L ^ 2) (H.ancestry.V depth)).s1 ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 W.Delta.eta).s2 ≤
          (scaleAll (L ^ 2) (H.ancestry.V depth)).s2 := by
    rw [H.terminal_eq, hJ, hP]
    apply terminal_le_scaleAll_marked hL hL2 hP1 hPL
    · exact physicalW_le_two_jacobianPhysicalW_of_chosenJets
        W jets heps F heta hjac
    · exact F.w
    · exact hPW
    · exact F.s1
    · exact hS1P
    · exact F.s2
    · exact hS2P
  convert H.toScaledSplitHistory B hEtotal L hterm using 1 <;> ring

end ConcreteAncestry

end FiniteNonaffineMajorHistory
