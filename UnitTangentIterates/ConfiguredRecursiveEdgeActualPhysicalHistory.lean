import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareNonaffineFiniteStability
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFullyPhysicalSplitTarget

/-!
# Finite physical-component history for an actual pullback stage

The canonical recost estimate uses the finite ancestry of a displayed stage,
not the auxiliary raw source mass.  This module packages exactly that
ancestry.  Each link consists of the two marking comparisons around the
intrinsic fully-physical transition.  The resulting chain feeds the existing
finite stability theorem and produces `StablePhysicalComponents` without a
new analytic axiom.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeActualPhysicalHistory

open AnchoredJacobiStableTransition
  FiniteColumnStablePhysicalComponentCompactness
  FiniteSmoothRearFamilyMarkingAwareNonaffineFiniteStability
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
  VariableArclengthScaledJacobiTransition

/-- One marked link in a finite physical-component ancestry. -/
structure PairedLink
    (source target : Components) (major : ℕ → ℝ) (j : ℕ)
    (C0 C1 C2 : ℝ) where
  intrinsicFront : Components
  intrinsicRear : Components
  epsPrev : ℝ
  epsCur : ℝ
  epsPrev_nonnegative : 0 ≤ epsPrev
  epsCur_nonnegative : 0 ≤ epsCur
  epsPrev_le : epsPrev ≤ major j
  epsCur_le : epsCur ≤ major (j + 1)
  adjacent_le : major j + major (j + 1) ≤ 1 / 4
  sourceComparison : SourceIntrinsicComparison source intrinsicFront
    (1 / (1 - epsPrev))
  intrinsicTransition : Transition intrinsicFront intrinsicRear
    1 1 0 C0 C1 C2
  targetComparison : TargetMarkingComparison intrinsicRear target
    (1 + epsCur) epsCur

namespace PairedLink

variable {source target : Components} {major : ℕ → ℝ} {j : ℕ}
  {C0 C1 C2 : ℝ}

/-- Convert one comparison package into the paired-major transition used by
finite compactness. -/
def toTransition
    (L : PairedLink source target major j C0 C1 C2)
    (hsource : source.Nonnegative)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hmajor0 : ∀ i, 0 ≤ major i) :
    Transition source target
      (NearIdentityDistortionBudget.invLower (pairedMajor major) j)
      (NearIdentityDistortionBudget.upper (pairedMajor major) j)
      (pairedMajor major j) C0 C1 C2 :=
  pairedTransition_of_rowComparisons hsource
    L.epsPrev_nonnegative L.epsCur_nonnegative hC0 hC1 hC2 hmajor0
    L.epsPrev_le L.epsCur_le L.adjacent_le L.sourceComparison
    L.intrinsicTransition L.targetComparison

/-- Build a paired link from the theorem-produced fully physical intrinsic
transition.  Only the two marking comparisons and their scalar error bounds
remain row-specific. -/
def ofFullyPhysical
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      Gamma P0 kh khat Qmax}
    (applied : FiniteSmoothRearFamilyMarkingAwareAppliedSource.Applied Gamma A)
    {source target : Components} {major : ℕ → ℝ} {j : ℕ}
    {epsPrev epsCur : ℝ}
    (hkh : 0 < kh)
    (separated :
      FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.SeparatedFacts
        A P1)
    (integrable :
      ControlledJunctionPathFunctionalBounds.FunctionalIntegrable Gamma.eta)
    (hepsPrev0 : 0 ≤ epsPrev) (hepsCur0 : 0 ≤ epsCur)
    (hprev : epsPrev ≤ major j)
    (hcur : epsCur ≤ major (j + 1))
    (hadjacent : major j + major (j + 1) ≤ 1 / 4)
    (HS : SourceIntrinsicComparison source
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        A.P Gamma.eta) (1 / (1 - epsPrev)))
    (HT : TargetMarkingComparison
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A)
        (FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A))
      target (1 + epsCur) epsCur) :
    PairedLink source target major j
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC0 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2 kh) where
  intrinsicFront :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
      A.P Gamma.eta
  intrinsicRear :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
      (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A)
      (FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A)
  epsPrev := epsPrev
  epsCur := epsCur
  epsPrev_nonnegative := hepsPrev0
  epsCur_nonnegative := hepsCur0
  epsPrev_le := hprev
  epsCur_le := hcur
  adjacent_le := hadjacent
  sourceComparison := HS
  intrinsicTransition :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings.fullyPhysicalTransition
      (E := applied) hkh separated integrable
  targetComparison := HT

/-- A fully physical history link has no incoming marking comparison: the
successor front is the chosen path density itself.  Only the outgoing fixed
terminal marking is compared, directly in the normalized physical
components. -/
def ofFullyPhysicalTarget
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      Gamma P0 kh khat Qmax}
    (applied : FiniteSmoothRearFamilyMarkingAwareAppliedSource.Applied Gamma A)
    {target : ℝ → ℝ → ℝ} {major : ℕ → ℝ} {j : ℕ} {eps : ℝ}
    (hkh : 0 < kh)
    (separated :
      FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.SeparatedFacts
        A P1)
    (frontIntegrable :
      ControlledJunctionPathFunctionalBounds.FunctionalIntegrable Gamma.eta)
    (targetSlices :
      FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison.TargetSlices
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A)
        (FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A)
        target (1 + eps) eps)
    (heps0 : 0 ≤ eps)
    (hprevious : 0 ≤ major j)
    (hcur : eps ≤ major (j + 1))
    (hadjacent : major j + major (j + 1) ≤ 1 / 4) :
    PairedLink
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        A.P Gamma.eta)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A) target)
      major j
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC0 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2 kh) where
  intrinsicFront :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
      A.P Gamma.eta
  intrinsicRear :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
      (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A)
      (FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity A)
  epsPrev := 0
  epsCur := eps
  epsPrev_nonnegative := le_rfl
  epsCur_nonnegative := heps0
  epsPrev_le := hprevious
  epsCur_le := hcur
  adjacent_le := hadjacent
  sourceComparison :=
    { w := le_rfl
      s0 := le_rfl
      s1 := by simp }
  intrinsicTransition :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings.fullyPhysicalTransition
      (E := applied) hkh separated frontIntegrable
  targetComparison := targetSlices.toTargetMarkingComparison

end PairedLink

/-- A chosen row produces the exact paired-major transition once its retained
normalized jet error is compared with the configured scalar major. -/
def pairedTransitionOfChosen
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      Gamma P0 kh khat Qmax}
    {Eap : FiniteSmoothRearFamilyMarkingAwareAppliedSource.Applied Gamma A}
    (W : FiniteSmoothRearFamilyMarkingAwareAppliedSource.ChosenPath
      Gamma A Eap.Phi a b)
    (hkh : 0 < kh)
    (S : FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.SeparatedFacts
      A P1)
    (F : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable Gamma.eta)
    {major : ℕ → ℝ} {j : ℕ} {eps : ℝ}
    (J : FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.NormalizedJetBounds
      W eps)
    (heps : eps < 1)
    (hfloor : 1 ≤
      FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds.rearPeriodFloor
        P0 kh)
    (hC1 : 0 ≤ FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1 kh)
    (hC2 : 0 ≤ FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2 kh)
    (ha : 1 / (1 - eps) ≤
      NearIdentityDistortionBudget.invLower (pairedMajor major) j)
    (hMA : 1 + eps ≤
      NearIdentityDistortionBudget.upper (pairedMajor major) j)
    (hNA : eps ≤ pairedMajor major j) :
    Transition
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        A.P Gamma.eta)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A)
        W.Delta.eta)
      (NearIdentityDistortionBudget.invLower (pairedMajor major) j)
      (NearIdentityDistortionBudget.upper (pairedMajor major) j)
      (pairedMajor major j)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC0 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2 kh) := by
  let C :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalSplitTarget.Comparison.ofChosen
      W hkh S F J heps hfloor
  have hfront :
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        A.P Gamma.eta).Nonnegative :=
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents_nonnegative
      (fun t _ => (A.period_pos t).le) Gamma.eta
  have hden : 0 < 1 - eps := by linarith
  have H := FiniteSmoothRearFamilyMarkingAwareFullyPhysicalSplitTarget.transition
    Eap hkh S F C (one_div_pos.mpr hden).le
      (by linarith [J.eps_nonnegative])
    J.eps_nonnegative hfront hC1 hC2
  exact FiniteSmoothRearFamilyMarkingAwareFullyPhysicalSplitTarget.transition_mono
    H hfront ha hMA hNA (one_div_pos.mpr hden).le
      (by linarith [J.eps_nonnegative]) hC1 hC2

/-- The paired-major scalar inequalities are automatic from nonnegativity,
the current jet bound, and the configured adjacent-major smallness. -/
def pairedTransitionOfChosenMajor
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      Gamma P0 kh khat Qmax}
    {Eap : FiniteSmoothRearFamilyMarkingAwareAppliedSource.Applied Gamma A}
    (W : FiniteSmoothRearFamilyMarkingAwareAppliedSource.ChosenPath
      Gamma A Eap.Phi a b)
    (hkh : 0 < kh)
    (S : FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.SeparatedFacts
      A P1)
    (F : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable Gamma.eta)
    {major : ℕ → ℝ} {j : ℕ} {eps : ℝ}
    (J : FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.NormalizedJetBounds
      W eps)
    (heps : eps < 1)
    (hfloor : 1 ≤
      FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds.rearPeriodFloor
        P0 kh)
    (hC1 : 0 ≤ FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1 kh)
    (hC2 : 0 ≤ FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2 kh)
    (hmajor0 : ∀ i, 0 ≤ major i)
    (hcur : eps ≤ major (j + 1))
    (hadjacent : major j + major (j + 1) ≤ 1 / 4) :
    Transition
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        A.P Gamma.eta)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A)
        W.Delta.eta)
      (NearIdentityDistortionBudget.invLower (pairedMajor major) j)
      (NearIdentityDistortionBudget.upper (pairedMajor major) j)
      (pairedMajor major j)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC0 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2 kh) := by
  have hmu0 : 0 ≤ pairedMajor major j := pairedMajor_nonnegative hmajor0 j
  have hmuHalf : pairedMajor major j ≤ 1 / 2 := by
    unfold pairedMajor
    linarith [hmajor0 j, hmajor0 (j + 1)]
  have hepsmu : eps ≤ pairedMajor major j := by
    unfold pairedMajor
    linarith [hmajor0 j, hmajor0 (j + 1)]
  have hdenE : 0 < 1 - eps := by linarith
  have hdenM : 0 < 1 - pairedMajor major j := by linarith
  apply pairedTransitionOfChosen W hkh S F J heps hfloor hC1 hC2
  · apply (div_le_div_iff₀ hdenE hdenM).2
    nlinarith
  · simp [NearIdentityDistortionBudget.upper]
    linarith
  · exact hepsmu

/-- The complete finite ancestry needed to bound one canonically recosted
path.  The initial and terminal fields are the only comparisons not attached
to an individual link. -/
structure History
    {p q : Data} (Gamma : NormalPath p q)
    (V : ℕ → Components) (major : ℕ → ℝ)
    (depth : ℕ) (E C0 C1 C2 d : ℝ) where
  major_nonnegative : ∀ j, 0 ≤ major j
  major_summable : Summable major
  major_tsum_le : (∑' j, major j) ≤ E
  E_le : E ≤ 1 / 8
  C0_nonnegative : 0 ≤ C0
  C1_nonnegative : 0 ≤ C1
  C2_nonnegative : 0 ≤ C2
  d_nonnegative : 0 ≤ d
  components_nonnegative : ∀ j, j ≤ depth → (V j).Nonnegative
  initial_le : (V 0).w ≤ d ∧ (V 0).s0 ≤ d ∧
    (V 0).s1 ≤ d ∧ (V 0).s2 ≤ d
  link : ∀ j, j < depth → PairedLink (V j) (V (j + 1)) major j C0 C1 C2
  terminal_le :
    (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).w ≤
        (V depth).w ∧
    (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s0 ≤
        (V depth).s0 ∧
    (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s1 ≤
        (V depth).s1 ∧
    (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s2 ≤
        (V depth).s2

namespace History

variable {p q : Data} {Gamma : NormalPath p q}
  {V : ℕ → Components} {major : ℕ → ℝ}
  {depth : ℕ} {E C0 C1 C2 d : ℝ}

/-- A finite ancestry gives exactly the stable physical-component certificate
required by an actual stage's canonical recost. -/
def toStable
    (H : History Gamma V major depth E C0 C1 C2 d)
    (hT : Gamma.T = 1) (hC2path : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2path.eta1))
    (heta2 : Continuous (Function.uncurry hC2path.eta2)) :
    StablePhysicalComponents
      (CanonicalNormalPathRecost.recost Gamma hC2path heta heta1 heta2) 1
      (ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
        E C0 C1 C2) d := by
  apply stablePhysicalComponents_of_pairedJacobianTransitions Gamma hT
    hC2path heta heta1 heta2 depth H.major_nonnegative H.major_summable
    H.major_tsum_le H.E_le H.C0_nonnegative H.C1_nonnegative
    H.C2_nonnegative H.d_nonnegative H.components_nonnegative H.initial_le
  · intro j hj
    exact (H.link j hj).toTransition
      (H.components_nonnegative j (Nat.le_of_lt hj))
      H.C0_nonnegative H.C1_nonnegative H.C2_nonnegative
      H.major_nonnegative
  · exact H.terminal_le

end History

end ConfiguredRecursiveEdgeActualPhysicalHistory
