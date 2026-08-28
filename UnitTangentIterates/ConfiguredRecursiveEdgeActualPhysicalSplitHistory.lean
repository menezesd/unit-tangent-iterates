import UnitTangentIterates.ConfiguredRecursiveEdgeActualPhysicalHistory

/-!
# Split finite physical-component history

The actual chosen marking has independent inverse-lower, upper, and second
jet losses.  A `PairedLink` factors a transition through comparison records
whose target `W` channel is nonexpansive, so it cannot represent that split
loss.  This companion stores the already-composed paired transition directly.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeActualPhysicalSplitHistory

open AnchoredJacobiStableTransition
  ConfiguredRecursiveEdgeActualPhysicalHistory
  FiniteColumnStablePhysicalComponentCompactness
  FiniteSmoothRearFamilyMarkingAwareNonaffineFiniteStability
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW

/-- A finite ancestry whose links already include the split chosen-marking
distortion and have been weakened to the paired majorant. -/
structure SplitHistory
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
  link : ∀ j, j < depth →
    Transition (V j) (V (j + 1))
      (NearIdentityDistortionBudget.invLower (pairedMajor major) j)
      (NearIdentityDistortionBudget.upper (pairedMajor major) j)
      (pairedMajor major j) C0 C1 C2
  terminal_le :
    (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).w ≤
        (V depth).w ∧
    (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s0 ≤
        (V depth).s0 ∧
    (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s1 ≤
        (V depth).s1 ∧
    (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s2 ≤
        (V depth).s2

namespace SplitHistory

variable {p q : Data} {Gamma : NormalPath p q}
  {V : ℕ → Components} {major : ℕ → ℝ}
  {depth : ℕ} {E C0 C1 C2 d : ℝ}

/-- Every legacy factored history is also a direct split history. -/
def ofHistory
    (H : ConfiguredRecursiveEdgeActualPhysicalHistory.History
      Gamma V major depth E C0 C1 C2 d) :
    SplitHistory Gamma V major depth E C0 C1 C2 d where
  major_nonnegative := H.major_nonnegative
  major_summable := H.major_summable
  major_tsum_le := H.major_tsum_le
  E_le := H.E_le
  C0_nonnegative := H.C0_nonnegative
  C1_nonnegative := H.C1_nonnegative
  C2_nonnegative := H.C2_nonnegative
  d_nonnegative := H.d_nonnegative
  components_nonnegative := H.components_nonnegative
  initial_le := H.initial_le
  link := fun j hj => (H.link j hj).toTransition
    (H.components_nonnegative j (Nat.le_of_lt hj))
    H.C0_nonnegative H.C1_nonnegative H.C2_nonnegative
    H.major_nonnegative
  terminal_le := H.terminal_le

/-- A direct split history gives the same stable canonical recost certificate
as the older factored history. -/
def toStable
    (H : SplitHistory Gamma V major depth E C0 C1 C2 d)
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
  · exact H.link
  · exact H.terminal_le

end SplitHistory

end ConfiguredRecursiveEdgeActualPhysicalSplitHistory
