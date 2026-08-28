import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
import UnitTangentIterates.ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
import UnitTangentIterates.FinitePullbackStablePhysicalComponents

/-!
# Finite stability for compatible nonaffine presented rows

This file is the finite-depth consumer of the coordinate-invariant Jacobian
components.  Consecutive rows are joined only after their exact successor
compatibility has supplied the source and target comparisons; no scalar-period
component transition is reused.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareNonaffineFiniteStability

open AnchoredJacobiStableTransition
  FiniteColumnStablePhysicalComponentCompactness
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
  VariableArclengthScaledJacobiTransition

/-- A compatible nonaffine row, enlarged directly to the paired majorant used
by a finite column.  `HS` and `HT` are the exact comparison records produced
from the predecessor and current chosen rows respectively. -/
def pairedTransition_of_rowComparisons
    {source intrinsicFront intrinsicRear target : Components}
    {major : ℕ → ℝ} {j : ℕ} {epsPrev epsCur C0 C1 C2 : ℝ}
    (hsource : source.Nonnegative)
    (hepsPrev0 : 0 ≤ epsPrev) (hepsCur0 : 0 ≤ epsCur)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hmajor0 : ∀ i, 0 ≤ major i)
    (hprev : epsPrev ≤ major j)
    (hcur : epsCur ≤ major (j + 1))
    (hadjacent : major j + major (j + 1) ≤ 1 / 4)
    (HS : SourceIntrinsicComparison source intrinsicFront
      (1 / (1 - epsPrev)))
    (Hraw : Transition intrinsicFront intrinsicRear 1 1 0 C0 C1 C2)
    (HT : TargetMarkingComparison intrinsicRear target (1 + epsCur) epsCur) :
    Transition source target
      (NearIdentityDistortionBudget.invLower (pairedMajor major) j)
      (NearIdentityDistortionBudget.upper (pairedMajor major) j)
      (pairedMajor major j) C0 C1 C2 := by
  have hprevQuarter : epsPrev ≤ 1 / 4 := by
    calc
      epsPrev ≤ major j := hprev
      _ ≤ major j + major (j + 1) :=
        le_add_of_nonneg_right (hmajor0 (j + 1))
      _ ≤ 1 / 4 := hadjacent
  have hden : 0 < 1 - epsPrev := by linarith
  have hinv : 1 ≤ 1 / (1 - epsPrev) := by
    rw [le_div_iff₀ hden]
    linarith
  have hupper : 0 ≤ 1 + epsCur := by linarith
  have H := transition_of_intrinsic_and_markingComparisons
    hsource hinv hupper hepsCur0 hC0 hC1 hC2 HS Hraw HT
  have H' : Transition source target 1
      ((1 + epsCur) / (1 - epsPrev)) epsCur C0 C1 C2 := by
    simpa [div_eq_mul_inv] using H
  exact transition_to_pairedMajor hsource hC1 hC2 hepsPrev0 hepsCur0
    hmajor0 hprev hcur hadjacent H'

/-- A finite chain of Jacobian components inherits the configured nonaffine
stable target.  The terminal comparison is deliberately explicit: in a
concrete correlated column it is discharged by the terminal period floor and
the exact Jacobian physical-W identity. -/
def stablePhysicalComponents_of_pairedJacobianTransitions
    {p q : Data} (Gamma : NormalPath p q)
    (hT : Gamma.T = 1) (hC2path : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2path.eta1))
    (heta2 : Continuous (Function.uncurry hC2path.eta2))
    {V : ℕ → Components} {major : ℕ → ℝ}
    {E C0 C1 C2 d : ℝ} (depth : ℕ)
    (hmajor0 : ∀ j, 0 ≤ major j)
    (hmajor : Summable major) (htsum : (∑' j, major j) ≤ E)
    (hE : E ≤ 1 / 8)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hd : 0 ≤ d)
    (hV : ∀ j, j ≤ depth → (V j).Nonnegative)
    (hinit : (V 0).w ≤ d ∧ (V 0).s0 ≤ d ∧
      (V 0).s1 ≤ d ∧ (V 0).s2 ≤ d)
    (hstep : ∀ j, j < depth → Transition (V j) (V (j + 1))
      (NearIdentityDistortionBudget.invLower (pairedMajor major) j)
      (NearIdentityDistortionBudget.upper (pairedMajor major) j)
      (pairedMajor major j) C0 C1 C2)
    (hterminal :
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).w ≤
          (V depth).w ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s0 ≤
          (V depth).s0 ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s1 ≤
          (V depth).s1 ∧
      (ArclengthScaledJacobiTransition.physicalComponents 1 Gamma.eta).s2 ≤
          (V depth).s2) :
    StablePhysicalComponents
      (CanonicalNormalPathRecost.recost Gamma hC2path heta heta1 heta2) 1
      (ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
        E C0 C1 C2) d := by
  let B := pairedNearIdentityBudget hmajor0 hmajor htsum hE
  have H := FinitePullbackStablePhysicalComponents.depth_uniform_components_finite_of_budget
    depth B hC0 hC1 hC2 hd hV hinit hstep
  refine
    { cost_le_components := ?_
      w_le := hterminal.1.trans ?_
      s0_le := hterminal.2.1.trans ?_
      s1_le := hterminal.2.2.1.trans ?_
      s2_le := hterminal.2.2.2.trans ?_ }
  · simpa [ArclengthScaledJacobiTransition.physicalComponents] using
      CanonicalNormalPathRecost.cost_recost_le_markedComponents
        Gamma hT hC2path heta heta1 heta2
  · simpa [ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget]
      using H.1
  · simpa [ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget]
      using H.2.1
  · simpa [ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget]
      using H.2.2.1
  · simpa [ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget]
      using H.2.2.2

/-- Unconditional cost output for the canonically recosted horizontal step. -/
theorem recost_cost_le_four_configuredTarget_mul
    {p q : Data} {Gamma : NormalPath p q}
    {E C0 C1 C2 d : ℝ}
    (hC2path : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2path.eta1))
    (heta2 : Continuous (Function.uncurry hC2path.eta2))
    (H : StablePhysicalComponents
      (CanonicalNormalPathRecost.recost Gamma hC2path heta heta1 heta2) 1
      (ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
        E C0 C1 C2) d) :
    (CanonicalNormalPathRecost.recost Gamma hC2path heta heta1 heta2).cost ≤
      4 * ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
        E C0 C1 C2 * d := by
  exact H.cost_le_four_mul

/-- An original presented path has the same configured cost bound once its
stored cost density is compared with the canonical recost.  This hypothesis
is necessary: `NormalPath.m` is otherwise an arbitrary majorizing density. -/
theorem cost_le_four_configuredTarget_mul
    {p q : Data} {Gamma : NormalPath p q}
    {E C0 C1 C2 d : ℝ}
    (hC2path : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2path.eta1))
    (heta2 : Continuous (Function.uncurry hC2path.eta2))
    (hcost : Gamma.cost ≤
      (CanonicalNormalPathRecost.recost Gamma hC2path heta heta1 heta2).cost)
    (H : StablePhysicalComponents
      (CanonicalNormalPathRecost.recost Gamma hC2path heta heta1 heta2) 1
      (ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
        E C0 C1 C2) d) :
    Gamma.cost ≤
      4 * ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
        E C0 C1 C2 * d :=
  hcost.trans H.cost_le_four_mul

end FiniteSmoothRearFamilyMarkingAwareNonaffineFiniteStability
