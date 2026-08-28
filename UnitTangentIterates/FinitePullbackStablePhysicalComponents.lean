import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedArclengthTransition
import UnitTangentIterates.FiniteColumnStablePhysicalComponentCompactness
import UnitTangentIterates.CanonicalNormalPathRecost
import UnitTangentIterates.VariableArclengthScaledJacobiTransition
import UnitTangentIterates.NearIdentityDistortionBudget

/-!
# Stable physical components for finite pullback columns

The selected-inverse construction is only available through a prescribed
finite depth.  This module turns the row-local, arclength-scaled transition
at those finitely many depths into the uniform component certificate consumed
by finite-column compactness.  No infinite analytic recursion is assumed.

The finite component sequence is extended by zero after its terminal depth.
This harmless scalar extension permits direct use of
`AnchoredJacobiStableTransition.depth_uniform_components`; it does not extend
the geometric pullback construction.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric MarkedTopology
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed

namespace FinitePullbackStablePhysicalComponents

open AnchoredJacobiStableTransition
open ArclengthScaledJacobiTransition
open FiniteColumnStablePhysicalComponentCompactness

/-- The identity junction has zero total distortion in every channel. -/
def identityDistortionBudget :
    DistortionBudget (fun _ => 1) (fun _ => 1) (fun _ => 0) 0 0 0 where
  a_one := by simp
  MA_one := by simp
  NA_nonnegative := by simp
  Aw_nonnegative := le_rfl
  AM_nonnegative := le_rfl
  AN_nonnegative := le_rfl
  summable_a := by simpa using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  summable_MA := by simpa using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  summable_NA := summable_zero
  tsum_a_le := by simp
  tsum_MA_le := by simp
  tsum_NA_le := by simp

/-- Physical path components are nonnegative when the arclength scale is. -/
theorem physicalComponents_nonnegative {P : ℝ} (hP : 0 ≤ P)
    (eta : ℝ → ℝ → ℝ) : (physicalComponents P eta).Nonnegative := by
  have hW : 0 ≤ W eta 1 := by
    unfold W
    exact intervalIntegral.integral_nonneg (by norm_num) (fun t _ =>
      intervalIntegral.integral_nonneg (by norm_num) (fun u _ => abs_nonneg _))
  have hS : ∀ j : ℕ, 0 ≤ S j eta := by
    intro j
    unfold S
    exact intervalIntegral.integral_nonneg (by norm_num) (fun t _ => supNorm_nonneg _)
  exact
    { w := by simpa [physicalComponents] using mul_nonneg hP hW
      s0 := by simpa [physicalComponents] using hS 0
      s1 := by simpa [physicalComponents] using hS 1
      s2 := by simpa [physicalComponents] using hS 2 }

private def zeroComponents : Components :=
  { w := 0, s0 := 0, s1 := 0, s2 := 0 }

private theorem zeroComponents_nonnegative : zeroComponents.Nonnegative := by
  exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- A prescribed finite transition chain inherits the depth-uniform bound of
an arbitrary summable distortion budget.  No geometric object is asserted
beyond the terminal depth. -/
theorem depth_uniform_components_finite_of_budget
    {V : ℕ → Components} {a MA NA : ℕ → ℝ}
    {Aw AM AN C0 C1 C2 d : ℝ} (depth : ℕ)
    (B : DistortionBudget a MA NA Aw AM AN)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hd : 0 ≤ d)
    (hV : ∀ j, j ≤ depth → (V j).Nonnegative)
    (hinit : (V 0).w ≤ d ∧ (V 0).s0 ≤ d ∧
      (V 0).s1 ≤ d ∧ (V 0).s2 ≤ d)
    (hstep : ∀ j, j < depth →
      Transition (V j) (V (j + 1)) (a j) (MA j) (NA j) C0 C1 C2) :
    (V depth).w ≤ stableConst Aw AM AN C0 C1 C2 * d ∧
      (V depth).s0 ≤ stableConst Aw AM AN C0 C1 C2 * d ∧
      (V depth).s1 ≤ stableConst Aw AM AN C0 C1 C2 * d ∧
      (V depth).s2 ≤ stableConst Aw AM AN C0 C1 C2 * d := by
  let Vext : ℕ → Components := fun j ↦ if j ≤ depth then V j else zeroComponents
  have hVext : ∀ j, (Vext j).Nonnegative := by
    intro j
    by_cases hj : j ≤ depth
    · simpa [Vext, hj] using hV j hj
    · simpa [Vext, hj] using zeroComponents_nonnegative
  have hinitExt : (Vext 0).w ≤ d ∧ (Vext 0).s0 ≤ d ∧
      (Vext 0).s1 ≤ d ∧ (Vext 0).s2 ≤ d := by
    simpa [Vext] using hinit
  have hstepExt : ∀ j, Transition (Vext j) (Vext (j + 1))
      (a j) (MA j) (NA j) C0 C1 C2 := by
    intro j
    by_cases hj : j < depth
    · have hjle : j ≤ depth := Nat.le_of_lt hj
      have hjsle : j + 1 ≤ depth := Nat.succ_le_iff.mpr hj
      simpa [Vext, hjle, hjsle] using hstep j hj
    · have hdepth : depth ≤ j := Nat.le_of_not_gt hj
      by_cases heq : j = depth
      · subst j
        have hnext : ¬depth + 1 ≤ depth := by omega
        have H := hV depth le_rfl
        simp only [Vext, le_rfl, ↓reduceIte, hnext, zeroComponents]
        refine
          { w := mul_nonneg (B.a_nonnegative depth) H.w
            s0 := mul_nonneg hC0 H.w
            s1 := mul_nonneg
              (mul_nonneg (B.MA_nonnegative depth) hC1)
              (add_nonneg H.w H.s0)
            s2 := add_nonneg
              (mul_nonneg (mul_nonneg (sq_nonneg (MA depth)) hC2)
                (add_nonneg (add_nonneg H.w H.s0) H.s1))
              (mul_nonneg (mul_nonneg (B.NA_nonnegative depth) hC1)
                (add_nonneg H.w H.s0)) }
      · have hjnot : ¬j ≤ depth := by omega
        have hjsnot : ¬j + 1 ≤ depth := by omega
        simp only [Vext, hjnot, hjsnot, ↓reduceIte, zeroComponents]
        exact ⟨by simp, by simp, by simp, by simp⟩
  have H := depth_uniform_components B hC0 hC1 hC2 hd
    hVext hinitExt hstepExt depth
  simpa [Vext] using H

/-- A finite identity-junction transition chain has the same depth-uniform
bound as an infinite chain.  Only transitions strictly before `depth` are
required. -/
theorem depth_uniform_components_finite
    {V : ℕ → Components} {C0 C1 C2 d : ℝ} (depth : ℕ)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hd : 0 ≤ d)
    (hV : ∀ j, j ≤ depth → (V j).Nonnegative)
    (hinit : (V 0).w ≤ d ∧ (V 0).s0 ≤ d ∧
      (V 0).s1 ≤ d ∧ (V 0).s2 ≤ d)
    (hstep : ∀ j, j < depth →
      Transition (V j) (V (j + 1)) 1 1 0 C0 C1 C2) :
    (V depth).w ≤ stableConst 0 0 0 C0 C1 C2 * d ∧
      (V depth).s0 ≤ stableConst 0 0 0 C0 C1 C2 * d ∧
      (V depth).s1 ≤ stableConst 0 0 0 C0 C1 C2 * d ∧
      (V depth).s2 ≤ stableConst 0 0 0 C0 C1 C2 * d := by
  let Vext : ℕ → Components := fun j => if j ≤ depth then V j else zeroComponents
  have hVext : ∀ j, (Vext j).Nonnegative := by
    intro j
    by_cases hj : j ≤ depth
    · simpa [Vext, hj] using hV j hj
    · simpa [Vext, hj] using zeroComponents_nonnegative
  have hinitExt : (Vext 0).w ≤ d ∧ (Vext 0).s0 ≤ d ∧
      (Vext 0).s1 ≤ d ∧ (Vext 0).s2 ≤ d := by
    simpa [Vext] using hinit
  have hstepExt : ∀ j, Transition (Vext j) (Vext (j + 1))
      1 1 0 C0 C1 C2 := by
    intro j
    by_cases hj : j < depth
    · have hjle : j ≤ depth := Nat.le_of_lt hj
      have hjsle : j + 1 ≤ depth := Nat.succ_le_iff.mpr hj
      simpa [Vext, hjle, hjsle] using hstep j hj
    · have hdepth : depth ≤ j := Nat.le_of_not_gt hj
      by_cases heq : j = depth
      · subst j
        have hnext : ¬depth + 1 ≤ depth := by omega
        have hnonneg := hV depth le_rfl
        simp only [Vext, le_rfl, ↓reduceIte, hnext, zeroComponents]
        refine
          { w := by simpa using hnonneg.w
            s0 := by exact mul_nonneg hC0 hnonneg.w
            s1 := by
              simpa using mul_nonneg hC1 (add_nonneg hnonneg.w hnonneg.s0)
            s2 := by
              simpa using mul_nonneg hC2
                (add_nonneg (add_nonneg hnonneg.w hnonneg.s0) hnonneg.s1) }
      · have hjnot : ¬j ≤ depth := by omega
        have hjsnot : ¬j + 1 ≤ depth := by omega
        simp only [Vext, hjnot, hjsnot, ↓reduceIte, zeroComponents]
        exact ⟨by simp, by simp, by simp, by simp⟩
  have H := depth_uniform_components identityDistortionBudget
    hC0 hC1 hC2 hd hVext hinitExt hstepExt depth
  simpa [Vext] using H

/-- A finite variable-period selected-inverse chain with summable
near-identity junction jets gives the physical-component certificate consumed
by finite-column compactness. -/
def stablePhysicalComponentsOfFiniteVariableTransitions
    {p q : ℕ → Data} (Gamma : ∀ j, NormalPath (p j) (q j))
    (period : ℕ → ℝ → ℝ) {eps : ℕ → ℝ}
    {E C0 C1 C2 d : ℝ} (depth : ℕ)
    (heps0 : ∀ j, 0 ≤ eps j) (hepsHalf : ∀ j, eps j ≤ 1 / 2)
    (heps : Summable eps) (htsum : (∑' j, eps j) ≤ E)
    (hperiod0 : ∀ j, j ≤ depth → ∀ t ∈ Icc (0 : ℝ) 1,
      0 ≤ period j t)
    (hperiod1 : ∀ t ∈ Icc (0 : ℝ) 1, 1 ≤ period depth t)
    (hT : (Gamma depth).T = 1)
    (hC2path : C2NormalPathData (Gamma depth))
    (heta : Continuous (Function.uncurry (Gamma depth).eta))
    (heta1 : Continuous (Function.uncurry hC2path.eta1))
    (heta2 : Continuous (Function.uncurry hC2path.eta2))
    (hterminalFunctional :
      ControlledJunctionPathFunctionalBounds.FunctionalIntegrable
        (Gamma depth).eta)
    (hterminalPhysicalW : IntervalIntegrable
      (fun t ↦ period depth t *
        ∫ u in (0 : ℝ)..1, |(Gamma depth).eta t u|) volume 0 1)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hd : 0 ≤ d)
    (hinit :
      (VariableArclengthScaledJacobiTransition.physicalComponents
        (period 0) (Gamma 0).eta).w ≤ d ∧
      (VariableArclengthScaledJacobiTransition.physicalComponents
        (period 0) (Gamma 0).eta).s0 ≤ d ∧
      (VariableArclengthScaledJacobiTransition.physicalComponents
        (period 0) (Gamma 0).eta).s1 ≤ d ∧
      (VariableArclengthScaledJacobiTransition.physicalComponents
        (period 0) (Gamma 0).eta).s2 ≤ d)
    (hstep : ∀ j, j < depth → Transition
      (VariableArclengthScaledJacobiTransition.physicalComponents
        (period j) (Gamma j).eta)
      (VariableArclengthScaledJacobiTransition.physicalComponents
        (period (j + 1)) (Gamma (j + 1)).eta)
      (NearIdentityDistortionBudget.invLower eps j)
      (NearIdentityDistortionBudget.upper eps j) (eps j) C0 C1 C2) :
    StablePhysicalComponents
      (CanonicalNormalPathRecost.recost (Gamma depth)
        hC2path heta heta1 heta2)
      1 (stableConst (2 * E) E E C0 C1 C2) d := by
  let V : ℕ → Components := fun j ↦
    VariableArclengthScaledJacobiTransition.physicalComponents
      (period j) (Gamma j).eta
  let B := NearIdentityDistortionBudget.budget heps0 hepsHalf heps htsum
  have hV : ∀ j, j ≤ depth → (V j).Nonnegative := by
    intro j hj
    exact VariableArclengthScaledJacobiTransition.physicalComponents_nonnegative
      (hperiod0 j hj) _
  have H := depth_uniform_components_finite_of_budget depth B
    hC0 hC1 hC2 hd hV (by simpa [V] using hinit)
    (by intro j hj; simpa [V, B] using hstep j hj)
  have hW := VariableArclengthScaledJacobiTransition.W_le_physicalW
    hterminalFunctional.w hterminalPhysicalW hperiod1
  refine
    { cost_le_components := ?_
      w_le := ?_
      s0_le := ?_
      s1_le := ?_
      s2_le := ?_ }
  · simpa [physicalComponents] using
      CanonicalNormalPathRecost.cost_recost_le_markedComponents
        (Gamma depth) hT hC2path heta heta1 heta2
  · simpa [physicalComponents] using
      hW.trans (by simpa [V] using H.1)
  · simpa [physicalComponents,
      VariableArclengthScaledJacobiTransition.physicalComponents, V] using H.2.1
  · simpa [physicalComponents,
      VariableArclengthScaledJacobiTransition.physicalComponents, V] using H.2.2.1
  · simpa [physicalComponents,
      VariableArclengthScaledJacobiTransition.physicalComponents, V] using H.2.2.2

/-- A finite component chain can be converted to the compactness certificate
without requiring its `w` entry to have the old fixed-period definition.
This is the adapter used by the variable-period physical `W`: the terminal
comparison records that normalized `W,S0,S1,S2` are bounded by the terminal
intrinsic components. -/
def stablePhysicalComponentsOfFiniteChain
    {p q : Data} (Gamma : NormalPath p q)
    (hT : Gamma.T = 1) (hC2path : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2path.eta1))
    (heta2 : Continuous (Function.uncurry hC2path.eta2))
    {V : ℕ → Components} {C0 C1 C2 d : ℝ} (depth : ℕ)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hd : 0 ≤ d)
    (hV : ∀ j, j ≤ depth → (V j).Nonnegative)
    (hinit : (V 0).w ≤ d ∧ (V 0).s0 ≤ d ∧
      (V 0).s1 ≤ d ∧ (V 0).s2 ≤ d)
    (hstep : ∀ j, j < depth →
      Transition (V j) (V (j + 1)) 1 1 0 C0 C1 C2)
    (hterminal : (physicalComponents 1 Gamma.eta).w ≤ (V depth).w ∧
      (physicalComponents 1 Gamma.eta).s0 ≤ (V depth).s0 ∧
      (physicalComponents 1 Gamma.eta).s1 ≤ (V depth).s1 ∧
      (physicalComponents 1 Gamma.eta).s2 ≤ (V depth).s2) :
    StablePhysicalComponents
      (CanonicalNormalPathRecost.recost Gamma hC2path heta heta1 heta2)
      1 (stableConst 0 0 0 C0 C1 C2) d := by
  have H := depth_uniform_components_finite depth hC0 hC1 hC2 hd
    hV hinit hstep
  refine
    { cost_le_components := ?_
      w_le := ?_
      s0_le := ?_
      s1_le := ?_
      s2_le := ?_ }
  · simpa [physicalComponents] using
      CanonicalNormalPathRecost.cost_recost_le_markedComponents
        Gamma hT hC2path heta heta1 heta2
  · simpa using hterminal.1.trans H.1
  · simpa using hterminal.2.1.trans H.2.1
  · simpa using hterminal.2.2.1.trans H.2.2.1
  · simpa using hterminal.2.2.2.trans H.2.2.2

/-- Canonical recosting converts a finite arclength-transition chain into the
exact physical-component certificate required by the compactness theorem.
The returned path has the same endpoints and velocity field as `Gamma depth`.
-/
def stablePhysicalComponentsOfFiniteTransitions
    {p q : ℕ → Data} (Gamma : ∀ j, NormalPath (p j) (q j))
    (period : ℕ → ℝ) {C0 C1 C2 d : ℝ} (depth : ℕ)
    (hperiod : ∀ j, j ≤ depth → 1 ≤ period j)
    (hT : ∀ j, j ≤ depth → (Gamma j).T = 1)
    (hC2path : ∀ j, j ≤ depth → C2NormalPathData (Gamma j))
    (heta : ∀ j, j ≤ depth → Continuous (Function.uncurry (Gamma j).eta))
    (heta1 : ∀ j (hj : j ≤ depth),
      Continuous (Function.uncurry (hC2path j hj).eta1))
    (heta2 : ∀ j (hj : j ≤ depth),
      Continuous (Function.uncurry (hC2path j hj).eta2))
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hd : 0 ≤ d)
    (hinit : (physicalComponents (period 0) (Gamma 0).eta).w ≤ d ∧
      (physicalComponents (period 0) (Gamma 0).eta).s0 ≤ d ∧
      (physicalComponents (period 0) (Gamma 0).eta).s1 ≤ d ∧
      (physicalComponents (period 0) (Gamma 0).eta).s2 ≤ d)
    (hstep : ∀ j, j < depth →
      Transition
        (physicalComponents (period j) (Gamma j).eta)
        (physicalComponents (period (j + 1)) (Gamma (j + 1)).eta)
        1 1 0 C0 C1 C2) :
    StablePhysicalComponents
      (CanonicalNormalPathRecost.recost (Gamma depth)
        (hC2path depth le_rfl) (heta depth le_rfl)
        (heta1 depth le_rfl) (heta2 depth le_rfl))
      (period depth) (stableConst 0 0 0 C0 C1 C2) d := by
  let V : ℕ → Components := fun j => physicalComponents (period j) (Gamma j).eta
  have hV : ∀ j, j ≤ depth → (V j).Nonnegative := by
    intro j hj
    exact physicalComponents_nonnegative (zero_le_one.trans (hperiod j hj)) _
  have H := depth_uniform_components_finite depth hC0 hC1 hC2 hd hV hinit hstep
  refine
    { cost_le_components := ?_
      w_le := ?_
      s0_le := ?_
      s1_le := ?_
      s2_le := ?_ }
  · simpa [physicalComponents] using
      CanonicalNormalPathRecost.cost_recost_le_scaled_components
        (Gamma depth) (hT depth le_rfl) (hC2path depth le_rfl)
        (heta depth le_rfl) (heta1 depth le_rfl) (heta2 depth le_rfl)
        (hperiod depth le_rfl)
  · simpa [V] using H.1
  · simpa [V] using H.2.1
  · simpa [V] using H.2.2.1
  · simpa [V] using H.2.2.2

end FinitePullbackStablePhysicalComponents
