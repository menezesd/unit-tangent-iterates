import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenVariableTransitionLinear
import UnitTangentIterates.AnchoredJacobiStableTransitionMonotone
import UnitTangentIterates.NearIdentityDistortionBudget
import UnitTangentIterates.FinitePullbackStablePhysicalComponents

/-!
# Consecutive affine chosen-transition towers

This is the dependent finite-column interface between the row-local physical
Jacobi theorem and the stable-component induction.  It records the two exact
identifications that must not be replaced by range equalities: the chosen
rear path is the next lifted path, and its intrinsic rear period is the next
affine source period.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareAffineChosenTransitionTower

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTransitionLinear
  FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW
  FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction
  VariableArclengthScaledJacobiTransition

/-- An exact chain of affine-normalized theorem-produced chosen rows. -/
structure Tower
    (p q : ℕ → Data) (Gamma : ∀ j, NormalPath (p j) (q j))
    (P0 kh khat Qmax P1 M : ℝ) where
  source : ∀ j, MarkingAwareSource (Gamma j) P0 kh khat Qmax
  applied : ∀ j, Applied (Gamma j) (source j)
  chosen : ∀ j, ChosenPath (Gamma j) (source j) (applied j).Phi
    (p (j + 1)) (q (j + 1))
  separated : ∀ j, SeparatedFacts (source j) P1
  functional : ∀ j, FunctionalIntegrable (Gamma j).eta
  c2 : ∀ j, C2NormalPathData (Gamma j)
  eta_continuous : ∀ j, Continuous (Function.uncurry (Gamma j).eta)
  eta1_continuous : ∀ j, Continuous (Function.uncurry (c2 j).eta1)
  eta2_continuous : ∀ j, Continuous (Function.uncurry (c2 j).eta2)
  time_one : ∀ j, (Gamma j).T = 1
  sourceMass_le : ∀ j, sourceMass (source j) ≤ M
  chosen_eq_next : ∀ j, (chosen j).Delta = Gamma (j + 1)
  period_eq_next : ∀ j t,
    rearPeriod (source j) t = (source (j + 1)).P t

/-- The genuine all-time normalized marking error at one tower depth. -/
def Tower.eps
    {p q : ℕ → Data} {Gamma : ∀ j, NormalPath (p j) (q j)}
    {P0 kh khat Qmax P1 M : ℝ}
    (T : Tower p q Gamma P0 kh khat Qmax P1 M) (j : ℕ) : ℝ :=
  FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear.chosenJetLinearConst
      (T.source j) M * sourceMass (T.source j)

/-- Every consecutive pair in the tower carries the exact variable-period
stable transition. -/
def Tower.transition
    {p q : ℕ → Data} {Gamma : ∀ j, NormalPath (p j) (q j)}
    {P0 kh khat Qmax P1 M : ℝ}
    (T : Tower p q Gamma P0 kh khat Qmax P1 M) (j : ℕ)
    (hsmall : T.eps j < 1) :
    Transition
      (physicalComponents (T.source j).P (Gamma j).eta)
      (physicalComponents (T.source (j + 1)).P (Gamma (j + 1)).eta)
      (1 / (1 - T.eps j)) (1 + T.eps j) (T.eps j)
      (preGaugeC0 P0 P1 kh)
      (preGaugeC1 P0 P1 kh Qmax)
      (preGaugeC2 P0 P1 kh Qmax) := by
  have H := transition_of_flow_linear
    (T.chosen j) (T.separated j) (T.functional j) (T.time_one j)
    (T.sourceMass_le j) hsmall
  rw [T.chosen_eq_next j] at H
  have hperiod : rearPeriod (T.source j) = (T.source (j + 1)).P :=
    funext (T.period_eq_next j)
  rw [hperiod] at H
  simpa [Tower.eps] using H

/-- Enlarge the actual row distortion to a predeclared majorant.  This is the
noncircular bridge used by the finite induction: the majorant is chosen before
the resulting stable component constant. -/
def Tower.transitionMajor
    {p q : ℕ → Data} {Gamma : ∀ j, NormalPath (p j) (q j)}
    {P0 kh khat Qmax P1 M : ℝ}
    (T : Tower p q Gamma P0 kh khat Qmax P1 M) (j : ℕ)
    {major : ℕ → ℝ}
    (hle : T.eps j ≤ major j) (hhalf : major j ≤ 1 / 2) :
    Transition
      (physicalComponents (T.source j).P (Gamma j).eta)
      (physicalComponents (T.source (j + 1)).P (Gamma (j + 1)).eta)
      (NearIdentityDistortionBudget.invLower major j)
      (NearIdentityDistortionBudget.upper major j) (major j)
      (preGaugeC0 P0 P1 kh)
      (preGaugeC1 P0 P1 kh Qmax)
      (preGaugeC2 P0 P1 kh Qmax) := by
  let J := FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear.normalizedJetBounds_linear
    (T.chosen j) (T.separated j) (T.time_one j) (T.sourceMass_le j)
  have heps0 : 0 ≤ T.eps j := by simpa [Tower.eps] using J.eps_nonnegative
  have hsmall : T.eps j < 1 := lt_of_le_of_lt hle (hhalf.trans_lt (by norm_num))
  have H := T.transition j hsmall
  have hx := physicalComponents_nonnegative
    (fun t _ ↦ (T.source j).period_pos t |>.le) (Gamma j).eta
  have hcoef := preGaugeCoefficients_nonnegative (T.separated j)
  have hinv : 1 / (1 - T.eps j) ≤
      NearIdentityDistortionBudget.invLower major j := by
    apply one_div_le_one_div_of_le (by linarith)
    dsimp [NearIdentityDistortionBudget.invLower]
    linarith
  apply H.monoDistortion hx hcoef.2.1 hcoef.2.2 hinv
  · linarith
  · simpa [NearIdentityDistortionBudget.upper] using hle
  · exact hle

/-- A predeclared summable distortion majorant gives the terminal lifted path
uniform stable physical components at every finite depth. -/
def Tower.stableComponents
    {p q : ℕ → Data} {Gamma : ∀ j, NormalPath (p j) (q j)}
    {P0 kh khat Qmax P1 M : ℝ}
    (T : Tower p q Gamma P0 kh khat Qmax P1 M)
    (major : ℕ → ℝ) {E d : ℝ} (depth : ℕ)
    (hmajor0 : ∀ j, 0 ≤ major j)
    (hmajorHalf : ∀ j, major j ≤ 1 / 2)
    (hmajor : Summable major) (htsum : (∑' j, major j) ≤ E)
    (hactual : ∀ j, T.eps j ≤ major j)
    (hperiodOne : ∀ t ∈ Icc (0 : ℝ) 1, 1 ≤ (T.source depth).P t)
    (hC0 : 0 ≤ preGaugeC0 P0 P1 kh)
    (hC1 : 0 ≤ preGaugeC1 P0 P1 kh Qmax)
    (hC2 : 0 ≤ preGaugeC2 P0 P1 kh Qmax)
    (hd : 0 ≤ d)
    (hinit :
      (physicalComponents (T.source 0).P (Gamma 0).eta).w ≤ d ∧
      (physicalComponents (T.source 0).P (Gamma 0).eta).s0 ≤ d ∧
      (physicalComponents (T.source 0).P (Gamma 0).eta).s1 ≤ d ∧
      (physicalComponents (T.source 0).P (Gamma 0).eta).s2 ≤ d) :
    FiniteColumnStablePhysicalComponentCompactness.StablePhysicalComponents
      (CanonicalNormalPathRecost.recost (Gamma depth) (T.c2 depth)
        (T.eta_continuous depth) (T.eta1_continuous depth)
        (T.eta2_continuous depth)) 1
      (stableConst (2 * E) E E
        (preGaugeC0 P0 P1 kh)
        (preGaugeC1 P0 P1 kh Qmax)
        (preGaugeC2 P0 P1 kh Qmax)) d := by
  apply FinitePullbackStablePhysicalComponents.stablePhysicalComponentsOfFiniteVariableTransitions
    Gamma (fun j ↦ (T.source j).P) depth hmajor0 hmajorHalf hmajor htsum
  · intro j _ t _
    exact (T.source j).period_pos t |>.le
  · exact hperiodOne
  · exact T.time_one depth
  · exact T.functional depth
  · simpa [mul_comm] using
      (T.functional depth).w.mul_continuousOn
        (T.source depth).period_contDiff.continuous.continuousOn
  · exact hC0
  · exact hC1
  · exact hC2
  · exact hd
  · exact hinit
  · intro j _
    exact T.transitionMajor j (hactual j) (hmajorHalf j)

end FiniteSmoothRearFamilyMarkingAwareAffineChosenTransitionTower
