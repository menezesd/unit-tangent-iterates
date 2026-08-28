import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorSourceMass
import UnitTangentIterates.ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant

/-!
# Source-mass invariant for finite correlated successors

This quantitative sidecar uses the concrete automatic-successor density
retained by `ExactSuccessorBundle`.  Compatibility alone deliberately does
not determine the successor density.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath

namespace FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction
  ConfiguredCombinedPhysicalDiagonalLargeSeparation

/-- The retained automatic density determines the successor source mass
exactly. -/
theorem exactSuccessorBundle_sourceMass_eq_cost_div_sqrt
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap khatNext QmaxNext : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} {W : ChosenPath Gamma A E.Phi a b}
    (X : FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower.ExactSuccessorBundle
      W (periodLower := periodLower) (kap := kap)
      (khatNext := khatNext) (QmaxNext := QmaxNext)) :
    sourceMass X.source = W.Delta.cost / Real.sqrt (1 - kap ^ 2) := by
  unfold sourceMass PathMetric.NormalPath.cost
  rw [X.density_eq]
  change (∫ t in (0 : ℝ)..W.Delta.T,
    W.Delta.m t / Real.sqrt (1 - kap ^ 2)) = _
  rw [intervalIntegral.integral_div]

/-- At the configured common curvature ceiling, a chosen-cost estimate
`4 * D * d` gives the successor-mass estimate `8 * D * d`. -/
theorem exactSuccessorBundle_sourceMass_le_eight_mul
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap khatNext QmaxNext D d : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} {W : ChosenPath Gamma A E.Phi a b}
    (X : FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower.ExactSuccessorBundle
      W (periodLower := periodLower) (kap := kap)
      (khatNext := khatNext) (QmaxNext := QmaxNext))
    (hkap : kap = sourceKh) (hcost : W.Delta.cost ≤ 4 * D * d) :
    sourceMass X.source ≤ 8 * D * d := by
  rw [exactSuccessorBundle_sourceMass_eq_cost_div_sqrt X, hkap, sourceKh_eq]
  have hsquare :
      (Real.sqrt (1 - (5 / 6 : ℝ) ^ 2)) ^ 2 = 1 - (5 / 6 : ℝ) ^ 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt0 : 0 ≤ Real.sqrt (1 - (5 / 6 : ℝ) ^ 2) := Real.sqrt_nonneg _
  have hsqrtHalf : (1 / 2 : ℝ) ≤ Real.sqrt (1 - (5 / 6 : ℝ) ^ 2) := by
    nlinarith
  have hsqrtPos : 0 < Real.sqrt (1 - (5 / 6 : ℝ) ^ 2) := by linarith
  have hcost0 : 0 ≤ W.Delta.cost := W.Delta.cost_nonneg
  rw [div_le_iff₀ hsqrtPos]
  nlinarith

/-- Rowwise source-mass invariant carried independently of the finite
column's endpoint and analytic data. -/
structure SourceMassInvariant
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    (S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax)
    (D : ℝ) (defect : ℕ → ℝ) : Prop where
  sourceMass_le : ∀ n, sourceMass (S.source n) ≤ D * defect n

/-- The concrete exact successor preserves the source-mass invariant with
the explicit factor-eight target. -/
theorem SuccessorBundles.nextSourceMassInvariant
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt D : ℝ}
    {defect : ℕ → ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {H : ReadyColumn S} {B : RowBounds H} (X : SuccessorBundles H B)
    (hkh : ∀ n, kh n = sourceKh)
    (hcost : ∀ n, (H.row (n + 1)).output.chosen.Delta.cost ≤
      4 * D * defect n) :
    SourceMassInvariant X.nextColumn (8 * D) defect := by
  constructor
  intro n
  have Hmass := exactSuccessorBundle_sourceMass_le_eight_mul
    (X.bundle n) (hkh n) (hcost n)
  simpa [SuccessorBundles.nextColumn, mul_assoc] using Hmass

/-- A configured source-mass invariant supplies exactly the mass hypothesis
of the genuine all-time gauge-error majorant. -/
theorem SourceMassInvariant.chosenJetError_le_major
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k j : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : FiniteColumn Q current e k P0 P1 khat G1 Cg C c dlt kh Qmax}
    {MA NA : ℝ}
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    {Etotal Dtarget : ℝ}
    (O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output
      J Etotal Dtarget)
    (I : SourceMassInvariant S Dtarget
      (ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.scaledSuccessorPhysicalDefect
        O.data))
    (hkh : kh j = sourceKh)
    (hperiod : rearPeriod (S.source j) 0 ≤
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.ellCap O.data (j + 1))
    (hfloor : 1 ≤
      FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds.rearPeriodFloor
        (P0 j) (kh j)) :
    FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear.chosenJetLinearConst
        (S.source j) J.scalar.Mend * sourceMass (S.source j) ≤ O.major j :=
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.chosenJetLinear_mul_sourceMass_le_major
    O j hkh hperiod hfloor (I.sourceMass_le j)

end FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn
