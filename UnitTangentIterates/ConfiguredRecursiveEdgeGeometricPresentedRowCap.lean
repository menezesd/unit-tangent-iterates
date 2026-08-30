import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareDirectCappedProvider

/-!
# Configured cap for a transition-free geometric presented row

This is the numerical cap adapter for the geometric recursion.  It retains
only scalar source/terminal ceilings and the shifted diagonal cost identity;
no transition certificate or recursive provider field is used.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeGeometricPresentedRowCap

open FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily
  InterpolationVariableSpeedSelInvAdapter
  ConstructedConfiguredInductiveTubeBudget.WeightedData

/-- Minimal configured scalar data which construct a geometric presented row
cap after shifting the large-separation sequence by `N`. -/
structure ConfiguredCapBounds
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C
      c dlt kh Qmax}
    (R : GeometricPresentedRowSelection (n := n) S)
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (diagonal : ℕ → ℝ) (N : ℕ) (M kh0 : ℝ) : Prop where
  kh_eq : kh n = kh0
  error_eq : e n (k + 1) =
    ExponentialDiagonalLargeSeparation.shiftSequence diagonal N
      (n + (k + 1))
  defect_lt_M :
    ExponentialDiagonalLargeSeparation.shiftSequence diagonal N
      (n + (k + 1)) < M
  Lmax_le : R.terminalInput.Lmax ≤
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.speedCap
      (shift D N) (n + 1)
  length_le : R.terminalInput.physical.L ≤
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.lengthCap
      (shift D N) (n + 1)
  kb_le : R.terminalInput.physical.kb ≤
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat (shift D N)
  kL_le : R.terminalInput.physical.kL ≤
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKd (shift D N)

/-- The configured source cost and physical terminal ceilings supply all
three fields of `GeometricPresentedRowCap`. -/
def ConfiguredCapBounds.rowCap
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C
      c dlt kh Qmax}
    {R : GeometricPresentedRowSelection (n := n) S}
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {diagonal : ℕ → ℝ} {N : ℕ} {M kh0 : ℝ}
    (H : ConfiguredCapBounds R D diagonal N M kh0) :
    GeometricPresentedRowCap R M
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.successorEndpointConversion
        (shift D N) kh0 M n)
      (ExponentialDiagonalLargeSeparation.shiftSequence diagonal N
        (n + (k + 1))) where
  cost_le_M := by
    have hcost : R.output.chosen.Delta.cost ≤ e n (k + 1) := by
      rw [R.output.chosen.cost_eq]
      exact R.terminalInput.cost_le
    calc
      R.output.chosen.Delta.cost ≤ e n (k + 1) := hcost
      _ = ExponentialDiagonalLargeSeparation.shiftSequence diagonal N
          (n + (k + 1)) := H.error_eq
      _ ≤ M := H.defect_lt_M.le
  coefficient_le := by
    let D' := shift D N
    have hQ0 : 0 ≤ R.terminalInput.Lmax :=
      (S.source n).rear_period_pos 0 |>.le.trans
        (R.terminalInput.rearPeriod_le 0)
    have hell0 : 0 ≤ rearPeriod (S.source n) 0 :=
      ((S.source n).rear_period_pos 0).le
    have hell : rearPeriod (S.source n) 0 ≤
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.ellCap D' (n + 1) := by
      apply (R.terminalInput.rearPeriod_le 0).trans
      simpa [D', ConfiguredCombinedPhysicalDiagonalLargeSeparation.ellCap,
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.speedCap] using H.Lmax_le
    have hkappa := rearKappa1_nonneg (S.source n).kh_nonnegative
      (S.source n).kh_lt_one
    have hkappa2 := rearKappa2_nonneg (S.source n).kh_nonnegative
      (S.source n).kh_lt_one
    have hcost : R.output.chosen.Delta.cost ≤
        ExponentialDiagonalLargeSeparation.shiftSequence diagonal N
          (n + (k + 1)) := by
      calc
        R.output.chosen.Delta.cost ≤ e n (k + 1) := by
          rw [R.output.chosen.cost_eq]
          exact R.terminalInput.cost_le
        _ = _ := H.error_eq
    have hM0 : 0 ≤ M :=
      R.output.chosen.Delta.cost_nonneg.trans
        (hcost.trans H.defect_lt_M.le)
    have hL0 : 0 ≤ R.terminalInput.physical.L := by
      rw [← R.terminalInput.physical.perim_eq]
      exact zero_le_one.trans R.terminal_perim_ge_one
    have hkb0 : 0 ≤ R.terminalInput.physical.kb :=
      (abs_nonneg (R.terminalInput.physical.curvature 0)).trans
        (R.terminalInput.physical.curvature_bound 0)
    have hkL0 : 0 ≤ R.terminalInput.physical.kL := by
      have HL := R.terminalInput.physical.curvature_lipschitz 0 1
      have H0 := (abs_nonneg
        (R.terminalInput.physical.curvature 0 -
          R.terminalInput.physical.curvature 1)).trans HL
      norm_num at H0
      exact H0
    have hmono :=
      FiniteSmoothRearFamilyMarkingAwareDirectCappedProvider.canonicalMarkingLinearConst_mono_fixed
        hQ0 H.Lmax_le hell0 hell hkappa hkappa2 hM0
        hL0 H.length_le hkb0 H.kb_le hkL0 H.kL_le
    simpa [ConfiguredCombinedPhysicalDiagonalLargeSeparation.successorEndpointConversion,
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.endpointConversion,
      ConfiguredGaugeEndpointLinearRadius.endpointLinearCoeff, H.kh_eq, D'] using hmono
  cost_le_defect := by
    calc
      R.output.chosen.Delta.cost ≤ e n (k + 1) := by
        rw [R.output.chosen.cost_eq]
        exact R.terminalInput.cost_le
      _ = ExponentialDiagonalLargeSeparation.shiftSequence diagonal N
          (n + (k + 1)) := H.error_eq

end ConfiguredRecursiveEdgeGeometricPresentedRowCap
