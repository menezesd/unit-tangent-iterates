import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareDirectSuccessor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareConfiguredTransition
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCappedProvider
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenTerminalCap
import UnitTangentIterates.ConfiguredCombinedPhysicalDiagonalLargeSeparation
import UnitTangentIterates.ConfiguredPolynomialDiagonalStableRowDefectProvider

/-!
# Concrete capped providers from actual chosen terminal rows

The terminal output supplies the endpoint estimate, while its terminal input
supplies curvature nonnegativity of the retained ordinary base.  Only the
three numerical comparisons needed to weaken the exact endpoint estimate to
a configured row cap remain as provider data.
-/

noncomputable section

open MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareDirectCappedProvider

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCappedProvider
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareConfiguredTransition
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareDirectSuccessor
  FiniteSmoothRearFamilyMarkingAwarePhysicalCore
  GaugeMarkedDataOfRearFamily
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- Monotonicity of the canonical endpoint coefficient in its geometric
period, speed, length, curvature, and curvature-Lipschitz inputs when the
rear curvature constants and cost cap are fixed. -/
theorem canonicalMarkingLinearConst_mono_fixed
    {Q Q' ell ell' kappa kappa2 M L L' kb kb' kL kL' : ℝ}
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ Q')
    (hell0 : 0 ≤ ell) (hell : ell ≤ ell')
    (hkappa : 0 ≤ kappa) (hkappa2 : 0 ≤ kappa2) (hM : 0 ≤ M)
    (hL0 : 0 ≤ L) (hL : L ≤ L')
    (hkb0 : 0 ≤ kb) (hkb : kb ≤ kb')
    (hkL0 : 0 ≤ kL) (hkL : kL ≤ kL') :
    InterpolationVariableSpeedSelInvAdapter.canonicalMarkingLinearConst
      Q ell kappa kappa2 M L kb kL ≤
    InterpolationVariableSpeedSelInvAdapter.canonicalMarkingLinearConst
      Q' ell' kappa kappa2 M L' kb' kL' := by
  let A := 2 * Q * kappa
  let A' := 2 * Q' * kappa
  let B := ell * kappa * (Real.exp (kappa * M) + 1)
  let B' := ell' * kappa * (Real.exp (kappa * M) + 1)
  let D := ell ^ 2 * Real.exp (2 * kappa * M) * kappa2
  let D' := ell' ^ 2 * Real.exp (2 * kappa * M) * kappa2
  have hQ'0 : 0 ≤ Q' := hQ0.trans hQ
  have hell'0 : 0 ≤ ell' := hell0.trans hell
  have hL'0 : 0 ≤ L' := hL0.trans hL
  have hkb'0 : 0 ≤ kb' := hkb0.trans hkb
  have hkL'0 : 0 ≤ kL' := hkL0.trans hkL
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA'0 : 0 ≤ A' := by dsimp [A']; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB'0 : 0 ≤ B' := by dsimp [B']; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hA : A ≤ A' := by dsimp [A, A']; gcongr
  have hB : B ≤ B' := by dsimp [B, B']; gcongr
  have hD : D ≤ D' := by
    dsimp [D, D']
    have hs : ell ^ 2 ≤ ell' ^ 2 := (sq_le_sq₀ hell0 hell'0).2 hell
    gcongr
  have hinner : 2 * L + B * M ≤ 2 * L' + B' * M := by
    exact add_le_add (mul_le_mul_of_nonneg_left hL (by norm_num))
      (mul_le_mul_of_nonneg_right hB hM)
  have hsecond : B + L * kb * A ≤ B' + L' * kb' * A' := by
    apply add_le_add hB
    gcongr
  have hthird :
      D + kb * B * (2 * L + B * M) + L ^ 2 * (kL + kb ^ 2) * A ≤
      D' + kb' * B' * (2 * L' + B' * M) +
        L' ^ 2 * (kL' + kb' ^ 2) * A' := by
    apply add_le_add
    · exact add_le_add hD (by gcongr)
    · have hLs : L ^ 2 ≤ L' ^ 2 := (sq_le_sq₀ hL0 hL'0).2 hL
      have hkbs : kb ^ 2 ≤ kb' ^ 2 := (sq_le_sq₀ hkb0 hkb'0).2 hkb
      gcongr
  simpa [InterpolationVariableSpeedSelInvAdapter.canonicalMarkingLinearConst,
    A, A', B, B', D, D'] using max_le_max hA (max_le_max hsecond hthird)

/-- The exact residual numerical cap data for one actual chosen row. -/
structure RowCap
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : ChosenRow (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S)
    (M endpoint diagonal' : ℝ) : Prop where
  cost_le_M : R.output.chosen.Delta.cost ≤ M
  coefficient_le :
    InterpolationVariableSpeedSelInvAdapter.canonicalMarkingLinearConst
      R.terminalInput.Lmax (rearPeriod (S.source n) 0)
      (rearKappa1 (kh n)) (rearKappa2 (kh n)) M
      R.terminalInput.physical.L R.terminalInput.physical.kb
      R.terminalInput.physical.kL ≤ endpoint
  cost_le_diagonal : R.output.chosen.Delta.cost ≤ diagonal'

theorem ChosenRow.endpoint_dist_le_cap
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {R : ChosenRow (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S}
    {M endpoint diagonal' : ℝ} (hM : 0 ≤ M)
    (H : RowCap R M endpoint diagonal') :
    dist R.output.jets.rear
      (S.column.step.richStage (n + 1)).terminalBase ≤
        endpoint * diagonal' := by
  have hL : 0 ≤ R.terminalInput.physical.L := by
    rw [← R.terminalInput.physical.perim_eq]
    exact zero_le_one.trans R.terminal_perim_ge_one
  have hkb : 0 ≤ R.terminalInput.physical.kb :=
    (abs_nonneg (R.terminalInput.physical.curvature 0)).trans
      (R.terminalInput.physical.curvature_bound 0)
  have hkL : 0 ≤ R.terminalInput.physical.kL := by
    have Hlip := R.terminalInput.physical.curvature_lipschitz 0 1
    have H0 := (abs_nonneg
      (R.terminalInput.physical.curvature 0 -
        R.terminalInput.physical.curvature 1)).trans Hlip
    norm_num at H0
    exact H0
  exact R.output.endpoint_dist_le_coefficient_mul_diagonal
    hM hL hkb hkL H.cost_le_M H.coefficient_le H.cost_le_diagonal

/-- Minimal configured specialization needed to derive the three `RowCap`
fields automatically. -/
structure ConfiguredCapBounds
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : ChosenRow (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S)
    (D : ConstructedConfiguredSequenceWeighted.Data) (M kh0 : ℝ) : Prop where
  kh_eq : kh n = kh0
  qmax_le : Qmax n ≤
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.ellCap D n
  error_eq : e n (k + 1) =
    ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect D
      (n + (k + 1))
  defect_lt_M :
    ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect D
      (n + (k + 1)) < M
  Lmax_le : R.terminalInput.Lmax ≤
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.speedCap D n
  length_le : R.terminalInput.physical.L ≤
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.lengthCap D n
  kb_le : R.terminalInput.physical.kb ≤ D.kstar
  kL_le : R.terminalInput.physical.kL ≤ D.kd

/-- The configured source, scalar cost cap, and physical terminal ceilings
construct all three numerical fields of `RowCap`. -/
def ConfiguredCapBounds.rowCap
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {R : ChosenRow (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S}
    {D : ConstructedConfiguredSequenceWeighted.Data} {M kh0 : ℝ}
    (H : ConfiguredCapBounds R D M kh0) :
    RowCap R M
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.endpointConversion
        D kh0 M n)
      (ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect D
        (n + (k + 1))) where
  cost_le_M := by
    have hcost : R.output.chosen.Delta.cost ≤ e n (k + 1) := by
      rw [R.output.chosen.cost_eq]
      exact R.terminalInput.cost_le
    calc
      R.output.chosen.Delta.cost ≤ e n (k + 1) := hcost
      _ = ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect D
          (n + (k + 1)) := H.error_eq
      _ ≤ M := H.defect_lt_M.le
  coefficient_le := by
    have hQ0 : 0 ≤ R.terminalInput.Lmax :=
      (S.source n).rear_period_pos 0 |>.le.trans
        (R.terminalInput.rearPeriod_le 0)
    have hell0 : 0 ≤ rearPeriod (S.source n) 0 :=
      ((S.source n).rear_period_pos 0).le
    have hell : rearPeriod (S.source n) 0 ≤
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.ellCap D n :=
      ((S.source n).rear_period_le 0).trans H.qmax_le
    have hkappa := rearKappa1_nonneg (S.source n).kh_nonnegative
      (S.source n).kh_lt_one
    have hkappa2 := rearKappa2_nonneg (S.source n).kh_nonnegative
      (S.source n).kh_lt_one
    have hM0 : 0 ≤ M :=
      (ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect_nonneg
        D (n + (k + 1))).trans H.defect_lt_M.le
    have hL0 : 0 ≤ R.terminalInput.physical.L := by
      rw [← R.terminalInput.physical.perim_eq]
      exact zero_le_one.trans R.terminal_perim_ge_one
    have hkb0 : 0 ≤ R.terminalInput.physical.kb :=
      (abs_nonneg (R.terminalInput.physical.curvature 0)).trans
        (R.terminalInput.physical.curvature_bound 0)
    have hkL0 : 0 ≤ R.terminalInput.physical.kL := by
      have Hlip := R.terminalInput.physical.curvature_lipschitz 0 1
      have H0 := (abs_nonneg
        (R.terminalInput.physical.curvature 0 -
          R.terminalInput.physical.curvature 1)).trans Hlip
      norm_num at H0
      exact H0
    have hmono := canonicalMarkingLinearConst_mono_fixed
      hQ0 H.Lmax_le hell0 hell hkappa hkappa2 hM0
      hL0 H.length_le hkb0 H.kb_le hkL0 H.kL_le
    simpa [ConfiguredCombinedPhysicalDiagonalLargeSeparation.endpointConversion,
      ConfiguredGaugeEndpointLinearRadius.endpointLinearCoeff, H.kh_eq] using hmono
  cost_le_diagonal := by
    have hcost : R.output.chosen.Delta.cost ≤ e n (k + 1) := by
      rw [R.output.chosen.cost_eq]
      exact R.terminalInput.cost_le
    calc
      R.output.chosen.Delta.cost ≤ e n (k + 1) := hcost
      _ = ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect D
          (n + (k + 1)) := H.error_eq

/-- An all-depth concrete chosen-row provider with the rowwise numerical data
needed for the successor caps. -/
structure CappedChosenRowProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (endpointConversion diagonal' : ℕ → ℝ) where
  chosen : ChosenRowProvider Q e P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax a MA NA K0 K1 K2
  M : ℝ
  M_nonnegative : 0 ≤ M
  cap : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (n : ℕ),
    RowCap ((chosen.rows S).row n) M (endpointConversion n)
      (diagonal' (n + (k + 1)))

/-- A chosen-row provider whose caps are discharged solely by configured
source/terminal bounds. -/
structure ConfiguredChosenRowProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (D : ConstructedConfiguredSequenceWeighted.Data) (M kh0 : ℝ) where
  chosen : ChosenRowProvider Q e P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax a MA NA K0 K1 K2
  M_nonnegative : 0 ≤ M
  bounds : ∀ {current k}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (n : ℕ),
    ConfiguredCapBounds ((chosen.rows S).row n) D M kh0

/-- Pointwise automatic construction of the concrete capped provider. -/
def ConfiguredChosenRowProvider.capped
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {D : ConstructedConfiguredSequenceWeighted.Data} {M kh0 : ℝ}
    (G : ConfiguredChosenRowProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2 D M kh0) :
    CappedChosenRowProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.endpointConversion
        D kh0 M)
      (ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect D) where
  chosen := G.chosen
  M := M
  M_nonnegative := G.M_nonnegative
  cap S n := (G.bounds S n).rowCap

/-- Forget the concrete rows while retaining their caps, producing the exact
`CappedProvider` consumed by recursive row production. -/
def CappedChosenRowProvider.cappedProvider
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {endpointConversion diagonal' : ℕ → ℝ}
    (G : CappedChosenRowProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2
      endpointConversion diagonal') :
    CappedProvider Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 endpointConversion diagonal' where
  provider := G.chosen.provider
  successorCap S := by
    let F := G.chosen.rows S
    change ColumnCap (mappedColumn G.chosen.provider S)
      endpointConversion diagonal'
    refine { endpoint_dist := ?_, terminal_curvature := ?_ }
    · intro n
      have H :=
        FiniteSmoothRearFamilyMarkingAwareDirectCappedProvider.ChosenRow.endpoint_dist_le_cap
          (R := F.row n) G.M_nonnegative (G.cap S n)
      simpa [ChosenRowProvider.provider, ChosenRowFamily.successor,
        successorOfRows, F] using H
    · intro n u
      have H := (F.row n).terminalInput.zero_floor_tube.curv_lb u
      simpa [ChosenRowProvider.provider, ChosenRowFamily.successor,
        successorOfRows, F,
        ConfiguredEnrichedQuantitativePhysicalProducer.orientedNumerator] using H

/-- Capped theorem-produced nonaffine rows over only invariant-carrying
recursive states. -/
structure SlicedCappedNonaffineRowProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal kh Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (endpointConversion diagonal' : ℕ → ℝ) where
  rows : RecursiveSlicedNonaffineRowProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2
  M : ℝ
  M_nonnegative : 0 ≤ M
  cap : ∀ {current k}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2} (H : SlicedCorrelatedColumn S) (n : ℕ),
    RowCap ((rows.rows.family H).chosenFamily.row n) M
      (endpointConversion n) (diagonal' (n + (k + 1)))

/-- Forget concrete rows while preserving the sliced recursive invariant and
their terminal caps. -/
def SlicedCappedNonaffineRowProvider.slicedCappedProvider
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {endpointConversion diagonal' : ℕ → ℝ}
    (G : SlicedCappedNonaffineRowProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2
      endpointConversion diagonal') :
    SlicedCappedProvider Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 endpointConversion diagonal' where
  provider := G.rows.slicedProvider
  successorCap S H := by
    let F := (G.rows.rows.family H).chosenFamily
    change ColumnCap (F.successor.mappedColumn) endpointConversion diagonal'
    refine { endpoint_dist := ?_, terminal_curvature := ?_ }
    · intro n
      have hcap := ChosenRow.endpoint_dist_le_cap
        (R := F.row n) G.M_nonnegative (G.cap H n)
      simpa [F, ChosenRowFamily.successor, successorOfRows] using hcap
    · intro n u
      have hcurv := (F.row n).terminalInput.zero_floor_tube.curv_lb u
      simpa [F, ChosenRowFamily.successor, successorOfRows,
        ConfiguredEnrichedQuantitativePhysicalProducer.orientedNumerator] using hcurv

end FiniteSmoothRearFamilyMarkingAwareDirectCappedProvider
