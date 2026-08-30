import UnitTangentIterates.ConfiguredRecursiveEdgeOutputUpperSpeedCap
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalCompositionBase
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionInitialNormalization

/-! # Configured canonical rows for the transition-free geometric recursion -/

noncomputable section

set_option maxHeartbeats 2000000

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeGeometricPresentedCanonicalRowProvider

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeGeometricPresentedCanonicalRowProvider
  ConfiguredRecursiveEdgeOutputUpperSpeedCap
  ConfiguredRecursiveEdgePhysicalCompositionBase
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
  FiniteSmoothRearFamilyMarkingAwareCompositionInitialNormalization
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily

variable {MA NA : ℝ}

/-- Every reachable source has the same three fixed-row flow ceilings as the
configured base.  The period estimate uses only the actual time-zero rear and
the inductively retained fixed-row tube. -/
theorem reachable_flowCeilings
    (J : RowJetScalarOutput MA NA) {current : ℕ → Data} {k : ℕ}
    {S : GeometricCorrelatedColumn (Q J.scalar) current
      (compositionError J) k
      (edgeSourceP0 (D J.scalar)) (edgeP1 (D J.scalar) MA)
      (fun _ ↦ pathKhat J.scalar) (edgeG1 (D J.scalar) MA NA)
      (edgeCgWithKhat (D J.scalar) (pathKhat J.scalar) MA NA)
      (rowC J.scalar)
      (ConfiguredCanonicalPairSource.commonC (D J.scalar))
      (ConfiguredCanonicalPairSource.commonDlt (D J.scalar))
      khRow (Qmax J.scalar)}
    (H : GeometricCompositionInvariant S) (n : ℕ) :
    let A := S.source n
    let M := ∫ t in (0 : ℝ)..(S.path n).T, A.m t
    GaugeFlowDerivCost.costP1 (rearPeriod A 0)
        (pathKhat J.scalar) M ≤ edgeP1 (D J.scalar) MA n ∧
      GaugeFlowDerivCost.costG1 (rearPeriod A 0)
          (pathKhat J.scalar) (GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh) M ≤
        edgeG1 (D J.scalar) MA NA n ∧
      pathKhat J.scalar * GaugeFlowDerivCost.costG1 (rearPeriod A 0)
          (pathKhat J.scalar) (GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh) M +
        GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh *
          GaugeFlowDerivCost.costP1 (rearPeriod A 0)
            (pathKhat J.scalar) M ^ 2 ≤
        edgeCgWithKhat (D J.scalar) (pathKhat J.scalar) MA NA n := by
  dsimp only
  let A := S.source n
  let M := ∫ t in (0 : ℝ)..(S.path n).T, A.m t
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg
    (S.path n).T_pos.le (fun t _ ↦ A.density_nonnegative t)
  have hM1 : M ≤ 1 := by
    apply (H.source_cost_le n).trans
    simpa [compositionError, ConfiguredDiagonalStableRowDefectProvider.error,
      edgeCompositionPhysicalDefect, Nat.add_assoc] using
      (J.composition_mass_one (n + k + 1))
  have hell0 : 0 ≤ rearPeriod A 0 := (A.rear_period_pos 0).le
  have hellC : rearPeriod A 0 ≤ rowC J.scalar n :=
    H.rearPeriod_zero_le_initialUpper n
  have hCQ : rowC J.scalar n ≤ edgeSpeedCap (D J.scalar) n := by
    simpa [rowC, D] using
      (outputUpper_le_edgeSpeedCap J.scalar.E.data J.scalar.large n)
  simpa [A, M, pathKhat, khRow] using
    (flowCeilings_of_mass_one (D J.scalar) n hell0
      (hellC.trans hCQ) hM0 hM1 (MA := MA) (NA := NA))

/-- The canonical theorem-produced row at an arbitrary reachable configured
geometric column. -/
noncomputable def row
    (J : RowJetScalarOutput MA NA) {current : ℕ → Data} {k : ℕ}
    {S : GeometricCorrelatedColumn (Q J.scalar) current
      (compositionError J) k
      (edgeSourceP0 (D J.scalar)) (edgeP1 (D J.scalar) MA)
      (fun _ ↦ pathKhat J.scalar) (edgeG1 (D J.scalar) MA NA)
      (edgeCgWithKhat (D J.scalar) (pathKhat J.scalar) MA NA)
      (rowC J.scalar)
      (ConfiguredCanonicalPairSource.commonC (D J.scalar))
      (ConfiguredCanonicalPairSource.commonDlt (D J.scalar))
      khRow (Qmax J.scalar)}
    (H : GeometricCompositionInvariant S) (n : ℕ) :
    GeometricPresentedRowSelection (n := n) S := by
  have F := reachable_flowCeilings J H n
  exact FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow.row
    H n F.1 F.2.1 F.2.2

/-- The exact composition-scaled scalar for the successor produced below row
`n+1`.  Both analytic parameters and the coefficient use the same diagonal
index `n+k+1`; the source defect is the following diagonal. -/
noncomputable def compositionScalar
    (J : RowJetScalarOutput MA NA) {current : ℕ → Data} {k : ℕ}
    {S : GeometricCorrelatedColumn (Q J.scalar) current
      (compositionError J) k
      (edgeSourceP0 (D J.scalar)) (edgeP1 (D J.scalar) MA)
      (fun _ ↦ pathKhat J.scalar) (edgeG1 (D J.scalar) MA NA)
      (edgeCgWithKhat (D J.scalar) (pathKhat J.scalar) MA NA)
      (rowC J.scalar)
      (ConfiguredCanonicalPairSource.commonC (D J.scalar))
      (ConfiguredCanonicalPairSource.commonDlt (D J.scalar))
      khRow (Qmax J.scalar)}
    (H : GeometricCompositionInvariant S) (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorCompositionScale.Scalar
      (A := S.source (n + 1)) (kap := sourceKh)
      (P0Next := edgeSourceP0 (D J.scalar) (n + k + 1))
      (khatNext := pathKhat J.scalar)
      (QmaxNext := edgeSpeedCap (D J.scalar) (n + k + 1))
      (row J H (n + 1)).output.chosen := by
  let q := n + k + 1
  let W := (row J H (n + 1)).output.chosen
  let coeff := edgeCompositionCoeff (D J.scalar) q
  have hsqrt : 0 < Real.sqrt (1 - sourceKh ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [sourceKh_nonnegative, sourceKh_lt_one])
  have hcost : W.Delta.cost ≤
      edgeCompositionPhysicalDefect (D J.scalar) (q + 1) := by
    have h := FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow.chosen_cost_le
      H (n + 1)
    simpa [W, q, compositionError,
      ConfiguredDiagonalStableRowDefectProvider.error,
      edgeCompositionPhysicalDefect, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using h
  have hfactor : 0 ≤ coeff / Real.sqrt (1 - sourceKh ^ 2) :=
    div_nonneg (zero_le_one.trans (edgeCompositionCoeff_one_le (D J.scalar) q))
      hsqrt.le
  refine
    { curvature_le := H.rearCurvature_le (n + 1)
      period_le := fun t ↦ by
        simpa [Qmax, q, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (S.source (n + 1)).rear_period_le t
      rearKappa1_le := by
        simpa [D, pathKhat] using
          (rearKappa1_sourceKh_le_analyticKhat (D J.scalar))
      numerical_A := by
        simpa [Qmax, pathKhat, D, q] using
          (ConfiguredRecursiveEdgeSourceP0.numerical_A (D J.scalar) q)
      numerical_K := by
        simpa [Qmax, pathKhat, D, q,
          khRow, sourceConst, curvatureConst, derivativeConst] using
          (ConfiguredRecursiveEdgeSourceP0.numerical_K (D J.scalar) q)
      coeff := coeff
      coeff_ge_one := edgeCompositionCoeff_one_le (D J.scalar) q
      scaled_mass_le_one := ?_
      coeff_first := by
        let Qq := edgeSpeedCap (D J.scalar) q
        let k1 := GaugeMarkedDataOfRearFamily.rearKappa1 sourceKh
        let ka := analyticKhat (D J.scalar)
        have hk : k1 ≤ ka := rearKappa1_sourceKh_le_analyticKhat (D J.scalar)
        have hQ0 : 0 ≤ Qq := edgeSpeedCap_nonnegative (D J.scalar) q
        have hp : GaugeFlowDerivCost.costP1 Qq k1 1 ≤
            GaugeFlowDerivCost.costP1 Qq ka 1 := by
          unfold GaugeFlowDerivCost.costP1
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by simpa using hk)) hQ0
        calc
          2 * GaugeFlowDerivCost.costP1 Qq k1 1 ≤
              2 * GaugeFlowDerivCost.costP1 Qq ka 1 := by linarith
          _ ≤ coeff := by
            simpa [coeff, edgeFlowP1AtOne, Qq] using
              (edgeCompositionCoeff_first (D J.scalar) q)
      coeff_second := by
        let Qq := edgeSpeedCap (D J.scalar) q
        let k1 := GaugeMarkedDataOfRearFamily.rearKappa1 sourceKh
        let k2 := GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh
        let ka := analyticKhat (D J.scalar)
        let p := GaugeFlowDerivCost.costP1 Qq k1 1
        let pa := GaugeFlowDerivCost.costP1 Qq ka 1
        let g := GaugeFlowDerivCost.costG1 Qq k1 k2 1
        let ga := GaugeFlowDerivCost.costG1 Qq ka k2 1
        have hk : k1 ≤ ka := rearKappa1_sourceKh_le_analyticKhat (D J.scalar)
        have hQ0 : 0 ≤ Qq := edgeSpeedCap_nonnegative (D J.scalar) q
        have hp : p ≤ pa := by
          unfold p pa GaugeFlowDerivCost.costP1
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by simpa using hk)) hQ0
        have hp0 : 0 ≤ p := by unfold p GaugeFlowDerivCost.costP1; positivity
        have hpa0 : 0 ≤ pa := hp0.trans hp
        have hpsq : p ^ 2 ≤ pa ^ 2 := (sq_le_sq₀ hp0 hpa0).2 hp
        have hk20 : 0 ≤ k2 :=
          GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
            sourceKh_nonnegative sourceKh_lt_one
        have hg : g ≤ ga := by
          unfold g ga GaugeFlowDerivCost.costG1
          exact mul_le_mul_of_nonneg_right hpsq (mul_nonneg hk20 zero_le_one)
        have hd0 : 0 ≤
            FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.sourceConst
              (kh := khRow (n + 1)) (kap := sourceKh) + 2 := by
          have := ConfiguredRecursiveSourceP0Growth.intrinsicSourceConst_nonnegative
          simpa [khRow, sourceConst, derivativeConst] using add_nonneg this (by norm_num : (0 : ℝ) ≤ 2)
        calc
          (FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.sourceConst
                (kh := khRow (n + 1)) (kap := sourceKh) + 2) * p ^ 2 +
              2 * g ≤
            (FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.sourceConst
                (kh := khRow (n + 1)) (kap := sourceKh) + 2) * pa ^ 2 +
              2 * ga := add_le_add
                (mul_le_mul_of_nonneg_left hpsq hd0) (by linarith)
          _ ≤ coeff := by
            simpa [coeff, edgeFlowP1AtOne, edgeFlowG1AtOne, Qq, p, pa,
              g, ga, ka, k2, khRow, sourceConst, derivativeConst] using
              (edgeCompositionCoeff_second (D J.scalar) q) }
  calc
    (∫ t in (0 : ℝ)..W.Delta.T,
        coeff * density W (kap := sourceKh) t) =
        coeff / Real.sqrt (1 - sourceKh ^ 2) * W.Delta.cost := by
      simp only [density, div_eq_mul_inv]
      rw [show W.Delta.cost =
        ∫ t in (0 : ℝ)..W.Delta.T, W.Delta.m t from rfl]
      rw [show (fun t ↦ coeff * (W.Delta.m t *
          (Real.sqrt (1 - sourceKh ^ 2))⁻¹)) =
          (fun t ↦ (coeff * (Real.sqrt (1 - sourceKh ^ 2))⁻¹) *
            W.Delta.m t) by funext t; ring]
      rw [intervalIntegral.integral_const_mul]
    _ ≤ coeff / Real.sqrt (1 - sourceKh ^ 2) *
        edgeCompositionPhysicalDefect (D J.scalar) (q + 1) :=
      mul_le_mul_of_nonneg_left hcost hfactor
    _ ≤ 1 := J.composition_scaled_mass_one q (q + 1) (Nat.le_succ q)

/-- The exact phase-normalized analytic successor below row `n+1`.  Its
initial selected rear is a cyclic shift of row `n`'s presented rear.  The
ordinary front tube required by physical selected-inverse uniqueness is not
an extra input: it is transported from the retained ordinary tube of
`S.initial (n+1)` through the exact terminal-front phase. -/
theorem exists_phaseNormalizedSuccessor
    (J : RowJetScalarOutput MA NA) {current : ℕ → Data} {k : ℕ}
    {S : GeometricCorrelatedColumn (Q J.scalar) current
      (compositionError J) k
      (edgeSourceP0 (D J.scalar)) (edgeP1 (D J.scalar) MA)
      (fun _ ↦ pathKhat J.scalar) (edgeG1 (D J.scalar) MA NA)
      (edgeCgWithKhat (D J.scalar) (pathKhat J.scalar) MA NA)
      (rowC J.scalar)
      (ConfiguredCanonicalPairSource.commonC (D J.scalar))
      (ConfiguredCanonicalPairSource.commonDlt (D J.scalar))
      khRow (Qmax J.scalar)}
    (H : GeometricCompositionInvariant S) (n : ℕ) :
    Nonempty (PhaseNormalizedCompositionSuccessor
      (row J H (n + 1)).output.chosen.Delta (S.source (n + 1))
      (edgeSourceP0 (D J.scalar) (n + k + 1)) sourceKh
      (pathKhat J.scalar) (edgeSpeedCap (D J.scalar) (n + k + 1))
      (row J H n).presented) := by
  let q := n + k + 1
  let R := row J H n
  let W := (row J H (n + 1)).output.chosen
  let A := S.source (n + 1)
  obtain ⟨cF, dF, hcF, hinitial⟩ := H.initialOrdinaryTube (n + 1)
  have hfront : IsTubeMember cF 0 dF R.terminalInput.frontData := by
    change IsTubeMember cF 0 dF
      (FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow.geometry
        H n).frontData
    rw [(FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow.geometry
      H n).frontData_eq, H.terminalFront_eq_phase n]
    exact MarkedShift.isTubeMember_shiftData hinitial
      (H.terminalFront_phase n)
  have hF : FiniteSmoothRearFamilyMarkingAwareSuccessorFront.front A 0 =
      ev (MarkedShift.shiftData (-(H.terminalFront_phase n))
        R.terminalInput.frontData) := by
    rw [H.nextFront_zero n]
    change ev (S.initial (n + 1)) = ev (MarkedShift.shiftData
      (-(H.terminalFront_phase n))
      (FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow.geometry
        H n).frontData)
    rw [(FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow.geometry
      H n).frontData_eq, H.terminalFront_eq_phase n]
    rw [MarkedShift.shiftData_add]
    simp
  have hP : FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period A 0 =
      perim R.terminalInput.frontData := by
    rw [H.nextPeriod_zero n]
    change perim (S.initial (n + 1)) = perim
      (FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow.geometry
        H n).frontData
    rw [(FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow.geometry
      H n).frontData_eq, H.terminalFront_eq_phase n]
    exact (SelectedInverseShiftEquivariance.perim_shiftData hinitial
      (H.terminalFront_phase n)).symm
  have hP0one : edgeSourceP0 (D J.scalar) q ≤ 1 := by
    have hkh := analyticKhat_nonnegative (D J.scalar)
    have hR : 0 ≤ GaugeRearFamilyFromFront.rearDriftConst
        (edgeSpeedCap (D J.scalar) q) sourceKh :=
      GaugeRearFamilyFromFront.rearDriftConst_nonneg
        (edgeSpeedCap_nonnegative (D J.scalar) q)
        sourceKh_nonnegative sourceKh_lt_one
    have hInv : 1 ≤ 1 / edgeSourceP0 (D J.scalar) q := by
      have h := ConfiguredRecursiveEdgeSourceP0.numerical_A (D J.scalar) q
      nlinarith [mul_nonneg hkh hR]
    have hp := edgeSourceP0_pos (D J.scalar) q
    have h := (le_div_iff₀ hp).mp hInv
    simpa using h
  have hPl : ∀ t, edgeSourceP0 (D J.scalar) q ≤
      FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period A t := by
    intro t
    have hdelta : Continuous (A.delta t) :=
      Differentiable.continuous fun s ↦ (A.steering t s).differentiableAt
    have hcos : ∀ s, Real.sqrt (1 - sourceKh ^ 2) ≤
        Real.cos (A.delta t s) := fun s ↦
      Shadowing.cos_ge_of_mem_strip
        (A.strip_nonnegative t s) (A.strip_le t s)
    have hrear : Real.sqrt (1 - sourceKh ^ 2) * A.P t ≤
        FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period A t :=
      ArclengthInverse.rearArclength_ge hdelta hcos (A.period_pos t).le
    have hscale : 1 ≤ Real.sqrt (1 - sourceKh ^ 2) * A.P t := by
      simpa [A, khRow] using H.frontPeriodScaleOne (n + 1) t
    exact hP0one.trans (hscale.trans hrear)
  have hPu : ∀ t, FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period A t ≤
      (H.slice (n + 1)).periodUpper := by
    intro t
    have hdelta : Continuous (A.delta t) :=
      Differentiable.continuous fun s ↦ (A.steering t s).differentiableAt
    exact (ArclengthInverse.rearArclength_le_of_period hdelta
      (A.period_pos t).le).trans (by
        simpa [A] using (H.slice (n + 1)).period_upper t)
  exact
    FiniteSmoothRearFamilyMarkingAwareCompositionInitialNormalization.ChosenPath.exists_phaseNormalizedCompositionSuccessor
    (A := A) (periodLower := edgeSourceP0 (D J.scalar) q)
    (periodUpper := (H.slice (n + 1)).periodUpper)
    (kap := sourceKh) (khatNext := pathKhat J.scalar)
    (QmaxNext := edgeSpeedCap (D J.scalar) q)
    (Md := (H.sidecars (n + 1)).selection.Md)
    (MP := (H.sidecars (n + 1)).selection.MP)
    (rear := R.presented) (frontData := R.terminalInput.frontData) W
    (edgeSourceP0_pos (D J.scalar) q)
    sourceKh_nonnegative sourceKh_lt_one
    hPl hPu
    (H.sidecars (n + 1)).selection.normalizedCurvatureTime_le
    (H.sidecars (n + 1)).selection.periodTime_le
    (compositionScalar J H n)
    R.output.frontKinematics hcF hfront
    R.terminalInput.physical.cq_pos R.terminalInput.zero_floor_tube
    (-(H.terminalFront_phase n)) hF hP

/-- The canonical choice of the exact phase-normalized successor. -/
noncomputable def phaseNormalizedSuccessor
    (J : RowJetScalarOutput MA NA) {current : ℕ → Data} {k : ℕ}
    {S : GeometricCorrelatedColumn (Q J.scalar) current
      (compositionError J) k
      (edgeSourceP0 (D J.scalar)) (edgeP1 (D J.scalar) MA)
      (fun _ ↦ pathKhat J.scalar) (edgeG1 (D J.scalar) MA NA)
      (edgeCgWithKhat (D J.scalar) (pathKhat J.scalar) MA NA)
      (rowC J.scalar)
      (ConfiguredCanonicalPairSource.commonC (D J.scalar))
      (ConfiguredCanonicalPairSource.commonDlt (D J.scalar))
      khRow (Qmax J.scalar)}
    (H : GeometricCompositionInvariant S) (n : ℕ) :
    PhaseNormalizedCompositionSuccessor
      (row J H (n + 1)).output.chosen.Delta (S.source (n + 1))
      (edgeSourceP0 (D J.scalar) (n + k + 1)) sourceKh
      (pathKhat J.scalar) (edgeSpeedCap (D J.scalar) (n + k + 1))
      (row J H n).presented :=
  Classical.choice (exists_phaseNormalizedSuccessor J H n)

end ConfiguredRecursiveEdgeGeometricPresentedCanonicalRowProvider
