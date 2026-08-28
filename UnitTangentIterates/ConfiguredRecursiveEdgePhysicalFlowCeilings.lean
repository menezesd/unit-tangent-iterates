import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0RowJetTail
import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor

/-! # Mass-one flow ceilings for the physical edge source -/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePhysicalFlowCeilings

open ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource

variable {MA NA : ℝ}

theorem source_cost_le_one
    (J : RowJetScalarOutput MA NA) (C : ℕ → ℝ)
    {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    (∫ t in (0 : ℝ)..(edgeOutput J.scalar (n + 1)).increment.T,
      (source J.scalar C (MA0 := MA0) (NA0 := NA0)
        (K0 := K0) (K1 := K1) (K2 := K2) n).m t) ≤ 1 := by
  have hraw := (edgeSource_cost_le_compositionPhysicalDefect J.scalar n).trans
    (J.composition_mass_one (n + 1))
  simpa [source, presentation, edgeSourceAt, edgeScaledBoundsAt,
    edgeSourceFamily, edgeScaledBounds] using hraw

theorem source_flowCeilings
    (J : RowJetScalarOutput MA NA) (C : ℕ → ℝ)
    {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    let A := source J.scalar C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n
    let M := ∫ t in (0 : ℝ)..(edgeOutput J.scalar (n + 1)).increment.T, A.m t
    GaugeFlowDerivCost.costP1 (rearPeriod A 0) (analyticKhat (data J.scalar)) M ≤
        edgeP1 (data J.scalar) MA0 n ∧
      GaugeFlowDerivCost.costG1 (rearPeriod A 0) (analyticKhat (data J.scalar))
          (GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh) M ≤
        edgeG1 (data J.scalar) MA0 NA0 n ∧
      analyticKhat (data J.scalar) *
          GaugeFlowDerivCost.costG1 (rearPeriod A 0)
            (analyticKhat (data J.scalar))
            (GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh) M +
        GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh *
          GaugeFlowDerivCost.costP1 (rearPeriod A 0)
            (analyticKhat (data J.scalar)) M ^ 2 ≤
        edgeCgWithKhat (data J.scalar) (analyticKhat (data J.scalar))
          MA0 NA0 n := by
  dsimp only
  let A := source J.scalar C (MA0 := MA0) (NA0 := NA0)
    (K0 := K0) (K1 := K1) (K2 := K2) n
  let M := ∫ t in (0 : ℝ)..(edgeOutput J.scalar (n + 1)).increment.T, A.m t
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg
    (edgeOutput J.scalar (n + 1)).increment.T_pos.le
    (fun t _ ↦ A.density_nonnegative t)
  have hM1 : M ≤ 1 := source_cost_le_one J C n
  exact flowCeilings_of_mass_one (data J.scalar) n
    (A.rear_period_pos 0).le (A.rear_period_le 0) hM0 hM1

/-- The actual source flow is also bounded by the successor-indexed ceilings
used in the density multiplier. -/
theorem source_flowCeilings_next
    (J : RowJetScalarOutput MA NA) (C : ℕ → ℝ)
    {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    let A := source J.scalar C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n
    let M := ∫ t in (0 : ℝ)..(edgeOutput J.scalar (n + 1)).increment.T, A.m t
    GaugeFlowDerivCost.costP1 (rearPeriod A 0) (analyticKhat (data J.scalar)) M ≤
        edgeFlowP1AtOne (data J.scalar) (n + 1) ∧
      GaugeFlowDerivCost.costG1 (rearPeriod A 0) (analyticKhat (data J.scalar))
          (GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh) M ≤
        edgeFlowG1AtOne (data J.scalar) (n + 1) := by
  dsimp only
  let A := source J.scalar C (MA0 := MA0) (NA0 := NA0)
    (K0 := K0) (K1 := K1) (K2 := K2) n
  let M := ∫ t in (0 : ℝ)..(edgeOutput J.scalar (n + 1)).increment.T, A.m t
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg
    (edgeOutput J.scalar (n + 1)).increment.T_pos.le
    (fun t _ ↦ A.density_nonnegative t)
  have hM1 : M ≤ 1 := source_cost_le_one J C n
  have hspeed : edgeSpeedCap (data J.scalar) n ≤
      edgeSpeedCap (data J.scalar) (n + 1) := by
    unfold edgeSpeedCap speedCap
    have hs := (data J.scalar).separation_step (n + 1)
    have hd := (data J.scalar).deltaStep_pos
    nlinarith
  have hell0 := (A.rear_period_pos 0).le
  have hell := (A.rear_period_le 0).trans hspeed
  constructor
  · change GaugeFlowDerivCost.costP1 (rearPeriod A 0)
      (analyticKhat (data J.scalar)) M ≤ _
    simpa only [edgeFlowP1AtOne] using GaugeFlowDerivCost.costP1_le
      hell0 hell (analyticKhat_nonnegative (data J.scalar)) hM0 hM1
  · change GaugeFlowDerivCost.costG1 (rearPeriod A 0)
      (analyticKhat (data J.scalar))
      (GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh) M ≤ _
    simpa only [edgeFlowG1AtOne] using GaugeFlowDerivCost.costG1_le
      hell0 hell (analyticKhat_nonnegative (data J.scalar))
      (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
        sourceKh_nonnegative sourceKh_lt_one) hM0 hM1

/-- The noncircular composition multiplier discharges both density hypotheses
of `Applied.normal_sup_of_spatial`. -/
theorem source_composition_budgets
    (J : RowJetScalarOutput MA NA) (C : ℕ → ℝ)
    {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    let A := source J.scalar C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n
    let Gamma := (edgeOutput J.scalar (n + 1)).increment
    let M := ∫ s in (0 : ℝ)..Gamma.T, A.m s
    (∀ t, 2 * (Gamma.m t / Real.sqrt (1 - sourceKh ^ 2)) *
        GaugeFlowDerivCost.costP1 (rearPeriod A 0)
          (GaugeMarkedDataOfRearFamily.rearKappa1 sourceKh) M ≤ A.m t) ∧
      (∀ t,
        (A.Dd t + 2 * (Gamma.m t / Real.sqrt (1 - sourceKh ^ 2))) *
            GaugeFlowDerivCost.costP1 (rearPeriod A 0)
              (GaugeMarkedDataOfRearFamily.rearKappa1 sourceKh) M ^ 2 +
          2 * (Gamma.m t / Real.sqrt (1 - sourceKh ^ 2)) *
            GaugeFlowDerivCost.costG1 (rearPeriod A 0)
              (GaugeMarkedDataOfRearFamily.rearKappa1 sourceKh)
              (GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh) M ≤ A.m t) := by
  dsimp only
  let A := source J.scalar C (MA0 := MA0) (NA0 := NA0)
    (K0 := K0) (K1 := K1) (K2 := K2) n
  let Gamma := (edgeOutput J.scalar (n + 1)).increment
  let M := ∫ s in (0 : ℝ)..Gamma.T, A.m s
  let raw := fun t ↦
    (edgeBoundsAt J.scalar n (initialRearPhase J.scalar n)).m t
  let coeff := edgeCompositionCoeff (data J.scalar) (n + 1)
  let p := GaugeFlowDerivCost.costP1 (rearPeriod A 0)
    (GaugeMarkedDataOfRearFamily.rearKappa1 sourceKh) M
  let g := GaugeFlowDerivCost.costG1 (rearPeriod A 0)
    (GaugeMarkedDataOfRearFamily.rearKappa1 sourceKh)
    (GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh) M
  let p1 := edgeFlowP1AtOne (data J.scalar) (n + 1)
  let g1 := edgeFlowG1AtOne (data J.scalar) (n + 1)
  have hflow := source_flowCeilings_next J C
    (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2) n
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg Gamma.T_pos.le
    (fun t _ ↦ A.density_nonnegative t)
  let pa := GaugeFlowDerivCost.costP1 (rearPeriod A 0)
    (analyticKhat (data J.scalar)) M
  let ga := GaugeFlowDerivCost.costG1 (rearPeriod A 0)
    (analyticKhat (data J.scalar))
    (GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh) M
  change pa ≤ p1 ∧ ga ≤ g1 at hflow
  have hkhat := rearKappa1_sourceKh_le_analyticKhat (data J.scalar)
  have hpK : p ≤ pa := by
    unfold p pa GaugeFlowDerivCost.costP1
    apply mul_le_mul_of_nonneg_left
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hkhat hM0
    exact (A.rear_period_pos 0).le
  have hp := hpK.trans hflow.1
  have hgK : g ≤ ga := by
    unfold g ga GaugeFlowDerivCost.costG1
    have hp0' : 0 ≤ GaugeFlowDerivCost.costP1 (rearPeriod A 0)
        (GaugeMarkedDataOfRearFamily.rearKappa1 sourceKh) M := by
      unfold GaugeFlowDerivCost.costP1
      exact mul_nonneg (A.rear_period_pos 0).le (Real.exp_pos _).le
    have hpa0 : 0 ≤ GaugeFlowDerivCost.costP1 (rearPeriod A 0)
        (analyticKhat (data J.scalar)) M := hp0'.trans hpK
    have hsquare := (sq_le_sq₀ hp0' hpa0).2 hpK
    exact mul_le_mul_of_nonneg_right hsquare
      (mul_nonneg (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
        sourceKh_nonnegative sourceKh_lt_one) hM0)
  have hg := hgK.trans hflow.2
  have hp0 : 0 ≤ p := by
    unfold p GaugeFlowDerivCost.costP1
    exact mul_nonneg (A.rear_period_pos 0).le (Real.exp_pos _).le
  have hg0 : 0 ≤ g := by
    unfold g GaugeFlowDerivCost.costG1
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
        sourceKh_nonnegative sourceKh_lt_one) hM0)
  have hp10 := edgeFlowP1AtOne_nonneg (data J.scalar) (n + 1)
  have hg10 := edgeFlowG1AtOne_nonneg (data J.scalar) (n + 1)
  have hfirst := edgeCompositionCoeff_first (data J.scalar) (n + 1)
  have hsecond := edgeCompositionCoeff_second (data J.scalar) (n + 1)
  constructor
  · intro t
    have hraw0 : 0 ≤ raw t :=
      (edgeBoundsAt J.scalar n (initialRearPhase J.scalar n)).density_nonnegative t
    have hbase : Gamma.m t / Real.sqrt (1 - sourceKh ^ 2) ≤ raw t :=
      (edgeBoundsAt J.scalar n (initialRearPhase J.scalar n)).density_domination t
    have hbase0 : 0 ≤ Gamma.m t / Real.sqrt (1 - sourceKh ^ 2) :=
      div_nonneg (Gamma.m_nonneg t) (Real.sqrt_nonneg _)
    have hmul : 2 * (Gamma.m t / Real.sqrt (1 - sourceKh ^ 2)) * p ≤
        coeff * raw t := by
      calc
        2 * (Gamma.m t / Real.sqrt (1 - sourceKh ^ 2)) * p ≤
            2 * raw t * p1 := by nlinarith
        _ ≤ coeff * raw t := by nlinarith
    simpa [A, Gamma, M, raw, coeff, p] using hmul
  · intro t
    let d := FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst
      sourceKh
      (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst sourceKh)
    have hraw0 : 0 ≤ raw t :=
      (edgeBoundsAt J.scalar n (initialRearPhase J.scalar n)).density_nonnegative t
    have hbase : Gamma.m t / Real.sqrt (1 - sourceKh ^ 2) ≤ raw t :=
      (edgeBoundsAt J.scalar n (initialRearPhase J.scalar n)).density_domination t
    have hbase0 : 0 ≤ Gamma.m t / Real.sqrt (1 - sourceKh ^ 2) :=
      div_nonneg (Gamma.m_nonneg t) (Real.sqrt_nonneg _)
    have hd0 : 0 ≤ d :=
      ConfiguredRecursiveSourceP0Growth.intrinsicSourceConst_nonnegative
    have hddraw :=
      (edgeBoundsAt J.scalar n (initialRearPhase J.scalar n)).Dd_le t
    have hdconst :
        (edgeBoundsAt J.scalar n (initialRearPhase J.scalar n)).d ≤ d := by
      change ConfiguredBaseProfiledResidualConstructor.auditedJacobiSourceConst
        (sourceCertificate J.scalar) ≤ d
      exact edgeAuditedJacobiSourceConst_le_intrinsic (O := J.scalar)
    have hdd : A.Dd t ≤ d * raw t := by
      calc
        A.Dd t =
            (edgeBoundsAt J.scalar n (initialRearPhase J.scalar n)).Dd t := by
          simp [A]
        _ ≤ (edgeBoundsAt J.scalar n (initialRearPhase J.scalar n)).d * raw t :=
          hddraw
        _ ≤ d * raw t := mul_le_mul_of_nonneg_right hdconst hraw0
    have hsqp : p ^ 2 ≤ p1 ^ 2 := (sq_le_sq₀ hp0 hp10).2 hp
    have hfac : A.Dd t + 2 * (Gamma.m t / Real.sqrt (1 - sourceKh ^ 2)) ≤
        (d + 2) * raw t := by nlinarith
    have hfac1 : 0 ≤ (d + 2) * raw t :=
      mul_nonneg (add_nonneg hd0 (by norm_num)) hraw0
    have hterm1 :
        (A.Dd t + 2 * (Gamma.m t / Real.sqrt (1 - sourceKh ^ 2))) * p ^ 2 ≤
          ((d + 2) * p1 ^ 2) * raw t := by
      calc
        _ ≤ ((d + 2) * raw t) * p1 ^ 2 :=
          mul_le_mul hfac hsqp (sq_nonneg p) hfac1
        _ = ((d + 2) * p1 ^ 2) * raw t := by ring
    have hterm2 : 2 * (Gamma.m t / Real.sqrt (1 - sourceKh ^ 2)) * g ≤
        (2 * g1) * raw t := by nlinarith
    have htotal :
        (A.Dd t + 2 * (Gamma.m t / Real.sqrt (1 - sourceKh ^ 2))) * p ^ 2 +
            2 * (Gamma.m t / Real.sqrt (1 - sourceKh ^ 2)) * g ≤
          coeff * raw t := by
      calc
        _ ≤ (((d + 2) * p1 ^ 2) + 2 * g1) * raw t := by
          nlinarith [hterm1, hterm2]
        _ ≤ coeff * raw t :=
          mul_le_mul_of_nonneg_right hsecond hraw0
    simpa [A, Gamma, M, raw, coeff, p, g, d] using htotal

/-- The physically normalized configured edge source automatically satisfies
the terminal composed-normal `C²` bound once its retained spatial frame
certificate is supplied. -/
theorem source_normal_sup
    (J : RowJetScalarOutput MA NA) (C : ℕ → ℝ)
    {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    let A := source J.scalar C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n
    let Gamma := sourcePath J.scalar C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n
    ∀ (E : Applied Gamma A)
      (R : SpatialFrameRegularity Gamma A.Ydot A.Theta A.delta A.sf
        A.P A.m sourceKh (edgeSpeedCap (data J.scalar) n)),
      ∀ t, ∀ j ≤ 2, MarkedTopology.supNorm
        (iteratedDeriv j (fun u ↦ rearNormal A t (E.Phi t u))) ≤ A.m t := by
  dsimp only
  intro E R
  have H := source_composition_budgets J C
    (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2) n
  exact E.normal_sup_of_spatial R H.1 H.2

/-- The physically normalized base source retains its complete recursive
package together with both noncircular composition-density budgets. -/
noncomputable def compositionRecursiveAnalyticSuccessor
    (J : RowJetScalarOutput MA NA) (C : ℕ → ℝ)
    {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor.CompositionRecursiveAnalyticSuccessor
      (sourcePath J.scalar C (MA0 := MA0) (NA0 := NA0)
        (K0 := K0) (K1 := K1) (K2 := K2) n)
      (source J.scalar C (MA0 := MA0) (NA0 := NA0)
        (K0 := K0) (K1 := K1) (K2 := K2) n)
      (edgeSourceP0 (data J.scalar) n) sourceKh
      (analyticKhat (data J.scalar)) (edgeSpeedCap (data J.scalar) n) := by
  let X := recursiveAnalyticSuccessor J.scalar C
    (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2) n
  have H := source_composition_budgets J C
    (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2) n
  refine { toRecursiveAnalyticSuccessor := X
           composition_d1 := ?_
           composition_d2 := ?_ }
  · simpa [X] using H.1
  · simpa [X] using H.2

@[simp] theorem compositionRecursiveAnalyticSuccessor_source
    (J : RowJetScalarOutput MA NA) (C : ℕ → ℝ)
    {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    (compositionRecursiveAnalyticSuccessor J C
      (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2) n).source =
      source J.scalar C (MA0 := MA0) (NA0 := NA0)
        (K0 := K0) (K1 := K1) (K2 := K2) n := by
  simp [compositionRecursiveAnalyticSuccessor]

end ConfiguredRecursiveEdgePhysicalFlowCeilings
