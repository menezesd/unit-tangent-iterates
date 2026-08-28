import UnitTangentIterates.ConfiguredCorrelatedConstructionCoreProvider
import UnitTangentIterates.MarkingFlowDefectC2

/-!
# Quantitative cap for the configured correlated base column

The depth-zero gauge uses the interpolation curvature bounds, not the
selected-rear bounds used by successor rows.  This file keeps its conversion
separate and proves the exact phase/rigid endpoint cap selected by
`baseCorrelated`.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredCorrelatedBaseColumnCap

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredApproximateDefectPathRowwise
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredEnrichedConstructionCoreProvider
  ConfiguredCorrelatedConstructionCoreProvider
  ConfiguredRowDefectProvider
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  FiniteSmoothRearFamilyCorrelatedPhysicalCore

def baseCost (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) : ℝ :=
  InterpolationPathDist.costE (D.Hs n) (edgeEps D n)

def baseKappa (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  4 * D.kstar

def baseKappa2 (D : ConstructedConfiguredSequenceWeighted.Data) : ℝ :=
  4 * D.kd + 4 * D.kstar + 16 * D.kstar ^ 2

def baseFirstCoeff (D : ConstructedConfiguredSequenceWeighted.Data)
    (M : ℝ) (n : ℕ) : ℝ :=
  (2 * D.Hs n) * baseKappa D * (Real.exp (baseKappa D * M) + 1)

def baseSecondCoeff (D : ConstructedConfiguredSequenceWeighted.Data)
    (M : ℝ) (n : ℕ) : ℝ :=
  (2 * D.Hs n) ^ 2 * Real.exp (2 * baseKappa D * M) * baseKappa2 D

/-- Linear coefficient for the reanchored depth-zero terminal marking. -/
def baseEndpointConversion (D : ConstructedConfiguredSequenceWeighted.Data)
    (M : ℝ) (n : ℕ) : ℝ :=
  let ell := 2 * D.Hs n
  let A := 2 * baseFirstCoeff D M n
  let B := baseFirstCoeff D M n
  let E := baseSecondCoeff D M n
  max A (max (B + ell * D.kstar * A)
    (E + D.kstar * B * (2 * ell + B * M) +
      ell ^ 2 * (D.kd + D.kstar ^ 2) * A))

theorem baseTransportMarkingBound_le
    (D : ConstructedConfiguredSequenceWeighted.Data) {M : ℝ}
    (hH0 : 1 ≤ D.Hs 0) (hM : ∀ n, rowDefect D n ≤ M) (n : ℕ) :
    baseTransportMarkingBound D n ≤
      baseEndpointConversion D M n * rowDefect D n := by
  let ell := 2 * D.Hs n
  let x := baseCost D n
  let kap := baseKappa D
  let kap2 := baseKappa2 D
  let A1 := baseFirstCoeff D M n
  let A2 := baseSecondCoeff D M n
  have hH : 1 ≤ D.Hs n := hH0.trans (D.separation_lower n)
  have heps0 : 0 ≤ edgeEps D n := edgeEps_nonneg D n
  have hx0 : 0 ≤ x := by
    exact InterpolationPathDist.costE_nonneg (D.model.separation_pos n).le heps0
  have hds0 : 0 ≤ rowDsup D n :=
    CurvatureStabilityL1.l1Modulus_nonneg _ _ _
  have hxrow : x ≤ rowDefect D n := by
    exact InterpolationPathDist.costE_le_interpPathCost D.kstar_nonneg D.kd_nonneg
      hds0 (D.model.separation_pos n).le heps0
  have hxM : x ≤ M := hxrow.trans (hM n)
  have hepsx : edgeEps D n ≤ x := by
    dsimp [x, baseCost, InterpolationPathDist.costE]
    nlinarith
  have hkap0 : 0 ≤ kap := by
    dsimp [kap, baseKappa]
    exact mul_nonneg (by norm_num) D.kstar_nonneg
  have hkap20 : 0 ≤ kap2 := by
    dsimp [kap2, baseKappa2]
    exact add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) D.kd_nonneg)
        (mul_nonneg (by norm_num) D.kstar_nonneg))
      (mul_nonneg (by norm_num) (sq_nonneg D.kstar))
  have hC1 : baseGaugeC1 D n = kap * x := by
    simp only [baseGaugeC1, InterpolationGauge.interpolationSmoothC1]
    dsimp [kap, baseKappa, x, baseCost, InterpolationPathDist.costE]
  have hC2 : baseGaugeC2 D n ≤ kap2 * x := by
    calc
      baseGaugeC2 D n = 4 * D.kd * x + 4 * D.kstar * edgeEps D n +
          16 * D.kstar ^ 2 * x := by
        simp only [baseGaugeC2, InterpolationGauge.interpolationSmoothC2]
        dsimp [x, baseCost, InterpolationPathDist.costE]
        ring
      _ ≤ 4 * D.kd * x + 4 * D.kstar * x + 16 * D.kstar ^ 2 * x := by
        gcongr
      _ = kap2 * x := by
        dsimp [kap2, baseKappa2]
        ring
  have hflow := MarkingFlowDefectC2.flowDefectInt_linear_bounds
    (ell := ell) (kappa := kap) (kappa2 := kap2) (x := x) (M := M)
    (by dsimp [ell]; positivity) hkap0 hkap20 hx0 hxM
  have hE1 : baseMarkingE1 D n ≤ A1 * x := by
    simpa [baseMarkingE1, MarkingFlowDefectC2.flowDefectC1Int,
      ell, A1, baseFirstCoeff, hC1] using hflow.1
  have hE2 : baseMarkingE2 D n ≤ A2 * x := by
    have hfac : 0 ≤ ell ^ 2 * Real.exp (2 * (kap * x)) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hC2 hfac
    have hraw : baseMarkingE2 D n ≤
        MarkingFlowDefectC2.flowDefectC2Int ell (kap * x) (kap2 * x) := by
      simpa [baseMarkingE2, MarkingFlowDefectC2.flowDefectC2Int,
        ell, hC1, mul_assoc, mul_left_comm, mul_comm] using hmul
    exact hraw.trans (by
      simpa [A2, baseSecondCoeff, ell] using hflow.2)
  have hE10 : 0 ≤ baseMarkingE1 D n := by
    unfold baseMarkingE1
    have hc : 0 ≤ baseGaugeC1 D n := by rw [hC1]; positivity
    exact mul_nonneg (by positivity)
      (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith)))
  have hE20 : 0 ≤ baseMarkingE2 D n := by
    unfold baseMarkingE2
    have hC20 : 0 ≤ baseGaugeC2 D n := by
      simp only [baseGaugeC2, InterpolationGauge.interpolationSmoothC2]
      exact add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) D.kd_nonneg)
          (mul_nonneg (mul_nonneg (by norm_num) (D.model.separation_pos n).le) heps0))
        (mul_nonneg (mul_nonneg (by norm_num) D.kstar_nonneg)
          (add_nonneg heps0 (mul_nonneg
            (mul_nonneg (by norm_num) D.kstar_nonneg)
            (mul_nonneg (mul_nonneg (by norm_num) (D.model.separation_pos n).le) heps0))))
    positivity
  have hA10 : 0 ≤ A1 := by
    dsimp [A1, baseFirstCoeff]
    positivity
  have hA20 : 0 ≤ A2 := by
    dsimp [A2, baseSecondCoeff]
    positivity
  have hE0bd : 2 * baseMarkingE1 D n ≤ (2 * A1) * x := by
    nlinarith
  have hmark := MarkingDeviationC2.markingC2Bound_le_mul_of_component_linear
    (e0 := 2 * baseMarkingE1 D n) (e1 := baseMarkingE1 D n)
    (e2 := baseMarkingE2 D n)
    (x := x) (M := M) (A := 2 * A1) (B := A1) (D := A2)
    (L := ell) (kb := D.kstar) (kL := D.kd)
    hx0 hxM (mul_nonneg (by norm_num) hA10) hA10 hA20
    (by dsimp [ell]; positivity) D.kstar_nonneg D.kd_nonneg
    (mul_nonneg (by norm_num) hE10) hE10
    hE0bd hE1 hE2
  have hconv0 : 0 ≤ baseEndpointConversion D M n := by
    dsimp [baseEndpointConversion]
    exact (mul_nonneg (by norm_num) hA10).trans (le_max_left _ _)
  have hlin : baseTransportMarkingBound D n ≤
      baseEndpointConversion D M n * x := by
    simpa [baseTransportMarkingBound, baseEndpointConversion, ell, A1, A2]
      using hmark
  exact hlin.trans (mul_le_mul_of_nonneg_left hxrow hconv0)

theorem baseTransportMarkingBound_le_physicalDefect
    (D : ConstructedConfiguredSequenceWeighted.Data) {M : ℝ}
    (hH0 : 1 ≤ D.Hs 0) (hM : ∀ n, rowDefect D n ≤ M) (n : ℕ) :
    baseTransportMarkingBound D n ≤
      baseEndpointConversion D M n * physicalDefect D n := by
  have hrow := baseTransportMarkingBound_le D hH0 hM n
  have hcoef : 0 ≤ baseEndpointConversion D M n := by
    unfold baseEndpointConversion
    have hk : 0 ≤ baseKappa D := by
      unfold baseKappa
      exact mul_nonneg (by norm_num) D.kstar_nonneg
    have hfirst : 0 ≤ baseFirstCoeff D M n := by
      unfold baseFirstCoeff
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (D.model.separation_pos n).le) hk)
        (by positivity)
    exact (mul_nonneg (by norm_num) hfirst).trans (le_max_left _ _)
  have hscale : rowDefect D n ≤ physicalDefect D n := by
    unfold physicalDefect physicalCoeff
    have hrow0 := rowDefect_nonneg D n
    have hH : 1 ≤ 2 * D.Hs n := by
      have := hH0.trans (D.separation_lower n)
      linarith
    nlinarith
  exact hrow.trans (mul_le_mul_of_nonneg_left hscale hcoef)

/-- The exact depth-zero correlated column has the configured endpoint cap.
Its curvature field comes from the shifted canonical rear carrier, while its
endpoint distance is the retained interpolation marking estimate above. -/
theorem baseColumnCap
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 M : ℝ}
    (hH : 1 ≤ D.Hs 0) (khRow Qmax : ℕ → ℝ)
    (source : ∀ n, FiniteSmoothRearFamilyAnalyticSource.Source
      (((ConfiguredEnrichedConstructionCoreProvider.baseProvider S hQ C
          (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
          hH).base.step.richStage (n + 1)).stage.increment)
      (rowP0 D n) (khRow n) D.kstar (Qmax n))
    (hM : ∀ n, rowDefect D n ≤ M) :
    ColumnCap
      (ConfiguredCorrelatedConstructionCoreProvider.baseCorrelated
        S hQ C hH khRow Qmax source)
      (baseEndpointConversion D M) (physicalDefect D) := by
  refine ⟨?_, ?_⟩
  · intro n
    let A := presentations (S := S) (hQ := hQ) n
    let W := output S hQ n
    let R := Classical.choose (exists_richStage S hQ 1 C n)
    have hR := Classical.choose_spec (exists_richStage S hQ 1 C n)
    have hterminal :
        ((ConfiguredCorrelatedConstructionCoreProvider.baseCorrelated
          S hQ C hH khRow Qmax source).column.step.richStage n).terminalBase =
          RichStageDataPhaseRigidTransport.move A.translation A.rotation
            (W.marking.marking.psi A.phase) W.terminalBase := by
      calc
        _ = R.terminalBase := by
          rfl
        _ = RichStageDataPhaseRigidTransport.move A.translation A.rotation
            (rearPhase S hQ A) (S.carrier n).data := hR.1
        _ = RichStageDataPhaseRigidTransport.move A.translation A.rotation
            (W.marking.marking.psi A.phase) W.terminalBase := by
          exact (terminalBase_eq_physicalRear S hQ n).symm
    have hend := W.transported_endpoint_dist A.phase A.translation A.rotation
      A.rotation_norm
    change dist (movedRear S hQ n)
      ((ConfiguredCorrelatedConstructionCoreProvider.baseCorrelated
        S hQ C hH khRow Qmax source).column.step.richStage n).terminalBase ≤ _
    rw [hterminal]
    exact hend.trans (baseTransportMarkingBound_le_physicalDefect D hH hM n)
  · intro n u
    let A := presentations (S := S) (hQ := hQ) n
    let R := Classical.choose (exists_richStage S hQ 1 C n)
    have hR := Classical.choose_spec (exists_richStage S hQ 1 C n)
    have hterminal :
        ((ConfiguredCorrelatedConstructionCoreProvider.baseCorrelated
          S hQ C hH khRow Qmax source).column.step.richStage n).terminalBase =
          RichStageDataPhaseRigidTransport.move A.translation A.rotation
            (rearPhase S hQ A) (S.carrier n).data := by
      calc
        _ = R.terminalBase := by rfl
        _ = _ := hR.1
    rw [hterminal]
    have htube := MarkedRigid.isTubeMember_rigidData (a := A.translation) A.rotation_norm
      (MarkedShift.isTubeMember_shiftData (S.carrier n).tube (rearPhase S hQ A))
    change 0 ≤ ((starRingEnd ℂ)
      ((RichStageDataPhaseRigidTransport.move A.translation A.rotation
        (rearPhase S hQ A) (S.carrier n).data).2.1 u) *
      (RichStageDataPhaseRigidTransport.move A.translation A.rotation
        (rearPhase S hQ A) (S.carrier n).data).2.2 u).im
    simpa [RichStageDataPhaseRigidTransport.move] using htube.curv_lb u

end ConfiguredCorrelatedBaseColumnCap
