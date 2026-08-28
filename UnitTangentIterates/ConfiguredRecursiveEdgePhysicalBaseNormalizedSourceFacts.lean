import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRawDiagonalBase
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalFiniteColumnSourceMass
import UnitTangentIterates.ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
import UnitTangentIterates.ConfiguredRecursiveEdgeBaseFullyPhysicalComponentInitial
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSourceNormalizedFlowJets

/-! # Normalized source facts for the configured physical base row -/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric FlowDerivative

namespace ConfiguredRecursiveEdgePhysicalBaseNormalizedSourceFacts

open ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily
  ConfiguredBaseProfiledEdgeInitialGaugeRecursiveAnalyticSuccessorFamily
  ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredApproximateDefectPathActualTerminal
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgePhysicalCompositionBase
  ConfiguredRecursiveEdgePhysicalFiniteColumnBase
  ConfiguredRecursiveEdgePhysicalFiniteColumnSourceMass
  ConfiguredRecursiveEdgeRecostedRawDiagonalBase
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveSourceP0RowJetTail
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSourceNormalizedFlowJets
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction
  GaugeMarkedDataOfRearFamily GaugeTerminalNearIdentityJets
  ProfiledInterpolationFields
  CurvatureInterpolation

variable {MA NA K0 K1 K2 Etotal Dtarget : ℝ}

private theorem sourceKh_le_rearKappa1 :
    sourceKh ≤ rearKappa1 sourceKh := by
  norm_num [sourceKh_eq, rearKappa1]

/-- The untransported configured edge source has the exact interpolation
flow as its marking first jet. -/
private theorem edgeSource_phi1_eq_flowDeriv
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) (q0 t u : ℝ) :
    (edgeSourceAt O n q0).phi1 t u = flowDeriv
      (hx (sourceK0 (data O) (n + 1)) (sourceK1 (data O) (n + 1))
        (data O).model.thetaBase ((data O).Hs (n + 1)))
      (PhiB (edgeOutput O (n + 1)).sourcePhi)
      ((edgeSourceAt O n q0).P 0) t u := by
  let W := edgeOutput O (n + 1)
  have hflow := hasDerivAt_flow_initial
    W.sourceBounds.hlip W.sourceCertificate.field_cont
    W.sourceCertificate.field_flow
    (mul_pos (by norm_num) ((data O).model.separation_pos (n + 1)))
    W.sourceCertificate.phi_initial W.sourceCertificate.field_space u t
  have heq := (W.sourcePhi_space (PathMetricCircle.B t) u).unique
    (by simpa [PhiB] using hflow)
  have hperiod : (edgeSourceAt O n q0).P 0 = 2 * (data O).Hs (n + 1) := by
    rw [edgeSourceAt_period_eq]
    rfl
  rw [hperiod]
  simpa [edgeSourceAt, ConfiguredBaseProfiledInitialGaugeResidual.baseSource,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
    ConfiguredBaseProfiledInitialGaugeResidual.residual,
    ConfiguredBaseProfiledInitialGaugeResidual.geom,
    ConfiguredBaseProfiledSelectedRearGaugeReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearReanchoring.phi1,
    ConfiguredBaseInterpolationMarkingSource.phi1, W] using heq

private theorem interpolation_rate_le_source
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) (q0 t x : ℝ) :
    |hx (sourceK0 (data O) (n + 1)) (sourceK1 (data O) (n + 1))
        (data O).model.thetaBase ((data O).Hs (n + 1)) t x| ≤
      rearKappa1 sourceKh * (edgeSourceAt O n q0).m t := by
  let W := edgeOutput O (n + 1)
  let U := edgeSourceAt O n q0
  have ha := B_mem_Icc t
  have hk0 : 0 ≤ sourceK0 (data O) (n + 1) x := by
    rw [sourceK0, ← (data O).model.curvature_eq (n + 1)]
    exact (sourceCertificate O).front_nonnegative (n + 1) x
  have hk0le : sourceK0 (data O) (n + 1) x ≤ sourceKh := by
    rw [sourceK0, ← (data O).model.curvature_eq (n + 1)]
    exact (sourceCertificate O).front_le (n + 1) x
  have hk1 : 0 ≤ sourceK1 (data O) (n + 1) x :=
    (sourceCertificate O).rear_nonnegative (n + 1) x
  have hk1le : sourceK1 (data O) (n + 1) x ≤ sourceKh :=
    (sourceCertificate O).rear_le (n + 1) x
  have hkappa0 : 0 ≤ kappa
      (sourceK0 (data O) (n + 1)) (sourceK1 (data O) (n + 1)) t x := by
    dsimp [kappa, kappaInterp]
    exact add_nonneg (mul_nonneg (by linarith [ha.1, ha.2]) hk0)
      (mul_nonneg ha.1 hk1)
  have hkappa : |kappa
      (sourceK0 (data O) (n + 1)) (sourceK1 (data O) (n + 1)) t x| ≤
      sourceKh := by
    rw [abs_of_nonneg hkappa0]
    dsimp [kappa, kappaInterp]
    calc
      (1 - PathMetricCircle.B t) * sourceK0 (data O) (n + 1) x +
          PathMetricCircle.B t * sourceK1 (data O) (n + 1) x ≤
          (1 - PathMetricCircle.B t) * sourceKh +
            PathMetricCircle.B t * sourceKh :=
        add_le_add
          (mul_le_mul_of_nonneg_left hk0le (by linarith [ha.1, ha.2]))
          (mul_le_mul_of_nonneg_left hk1le ha.1)
      _ = sourceKh := by ring
  have hcont : Continuous (PhiB W.sourcePhi t) :=
    W.sourcePhi_joint.comp (continuous_const.prodMk continuous_id)
  have hsurj : Surjective (PhiB W.sourcePhi t) :=
    surjective_of_continuous_quasiPeriodic
      (mul_pos (by norm_num) ((data O).model.separation_pos (n + 1)))
      hcont (W.sourceCertificate.phi_translation t)
  obtain ⟨u, hu⟩ := hsurj x
  have hen : |en (sourceK0 (data O) (n + 1))
      (sourceK1 (data O) (n + 1)) (data O).model.thetaBase
      ((data O).Hs (n + 1)) t x| ≤ W.increment.m t := by
    rw [← hu]
    simpa [ConfiguredBaseProfiledEdgeSourceFamily.data, W.source_eta_eq,
      InterpolationPathDist.pathEta, InterpolationPathDist.scaledEta,
      en, PhiB, abs_mul] using
      W.increment.abs_eta_le t u
  have hraw : |hx (sourceK0 (data O) (n + 1))
      (sourceK1 (data O) (n + 1)) (data O).model.thetaBase
      ((data O).Hs (n + 1)) t x| ≤ sourceKh * W.increment.m t :=
    abs_hx_le hkappa hen sourceKh_nonnegative (W.increment.m_nonneg t)
  have hsqrt : 0 < Real.sqrt (1 - sourceKh ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [sourceKh_nonnegative, sourceKh_lt_one])
  have hsqrt_le : Real.sqrt (1 - sourceKh ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith [sourceKh_nonnegative]
  have hmU : W.increment.m t ≤ U.m t := by
    have hdiv : W.increment.m t ≤
        W.increment.m t / Real.sqrt (1 - sourceKh ^ 2) := by
      rw [le_div_iff₀ hsqrt]
      exact mul_le_of_le_one_right (W.increment.m_nonneg t) hsqrt_le
    exact hdiv.trans (U.density_domination t)
  exact hraw.trans <| calc
    sourceKh * W.increment.m t ≤ sourceKh * U.m t :=
      mul_le_mul_of_nonneg_left hmU sourceKh_nonnegative
    _ ≤ rearKappa1 sourceKh * U.m t :=
      mul_le_mul_of_nonneg_right sourceKh_le_rearKappa1
        (U.density_nonnegative t)

/-- Exact all-time normalized marking jets on the configured physical base
source, before comparison with the scalar major. -/
def stageSourceJets
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (n : ℕ) :
    let A := (stage (K0 := K0) (K1 := K1) (K2 := K2) J n).source
    SourceNormalizedJetBounds A
      (jetLinearConst (A.P 0) 1 (rearKappa1 sourceKh) (rearKappa2 sourceKh)
        J.scalar.Mend * sourceMass A) := by
  let O := J.scalar
  let q0 := ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.initialRearPhase O n
  let U := edgeSourceAt O n q0
  let W := edgeOutput O (n + 1)
  have hmassStage : sourceMass
      ((stage (K0 := K0) (K1 := K1) (K2 := K2) J n).source) ≤ 1 :=
    (ConfiguredRecursiveEdgePhysicalFiniteColumnSourceMass.sourceMass_le_compositionPhysicalDefect
      J (K0 := K0) (K1 := K1) (K2 := K2) n).trans
      (J.composition_mass_one (n + 1))
  have hmassU : sourceMass U ≤ J.scalar.Mend := by
    have hUeq : sourceMass U = sourceMass
        ((stage (K0 := K0) (K1 := K1) (K2 := K2) J n).source) := by
      simp [U, stage, unaryStage,
        ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.stage,
        ConfiguredRecursiveEdgePhysicalGeometricBase.base,
        ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated_source,
        ConfiguredRecursiveEdgePhysicalCompositionBase.baseSource,
        ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.source,
        ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput,
        q0, sourceMass]
      rw [W.increment_time_one,
        ConfiguredRecursiveEdgePhysicalTerminalPhaseLink.source_path_time_one]
    rw [hUeq]
    exact hmassStage.trans J.one_le_Mend
  have hPone : ∀ t, 1 ≤ U.P t := by
    intro t
    rw [edgeSourceAt_period_eq]
    change 1 ≤ 2 * (data O).Hs (n + 1)
    have hH := O.large.separation_one.trans ((data O).separation_lower (n + 1))
    linarith
  let Phi := PhiB W.sourcePhi
  let hx0 := hx (sourceK0 (data O) (n + 1)) (sourceK1 (data O) (n + 1))
    (data O).model.thetaBase ((data O).Hs (n + 1))
  have JU : SourceNormalizedJetBounds U
      (jetLinearConst (U.P 0) 1 (rearKappa1 sourceKh) (rearKappa2 sourceKh)
        J.scalar.Mend * sourceMass U) :=
    sourceNormalizedJetBounds_of_flow U W.increment_time_one hPone Phi hx0
      (edgeSource_phi1_eq_flowDeriv O n q0)
      (fun t => by
        dsimp [Phi]
        have h := W.sourceCertificate.phi_translation t 0
        rw [show (1 : ℝ) = 0 + 1 by norm_num, h]
        rw [edgeSourceAt_period_eq]
        simp [ConfiguredBaseInterpolationShiftedFront.period])
      (fun t u => by
        dsimp [Phi, hx0]
        have hU0 : U.P 0 = 2 * (data O).Hs (n + 1) := by
          rw [edgeSourceAt_period_eq]
          rfl
        simpa [ConfiguredBaseProfiledEdgeSourceFamily.data, PhiB, hU0] using
          (hasDerivAt_flow_initial
            W.sourceBounds.hlip W.sourceCertificate.field_cont
            W.sourceCertificate.field_flow
            (mul_pos (by norm_num) ((data O).model.separation_pos (n + 1)))
            W.sourceCertificate.phi_initial W.sourceCertificate.field_space u t))
      (interpolation_rate_le_source O n q0) J.scalar.Mend hmassU
  let A := ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.presentation O n
  have JV := phaseRigid U JU A.phase A.translation A.rotation A.rotation_norm
  have JP := physicalRigidFields _ JV A.translation A.rotation A.rotation_norm
  simpa [stage, unaryStage,
    ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.stage,
    ConfiguredRecursiveEdgePhysicalGeometricBase.base,
    ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated_source,
    ConfiguredRecursiveEdgePhysicalCompositionBase.baseSource,
    ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.source,
    ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput,
    U, q0, A, sourceMass] using JP

/-- The exact normalized marking error carried by the configured base stage. -/
def stageEps
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (n : ℕ) : ℝ :=
  let A := (stage (K0 := K0) (K1 := K1) (K2 := K2) J n).source
  jetLinearConst (A.P 0) 1 (rearKappa1 sourceKh) (rearKappa2 sourceKh)
    J.scalar.Mend * sourceMass A

def shiftedStageSourceJets
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    {Etotal Dtarget : ℝ}
    (O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output
      J Etotal Dtarget)
    (n : ℕ) :
    let A := (stage (K0 := K0) (K1 := K1) (K2 := K2) J (O.N + n)).source
    SourceNormalizedJetBounds A
      (stageEps (K0 := K0) (K1 := K1) (K2 := K2) J (O.N + n)) := by
  simpa [stageEps] using
    (stageSourceJets (K0 := K0) (K1 := K1) (K2 := K2) J (O.N + n))

theorem stageEps_nonnegative
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (n : ℕ) :
    0 ≤ stageEps (K0 := K0) (K1 := K1) (K2 := K2) J n :=
  (stageSourceJets (K0 := K0) (K1 := K1) (K2 := K2) J n).eps_nonnegative

/-- After the scalar tail shift `O.N`, row `n` of the truthful base column is
controlled by row `n` of the shifted gauge majorant. -/
theorem stageEps_le_major
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
    {Etotal Dtarget : ℝ}
    (O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output
      J Etotal Dtarget)
    (hDtarget : 0 ≤ Dtarget) (n : ℕ) :
    stageEps (K0 := K0) (K1 := K1) (K2 := K2) J (O.N + n) ≤
      O.major n := by
  let q := O.N + n
  let A := (stage (K0 := K0) (K1 := K1) (K2 := K2) J q).source
  have hP : A.P 0 = 2 * (D J.scalar).Hs (q + 1) := by
    simpa [A, stage, unaryStage,
      ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.stage,
      ConfiguredRecursiveEdgePhysicalGeometricBase.base,
      ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated_source,
      ConfiguredRecursiveEdgePhysicalCompositionBase.baseSource,
      ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D,
      ConfiguredRecursiveEdgeSourceP0CappedRowProduction.period] using
      congrFun
        (ConfiguredRecursiveEdgeBaseFullyPhysicalComponentInitial.physicalBaseSource_period_eq
          (K0 := K0) (K1 := K1) (K2 := K2) J q) 0
  have hell0 : 0 ≤ A.P 0 := by
    rw [hP]
    exact mul_nonneg (by norm_num) ((D J.scalar).model.separation_pos (q + 1)).le
  have hell : A.P 0 ≤ ellCap O.data (n + 1) := by
    rw [hP]
    unfold ellCap ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data
    simp only [ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
      ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D]
    have hsep := (D J.scalar).model.separation_pos (q + 1)
    change 2 * (D J.scalar).Hs (q + 1) ≤
      3 * (1 + (D J.scalar).Hs (O.N + (n + 1)))
    rw [show O.N + (n + 1) = q + 1 by simp [q, Nat.add_assoc]]
    linarith
  have hcoeff : jetLinearConst (A.P 0) 1
      (rearKappa1 sourceKh) (rearKappa2 sourceKh) J.scalar.Mend ≤
      rowJetCoeff O.data J.scalar.Mend (n + 1) :=
    jetLinearConst_le_rowJetCoeff O.data J.scalar.Mend (n + 1)
      hell0 hell (by norm_num)
  have hmass : sourceMass A ≤
      edgeCompositionPhysicalDefect O.data (n + 1) := by
    have H :=
      ConfiguredRecursiveEdgePhysicalFiniteColumnSourceMass.sourceMass_le_compositionPhysicalDefect
        J (K0 := K0) (K1 := K1) (K2 := K2) q
    simpa [A, q, stage, unaryStage,
      ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.stage,
      ConfiguredRecursiveEdgePhysicalGeometricBase.base,
      ConfiguredRecursiveEdgePhysicalFiniteColumnBase.column,
      ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data,
      ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D,
      edgeCompositionPhysicalDefect, edgeCompositionPhysicalCoeff,
      physicalDefect, physicalCoeff, Nat.add_assoc] using H
  have hrow : 0 ≤ rowJetCoeff O.data J.scalar.Mend (n + 1) :=
    rowJetCoeff_nonnegative O.data J.scalar.Mend (n + 1)
  calc
    stageEps (K0 := K0) (K1 := K1) (K2 := K2) J q =
        jetLinearConst (A.P 0) 1 (rearKappa1 sourceKh)
          (rearKappa2 sourceKh) J.scalar.Mend * sourceMass A := rfl
    _ ≤ rowJetCoeff O.data J.scalar.Mend (n + 1) *
        edgeCompositionPhysicalDefect O.data (n + 1) :=
      mul_le_mul hcoeff hmass
        (FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear.sourceMass_nonnegative A)
        hrow
    _ = baseGaugeMajor O.data J.scalar.Mend n := rfl
    _ ≤ O.major n := by
      rw [ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.major,
        combinedGaugeMajor]
      exact le_add_of_nonneg_right
        (gaugeMajor_nonnegative O.data J.scalar.Mend Dtarget hDtarget n)

end ConfiguredRecursiveEdgePhysicalBaseNormalizedSourceFacts
