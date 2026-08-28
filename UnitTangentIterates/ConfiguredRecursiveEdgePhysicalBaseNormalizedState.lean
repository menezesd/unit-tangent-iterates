import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalBaseNormalizedSourceFacts
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalBaseIntrinsicFunctional
import UnitTangentIterates.ConfiguredRecursiveEdgeGaugeMajorantShift
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedNormalizedReachableState
import UnitTangentIterates.ConfiguredRecursiveEdgeRearPeriodFloor

/-! # Row-local normalized state for the configured physical base -/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePhysicalBaseNormalizedState

open ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgePhysicalBaseNormalizedSourceFacts
  ConfiguredRecursiveEdgePhysicalCompositionBase
  ConfiguredRecursiveEdgePhysicalFiniteColumnBase
  ConfiguredRecursiveEdgeRecostedReachableFacts
  ConfiguredRecursiveEdgeRecostedRawDiagonalBase
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0Growth
  FiniteSmoothRearFamilyMarkingAwareSource

variable {MA NA K0 K1 K2 Etotal Dtarget : ℝ}
  {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}

private theorem transportOutput_eta_continuous
    {D0 : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data} {n : ℕ}
    {A : ConfiguredApproximateDefectPathActualTerminal.RearCarrier D0 n}
    (W : ConfiguredApproximateDefectPathActualTerminal.Output D0 Q n A)
    {bound c C dlt : ℝ} (hbound : NormalPath.cost W.increment ≤ bound)
    (phase : ℝ) (frontOut : Data) (a w : ℂ) (hw : ‖w‖ = 1)
    (hRange : VariableMarkedTube.GeometricUnitTangentRangeEdge
      frontOut (RichStageDataPhaseRigidTransport.move a w phase W.rear))
    (hHarnack : VariableMarkedTube.ArclengthHarnackCertificate
      (RichStageDataPhaseRigidTransport.move a w phase W.rear)) :
    Continuous (uncurry
      (RichStageDataPhaseRigidTransport.transportOutput
        (c := c) (C := C) (dlt := dlt) W hbound phase frontOut a w hw
          hRange hHarnack).stage.increment.eta) := by
  have H : Continuous (fun p : ℝ × ℝ =>
      W.increment.eta p.1 (p.2 + phase)) :=
    W.increment_eta_cont.comp
      (continuous_fst.prodMk (continuous_snd.add continuous_const))
  simpa [RichStageDataPhaseRigidTransport.transportOutput,
    RichStageDataPhaseRigidTransport.transport,
    NormalPathC2IncrementVariableSpeed.rigidPath,
    MarkedRigid.NormalPathRigid.rigidPathOf, MarkedShift.shiftPath,
    MarkedShift.shiftPathOf] using H

/-- Functional regularity of the exact displayed base path. -/
def stageFunctional (J :
    ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (n : ℕ) :
    ControlledJunctionPathFunctionalBounds.FunctionalIntegrable
      (stage (K0 := K0) (K1 := K1) (K2 := K2) J n).Gamma.eta := by
  have H :=
    (ConfiguredGaugeFirstPhysicalSequence.richStage_spec
      J.scalar.pair.input J.scalar.model_data 1 (rowC J.scalar) (n + 1)).2.2
  simpa [stage, unaryStage,
    ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.stage,
    ConfiguredRecursiveEdgePhysicalGeometricBase.base,
    compositionBaseCorrelated, baseCorrelated,
    ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseCorrelated,
    ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseProvider,
    ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseColumnStep] using H

/-- Joint continuity of the density on the exact displayed base path. -/
theorem stageEtaContinuous (J :
    ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    (n : ℕ) :
    Continuous (uncurry
      (stage (K0 := K0) (K1 := K1) (K2 := K2) J n).Gamma.eta) := by
  change Continuous (uncurry
    (ConfiguredGaugeFirstPhysicalSequence.richStage J.scalar.pair.input
      J.scalar.model_data 1 (rowC J.scalar) (n + 1)).stage.increment.eta)
  unfold ConfiguredGaugeFirstPhysicalSequence.richStage
    ConfiguredGaugeFirstPhysicalSequence.richStagePackage
  dsimp only
  apply transportOutput_eta_continuous
  /-
  simpa [stage, unaryStage,
    ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.stage,
    ConfiguredRecursiveEdgePhysicalGeometricBase.base,
    compositionBaseCorrelated_path, baseCorrelated_path,
    ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.sourcePath] using
    (edgeOutput J.scalar (n + 1)).increment_eta_cont
  -/

/-- Complete source-side facts at local row zero after shifting the gauge
output to row `n`. -/
def sourceFacts
    (O : Output J Etotal Dtarget) (hDtarget : 0 ≤ Dtarget) (n : ℕ) :
    let Orow := O.shiftOutput n
    let q := Orow.N
    let S := stage (K0 := K0) (K1 := K1) (K2 := K2) J q
    SourceFacts Orow S.source (edgeP1 (D J.scalar) MA q) 0 := by
  dsimp only
  let Orow := O.shiftOutput n
  let q := Orow.N
  let S := stage (K0 := K0) (K1 := K1) (K2 := K2) J q
  refine
    { slice := slice (K0 := K0) (K1 := K1) (K2 := K2) J q
      periodUpper_le := ?_
      functional := stageFunctional (K0 := K0) (K1 := K1) (K2 := K2) J q
      eps := stageEps (K0 := K0) (K1 := K1) (K2 := K2) J q
      jets := stageSourceJets (K0 := K0) (K1 := K1) (K2 := K2) J q
      eps_le_major := ?_ }
  · simpa [S] using
      (ConfiguredRecursiveEdgePhysicalGeometricBase.invariant J
        (K0 := K0) (K1 := K1) (K2 := K2)).periodUpper_le q
  · simpa [Orow, q] using
      (stageEps_le_major (K0 := K0) (K1 := K1) (K2 := K2)
        Orow hDtarget 0)

/-- Callback-free normalized state at local depth zero of row `n`.  The
geometric stage index is the exact tail-shifted index `(O.shiftOutput n).N`. -/
def baseState
    (O : Output J Etotal Dtarget) (hDtarget : 0 ≤ Dtarget)
    (hEtotal : Etotal ≤ 1 / 8) (n : ℕ) :
    let Orow := O.shiftOutput n
    let q := Orow.N
    let S := stage (K0 := K0) (K1 := K1) (K2 := K2) J q
    ConfiguredRecursiveEdgeRecostedNormalizedReachableState.State Orow S.asUnary
      (edgeP1 (D J.scalar) MA q) 0
      (edgePhysicalDefect (D J.scalar) (q + 1)) := by
  dsimp only
  let Orow := O.shiftOutput n
  let q := Orow.N
  let S := stage (K0 := K0) (K1 := K1) (K2 := K2) J q
  let SF := sourceFacts (K0 := K0) (K1 := K1) (K2 := K2)
    O hDtarget n
  let IF :=
    ConfiguredRecursiveEdgePhysicalBaseIntrinsicFunctional.stageIntrinsicFrontFunctionalFacts
      (K0 := K0) (K1 := K1) (K2 := K2) J q
  have heps : SF.eps ≤ 1 / 4 := by
    have hmajor : Orow.major 0 ≤ ∑' i, Orow.major i :=
      Orow.major_summable'.le_tsum 0
        (fun i _ => Orow.major_nonnegative' i)
    have H := SF.eps_le_major.trans (hmajor.trans Orow.major_tsum_le')
    linarith
  have hweighted : IntervalIntegrable (fun t =>
      S.source.P t * ∫ u in (0 : ℝ)..1,
        |S.source.etaF t (S.source.P t * u)|) volume 0 1 := by
    have H := IF.functional.w.const_mul
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.period J.scalar
        (q + 1) 0)
    simpa [FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink.intrinsicFront,
      S, stage, unaryStage,
      ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.stage,
      ConfiguredRecursiveEdgePhysicalGeometricBase.base,
      ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated_source,
      ConfiguredRecursiveEdgePhysicalCompositionBase.baseSource,
      ConfiguredRecursiveEdgeBaseFullyPhysicalComponentInitial.physicalBaseSource_period_eq]
      using H
  have hjac : IntervalIntegrable (fun t => ∫ u in (0 : ℝ)..1,
      S.source.phi1 t u * |S.Gamma.eta t u|) volume 0 1 :=
    FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW.source_jacobianPhysicalW_integrable
      SF.nonaffine hweighted
  let B := ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated J
    (K0 := K0) (K1 := K1) (K2 := K2)
  have Fbase : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable
      (B.column.step.richStage (q + 1)).stage.increment.eta := by
    simpa [S, B, stage, unaryStage,
      ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.stage,
      ConfiguredRecursiveEdgePhysicalGeometricBase.base,
      compositionBaseCorrelated_path] using
      (stageFunctional (K0 := K0) (K1 := K1) (K2 := K2) J q)
  have hetabase : ∀ t, Continuous
      ((B.column.step.richStage (q + 1)).stage.increment.eta t) := by
    intro t
    have H : Continuous (fun u : ℝ =>
        (stage (K0 := K0) (K1 := K1) (K2 := K2) J q).Gamma.eta t u) :=
      (stageEtaContinuous
        (K0 := K0) (K1 := K1) (K2 := K2) J q).comp
        ((continuous_const : Continuous (fun _ : ℝ => t)).prodMk continuous_id)
    simpa [S, B, stage, unaryStage,
      ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.stage,
      ConfiguredRecursiveEdgePhysicalGeometricBase.base,
      compositionBaseCorrelated_path] using H
  have hjacbase : IntervalIntegrable (fun t => ∫ u in (0 : ℝ)..1,
      (B.source q).phi1 t u *
        |(B.column.step.richStage (q + 1)).stage.increment.eta t u|)
      volume 0 1 := by
    simpa [S, B, stage, unaryStage,
      ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.stage,
      ConfiguredRecursiveEdgePhysicalGeometricBase.base,
      compositionBaseCorrelated_source, compositionBaseCorrelated_path] using hjac
  let raw := ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints.configuredBaseAncestry
    (K0 := K0) (K1 := K1) (K2 := K2) Orow J q SF.eps SF.jets heps
      Fbase hetabase hjacbase
  let concrete :
      ConfiguredRecursiveEdgeNonaffineChosenMajorEndpoints.ConcreteAncestry
        (O := Orow) (B.column.step.richStage (q + 1)).stage.increment 0
          (edgePhysicalDefect (D J.scalar) (q + 1)) :=
    { ancestry := raw
      terminalJ := raw.baseJ
      terminalP := raw.baseP
      terminal_eq := raw.base_eq }
  refine
    { sourceFacts := SF
      intrinsic := IF
      periodFloor := ConfiguredRecursiveEdgeRearPeriodFloor.one_le_rearPeriod
      ancestry := ?_
      terminalJ_eq := ?_
      terminalP_eq := ?_ }
  · simpa [S, B, stage, unaryStage,
      ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.stage,
      ConfiguredRecursiveEdgePhysicalGeometricBase.base,
      compositionBaseCorrelated_path] using concrete
  · rfl
  · rfl

end ConfiguredRecursiveEdgePhysicalBaseNormalizedState
