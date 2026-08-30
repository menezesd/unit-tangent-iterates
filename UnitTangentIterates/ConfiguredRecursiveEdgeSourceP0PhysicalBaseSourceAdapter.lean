import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter
import UnitTangentIterates.ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily
import UnitTangentIterates.MarkingAwareSourcePhysicalRigidTransport
import UnitTangentIterates.ConfiguredBaseProfiledEdgeInitialGaugeRecursiveAnalyticSuccessorFamily
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessorTransport
import UnitTangentIterates.PhysicalRearLimitKinematicClosure
import UnitTangentIterates.SelectedInverseUnique
import UnitTangentIterates.ConfiguredAlignedQGeometry

/-! # Physically normalized exact edge source for the base column -/

noncomputable section

open MarkedSpace PathMetric RearOwnArclength RearTrack

namespace ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter

open ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeSourceP0
  FiniteSmoothRearFamilyMarkingAwareSource

variable {MA NA : ℝ}

def sourcePath
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :=
  ((ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseProvider
    O.pair.input O.model_data C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) O.large.separation_one
      (kstar_le_analyticKhat (data O))).base.step.richStage (n + 1)).stage.increment

def presentation
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :=
  ConfiguredGaugeFirstPhysicalSequence.presentations
    O.pair.input O.model_data (n + 1)

/-- Initial rear-arclength coordinate represented by the normalized phase of
the base column. -/
def initialRearPhase
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) : ℝ :=
  rearArclength ((edgeSourceFamily O n).delta 0)
    ((edgeSourceFamily O n).P 0) * (presentation O n).phase

/-- Exact edge source with both its physical rear origin and its Euclidean
presentation aligned to the configured base column. -/
noncomputable def source
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    MarkingAwareSource
      (((ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseProvider
        O.pair.input O.model_data C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) O.large.separation_one
          (kstar_le_analyticKhat (data O))).base.step.richStage
            (n + 1)).stage.increment)
      (edgeSourceP0 (data O) n) sourceKh (analyticKhat (data O))
      (edgeSpeedCap (data O) n) := by
  let A := presentation O n
  let U := edgeSourceAt O n (initialRearPhase O n)
  let V := ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput
    O.pair.input O.model_data C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) O.large.separation_one
      (kstar_le_analyticKhat (data O)) n U
  exact V.physicalRigidFields A.translation A.rotation A.rotation_norm

@[simp] theorem source_kx
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    (source O C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n).kx =
      SelInvFrontStripC2.stripCurvConst sourceKh := by
  simp [source, ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput,
    MarkingAwareSource.physicalRigidFields, MarkingAwareSource.phaseRigid,
    edgeSourceAt, ConfiguredBaseProfiledInitialGaugeResidual.baseSource,
    ConfiguredBaseProfiledInitialGaugeResidual.residual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
    edgeScaledBoundsAt, ConfiguredBaseProfiledInitialGaugeResidual.Bounds.scale,
    edgeBoundsAt, ConfiguredBaseProfiledInitialGaugeResidual.auditedBounds]

@[simp] theorem source_m
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) (t : ℝ) :
    (source O C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n).m t =
      ConfiguredRecursiveEdgeSourceP0Growth.edgeCompositionCoeff
        (data O) (n + 1) *
          (edgeBoundsAt O n (initialRearPhase O n)).m t := by
  simp [source, ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput,
    edgeSourceAt, ConfiguredBaseProfiledInitialGaugeResidual.baseSource,
    ConfiguredBaseProfiledInitialGaugeResidual.residual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
    edgeScaledBoundsAt, ConfiguredBaseProfiledInitialGaugeResidual.Bounds.scale]

@[simp] theorem source_Dd
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) (t : ℝ) :
    (source O C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n).Dd t =
      (edgeBoundsAt O n (initialRearPhase O n)).Dd t := by
  simp [source, ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput,
    edgeSourceAt, ConfiguredBaseProfiledInitialGaugeResidual.baseSource,
    ConfiguredBaseProfiledInitialGaugeResidual.residual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
    edgeScaledBoundsAt, ConfiguredBaseProfiledInitialGaugeResidual.Bounds.scale]

/-- Normalized front shift between the gauge-origin-normalized source and the
displayed configured front.  It is intentionally not identified with the
displayed rear phase. -/
def sourceFrontShift
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) : ℝ :=
  let W := edgeOutput O (n + 1)
  let S := edgeSelected O n
  let G := (edgeReanchoredAt O n (initialRearPhase O n)).gauge
  let A := presentation O n
  (ConfiguredBaseProfiledSelectedRearReanchoring.frontPhase W 0 +
      ConfiguredBaseProfiledSelectedRearGaugeReanchoring.sigma W S G.q 0) /
      (2 * (data O).Hs (n + 1)) - A.phase

/-- The source front is the displayed physical front with the explicit
nonaffine-gauge-induced constant shift above. -/
theorem source_front_zero_eq_shift
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    (source O C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n).F 0 =
      ev (MarkedShift.shiftData (sourceFrontShift O n)
        (presentation O n).data) := by
  funext s
  have htube : IsTubeMember (ConfiguredCanonicalPairSource.commonC (data O)) 0
      (ConfiguredCanonicalPairSource.commonDlt (data O))
      (presentation O n).data := by
    simpa [presentation, ConfiguredGaugeFirstPhysicalSequence.alignedQ,
      ConfiguredGaugeFirstPhysicalSequence.Presentation.data] using
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ_tube O.pair.input
        O.model_data (n + 1))
  have hperim : perim (presentation O n).data =
      2 * (data O).Hs (n + 1) := by
    simpa [presentation, ConfiguredGaugeFirstPhysicalSequence.alignedQ,
      ConfiguredGaugeFirstPhysicalSequence.Presentation.data] using
      (ConfiguredAlignedQGeometry.perim_eq O.pair O.model_data (n + 1))
  have hev (x : ℝ) : ev (presentation O n).data x =
      (presentation O n).translation + (presentation O n).rotation *
        (O.Q (n + 1)).1
          (x / (2 * (data O).Hs (n + 1)) + (presentation O n).phase) := by
    rw [ev, hperim]
    simp [presentation, ConfiguredGaugeFirstPhysicalSequence.Presentation.data,
      RichStageDataPhaseRigidTransport.move, MarkedRigid.rigidData,
      MarkedShift.shiftData, MarkedShift.shiftMap]
  rw [SelectedInverseShiftEquivariance.ev_shiftData htube
    (hperim.trans_gt (mul_pos (by norm_num)
      ((data O).model.separation_pos (n + 1)))).ne']
  rw [hperim]
  rw [hev]
  have hH : 2 * (data O).Hs (n + 1) ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt ((data O).model.separation_pos (n + 1)))
  have hHs : (data O).Hs (n + 1) ≠ 0 :=
    ne_of_gt ((data O).model.separation_pos (n + 1))
  have hw : (presentation O n).rotation ≠ 0 := by
    intro h
    have := (presentation O n).rotation_norm
    rw [h, norm_zero] at this
    norm_num at this
  have hQcurve (u : ℝ) : (O.Q (n + 1)).1 u =
      CurvatureInterpolation.interpCurve
        (ConfiguredApproximateDefectPathActualTerminal.sourceK0
          (data O) (n + 1)) (data O).model.thetaBase
          ((data O).Hs (n + 1)) (2 * (data O).Hs (n + 1) * u) := by
    have h := congrFun (O.model_data (n + 1)).2
      (2 * (data O).Hs (n + 1) * u)
    rw [ev, (O.model_data (n + 1)).1] at h
    have hu : 2 * (data O).Hs (n + 1) * u /
        (2 * (data O).Hs (n + 1)) = u := by
      field_simp [hHs]
    simpa [hu, TwoCapPairsAssembly.front,
      ConfiguredApproximateDefectPathActualTerminal.sourceK0,
      ← (data O).model.curvature_eq (n + 1)] using h
  rw [hQcurve]
  simp [source, sourceFrontShift,
    ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput,
    edgeSourceAt, ConfiguredBaseProfiledInitialGaugeResidual.baseSource,
    ConfiguredBaseProfiledInitialGaugeResidual.residual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
    ConfiguredBaseProfiledSelectedRearGaugeReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearGaugeReanchoring.F,
    ConfiguredBaseProfiledSelectedRearReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearReanchoring.F,
    ConfiguredBaseProfiledSelectedRearReanchoring.rawF,
    MarkingAwareSource.physicalRigidFields, MarkingAwareSource.phaseRigid,
    TimeDependentSpatialReanchoring.shift, ProfiledInterpolationFields.Y,
    CurvatureInterpolation.kappaInterp, hw]
  field_simp [hH, hHs]
  ring_nf

/-- The terminal rear phase selected by the gauge ODE; this replaces the old
independently chosen terminal marking. -/
def terminalRearPhase
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) : ℝ :=
  (edgeReanchoredAt O n (initialRearPhase O n)).gauge.q 1

theorem gauge_initial
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    (edgeReanchoredAt O n (initialRearPhase O n)).gauge.q 0 =
      initialRearPhase O n :=
  edgeGauge_initial O n (initialRearPhase O n)

/-- A time-zero source whose front and physical period agree with a retained
physical selected-rear package has exactly its retained rear curve.  The
marking is forced by uniqueness: first the two front curvatures agree, then
the periodic steering solutions agree, and finally the two arclength inverses
agree. -/
theorem rearOwn_zero_eq_physicalRear
    {p q rear front : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (K : PhysicalRearLimitKinematics kh rear front)
    (hF : A.F 0 = ev front) (hP : A.P 0 = perim front) (x : ℝ) :
    rearOwn A.F A.Theta A.delta A.sf 0 x = ev rear x := by
  let theta := NormalizedSteeringPhysicalRescaling.thetaPhys K.steering
    (perim front) K.theta0
  let delta := NormalizedSteeringPhysicalRescaling.deltaPhys K.steering
    (perim front)
  let kappa := NormalizedSteeringPhysicalRescaling.curvaturePhys K.steering
    (perim front)
  have hPpos : 0 < perim front := by
    rw [← hP]
    exact A.period_pos 0
  have hX (s : ℝ) : HasDerivAt (ev front)
      (Complex.exp (Complex.I * (A.Theta 0 s : ℂ))) s := by
    rw [← hF]
    exact A.front_frenet 0 s
  have htheta (s : ℝ) : HasDerivAt theta (kappa s) s := by
    exact NormalizedSteeringPhysicalRescaling.hasDerivAt_thetaPhys
      K.steering K.curvature_continuous s
  have hkappa : A.K 0 = kappa := by
    funext s
    exact SelectedInverseTube.curvature_unique hX K.front_frenet
      (A.angle_frenet 0) htheta s
  have hdelta : A.delta 0 = delta := by
    have hodeA : ∀ s, HasDerivAt (A.delta 0)
        (kappa s - Real.sin (A.delta 0 s)) s := by
      intro s
      simpa [hkappa] using A.steering 0 s
    have hodeK : ∀ s, HasDerivAt delta
        (kappa s - Real.sin (delta s)) s := by
      exact NormalizedSteeringPhysicalRescaling.hasDerivAt_deltaPhys
        K.steering hPpos
    have harc : Real.arcsin kh ≤ Real.pi / 2 :=
      Real.arcsin_le_pi_div_two kh
    have hneg : -(Real.pi / 2) ≤ (0 : ℝ) :=
      neg_nonpos.mpr (div_nonneg Real.pi_pos.le (by norm_num))
    exact Shadowing.steering_unique hPpos hodeA hodeK
      (by simpa [hP] using A.steering_periodic 0)
      (NormalizedSteeringPhysicalRescaling.deltaPhys_periodic K.steering)
      (fun s ↦ ⟨hneg.trans (A.strip_nonnegative 0 s),
        (A.strip_le 0 s).trans harc⟩)
      (fun s ↦ ⟨by
          have H := NormalizedSteeringPhysicalRescaling.deltaPhys_mem
            K.steering (P := perim front) s
          exact hneg.trans H.1,
        (NormalizedSteeringPhysicalRescaling.deltaPhys_mem
          K.steering (P := perim front) s).2.trans harc⟩)
  have hdeltaC : Continuous (A.delta 0) :=
    A.steering_contDiff.continuous.comp
      (continuous_const.prodMk continuous_id)
  have hmono : StrictMono (rearArclength (A.delta 0)) :=
    RearTrack.strictMono_rearArclength hdeltaC A.kh_lt_one A.kh_nonnegative
      (A.strip_nonnegative 0) (A.strip_le 0)
  have hsf : A.sf 0 = K.sf := by
    funext y
    apply hmono.injective
    rw [A.sf_rightInverse 0 y, hdelta, K.arclength_rightInverse y]
  have hexp (s : ℝ) :
      Complex.exp (Complex.I * (A.Theta 0 s : ℂ)) =
        Complex.exp (Complex.I * (theta s : ℂ)) :=
    (hX s).unique (K.front_frenet s)
  calc
    rearOwn A.F A.Theta A.delta A.sf 0 x =
        RearTrack.rearTrack (ev front) (A.Theta 0) (A.delta 0) (A.sf 0 x) := by
          rw [← hF]
          rfl
    _ = RearTrack.rearTrack (ev front) theta delta (K.sf x) := by
          rw [hdelta, hsf]
          exact SelectedInverseRearOwn.rearTrack_congr_angle hexp _
    _ = ev rear x := (K.rear_track x).symm

/-- Under the same physical identification, the intrinsic selected-rear
period is the perimeter of the retained physical rear. -/
theorem rearPeriod_zero_eq_physicalRear_perim
    {p q rear front : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (K : PhysicalRearLimitKinematics kh rear front)
    (hF : A.F 0 = ev front) (hP : A.P 0 = perim front) :
    FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A 0 =
      perim rear := by
  let theta := NormalizedSteeringPhysicalRescaling.thetaPhys K.steering
    (perim front) K.theta0
  let delta := NormalizedSteeringPhysicalRescaling.deltaPhys K.steering
    (perim front)
  let kappa := NormalizedSteeringPhysicalRescaling.curvaturePhys K.steering
    (perim front)
  have hPpos : 0 < perim front := by
    rw [← hP]
    exact A.period_pos 0
  have hX (s : ℝ) : HasDerivAt (ev front)
      (Complex.exp (Complex.I * (A.Theta 0 s : ℂ))) s := by
    rw [← hF]
    exact A.front_frenet 0 s
  have htheta (s : ℝ) : HasDerivAt theta (kappa s) s := by
    exact NormalizedSteeringPhysicalRescaling.hasDerivAt_thetaPhys
      K.steering K.curvature_continuous s
  have hkappa : A.K 0 = kappa := by
    funext s
    exact SelectedInverseTube.curvature_unique hX K.front_frenet
      (A.angle_frenet 0) htheta s
  have hdelta : A.delta 0 = delta := by
    have hodeA : ∀ s, HasDerivAt (A.delta 0)
        (kappa s - Real.sin (A.delta 0 s)) s := by
      intro s
      simpa [hkappa] using A.steering 0 s
    have hodeK : ∀ s, HasDerivAt delta
        (kappa s - Real.sin (delta s)) s := by
      exact NormalizedSteeringPhysicalRescaling.hasDerivAt_deltaPhys
        K.steering hPpos
    have harc : Real.arcsin kh ≤ Real.pi / 2 :=
      Real.arcsin_le_pi_div_two kh
    have hneg : -(Real.pi / 2) ≤ (0 : ℝ) :=
      neg_nonpos.mpr (div_nonneg Real.pi_pos.le (by norm_num))
    exact Shadowing.steering_unique hPpos hodeA hodeK
      (by simpa [hP] using A.steering_periodic 0)
      (NormalizedSteeringPhysicalRescaling.deltaPhys_periodic K.steering)
      (fun s ↦ ⟨hneg.trans (A.strip_nonnegative 0 s),
        (A.strip_le 0 s).trans harc⟩)
      (fun s ↦ ⟨by
          have H := NormalizedSteeringPhysicalRescaling.deltaPhys_mem
            K.steering (P := perim front) s
          exact hneg.trans H.1,
        (NormalizedSteeringPhysicalRescaling.deltaPhys_mem
          K.steering (P := perim front) s).2.trans harc⟩)
  change rearArclength (A.delta 0) (A.P 0) = perim rear
  rw [hdelta, hP, K.rear_perimeter]

/-- The complete recursive source package in the configured physical base
column.  The gauge initial value is proved directly, then the path phase and
physical fields are transported together; no equality with the canonical
gauge phase is used. -/
noncomputable def recursiveAnalyticSuccessor
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor.RecursiveAnalyticSuccessor
      (sourcePath O C (MA0 := MA0) (NA0 := NA0)
        (K0 := K0) (K1 := K1) (K2 := K2) n)
      (source O C (MA0 := MA0) (NA0 := NA0)
        (K0 := K0) (K1 := K1) (K2 := K2) n)
      (edgeSourceP0 (data O) n) sourceKh (analyticKhat (data O))
      (edgeSpeedCap (data O) n) := by
  let A := presentation O n
  let X :=
    ConfiguredBaseProfiledEdgeInitialGaugeRecursiveAnalyticSuccessorFamily.recursiveAnalyticSuccessorAt
      O n (initialRearPhase O n)
  let R :=
    FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessorTransport.RecursiveAnalyticSuccessor.phasePhysicalRigid
      X A.phase A.translation A.rotation A.rotation_norm
  let Z := R.rebase (source O C (MA0 := MA0) (NA0 := NA0)
    (K0 := K0) (K1 := K1) (K2 := K2) n)
  simpa [sourcePath, source, presentation,
    ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput,
    ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseProvider,
    ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseColumnStep,
    ConfiguredRecursiveSourceP0ConstructionCoreProvider.lowerRichStageP0,
    ConfiguredGaugeFirstPhysicalSequence.richStage,
    ConfiguredGaugeFirstPhysicalSequence.richStagePackage,
    TriangularMarkedRecursiveChoiceVariableTerminalConstructor.RichStageData.monoAnalytic,
    RichStageDataPhaseRigidTransport.transportOutput, A, X, R, Z] using Z

@[simp] theorem recursiveAnalyticSuccessor_source
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    (recursiveAnalyticSuccessor O C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n).source =
      source O C (MA0 := MA0) (NA0 := NA0)
        (K0 := K0) (K1 := K1) (K2 := K2) n := by
  simp [recursiveAnalyticSuccessor, source, presentation,
    ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput,
    ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseProvider,
    ConfiguredRecursiveEdgeSourceP0ConstructionCoreProvider.baseColumnStep,
    ConfiguredRecursiveSourceP0ConstructionCoreProvider.lowerRichStageP0,
    ConfiguredGaugeFirstPhysicalSequence.richStage,
    ConfiguredGaugeFirstPhysicalSequence.richStagePackage,
    TriangularMarkedRecursiveChoiceVariableTerminalConstructor.RichStageData.monoAnalytic,
    RichStageDataPhaseRigidTransport.transportOutput,
    FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessorTransport.RecursiveAnalyticSuccessor.phasePhysicalRigid,
    FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor.RecursiveAnalyticSuccessor.rebase,
    ConfiguredBaseProfiledEdgeInitialGaugeRecursiveAnalyticSuccessorFamily.recursiveAnalyticSuccessorAt,
    FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor.RecursiveAnalyticSuccessor.ofExact]

end ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter
