import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedCurvature
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierRowBudget
import UnitTangentIterates.ConfiguredFiniteBasePhysicalRearCertificate
import UnitTangentIterates.MarkingAwareSourceSelectedInverseCertificate
import UnitTangentIterates.ReachableVariableSpeedFrontCurvatureIntrinsicStable

/-!
# Intrinsic curvature discharge for prepared successors

This module supplies the model facts needed by the intrinsic curvature
estimate.  It deliberately uses no raw-coordinate curvature evolution or
compact-component callback: the configured half-curvature carrier, coherent
marked distance, source-mass tail, and exact stopping are sufficient.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFinitePreparedIntrinsicCurvature

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredRecursiveEdgeFiniteColumnScalarClosing
  ConfiguredRecursiveEdgeRecostFinitePreparedCurvature
  ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostMultiplierRowBudget
  CurvatureInterpolation
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareSource
  VariableMarkedTube

private theorem carrier_curve_deriv
    {D : ConstructedConfiguredSequenceWeighted.Data} {n : ℕ}
    (A : RearCarrier D n) (s : ℝ) :
    HasDerivAt (ev A.data)
      (Complex.exp (Complex.I *
        (tangentAngle (D.model.configs n).kH D.model.thetaBase s : ℂ))) s := by
  rw [A.curve_eq]
  simpa [SelectedInverseCarrier.tau_eq_exp] using
    (hasDerivAt_interpCurve
      (kappa := (D.model.configs n).kH)
      (θ₀ := D.model.thetaBase) (L := D.Hs n)
      (D.model.configs n).continuous_kH s)

private theorem carrier_angle_deriv
    {D : ConstructedConfiguredSequenceWeighted.Data} (n : ℕ) (s : ℝ) :
    HasDerivAt
      (tangentAngle (D.model.configs n).kH D.model.thetaBase)
      ((D.model.configs n).kH s) s :=
  hasDerivAt_tangentAngle (D.model.configs n).continuous_kH s

private theorem carrier_arcCurv_eq
    {D : ConstructedConfiguredSequenceWeighted.Data} {n : ℕ}
    (A : RearCarrier D n) (s : ℝ) :
    UnconditionalAssembly.arcCurv A.data s =
      (D.model.configs n).kH s := by
  symm
  exact RearTrackEmbedded.curvature_eq_arcCurv
    A.c_pos A.tube (carrier_curve_deriv A)
      (carrier_angle_deriv (D := D) n) s

private theorem carrier_dataCurv_eq
    {D : ConstructedConfiguredSequenceWeighted.Data} {n : ℕ}
    (A : RearCarrier D n) (u : ℝ) :
    CurvatureFromMarkedDistance.dataCurv A.data u =
      (D.model.configs n).kH ((2 * D.Hs n) * u) := by
  have h := carrier_arcCurv_eq A ((2 * D.Hs n) * u)
  have hH : 0 < D.Hs n := D.model.separation_pos n
  have hdiv : (2 * D.Hs n * u) / (2 * D.Hs n) = u := by
    field_simp
  simpa [UnconditionalAssembly.arcCurv, A.perim_eq, hdiv] using h

private theorem rearCarrier_acceleration_le_actual
    {D : ConstructedConfiguredSequenceWeighted.Data} {n : ℕ}
    (C : ConfiguredActualSubunitCurvature.Certificate D)
    (A : RearCarrier D n) (u : ℝ) :
    ‖A.data.2.2 u‖ ≤ (2 * D.Hs n) ^ 2 * C.k0 := by
  have hv : 0 < ‖A.data.2.1 u‖ :=
    lt_of_lt_of_le A.c_pos (A.tube.speed_lb u)
  have hk := C.rear_le n ((2 * D.Hs n) * u)
  rw [CurvatureFromMarkedDistance.norm_acc_eq A.tube hv,
    carrier_dataCurv_eq A u,
    abs_of_nonneg ((D.model.configs n).kH_nonneg _),
    norm_vel_eq_perim A.tube u, A.perim_eq]
  calc
    (D.model.configs n).kH ((2 * D.Hs n) * u) * (2 * D.Hs n) ^ 2 ≤
        C.k0 * (2 * D.Hs n) ^ 2 :=
      mul_le_mul_of_nonneg_right hk (sq_nonneg _)
    _ = (2 * D.Hs n) ^ 2 * C.k0 := by ring

private noncomputable def closingCarrier
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J} (R : RecostClosingOutput J O) (n : ℕ) :
    RearCarrier R.data n := by
  let A := J.scalar.pair.carriers (R.totalShift + n)
  exact
    { data := A.data
      c := A.c
      dlt := A.dlt
      c_pos := A.c_pos
      dlt_pos := A.dlt_pos
      tube := A.tube
      perim_eq := by
        simpa [RecostClosingOutput.data,
          ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
          ConfiguredBaseProfiledEdgeSourceFamily.data,
          ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
          Nat.add_assoc] using A.perim_eq
      curve_eq := by
        simpa [RecostClosingOutput.data,
          ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
          ConfiguredBaseProfiledEdgeSourceFamily.data,
          ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
          Nat.add_assoc] using A.curve_eq }

theorem configuredBase_perim_eq
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J} (R : RecostClosingOutput J O) (n : ℕ) :
    perim (base R n) = 2 * R.data.Hs n := by
  change perim (ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar
    (R.totalShift + n)) = _
  rw [ConfiguredRecursiveEdgePhysicalInitialData.initial_perim_eq]
  simp [RecostClosingOutput.data, RecostClosingOutput.totalShift,
    ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
    ConfiguredBaseProfiledEdgeSourceFamily.data,
    ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
    Nat.add_assoc]

/-- The configured model row has its exact current-row speed.  Chord radius
zero is all the intrinsic local estimate needs from the model certificate. -/
theorem configuredBase_exact_tube
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J} (R : RecostClosingOutput J O) (n : ℕ) :
    IsTubeMember (2 * R.data.Hs n) 0 0 (base R n) := by
  have h := ConfiguredRecursiveEdgePhysicalInitialData.initial_tube
    J.scalar (R.totalShift + n)
  change IsTubeMember (2 * R.data.Hs n) 0 0
    (ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar
      (R.totalShift + n))
  refine
    { hasDerivAt_curve := h.hasDerivAt_curve
      hasDerivAt_vel := h.hasDerivAt_vel
      periodic := h.periodic
      speed_const := h.speed_const
      speed_lb := ?_
      curv_lb := h.curv_lb
      chord := ?_ }
  · intro u
    rw [norm_vel_eq_perim h u]
    simpa [base] using (configuredBase_perim_eq R n).ge
  · intro u hu v hv
    simp

/-- The actual half-curvature certificate gives the sharp acceleration
ceiling for the fixed configured model row. -/
theorem configuredBase_acceleration_le_half
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J} (R : RecostClosingOutput J O) (n : ℕ) (u : ℝ) :
    ‖(base R n).2.2 u‖ ≤ (2 * R.data.Hs n) ^ 2 * (1 / 2) := by
  let C : ConfiguredActualSubunitCurvature.Certificate R.data := by
    simpa [RecostClosingOutput.data] using
      (J.scalar.actualCertificate.shift R.totalShift)
  have hC : C.k0 = 1 / 2 := by
    simpa [C, RecostClosingOutput.data] using
      J.scalar.actualCertificate_k0
  let q := R.totalShift + n
  let P := ConfiguredRecursiveEdgePhysicalInitialData.previousPresentation
    J.scalar q
  let r := ConfiguredGaugeFirstPhysicalSequence.rearPhase
    J.scalar.pair.input J.scalar.model_data P
  have h := rearCarrier_acceleration_le_actual C (closingCarrier R n)
    (u + ConfiguredRecursiveEdgePhysicalInitialData.rearShift J.scalar q + r)
  change ‖P.rotation *
    (J.scalar.pair.input.carrier q).data.2.2
      (u + ConfiguredRecursiveEdgePhysicalInitialData.rearShift J.scalar q + r)‖ ≤ _
  rw [J.scalar.pair.input_carrier q, norm_mul, P.rotation_norm, one_mul]
  simpa [closingCarrier, hC] using h

/-- An ordinary constant-speed tube is a variable-speed tube with the exact
perimeter as upper speed. -/
theorem variableTube_of_tube
    {c : ℝ} {a : Data} (h : IsTubeMember c 0 0 a) :
    IsVariableTubeMember c (perim a) 0 0 a where
  hasDerivAt_curve := h.hasDerivAt_curve
  hasDerivAt_vel := h.hasDerivAt_vel
  periodic := h.periodic
  speed_lb := h.speed_lb
  speed_ub := fun u ↦ (norm_vel_eq_perim h u).le
  curv_lb := h.curv_lb
  chord := h.chord

theorem positive_speed_margin
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J} (R : RecostClosingOutput J O) (n : ℕ) :
    0 < 2 * R.data.Hs n - R.radius n := by
  have hH : 1 ≤ R.data.Hs n :=
    R.separation_one.trans (R.data.separation_lower n)
  have hr := R.radius_small n
  nlinarith

theorem initial_ratio_le_kbar
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J} (R : RecostClosingOutput J O) (n : ℕ) :
    ((2 * R.data.Hs n) ^ 2 * (1 / 2) + R.radius n) /
        (2 * R.data.Hs n - R.radius n) ^ 2 ≤
      TubeConstants.kbar (1 / 2) := by
  norm_num [TubeConstants.kbar]
  exact model_ratio_le_two_thirds
    (R.separation_one.trans (R.data.separation_lower n))
    (R.radius_nonnegative n) (R.radius_small n).le

/-- The intrinsic active-time estimate followed by exact stopping gives the
global curvature bound, with no stable-component or raw PDE premise. -/
theorem all_real_intrinsic_le_sourceKh_of_canonicalModel
    {p q a b model : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b)
    (R : SpatialFrameRegularity Gamma A.Ydot A.Theta A.delta A.sf
      A.P A.m kh Qmax)
    (S : AnalyticSuccessorSliceFacts A)
    (hT : Gamma.T = 1)
    {c0 k0 d0 c C kmin delta A0 r : ℝ}
    (hmodel : IsTubeMember c0 k0 d0 model)
    (hp : IsVariableTubeMember c C kmin delta a)
    (hloc : 0 < c0 - r)
    (hmodelAcc : ∀ u, ‖model.2.2 u‖ ≤ A0)
    (hdist : dist model a ≤ r)
    (hinitial : (A0 + r) / (c0 - r) ^ 2 ≤ TubeConstants.kbar (1 / 2))
    (hsmall :
      (A.d + 2 +
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh ^ 2) *
          (∫ t in (0 : ℝ)..1, A.m t) <
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh -
          TubeConstants.kbar (1 / 2))
    (t s : ℝ) :
    |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature A t s| ≤
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh := by
  apply ChosenStopped.all_real_intrinsic_le_of_chosen_active_lt A W R S
  intro tau ht u
  exact ReachableVariableSpeedFrontCurvatureIntrinsicStable.active_intrinsic_abs_curvature_lt_sourceKh_of_canonicalModel
      A E W hmodel hp hloc hmodelAcc hdist hinitial hsmall
      (by simpa [hT] using ht) (E.Phi tau u)

end ConfiguredRecursiveEdgeRecostFinitePreparedIntrinsicCurvature
