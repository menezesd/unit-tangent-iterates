import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFiniteNativePresentedInput
import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0Growth
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareDirectCappedProvider
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorSourceMass

/-! # Intrinsic configured caps for native presented terminal geometry

The endpoint estimate is local to one theorem-produced terminal geometry.
No correlated column or global presented-row selection is needed: the exact
physical terminal identities and the source mass supply every input of the
linear marking-deviation bound.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFinitePresentedGeometryCap

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredGaugeEndpointLinearRadius
  ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostFiniteNativePresentedInput
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0Growth
  FiniteHistoryMajorBudget
  FiniteNonaffineMajorLayer
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareDirectCappedProvider
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorSourceMass
  FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalInputCore
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction
  GaugeMarkedDataOfRearFamily
  InterpolationVariableSpeedSelInvAdapter

/-- Multiplier scaling and direct recosting preserve the automatic exact
successor's sharp spatial-curvature constant. -/
@[simp] theorem scaledInput_source_kx
    {P0u khu khatu Qmaxu : ℕ → ℝ} {j : ℕ}
    {S : Stage P0u khu khatu Qmaxu j}
    {C : ConfiguredRecursiveEdgeRecostedPreCarrier.Core S}
    {p0 kh0 khat0 qmax0 : ℝ}
    (I : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input
      C p0 kh0 khat0 qmax0) :
    I.source.kx = SelInvFrontStripC2.stripCurvConst kh0 := by
  change FiniteSmoothRearFamilyMarkingAwareSmoothSource.successorKx kh0 =
    SelInvFrontStripC2.stripCurvConst kh0
  rfl

/-- The intrinsic marking cap of a terminal core induced by `G` is charged
against the actual source mass.  The successor index in the configured
endpoint conversion is forced by
`edgeSpeedCap D q = speedCap D (q + 1)`. -/
theorem intrinsicEndpointCap_le_configuredAllowance
    {p q0 a b initial : Data} {Gamma : NormalPath p q0}
    {Delta : NormalPath a b}
    {P0 kh khat Qmax periodLower khatNext QmaxNext bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {X : RecursiveAnalyticSuccessor Delta A periodLower sourceKh
      khatNext QmaxNext}
    {E : Applied Delta X.source}
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E0 C0 C1 C2 M : ℝ) (q : ℕ)
    (G : PresentedTerminalGeometry X.source E)
    (I : Inputs (bound := bound) X E G initial)
    (O : PresentedOutputCore E I.toPresentedTerminalInputCore)
    (hLmax : G.Lmax = edgeSpeedCap D q)
    (hkx : X.source.kx ≤ analyticKd D)
    (hmass : sourceMass X.source ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
        D E0 C0 C1 C2 q)
    (hallowM :
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
          D E0 C0 C1 C2 q ≤ M) :
    intrinsicEndpointCap O ≤
      edgeEndpointConversion D sourceKh M q *
        ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
          D E0 C0 C1 C2 q := by
  let allowance :=
    ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
      D E0 C0 C1 C2 q
  have hcostSource : O.chosen.Delta.cost ≤ sourceMass X.source := by
    simpa [sourceMass] using O.chosen.cost_eq.le
  have hcostAllowance : O.chosen.Delta.cost ≤ allowance :=
    hcostSource.trans hmass
  have hcostM : O.chosen.Delta.cost ≤ M :=
    hcostAllowance.trans hallowM
  have hM0 : 0 ≤ M := O.chosen.Delta.cost_nonneg.trans hcostM
  have hQ0 : 0 ≤ G.Lmax :=
    (X.source.rear_period_pos 0).le.trans (G.period_le 0)
  have hQ : G.Lmax ≤ speedCap D (q + 1) := by
    simpa [edgeSpeedCap] using hLmax.le
  have hell0 : 0 ≤ rearPeriod X.source 0 :=
    (X.source.rear_period_pos 0).le
  have hell : rearPeriod X.source 0 ≤ ellCap D (q + 1) :=
    (G.period_le 0).trans (by
      simpa [edgeSpeedCap, speedCap, ellCap] using hLmax.le)
  have hkappa : 0 ≤ rearKappa1 sourceKh :=
    rearKappa1_nonneg sourceKh_nonnegative sourceKh_lt_one
  have hkappa2 : 0 ≤ rearKappa2 sourceKh :=
    rearKappa2_nonneg sourceKh_nonnegative sourceKh_lt_one
  have hL0 : 0 ≤ G.physical.L := by
    rw [G.physical_L_eq]
    simpa [terminalPeriod] using (X.source.rear_period_pos Delta.T).le
  have hL : G.physical.L ≤ lengthCap D (q + 1) := by
    rw [G.physical_L_eq]
    calc
      terminalPeriod X.source ≤ G.Lmax := by
        simpa [terminalPeriod] using G.period_le Delta.T
      _ ≤ lengthCap D (q + 1) := by
        simpa [edgeSpeedCap, speedCap, lengthCap] using hLmax.le
  have hkb0 : 0 ≤ G.physical.kb := by
    rw [G.physical_kb_eq]
    exact hkappa
  have hkb : G.physical.kb ≤ analyticKhat D := by
    rw [G.physical_kb_eq]
    exact rearKappa1_sourceKh_le_analyticKhat D
  have hkL0 : 0 ≤ G.physical.kL := by
    have HL := G.physical.curvature_lipschitz 0 1
    have H0 := (abs_nonneg
      (G.physical.curvature 0 - G.physical.curvature 1)).trans HL
    norm_num at H0
    exact H0
  have hkL : G.physical.kL ≤ analyticKd D := by
    rw [G.physical_kL_eq]
    exact hkx
  have hmono := canonicalMarkingLinearConst_mono_fixed
    hQ0 hQ hell0 hell hkappa hkappa2 hM0
    hL0 hL hkb0 hkb hkL0 hkL
  have hcoefficientSucc :
      canonicalMarkingLinearConst G.Lmax (rearPeriod X.source 0)
          (rearKappa1 sourceKh) (rearKappa2 sourceKh) M
          G.physical.L G.physical.kb G.physical.kL ≤
        endpointConversion D sourceKh M (q + 1) := by
    simpa [endpointConversion, endpointLinearCoeff] using hmono
  have hcoefficient :
      canonicalMarkingLinearConst G.Lmax (rearPeriod X.source 0)
          (rearKappa1 sourceKh) (rearKappa2 sourceKh) M
          G.physical.L G.physical.kb G.physical.kL ≤
        edgeEndpointConversion D sourceKh M q :=
    hcoefficientSucc.trans
      (endpointConversion_succ_le_edgeEndpointConversion D sourceKh M q)
  have hlinear : intrinsicEndpointCap O ≤
      canonicalMarkingLinearConst G.Lmax (rearPeriod X.source 0)
          (rearKappa1 sourceKh) (rearKappa2 sourceKh) M
          G.physical.L G.physical.kb G.physical.kL *
        O.chosen.Delta.cost := by
    change MarkingDeviationC2.markingC2Bound
      (2 * G.Lmax * rearKappa1 sourceKh * O.chosen.Delta.cost)
      (MarkingFlowDefectC2.flowDefectC1Int (rearPeriod X.source 0)
        (rearKappa1 sourceKh * O.chosen.Delta.cost))
      (MarkingFlowDefectC2.flowDefectC2Int (rearPeriod X.source 0)
        (rearKappa1 sourceKh * O.chosen.Delta.cost)
        (rearKappa2 sourceKh * O.chosen.Delta.cost))
      G.physical.L G.physical.kb G.physical.kL ≤ _
    apply markingC2Bound_flow_le_linear
    · exact (X.source.rear_period_pos 0).le.trans (G.period_le 0)
    · exact (X.source.rear_period_pos 0).le
    · exact hkappa
    · exact hkappa2
    · exact hM0
    · exact hL0
    · exact hkb0
    · exact hkL0
    · exact O.chosen.Delta.cost_nonneg
    · exact hcostM
  have hcanonical : 0 ≤
      canonicalMarkingLinearConst G.Lmax (rearPeriod X.source 0)
        (rearKappa1 sourceKh) (rearKappa2 sourceKh) M
        G.physical.L G.physical.kb G.physical.kL :=
    canonicalMarkingLinearConst_nonneg hQ0 hkappa
  exact hlinear.trans
    (mul_le_mul hcoefficient hcostAllowance O.chosen.Delta.cost_nonneg
      (hcanonical.trans hcoefficient))

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  {H : Output R}
  {budget : ℕ → MajorBudget
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal}
  {k : ℕ} {S : ℕ → Node}
  {L : Layer budget (stateP1 H) (defect H) k S}
  {I : ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.InputData
    J H budget L}
  {n : ℕ} {bound : ℝ}

/-- Native finite-step form.  Its left side is definitionally the endpoint
cap of the core stored by `PreparedStepData.next`; callers only unfold the
prepared `next` and `pre` projections. -/
theorem boundaryFacts_core_endpointCap_le
    (B : BoundaryFacts I n bound)
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E0 C0 C1 C2 M : ℝ) (q : ℕ)
    (hLmax : B.geometry.Lmax = edgeSpeedCap D q)
    (hmass : sourceMass (I.analytic n).source ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
        D E0 C0 C1 C2 q)
    (hallowM :
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
          D E0 C0 C1 C2 q ≤ M) :
    B.core.geometric.endpointCap ≤
      edgeEndpointConversion D sourceKh M q *
        ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
          D E0 C0 C1 C2 q := by
  change intrinsicEndpointCap B.presentedInput.output ≤ _
  refine intrinsicEndpointCap_le_configuredAllowance
    (X := B.recursive) (E := I.step.nextApplied n)
    (G := B.geometry) (I := B.inputs) (O := B.presentedInput.output)
    D E0 C0 C1 C2 M q hLmax ?_ hmass hallowM
  change (I.analytic n).source.kx ≤ analyticKd D
  rw [scaledInput_source_kx]
  exact stripCurvConst_sourceKh_le_analyticKd D

end ConfiguredRecursiveEdgeRecostFinitePresentedGeometryCap
