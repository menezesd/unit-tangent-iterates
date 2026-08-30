import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedGeometrySchema
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicAnalyticReadiness
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNonaffinePreCarrierInput
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierSourceMass

/-! # Analytic inputs for arbitrary prepared recursion depth

A prepared finite layer already carries the normalized ancestry needed to
bound the canonical recost of its next-row cores.  The only additional
source-side input is the multiplier allowance for those next-row sources.
This file chooses the exact allowance witness, completes it through the
finite history to obtain the configured multiplier scalar, and retains the
scaled recursive facts needed by the next prepared layer.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFinitePreparedAnalytic

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostFinitePreparedGeometrySchema
  ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicAnalyticReadiness
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierNonaffinePreCarrierInput
  ConfiguredRecursiveEdgeRecostMultiplierScalar
  ConfiguredRecursiveEdgeRecostMultiplierSourceMass
  ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0Growth
  FiniteNonaffineMajorNormalizedState
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  (H : Output R)

/-- The local closing-data index of the source in row `n + 1` at depth `k`. -/
abbrev localIndex (n k : ℕ) : ℕ := n + k + 1

abbrev sourceNode {k : ℕ} (Z : PreparedReachable H k) (n : ℕ) :=
  Z.nodes (n + 1)

abbrev sourceCore {k : ℕ} (Z : PreparedReachable H k) (n : ℕ) :=
  Z.pre H (n + 1)

/-- The complete caller-owned provenance for the generic analytic bridge.
The geometric field is retained because it is also the nonmetric provenance
consumed when the resulting analytic inputs are assembled into a prepared
step. -/
structure BridgeData {k : ℕ} (Z : PreparedReachable H k) where
  configured : ∀ n, ConfiguredNode H.toClosing (n + k) (Z.nodes n)
  geometry : PreparedGeometryProvenance H k Z
  rearCurvature_le : ∀ n t s,
    |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature
      (sourceNode H Z n).stage.source t s| ≤ sourceKh
  sourceMass_le_allowance : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
        (sourceNode H Z n).stage.source ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
          H.toClosing.data
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2
          (localIndex n k)

/-- Configured scalar bounds for a next-row source at arbitrary depth. -/
noncomputable def scalar {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    Scalar
      (A := (sourceNode H Z n).stage.source)
      (kap := sourceKh)
      (P0Next := edgeSourceP0 H.toClosing.data (localIndex n k))
      (khatNext := analyticKhat H.toClosing.data)
      (QmaxNext := edgeSpeedCap H.toClosing.data (localIndex n k)) where
  curvature_le := D.rearCurvature_le n
  period_le := fun t => by
    calc
      rearPeriod (sourceNode H Z n).stage.source t ≤
          (sourceNode H Z n).stageQmax (sourceNode H Z n).stageIndex :=
        (sourceNode H Z n).stage.source.rear_period_le t
      _ = (sourceNode H Z n).Qmax :=
        (D.configured (n + 1)).stageQmax_at_index_eq
      _ = edgeSpeedCap
          (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData (J := J))
          (H.totalShift + ((n + 1) + k)) :=
        (D.configured (n + 1)).Qmax_eq
      _ = edgeSpeedCap H.toClosing.data (localIndex n k) := by
        rw [ConfiguredRecursiveEdgeRecostMultiplierIntrinsicAnalyticReadiness.edgeSpeedCap_data_local
          H.toClosing]
        simp only [ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing.Output.toClosing_totalShift]
        congr 1
        dsimp [localIndex]
        omega
  rearKappa1_le := rearKappa1_sourceKh_le_analyticKhat H.toClosing.data
  numerical_A := ConfiguredRecursiveEdgeSourceP0.numerical_A H.toClosing.data
    (localIndex n k)
  numerical_K := by
    simpa [FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.sourceConst,
      FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.derivativeConst,
      FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.curvatureConst] using
      (ConfiguredRecursiveEdgeSourceP0.numerical_K H.toClosing.data (localIndex n k))

/-- The normalized state on the successor-indexed row, rewritten to the
local diagonal index used by the analytic constructor. -/
noncomputable def normalizedState {k : ℕ} (Z : PreparedReachable H k)
    (n : ℕ) :
    State (budget H (localIndex n k))
      (S := (sourceNode H Z n).stage)
      (P1 := stateP1 H (localIndex n k))
      (depth := k)
      (edgeDefect := defect H (localIndex n k)) := by
  simpa [localIndex, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    Z.layer.normalized (n + 1)

theorem sourcePeriod_le_ellCap {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    rearPeriod (sourceNode H Z n).stage.source 0 ≤
      ellCap H.toClosing.data (localIndex n k + 1) := by
  simpa [ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap, speedCap, ellCap] using
    (scalar H D n).period_le 0

/-- The retained unscaled allowance witness.  It is used once to extend the
normalized ancestry and thereby prove the canonical recost cost estimate. -/
noncomputable def allowanceWitness {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    AllowanceWitness (sourceCore H Z n)
      (edgeSourceP0 H.toClosing.data (localIndex n k)) sourceKh
      (analyticKhat H.toClosing.data) (edgeSpeedCap H.toClosing.data (localIndex n k))
      (H.epsDiag (localIndex n k)) :=
  Classical.choice
    (by
      simpa only [ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_data]
        using
          (exists_input_of_allowance_recursive_spec
            (O := ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput
              H.toClosing)
            (q := localIndex n k)
            (E0 := ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal)
            (C0 := ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0)
            (C1 := ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1)
            (C2 := ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2)
            (sourceCore H Z n) (Z.selection (n + 1))
            (by
              simpa only [ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_data]
                using (scalar H D n))
            (normalizedState H Z n).periodFloor
            (by
              simpa only [ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_data]
                using (sourcePeriod_le_ellCap H D n))
            (by
              simpa only [ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_data]
                using (D.sourceMass_le_allowance n))
            (by
              simpa only [ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_data]
                using
                  (ConfiguredRecursiveEdgeRecostMultiplierScalar.mass_small_final
                    H.toClosing (localIndex n k)))
            (by
              simpa only [ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_data]
                using (H.recostJetMajor_le_epsDiag (localIndex n k)))
            (H.epsDiag_quarter (localIndex n k))))

/-- Finite-history completion of the allowance-built direct input. -/
noncomputable def completion {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :=
  (normalizedState H Z n).completion
    (budget H (localIndex n k))
    (sourceCore H Z n) (allowanceWitness H D n).input
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal_le_eighth
    (by
      rw [budget_major_of_le H (localIndex n k) (k + 1)
        (by dsimp [localIndex]; omega)]
      exact (allowanceWitness H D n).eps_eq.le)
    (edgeSpeedCap H.toClosing.data (localIndex n k))
    (one_le_edgeSpeedCap H.toClosing.data (localIndex n k))
    (two_le_recostPeriodScale H.toClosing.data (localIndex n k))
    (fun t _ => (scalar H D n).period_le t)

/-- Local closing data and the public global diagonal have the same outgoing
physical defect. -/
theorem edgePhysicalDefect_data_local (q : ℕ) :
    edgePhysicalDefect H.toClosing.data (q + 1) = defect H q := by
  change
    edgePhysicalDefect
        (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
          (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData (J := J))
          H.totalShift) (q + 1) =
      edgePhysicalDefect
        (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData (J := J))
        (H.totalShift + q + 1)
  unfold ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
  unfold ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect
  rw [ConstructedRowDefectLargeSeparation.rowDefect_shift]
  simp [ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect,
    ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalCoeff,
    ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
    Nat.add_assoc]

/-- The completed finite ancestry supplies the exact cost premise of the
configured multiplier scalar. -/
theorem recostCost_le {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (carrier (sourceCore H Z n).geometric.output.chosen
      (sourceCore H Z n).geometric.output.chosen.c2
      (sourceCore H Z n).eta_continuous
      (sourceCore H Z n).eta1_continuous
      (sourceCore H Z n).eta2_continuous).cost ≤
      4 * ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 *
        (2 * recostPeriodScale H.toClosing.data (localIndex n k) *
          edgePhysicalDefect H.toClosing.data (localIndex n k + 1)) := by
  rw [edgePhysicalDefect_data_local H]
  convert
    (ConfiguredRecursiveEdgeRecostedCarrierRow.CarrierRow.cost_le
      (Completion.carrier (completion H D n))) using 1 <;>
    simp [completion, recostPeriodScale,
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings,
      mul_assoc, mul_left_comm, mul_comm]

/-- The canonical scalar installed on the multiplier-scaled source. -/
noncomputable def configuredRecostScalar {k : ℕ}
    {Z : PreparedReachable H k} (D : BridgeData H Z) (n : ℕ) :=
  ConfiguredRecursiveEdgeRecostMultiplierScalar.recostScalar H.toClosing
    (localIndex n k) (sourceCore H Z n).geometric.output.chosen
    (sourceCore H Z n).geometric.output.chosen.c2
    (sourceCore H Z n).eta_continuous
    (sourceCore H Z n).eta1_continuous
    (sourceCore H Z n).eta2_continuous (recostCost_le H D n)

/-- Direct use of the strengthened scaled allowance constructor. -/
theorem exists_scaledAllowanceWitness {k : ℕ}
    {Z : PreparedReachable H k} (D : BridgeData H Z) (n : ℕ) :
    Nonempty (ScaledAllowanceWitness (sourceCore H Z n)
      (edgeSourceP0 H.toClosing.data (localIndex n k)) sourceKh
      (analyticKhat H.toClosing.data) (edgeSpeedCap H.toClosing.data (localIndex n k))
      (H.epsDiag (localIndex n k))) :=
  by
    simpa only [ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_data]
      using
        (exists_scaled_input_of_allowance_spec
          (O := ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput
            H.toClosing)
          (q := localIndex n k)
          (E0 := ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal)
          (C0 := ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0)
          (C1 := ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1)
          (C2 := ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2)
          (sourceCore H Z n) (Z.selection (n + 1))
          (by
            simpa only [ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_data]
              using (scalar H D n))
          (by
            simpa only [ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_data]
              using (configuredRecostScalar H D n))
          (normalizedState H Z n).periodFloor
          (by
            simpa only [ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_data]
              using (sourcePeriod_le_ellCap H D n))
          (by
            simpa only [ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_data]
              using (D.sourceMass_le_allowance n))
          (by
            simpa only [ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_data]
              using
                (ConfiguredRecursiveEdgeRecostMultiplierScalar.mass_small_final
                  H.toClosing (localIndex n k)))
          (by
            simpa only [ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_data]
              using (H.recostJetMajor_le_epsDiag (localIndex n k)))
          (H.epsDiag_quarter (localIndex n k)))

/-- Canonical strengthened witness with the configured scalar equality still
definitionally visible.  That equality is needed for the sharp allowance
bound and is not a field of `ScaledAllowanceWitness` itself. -/
noncomputable def scaledAllowanceWitness {k : ℕ}
    {Z : PreparedReachable H k} (D : BridgeData H Z) (n : ℕ) :
    ScaledAllowanceWitness (sourceCore H Z n)
      (edgeSourceP0 H.toClosing.data (localIndex n k)) sourceKh
      (analyticKhat H.toClosing.data) (edgeSpeedCap H.toClosing.data (localIndex n k))
      (H.epsDiag (localIndex n k)) :=
  (allowanceWitness H D n).toScaled (configuredRecostScalar H D n)

@[simp] theorem scaledAllowanceWitness_recostScalar {k : ℕ}
    {Z : PreparedReachable H k} (D : BridgeData H Z) (n : ℕ) :
    (scaledAllowanceWitness H D n).input.recostScalar =
      configuredRecostScalar H D n := rfl

theorem scaledAllowanceWitness_sourceMass_le_allowance {k : ℕ}
    {Z : PreparedReachable H k} (D : BridgeData H Z) (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
        (scaledAllowanceWitness H D n).input.source ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
          H.toClosing.data
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2
          (localIndex n k) := by
  exact ConfiguredRecursiveEdgeRecostMultiplierSourceMass.scaledInput_sourceMass_le_allowance
    H.toClosing (localIndex n k)
      (scaledAllowanceWitness H D n).input (recostCost_le H D n)
      (scaledAllowanceWitness_recostScalar H D n)

/-- A scaled witness cast to the exact global indices expected by finite
intrinsic `InputData`, together with the sharp source-mass estimate. -/
structure AnalyticPackage {k : ℕ} (Z : PreparedReachable H k) (n : ℕ) where
  geometry : PreparedGeometryProvenance H k Z
  witness : ScaledAllowanceWitness (sourceCore H Z n)
    (edgeSourceP0
      (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData (J := J))
      (ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal H n (k + 1)))
    sourceKh
    (analyticKhat
      (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData (J := J)))
    (edgeSpeedCap
      (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData (J := J))
      (ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal H n (k + 1)))
    (H.epsDiag (localIndex n k))
  sourceMass_le_allowance :
    FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
        witness.input.source ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
          H.toClosing.data
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2
          (localIndex n k)

/-- Transport only the three synchronized scalar indices of a scaled witness.
Eliminating the equalities here avoids simplifying a cast through the witness's
dependent input, bounds, and recursive carrier data. -/
noncomputable def transportScaledAllowanceWitness {k : ℕ}
    {Z : PreparedReachable H k} (n : ℕ)
    {p0 khat qmax p0' khat' qmax' eps : ℝ}
    (X : ScaledAllowanceWitness (sourceCore H Z n)
      p0 sourceKh khat qmax eps)
    (hp0 : p0 = p0') (hkhat : khat = khat') (hqmax : qmax = qmax') :
    ScaledAllowanceWitness (sourceCore H Z n)
      p0' sourceKh khat' qmax' eps := by
  cases hp0
  cases hkhat
  cases hqmax
  exact X

theorem transportScaledAllowanceWitness_sourceMass {k : ℕ}
    {Z : PreparedReachable H k} (n : ℕ)
    {p0 khat qmax p0' khat' qmax' eps : ℝ}
    (X : ScaledAllowanceWitness (sourceCore H Z n)
      p0 sourceKh khat qmax eps)
    (hp0 : p0 = p0') (hkhat : khat = khat') (hqmax : qmax = qmax') :
    FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
        (transportScaledAllowanceWitness H n X hp0 hkhat hqmax).input.source =
      FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
        X.input.source := by
  cases hp0
  cases hkhat
  cases hqmax
  rfl

opaque analyticPackage {k : ℕ}
    {Z : PreparedReachable H k} (D : BridgeData H Z) (n : ℕ) :
    AnalyticPackage H Z n := by
  let X := scaledAllowanceWitness H D n
  have hmass : FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
      X.input.source ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
          H.toClosing.data
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2
          (localIndex n k) := by
    simpa [X] using scaledAllowanceWitness_sourceMass_le_allowance H D n
  have hp0 : edgeSourceP0 H.toClosing.data (localIndex n k) =
      edgeSourceP0
        (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData (J := J))
        (ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal H n (k + 1)) := by
    simpa [localIndex,
      ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal,
      Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicAnalyticReadiness.edgeSourceP0_data_local
        H.toClosing (localIndex n k))
  have hkhat : analyticKhat H.toClosing.data =
      analyticKhat
        (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData (J := J)) := by
    simpa using
      (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicAnalyticReadiness.analyticKhat_data_local
        H.toClosing)
  have hqmax : edgeSpeedCap H.toClosing.data (localIndex n k) =
      edgeSpeedCap
        (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData (J := J))
        (ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal H n (k + 1)) := by
    simpa [localIndex,
      ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal,
      Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicAnalyticReadiness.edgeSpeedCap_data_local
        H.toClosing (localIndex n k))
  exact
    { geometry := D.geometry
      witness := transportScaledAllowanceWitness H n X hp0 hkhat hqmax
      sourceMass_le_allowance := by
        calc
          FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
              (transportScaledAllowanceWitness H n X hp0 hkhat hqmax).input.source =
              FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
                X.input.source :=
            transportScaledAllowanceWitness_sourceMass H n X hp0 hkhat hqmax
          _ ≤ _ := hmass }

/-- The analytic family consumed by the prepared successor step at depth
`k`. -/
noncomputable def preparedAnalytic {k : ℕ}
    {Z : PreparedReachable H k} (D : BridgeData H Z) (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input
      (sourceCore H Z n)
      (edgeSourceP0
        (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData (J := J))
        (ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal H n (k + 1)))
      sourceKh
      (analyticKhat
        (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData (J := J)))
      (edgeSpeedCap
        (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData (J := J))
        (ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal H n (k + 1))) :=
  (analyticPackage H D n).witness.input

/-- The transported allowance witness retains the exact configured period
ceiling at the global diagonal used by the intrinsic successor. -/
theorem preparedAnalytic_periodUpper_eq {k : ℕ}
    {Z : PreparedReachable H k} (D : BridgeData H Z) (n : ℕ) :
    (preparedAnalytic H D n).slice.periodUpper =
      ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
        (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
          (J := J))
        (ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal
          H n (k + 1)) :=
  (analyticPackage H D n).witness.periodUpper_eq

theorem preparedAnalytic_sourceMass_le_allowance {k : ℕ}
    {Z : PreparedReachable H k} (D : BridgeData H Z) (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
        (preparedAnalytic H D n).source ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance
          H.toClosing.data
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2
          (localIndex n k) := by
  exact (analyticPackage H D n).sourceMass_le_allowance

theorem preparedAnalytic_eps_le {k : ℕ}
    {Z : PreparedReachable H k} (D : BridgeData H Z) (n : ℕ) :
    (preparedAnalytic H D n).eps ≤
      (budget H (n + (k + 1))).major (k + 1) := by
  rw [budget_major_of_le H (n + (k + 1)) (k + 1) (by omega)]
  change (analyticPackage H D n).witness.input.eps ≤ _
  simpa only [localIndex, Nat.add_assoc] using
    (analyticPackage H D n).witness.eps_eq.le

/-- The strengthened allowance witness retains exact terminal curvature
through multiplier scaling and the configured global-index cast. -/
theorem preparedAnalytic_terminalCurvature_nonnegative {k : ℕ}
    {Z : PreparedReachable H k} (D : BridgeData H Z) (n : ℕ) (s : ℝ) :
    0 ≤ (preparedAnalytic H D n).source.K (sourceCore H Z n).path.T s := by
  exact
    (analyticPackage H D n).witness.recursiveFacts.terminalCurvature_nonnegative s

/-- The strengthened allowance witness retains the exact presented terminal
range through multiplier scaling and the configured global-index cast. -/
theorem preparedAnalytic_terminalRange {k : ℕ}
    {Z : PreparedReachable H k} (D : BridgeData H Z) (n : ℕ) :
    range ((preparedAnalytic H D n).source.F (sourceCore H Z n).path.T) =
      range (sourceCore H Z n).geometric.output.jets.rear.1 := by
  exact (analyticPackage H D n).witness.recursiveFacts.terminalRange

end ConfiguredRecursiveEdgeRecostFinitePreparedAnalytic
