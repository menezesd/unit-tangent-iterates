import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedNextPhase
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePresentedGeometryCap
import UnitTangentIterates.ConfiguredRecursiveEdgeFullRecostMetricDiagonal
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear

/-! # Raw-metric provenance for a prepared finite successor -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFinitePreparedNextMetric

open ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgeFullRecostMetricDiagonal
  ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostFiniteNativePresentedInput
  ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal
  ConfiguredRecursiveEdgeRecostedRawMetricGeometry
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveSourceP0FixedDistortion
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction
  NormalPathC2IncrementVariableSpeed

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    choice.MA0 choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  (H : Output R)
  {k : ℕ} {Z : PreparedReachable H k}

/-- The newly presented successor retains the raw chosen path with the
configured edge ceilings and the truthful multiplier source allowance. -/
noncomputable def nextRawMetric
    (I : PreparedStepData H Z)
    (sourceMass_le_allowance : ∀ n,
      sourceMass (I.input.analytic n).source ≤
        multiplierRecostSourceAllowance O.data distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2
          (H.toClosing.preShift + H.toClosing.large.N +
            (n + (k + 1))))
    (n : ℕ) :
    RawMetricGeometry.Bounded ((I.next H).pre H n).geometric := by
  let B := I.boundaryFacts H n
  let A := I.input.analytic n
  let D := O.data
  let r := n + (k + 1)
  let q := H.toClosing.preShift + H.toClosing.large.N + r
  have hOdata : O.data = shift (globalData (J := J)) O.N := by
    rfl
  have hindex :
      ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal
        H n (k + 1) = O.N + q := by
    simp [q, r,
      ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal,
      ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing.Output.totalShift,
      RecostClosingOutput.totalShift, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  have hP0 : I.input.step.targetP0 n = edgeSourceP0 D q := by
    change edgeSourceP0 (globalData (J := J))
        (ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal
          H n (k + 1)) =
      edgeSourceP0 O.data q
    rw [hOdata, hindex]
    rfl
  have hKhat : I.input.step.targetKhat n = analyticKhat D := by
    change analyticKhat (globalData (J := J)) = analyticKhat O.data
    rw [hOdata]
    rfl
  have hQmax : I.input.step.targetQmax n = edgeSpeedCap D q := by
    change edgeSpeedCap (globalData (J := J))
        (ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal
          H n (k + 1)) =
      edgeSpeedCap O.data q
    rw [hOdata, hindex]
    rfl
  have hmass : sourceMass A.source ≤
      multiplierRecostSourceAllowance D distortionTotal
        physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
        physicalTransitionCeilings.C2 q := by
    simpa [A, D, q, r] using sourceMass_le_allowance n
  have hmass0 : 0 ≤ sourceMass A.source :=
    sourceMass_nonnegative A.source
  have hallow1 : multiplierRecostSourceAllowance D distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2 q ≤ 1 := by
    simpa [D, q] using H.toClosing.mass_small r
  have hperiod : rearPeriod A.source 0 ≤ edgeSpeedCap D q := by
    calc
      rearPeriod A.source 0 ≤ I.input.step.targetQmax n :=
        A.source.rear_period_le 0
      _ = edgeSpeedCap D q := hQmax
  have hceilings :=
    flowCeilings_of_mass_one D (MA := choice.MA0) (NA := choice.NA0) q
      (A.source.rear_period_pos 0).le hperiod hmass0
      (hmass.trans hallow1)
  have hP1 := hceilings.1
  have hG1 := hceilings.2.1
  have hCg := hceilings.2.2
  change RawMetricGeometry.Bounded B.presentedInput.geometricInput
  exact
    { pathP0 := edgeSourceP0 D q
      pathP1 := edgeP1 D choice.MA0 q
      pathKhat := analyticKhat D
      pathG1 := edgeG1 D choice.MA0 choice.NA0 q
      pathCg := edgeCgWithKhat D (analyticKhat D)
        choice.MA0 choice.NA0 q
      start_curve_deriv := by
        intro u
        change HasDerivAt (⇑(I.input.nextDisplayed n).1)
          ((I.input.nextDisplayed n).2.1 u) u
        rw [B.displayed_eq]
        exact A.source.selectedRearData_curve_deriv 0 u
      start_vel_deriv := by
        intro u
        change HasDerivAt (⇑(I.input.nextDisplayed n).2.1)
          ((I.input.nextDisplayed n).2.2 u) u
        rw [B.displayed_eq]
        exact A.source.selectedRearData_velocity_deriv 0 u
      geometry := by
        have hstage := B.presentedInput.output.stage.increment_geometry
        simp only
          [ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows.Step.next]
          at hstage
        have hmono := hstage.mono B.presentedInput.output.stage.increment
          (by simpa only [hKhat] using analyticKhat_nonnegative D)
          (by simpa [A, sourceMass, hKhat] using hP1)
          (by simpa [A, sourceMass, hKhat] using hG1)
          (by simpa [A, sourceMass, hKhat] using hCg)
        simpa only [hP0, hKhat] using hmono
      rawBound := multiplierRecostSourceAllowance D distortionTotal
        physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
        physicalTransitionCeilings.C2 q
      rawBound_nonnegative :=
        multiplierRecostSourceAllowance_nonnegative D distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2 q
      cost_le := by
        change B.presentedInput.output.stage.increment.cost ≤ _
        rw [B.presentedInput.output.stage_eq,
          B.presentedInput.output.chosen.cost_eq]
        simpa [A, sourceMass] using hmass }

/-- The raw path charge and the reconstructed endpoint cap of a prepared
successor are both paid by the public error at depth `k + 1`. -/
theorem nextRawMetric_edgeBudget_le_error
    (I : PreparedStepData H Z)
    (sourceMass_le_allowance : ∀ n,
      sourceMass (I.input.analytic n).source ≤
        multiplierRecostSourceAllowance O.data distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2
          (H.toClosing.preShift + H.toClosing.large.N +
            (n + (k + 1))))
    (n : ℕ) :
    (nextRawMetric H I sourceMass_le_allowance n).edgeBudget ≤
      H.error n (k + 1) := by
  let B := I.boundaryFacts H n
  let A := I.input.analytic n
  let D := O.data
  let r := n + (k + 1)
  let q := H.toClosing.preShift + H.toClosing.large.N + r
  let M := nextRawMetric H I sourceMass_le_allowance n
  have hOdata : O.data = shift (globalData (J := J)) O.N := by
    rfl
  have hindex :
      ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal
        H n (k + 1) = O.N + q := by
    simp [q, r,
      ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal,
      ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing.Output.totalShift,
      RecostClosingOutput.totalShift, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  have hQmax : I.input.step.targetQmax n = edgeSpeedCap D q := by
    change edgeSpeedCap (globalData (J := J))
        (ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal
          H n (k + 1)) =
      edgeSpeedCap O.data q
    rw [hOdata, hindex]
    rfl
  have hmass : sourceMass A.source ≤
      multiplierRecostSourceAllowance D distortionTotal
        physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
        physicalTransitionCeilings.C2 q := by
    simpa [A, D, q, r] using sourceMass_le_allowance n
  have hallow1 : multiplierRecostSourceAllowance D distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2 q ≤ 1 := by
    simpa [D, q] using H.toClosing.mass_small r
  have hLmax : B.geometry.Lmax = edgeSpeedCap D q := by
    calc
      B.geometry.Lmax = I.input.step.targetQmax n := B.geometry_Lmax
      _ = edgeSpeedCap D q := hQmax
  have hendpoint : B.core.geometric.endpointCap ≤
      edgeEndpointConversion D sourceKh J.scalar.Mend q *
        multiplierRecostSourceAllowance D distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2 q := by
    exact
      ConfiguredRecursiveEdgeRecostFinitePresentedGeometryCap.boundaryFacts_core_endpointCap_le
        B D distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2 J.scalar.Mend q hLmax hmass
          (hallow1.trans J.one_le_Mend)
  have hendpoint' : ((I.next H).pre H n).geometric.endpointCap ≤
      edgeEndpointConversion D sourceKh J.scalar.Mend q *
        multiplierRecostSourceAllowance D distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2 q := by
    change B.core.geometric.endpointCap ≤ _
    exact hendpoint
  have hfactor : M.toRawMetricGeometry.pathFactor =
      edgeConversion D (analyticKhat D) choice.MA0 choice.NA0 q := by
    simp [M, D, q, r, nextRawMetric, RawMetricGeometry.pathFactor,
      edgeConversion]
  have hraw : M.rawBound =
      multiplierRecostSourceAllowance D distortionTotal
        physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
        physicalTransitionCeilings.C2 q := by
    simp [M, D, q, r, nextRawMetric]
  have hbudget : M.edgeBudget ≤
      fullRecostMetricDiagonal D choice.MA0 choice.NA0 distortionTotal
        physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
        physicalTransitionCeilings.C2 J.scalar.Mend q := by
    simpa only [RawMetricGeometry.Bounded.edgeBudget] using
      (recursiveRawEdgeBudget_le_fullRecostMetricDiagonal D
        choice.MA0 choice.NA0 distortionTotal physicalTransitionCeilings.C0
        physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
        J.scalar.Mend M.toRawMetricGeometry.pathFactor M.rawBound
        ((I.next H).pre H n).geometric.endpointCap q hfactor.le hraw.le
        M.rawBound_nonnegative hendpoint')
  change M.edgeBudget ≤ H.toClosing.error n (k + 1)
  rw [H.toClosing.error_eq_multiplierDiagonal]
  simpa [D, q, r, Nat.add_assoc] using hbudget

end ConfiguredRecursiveEdgeRecostFinitePreparedNextMetric
