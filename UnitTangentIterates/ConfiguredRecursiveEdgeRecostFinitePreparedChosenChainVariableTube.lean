import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPaperCapstone
import UnitTangentIterates.ConfiguredFiniteBasePhysicalRearCertificate
import UnitTangentIterates.ChordUniform
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedOuterTubeStep

/-!
# Variable-tube certificates for the prepared chosen chain

The multiplier paper capstone uses the fixed row constants selected by the
final recost closing output.  This file derives those constants directly for
the coherent chosen chain.  In particular, the configured physical base is
strengthened from its older common tube to the tail-local model tube before
the row budget is applied.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainVariableTube

open CoherentPhaseReachableMetricRange
  ConfiguredApproximateDefectPathActualTerminal
  ConfiguredRecursiveEdgeRecostFinitePreparedChosenChain
  ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostMultiplierRowBudget
  CurvatureInterpolation
  VariableMarkedTube

private theorem carrier_curve_deriv
    {D : ConstructedConfiguredSequenceWeighted.Data} {n : ℕ}
    (A : RearCarrier D n) (s : ℝ) :
    HasDerivAt (ev A.data)
      (Complex.exp
        (Complex.I *
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

/-- Every exact configured rear carrier has the acceleration ceiling of its
own configured row. -/
theorem rearCarrier_acceleration_le
    {D : ConstructedConfiguredSequenceWeighted.Data} {n : ℕ}
    (A : RearCarrier D n) (u : ℝ) :
    ‖A.data.2.2 u‖ ≤ ConfiguredInductiveTubeBudget.accBound D.model n := by
  change ‖A.data.2.2 u‖ ≤ (2 * D.Hs n) ^ 2 * D.model.kstar
  have hv : 0 < ‖A.data.2.1 u‖ :=
    lt_of_lt_of_le A.c_pos (A.tube.speed_lb u)
  have hk :
      (D.model.configs n).kH ((2 * D.Hs n) * u) ≤ D.model.kstar :=
    (D.model.configs n).kH_le _
  rw [CurvatureFromMarkedDistance.norm_acc_eq A.tube hv,
    carrier_dataCurv_eq A u,
    abs_of_nonneg ((D.model.configs n).kH_nonneg _),
    norm_vel_eq_perim A.tube u, A.perim_eq]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_right hk (sq_nonneg (2 * D.Hs n)))

/-- The exact carrier geometry recovers the stronger model tube based at the
current tail.  The stored `RearCarrier.tube` supplies regularity and convexity;
the exact `kH` presentation supplies the row-local speed and chord constants. -/
theorem rearCarrier_model_tube
    {D : ConstructedConfiguredSequenceWeighted.Data} {n : ℕ}
    (A : RearCarrier D n) :
    IsTubeMember (2 * D.Hs 0) 0
      (ConfiguredInductiveTubeBudget.chordBase D.model) A.data := by
  have hH0 : 0 < D.Hs 0 := D.separation_zero_pos
  have hkstar : 0 < D.model.kstar :=
    ConstructedConfiguredInductiveTubeBudget.configured_kstar_pos D.model
  have hturn : ∀ s,
      tangentAngle (D.model.configs n).kH D.model.thetaBase
          (s + perim A.data) =
        tangentAngle (D.model.configs n).kH D.model.thetaBase s +
          2 * Real.pi := by
    intro s
    rw [A.perim_eq]
    have hfirst := tangentAngle_add_halfPeriod
      (θ₀ := D.model.thetaBase)
      (D.model.configs n).continuous_kH
      (D.model.configs n).periodic_kH
      (D.model.configs n).integral_kH_eq_pi s
    have hsecond := tangentAngle_add_halfPeriod
      (θ₀ := D.model.thetaBase)
      (D.model.configs n).continuous_kH
      (D.model.configs n).periodic_kH
      (D.model.configs n).integral_kH_eq_pi (s + D.Hs n)
    rw [show s + 2 * D.Hs n = (s + D.Hs n) + D.Hs n by ring,
      hsecond, hfirst]
    ring
  have hcurve : ∀ s,
      HasDerivAt (ev A.data)
        (Complex.exp
          ((tangentAngle (D.model.configs n).kH D.model.thetaBase s : ℂ) *
            Complex.I)) s := by
    intro s
    simpa [mul_comm] using carrier_curve_deriv A s
  have hchord := Marked.chord_of_tube_curvature_ceiling
    A.c_pos A.tube hkstar hcurve
    (carrier_angle_deriv (D := D) n)
    (D.model.configs n).kH_nonneg
    (D.model.configs n).kH_le hturn
  have hchord_H0 :
      ConfiguredInductiveTubeBudget.chordBase D.model ≤ D.Hs 0 := by
    unfold ConfiguredInductiveTubeBudget.chordBase
      ConfiguredInductiveTubeBudget.chordCoeff
    have hmin := min_le_left (1 / 2 : ℝ)
      (Real.pi / (12 * D.model.kstar * D.Hs 0))
    calc
      min (1 / 2 : ℝ) (Real.pi / (12 * D.model.kstar * D.Hs 0)) *
            (2 * D.Hs 0) ≤
          (1 / 2) * (2 * D.Hs 0) :=
        mul_le_mul_of_nonneg_right hmin
          (mul_nonneg (by norm_num) hH0.le)
      _ = D.Hs 0 := by ring
  have hchord_kstar :
      ConfiguredInductiveTubeBudget.chordBase D.model ≤
        Real.pi / (6 * D.model.kstar) := by
    unfold ConfiguredInductiveTubeBudget.chordBase
      ConfiguredInductiveTubeBudget.chordCoeff
    have hmin := min_le_right (1 / 2 : ℝ)
      (Real.pi / (12 * D.model.kstar * D.Hs 0))
    calc
      min (1 / 2 : ℝ) (Real.pi / (12 * D.model.kstar * D.Hs 0)) *
            (2 * D.Hs 0) ≤
          (Real.pi / (12 * D.model.kstar * D.Hs 0)) *
            (2 * D.Hs 0) :=
        mul_le_mul_of_nonneg_right hmin
          (mul_nonneg (by norm_num) hH0.le)
      _ = Real.pi / (6 * D.model.kstar) := by
        field_simp [ne_of_gt hH0, ne_of_gt hkstar]
        <;> ring
  have hconstant :
      ConfiguredInductiveTubeBudget.chordBase D.model ≤
        min (perim A.data / 2) (Real.pi / (6 * D.model.kstar)) := by
    apply le_min
    · rw [A.perim_eq]
      calc
        ConfiguredInductiveTubeBudget.chordBase D.model ≤ D.Hs 0 :=
          hchord_H0
        _ ≤ D.Hs n := D.separation_lower n
        _ = (2 * D.Hs n) / 2 := by ring
    · exact hchord_kstar
  refine
    { hasDerivAt_curve := A.tube.hasDerivAt_curve
      hasDerivAt_vel := A.tube.hasDerivAt_vel
      periodic := A.tube.periodic
      speed_const := A.tube.speed_const
      speed_lb := ?_
      curv_lb := A.tube.curv_lb
      chord := ?_ }
  · intro u
    rw [norm_vel_eq_perim A.tube u, A.perim_eq]
    exact mul_le_mul_of_nonneg_left (D.separation_lower n) (by norm_num)
  · intro u hu v hv
    exact (mul_le_mul_of_nonneg_right hconstant
      (ChordArc.cyc_nonneg hu hv)).trans (hchord u hu v hv)

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

/-- The truthful configured physical initial row has the strong model tube
required by the final row budget, without identifying it with an aligned
model datum. -/
theorem configuredBase_model_tube
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J} (R : RecostClosingOutput J O) (n : ℕ) :
    IsTubeMember (2 * R.data.Hs 0) 0
      (ConfiguredInductiveTubeBudget.chordBase R.data.model) (base R n) := by
  let q := R.totalShift + n
  let P := ConfiguredRecursiveEdgePhysicalInitialData.previousPresentation
    J.scalar q
  let r := ConfiguredGaugeFirstPhysicalSequence.rearPhase
    J.scalar.pair.input J.scalar.model_data P
  change IsTubeMember (2 * R.data.Hs 0) 0
    (ConfiguredInductiveTubeBudget.chordBase R.data.model)
    (ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar q)
  rw [show ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar q =
    MarkedShift.shiftData
      (ConfiguredRecursiveEdgePhysicalInitialData.rearShift J.scalar q)
      (ConfiguredRecursiveEdgePhysicalInitialData.unshiftedRear J.scalar q) by
        rfl]
  apply MarkedShift.isTubeMember_shiftData
  rw [show ConfiguredRecursiveEdgePhysicalInitialData.unshiftedRear J.scalar q =
    RichStageDataPhaseRigidTransport.move P.translation P.rotation r
      (J.scalar.pair.input.carrier q).data by rfl]
  rw [J.scalar.pair.input_carrier q]
  simpa [RichStageDataPhaseRigidTransport.move, closingCarrier] using
    (MarkedRigid.isTubeMember_rigidData P.rotation_norm
      (MarkedShift.isTubeMember_shiftData
        (rearCarrier_model_tube (closingCarrier R n)) r))

/-- The same configured physical initial row has the acceleration ceiling
used by the final row budget. -/
theorem configuredBase_acceleration_le
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J} (R : RecostClosingOutput J O) (n : ℕ) (u : ℝ) :
    ‖(base R n).2.2 u‖ ≤
      ConfiguredInductiveTubeBudget.accBound R.data.model n := by
  let q := R.totalShift + n
  let P := ConfiguredRecursiveEdgePhysicalInitialData.previousPresentation
    J.scalar q
  let r := ConfiguredGaugeFirstPhysicalSequence.rearPhase
    J.scalar.pair.input J.scalar.model_data P
  have h := rearCarrier_acceleration_le (closingCarrier R n)
    (u + ConfiguredRecursiveEdgePhysicalInitialData.rearShift J.scalar q + r)
  change ‖P.rotation *
    (J.scalar.pair.input.carrier q).data.2.2
      (u + ConfiguredRecursiveEdgePhysicalInitialData.rearShift J.scalar q + r)‖ ≤
        ConfiguredInductiveTubeBudget.accBound R.data.model n
  rw [J.scalar.pair.input_carrier q, norm_mul, P.rotation_norm, one_mul]
  simpa [closingCarrier] using h

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  (H : Output R)

/-- The callback-free row budget selected by the final recost closing output. -/
noncomputable def paperBudget : BudgetType H.toClosing :=
  Classical.choice (exists_rowBudget H.toClosing)

/-- At every positive depth, prepared provenance identifies the coherent datum
with a common marking shift of the prepared canonical physical base. -/
theorem ordinaryTube_succ (C : ChosenChain H) (n k : ℕ) :
    IsTubeMember
      ((C.stepData k).input.pre n).geometric.terminal.physical.cq 0
      ((C.stepData k).input.pre n).geometric.terminal.physical.dlt
      ((ChosenChain.system H C).P n (k + 1)) := by
  rw [(ChosenChain.system H C).P_succ_eq_shift_canonical]
  simpa [ChosenChain.canonical] using
    (MarkedShift.isTubeMember_shiftData
      ((C.stepData k).input.pre n).geometric.terminal.zero_floor_tube
      ((ChosenChain.system H C).coherentPhase n k))

/-- Depth zero already lies in the exact fixed variable tube required by the
multiplier paper capstone. -/
theorem variableTube_zero (C : ChosenChain H) (n : ℕ) :
    IsVariableTubeMember
      (H.toClosing.data.Hs 0) (upper H.toClosing n) 0
      (ConfiguredInductiveTubeBudget.chordBase H.toClosing.data.model / 2)
      ((ChosenChain.system H C).P n 0) := by
  rw [(ChosenChain.system H C).P_zero]
  let hbase := configuredBase_model_tube H.toClosing n
  apply ConfiguredRecursiveEdgeRecostedOuterTubeStep.variableTube_of_prefix_step_le_rowRadius
      (paperBudget H) n hbase
      (configuredBase_acceleration_le H.toClosing n)
  · exact hbase.hasDerivAt_curve
  · exact hbase.hasDerivAt_vel
  · exact hbase.periodic
  · intro u
    simpa using hbase.curv_lb u
  · simpa using (paperBudget H).radius_nonnegative n

/-- Every successor depth lies in the same fixed rowwise variable tube. -/
theorem variableTube_succ (C : ChosenChain H) (n k : ℕ) :
    IsVariableTubeMember
      (H.toClosing.data.Hs 0) (upper H.toClosing n) 0
      (ConfiguredInductiveTubeBudget.chordBase H.toClosing.data.model / 2)
      ((ChosenChain.system H C).P n (k + 1)) := by
  let hp := ordinaryTube_succ H C n k
  apply CoherentPhaseReachableMetricRange.System.variableTube_next
    H.toClosing (ChosenChain.system H C) (paperBudget H) n k
    (configuredBase_model_tube H.toClosing n)
    (configuredBase_acceleration_le H.toClosing n)
  · exact hp.hasDerivAt_curve
  · exact hp.hasDerivAt_vel
  · exact hp.periodic
  · intro u
    simpa using hp.curv_lb u

/-- The first prepared successor, stated separately for the depth-one array
field used by downstream assembly. -/
theorem variableTube_one (C : ChosenChain H) (n : ℕ) :
    IsVariableTubeMember
      (H.toClosing.data.Hs 0) (upper H.toClosing n) 0
      (ConfiguredInductiveTubeBudget.chordBase H.toClosing.data.model / 2)
      ((ChosenChain.system H C).P n 1) := by
  simpa using variableTube_succ H C n 0

/-- Unconditional capstone tube membership at every row and every depth. -/
theorem variableTube (C : ChosenChain H) (n k : ℕ) :
    IsVariableTubeMember
      (H.toClosing.data.Hs 0) (upper H.toClosing n) 0
      (ConfiguredInductiveTubeBudget.chordBase H.toClosing.data.model / 2)
      ((ChosenChain.system H C).P n k) := by
  cases k with
  | zero => exact variableTube_zero H C n
  | succ k => simpa [Nat.succ_eq_add_one] using variableTube_succ H C n k

end ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainVariableTube
