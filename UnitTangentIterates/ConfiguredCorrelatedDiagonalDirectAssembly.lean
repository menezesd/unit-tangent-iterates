import UnitTangentIterates.FiniteSmoothRearFamilyCorrelatedDirectCapstone
import UnitTangentIterates.ConfiguredPhysicalDiagonalRowBudget
import UnitTangentIterates.ConfiguredAlignedQGeometry
import UnitTangentIterates.ConfiguredCorrelatedPhysicalProducerFromCap

/-!
# Configured diagonal assembly for the correlated physical core

This is the source-preserving sibling of `ConfiguredDiagonalDirectAssembly`.
All scalar tube and shadow bookkeeping is discharged from the configured
large-separation output.  The only model-side premise left explicit is the
base Harnack certificate, which is not currently retained by the weighted
configured sequence.
-/

noncomputable section

open Set Filter MarkedSpace PathMetric

namespace ConfiguredCorrelatedDiagonalDirectAssembly

open ConfiguredApproximateDefectPathRowwise
open ConfiguredCanonicalPairSource
open ConfiguredInductiveTubeBudget
open ConfiguredPhysicalDiagonalRowBudget
open ConstructedConfiguredInductiveTubeBudget
open ConstructedConfiguredInductiveTubeBudget.WeightedData
open ExponentialDiagonalLargeSeparation
open FiniteSmoothRearFamilyCorrelatedPhysicalCore
open FiniteSmoothRearFamilyCorrelatedDirectCapstone
open VariableMarkedTube

theorem conclude_of_physicalProducer
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {conversion diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D conversion diagonal Cw)
    {Qmodel : ℕ → Data} {kh0 C0 K : ℝ} {d : ℕ → ℝ}
    (A : ConfiguredCanonicalPairSource.Output
      (shift D L.N) Qmodel kh0 C0 K d)
    (hQ : ∀ n,
      perim (Qmodel n) = 2 * (shift D L.N).Hs n ∧
      ev (Qmodel n) = TwoCapPairsAssembly.front
        ((shift D L.N).kappas n) (shift D L.N).model.thetaBase
        ((shift D L.N).Hs n))
    {P1 khat G1 Cg : ℕ → ℝ} {period : ℕ → ℕ → ℝ}
    {sourceKh Qmax Mtotal : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : ConstructionCore
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      (rowError (shiftSequence diagonal L.N))
      (rowP0 (shift D L.N)) P1 khat
      G1 Cg (outputUpper D L)
      ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2)
      period (shiftSequence diagonal L.N) sourceKh Qmax Mtotal
      a MA NA K0 K1 K2)
    (physical : PhysicalProducer F kh0 ((shift D L.N).Hs 0)
      (chordBase (shift D L.N).model / 2))
    (hconversion0 : ∀ n, 0 ≤ conversion n)
    (hdiagonal0 : ∀ n, 0 ≤ diagonal n)
    (hpathConversion : ∀ n,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
        (rowP0 (shift D L.N) n) (P1 n) (khat n)
        (G1 n) (Cg n) ≤ shiftSequence conversion L.N n)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    (hmodelWidth : Width.width
      (range (TwoCapPairsAssembly.front
        ((shift D L.N).kappas 0) (shift D L.N).model.thetaBase
        ((shift D L.N).Hs 0))) direction ≤ Cw) :
    Nonempty (
      Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
        (fun n k ↦ F.columns k n)
        (rowError (shiftSequence diagonal L.N))
        (rowP0 (shift D L.N)) P1 khat
        G1 Cg (outputUpper D L)
        ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2),
        PaperFacingVariableTerminalOutput.Output O direction Cw
          ((shift D L.N).Hs 0)) := by
  let D' := shift D L.N
  let Q := ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ
  obtain ⟨RB⟩ := exists_rowBudget_of_output D L hconversion0 hdiagonal0
    Q P1 G1 Cg (ConfiguredAlignedQGeometry.perim_eq A hQ) khat
  have hH0 : 0 < D'.Hs 0 := D'.separation_zero_pos
  have hkstar : 0 < D'.model.kstar := configured_kstar_pos D'.model
  have hchord : 0 < chordBase D'.model := by
    rw [chordBase_eq_min D'.model hkstar]
    exact lt_min hH0 (div_pos Real.pi_pos (mul_pos (by norm_num) hkstar))
  have hbase : ∀ n, IsTubeMember (2 * D'.Hs 0) 0
      (chordBase D'.model) (Q n) := by
    intro n
    let hq := ConfiguredAlignedQGeometry.strict_model_tube A hQ n
    exact
      { hasDerivAt_curve := hq.hasDerivAt_curve
        hasDerivAt_vel := hq.hasDerivAt_vel
        periodic := hq.periodic
        speed_const := hq.speed_const
        speed_lb := fun u ↦ by
          rw [norm_vel_eq_perim hq u,
            ConfiguredAlignedQGeometry.perim_eq A hQ n]
          exact mul_le_mul_of_nonneg_left (D'.separation_lower n) (by norm_num)
        curv_lb := hq.curv_lb
        chord := hq.chord }
  have hpartial : ∀ n k,
      (∑ j ∈ Finset.range k,
        rowError (shiftSequence diagonal L.N) n j) ≤
      ShadowingTails.tail (rowError (shiftSequence diagonal L.N) n) 0 := by
    intro n k
    simpa [ShadowingTails.tail] using
      (F.defect.summable n).sum_le_tsum (Finset.range k)
        (fun i _ ↦ F.defect.nonnegative n i)
  have hradius : ∀ n,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
        (rowP0 D' n) (P1 n) (khat n) (G1 n) (Cg n) *
          ShadowingTails.tail (rowError (shiftSequence diagonal L.N) n) 0 ≤
        outputRadius D L n := by
    intro n
    unfold outputRadius rowRadius
    exact mul_le_mul_of_nonneg_right (hpathConversion n)
      (ShadowingTails.tail_nonneg (F.defect.nonnegative n) 0)
  apply FiniteSmoothRearFamilyCorrelatedDirectCapstone.exists_paperFacingOutput
    F RB hbase (ConfiguredAlignedQGeometry.acceleration_le A hQ)
      hpartial hradius hH0 (half_pos hchord)
      A.input.kh_nonneg A.input.kh_lt_one physical hH0
      hdirection
  · exact ConfiguredAlignedQGeometry.bounded_range A hQ 0
  · rw [ConfiguredAlignedQGeometry.width_zero_eq_model A hQ]
    exact hmodelWidth
  · rw [ConfiguredAlignedQGeometry.totalLength_eq A hQ 0]
  · intro O
    have hshadow : PaperFacingVariableTerminalOutput.shadowSize O ≤
        rowRadius (shiftSequence conversion L.N)
          (shiftSequence diagonal L.N) 0 := by
      change NormalPathC2IncrementVariableSpeed.c2ConstVar
          (rowP0 D' 0) (P1 0) (khat 0) (G1 0) (Cg 0) *
          ShadowingTails.tail
            (rowError (shiftSequence diagonal L.N) 0) 0 ≤ _
      exact mul_le_mul_of_nonneg_right (hpathConversion 0)
        (ShadowingTails.tail_nonneg
          (fun k ↦ F.defect.nonnegative 0 k) 0)
    have hleft : Cw + 2 * PaperFacingVariableTerminalOutput.shadowSize O ≤
        Cw + 2 * rowRadius (shiftSequence conversion L.N)
          (shiftSequence diagonal L.N) 0 := by linarith
    have hright :
        (2 * D'.Hs 0 - rowRadius (shiftSequence conversion L.N)
            (shiftSequence diagonal L.N) 0) / Real.pi ≤
        (2 * D'.Hs 0 - PaperFacingVariableTerminalOutput.shadowSize O) /
          Real.pi := by
      exact div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
    exact hleft.trans_lt (L.width_gap.trans_le hright)

/-- Configured correlated assembly from the actual selected endpoint caps.
The complete physical producer is derived internally from the row budget,
the constant physical curvature ceiling, and the depth-zero physical edge. -/
theorem conclude
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {pathConversion endpointConversion diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D
      (ConfiguredGaugeEndpointLinearRadius.combinedConversion
        pathConversion endpointConversion) diagonal Cw)
    {Qmodel : ℕ → Data} {kh0 C0 K : ℝ} {d : ℕ → ℝ}
    (A : ConfiguredCanonicalPairSource.Output
      (shift D L.N) Qmodel kh0 C0 K d)
    (hQ : ∀ n,
      perim (Qmodel n) = 2 * (shift D L.N).Hs n ∧
      ev (Qmodel n) = TwoCapPairsAssembly.front
        ((shift D L.N).kappas n) (shift D L.N).model.thetaBase
        ((shift D L.N).Hs n))
    {P1 khat G1 Cg : ℕ → ℝ} {period : ℕ → ℕ → ℝ}
    {sourceKh Qmax Mtotal : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : ConstructionCore
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      (rowError (shiftSequence diagonal L.N))
      (rowP0 (shift D L.N)) P1 khat
      G1 Cg (outputUpper D L)
      ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2)
      period (shiftSequence diagonal L.N) sourceKh Qmax Mtotal
      a MA NA K0 K1 K2)
    (R : CapFamily F (shiftSequence endpointConversion L.N)
      (shiftSequence diagonal L.N))
    (hpath0 : ∀ n, 0 ≤ pathConversion n)
    (hendpoint0 : ∀ n, 0 ≤ endpointConversion n)
    (hdiagonal0 : ∀ n, 0 ≤ diagonal n)
    (hpathConversion : ∀ n,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
        (rowP0 (shift D L.N) n) (P1 n) (khat n)
        (G1 n) (Cg n) ≤ shiftSequence pathConversion L.N n)
    (hkh : ∀ n, sourceKh n = kh0)
    (hbasePhysical : ∀ n, Nonempty (PhysicalRearLimitKinematics kh0
      (F.base.column.step.richStage n).terminalBase
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ (n + 1))))
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    (hmodelWidth : Width.width
      (range (TwoCapPairsAssembly.front
        ((shift D L.N).kappas 0) (shift D L.N).model.thetaBase
        ((shift D L.N).Hs 0))) direction ≤ Cw) :
    Nonempty (
      Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
        (fun n k ↦ F.columns k n)
        (rowError (shiftSequence diagonal L.N))
        (rowP0 (shift D L.N)) P1 khat
        G1 Cg (outputUpper D L)
        ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2),
        PaperFacingVariableTerminalOutput.Output O direction Cw
          ((shift D L.N).Hs 0)) := by
  let physical :=
    ConfiguredCorrelatedPhysicalProducerFromCap.physicalProducer_of_capFamily
      L A hQ F R hpath0 hendpoint0 hdiagonal0 hpathConversion hkh
        hbasePhysical
  apply conclude_of_physicalProducer L A hQ F physical
  · exact ConfiguredGaugeEndpointLinearRadius.combinedConversion_nonneg
      hpath0 hendpoint0
  · exact hdiagonal0
  · intro n
    exact (hpathConversion n).trans (le_add_of_nonneg_right
      (hendpoint0 (L.N + n)))
  · exact hdirection
  · exact hmodelWidth

end ConfiguredCorrelatedDiagonalDirectAssembly
