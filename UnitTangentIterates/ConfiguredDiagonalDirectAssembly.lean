import UnitTangentIterates.ConfiguredPhysicalDiagonalRowBudget
import UnitTangentIterates.EnrichedPhysicalStageProducerFromRowBudget
import UnitTangentIterates.ConfiguredAlignedQGeometry
import UnitTangentIterates.PaperMainTheoremDirectProjection

/-!
# Configured direct assembly with a reserved diagonal radius

This theorem performs all geometric and scalar bookkeeping after the enriched
recursive core has been selected.  The reserved conversion may strictly
majorize the path conversion, as required to absorb terminal re-marking.
-/

noncomputable section

open Set MarkedSpace PathMetric

namespace ConfiguredDiagonalDirectAssembly

open ConfiguredApproximateDefectPathRowwise
open ConfiguredCanonicalPairSource
open ConfiguredInductiveTubeBudget
open ConfiguredPhysicalDiagonalRowBudget
open ConstructedConfiguredInductiveTubeBudget
open ConstructedConfiguredInductiveTubeBudget.WeightedData
open DiagonalEnrichedConstructionCoreDirectCapstone
open EnrichedPhysicalChosenRichFamily
open EnrichedPhysicalStageProducerFromRowBudget
open ExponentialDiagonalLargeSeparation
open VariableTerminalRowTubeAdapter

/-- Forget the direct limit package and expose exactly the geometric theorem
asserted in the paper. -/
theorem mainTheorem_of_output
    {Q : ℕ → Data} {P : ℕ → ℕ → Data}
    {e : ℕ → ℕ → ℝ} {P0 P1 khat G1 Cg C : ℕ → ℝ}
    {c dlt : ℝ}
    {O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt}
    {direction : ℂ} {modelWidth H : ℝ}
    (A : PaperFacingVariableTerminalOutput.Output O direction modelWidth H) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L :=
  PaperMainTheoremDirectProjection.of_output A

theorem conclude
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {conversion diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D conversion diagonal Cw)
    {Qmodel : ℕ → Data} {kh C0 K : ℝ} {d : ℕ → ℝ}
    (A : ConfiguredCanonicalPairSource.Output
      (shift D L.N) Qmodel kh C0 K d)
    (hQ : ∀ n,
      perim (Qmodel n) = 2 * (shift D L.N).Hs n ∧
      ev (Qmodel n) = TwoCapPairsAssembly.front
        ((shift D L.N).kappas n) (shift D L.N).model.thetaBase
        ((shift D L.N).Hs n))
    {P1 G1 Cg : ℕ → ℝ}
    {period : ℕ → ℕ → ℝ}
    {GaugeCertificate : GaugeFamily
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      (rowError (shiftSequence diagonal L.N))
      (rowP0 (shift D L.N)) P1 (fun _ ↦ (shift D L.N).kstar)
      G1 Cg (outputUpper D L)
      ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2)}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : ConstructionCore
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      (rowError (shiftSequence diagonal L.N))
      (rowP0 (shift D L.N)) P1 (fun _ ↦ (shift D L.N).kstar)
      G1 Cg (outputUpper D L)
      ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2)
      period (shiftSequence diagonal L.N) GaugeCertificate
      a MA NA K0 K1 K2)
    (G : PhysicalProducer F kh ((shift D L.N).Hs 0)
      (chordBase (shift D L.N).model / 2))
    (hconversion0 : ∀ n, 0 ≤ conversion n)
    (hdiagonal0 : ∀ n, 0 ≤ diagonal n)
    (hpathConversion : ∀ n,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
        (rowP0 (shift D L.N) n) (P1 n) (shift D L.N).kstar
        (G1 n) (Cg n) ≤ shiftSequence conversion L.N n)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    (hmodelWidth : Width.width
      (range (TwoCapPairsAssembly.front
        ((shift D L.N).kappas 0) (shift D L.N).model.thetaBase
        ((shift D L.N).Hs 0))) direction ≤ Cw) :
    Nonempty (
      Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
        (fun n k ↦ columns F.baseProvider F.mapProvider k n)
        (rowError (shiftSequence diagonal L.N))
        (rowP0 (shift D L.N)) P1 (fun _ ↦ (shift D L.N).kstar)
        G1 Cg (outputUpper D L)
        ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2),
        PaperFacingVariableTerminalOutput.Output O direction Cw
          ((shift D L.N).Hs 0)) := by
  let D' := shift D L.N
  let Q := ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ
  obtain ⟨RB⟩ := exists_rowBudget_of_output D L hconversion0 hdiagonal0
    Q P1 G1 Cg (ConfiguredAlignedQGeometry.perim_eq A hQ)
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
        (rowP0 D' n) (P1 n) D'.kstar (G1 n) (Cg n) *
          ShadowingTails.tail (rowError (shiftSequence diagonal L.N) n) 0 ≤
        outputRadius D L n := by
    intro n
    unfold outputRadius rowRadius
    exact mul_le_mul_of_nonneg_right (hpathConversion n)
      (ShadowingTails.tail_nonneg (F.defect.nonnegative n) 0)
  let G' : EnrichedStageProducer F kh (D'.Hs 0) (chordBase D'.model / 2) :=
    toEnrichedStageProducer F G RB hbase
      (ConfiguredAlignedQGeometry.acceleration_le A hQ) hpartial hradius
  apply DiagonalEnrichedConstructionCoreDirectCapstone.exists_paperFacingOutput
    L F G' hpathConversion A.input.kh_nonneg A.input.kh_lt_one hH0
    (half_pos hchord) hH0 hdirection
  · exact ConfiguredAlignedQGeometry.bounded_range A hQ 0
  · rw [ConfiguredAlignedQGeometry.width_zero_eq_model A hQ]
    exact hmodelWidth
  · rw [ConfiguredAlignedQGeometry.totalLength_eq A hQ 0]
  · rfl
  · rfl

end ConfiguredDiagonalDirectAssembly
