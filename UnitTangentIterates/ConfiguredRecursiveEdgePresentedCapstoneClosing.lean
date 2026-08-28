import UnitTangentIterates.ConfiguredRecursiveEdgePresentedCapstonePhysicalBounds
import UnitTangentIterates.ConfiguredRecursiveEdgePresentedCapstoneRetainedStrictness

/-!
# Configured closing for reachable presented recursion

This is the final downstream composition before inserting the concrete
reachable provider.  It combines the configured large-separation gap with the
physical bounds and retained rear strictness, then projects the paper-facing
limit to the ordinary curve theorem.
-/

noncomputable section

open Set Function Filter MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePresentedCapstoneClosing

open ConfiguredInductiveTubeBudget
  ConstructedConfiguredInductiveTubeBudget
  ConfiguredAlignedQGeometry
  ConfiguredApproximateDefectPathRowwise
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredGaugeEndpointLinearRadius
  ConfiguredPhysicalDiagonalRowBudget
  ConfiguredRecursiveEdgePresentedCapstoneAdapter
  ConfiguredRecursiveEdgePresentedCapstoneAdapter.RecursiveConstruction
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGrid
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedSlicedInvariant
  RichFamilyPhysicalMarkingIntegration

/-- Configured large separation closes a reachable presented recursion from
its already-constructed physical rows. -/
theorem exists_paperFacingOutput_of_configuredClosing
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {conversion diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D conversion diagonal Cw)
    (hdiagonal : ∀ j, 0 ≤ diagonal j) (hsummable : Summable diagonal)
    {Qmodel : ℕ → Data} {kh0 C0 K : ℝ} {d : ℕ → ℝ}
    (A : ConfiguredCanonicalPairSource.Output
      (shift D L.N) Qmodel kh0 C0 K d)
    (hQ : ∀ n, perim (Qmodel n) = 2 * (shift D L.N).Hs n ∧
      ev (Qmodel n) = TwoCapPairsAssembly.front
        ((shift D L.N).kappas n) (shift D L.N).model.thetaBase
        ((shift D L.N).Hs n))
    {P0 P1 khat G1 Cg : ℕ → ℝ} {period : ℕ → ℕ → ℝ}
    {kh Qmax : ℕ → ℝ} {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : RecursivePresentedConstructionCore
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      (rowError (shiftSequence diagonal L.N))
      P0 P1 khat G1 Cg (outputUpper D L)
      ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2)
      period (shiftSequence diagonal L.N) kh Qmax a MA NA K0 K1 K2)
    (tube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      ((shift D L.N).Hs 0) (outputUpper D L n) 0
      (chordBase (shift D L.N).model / 2) (markedGrid F n k))
    (physical : PhysicalRowBounds (rearRows F) (markedGrid F)
      ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2))
    (physicalDefect : ∀ n, Tendsto
      (fun k => dist (rearRows F n k) (markedGrid F n k))
      atTop (nhds 0))
    (hpathConversion : ∀ n,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
        (P0 n) (P1 n) (khat n) (G1 n) (Cg n) ≤
          shiftSequence conversion L.N n)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    (hmodelWidth : Width.width
      (range (TwoCapPairsAssembly.front ((shift D L.N).kappas 0)
        (shift D L.N).model.thetaBase ((shift D L.N).Hs 0))) direction ≤ Cw) :
    Nonempty (
      Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
        (markedGrid F)
        (FiniteSmoothRearFamilyMarkingAwarePresentedSlicedAssembly.ConstructionCore.depthError
          (rowError (shiftSequence diagonal L.N)))
        P0 P1 khat G1 Cg (outputUpper D L)
        ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2),
        PaperFacingVariableTerminalOutput.Output O direction Cw
          ((shift D L.N).Hs 0)) := by
  let D' := shift D L.N
  let Q := ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ
  have hH0 : 0 < D'.Hs 0 := D'.separation_zero_pos
  have hkstar : 0 < D'.model.kstar := configured_kstar_pos D'.model
  have hchord : 0 < chordBase D'.model := by
    rw [chordBase_eq_min D'.model hkstar]
    exact lt_min hH0 (div_pos Real.pi_pos (mul_pos (by norm_num) hkstar))
  have herr0 : ∀ n k,
      0 ≤ rowError (shiftSequence diagonal L.N) n k := by
    intro n k
    exact hdiagonal (L.N + (n + k))
  have herrsum : ∀ n,
      Summable (rowError (shiftSequence diagonal L.N) n) := by
    intro n
    simpa [rowError, shiftSequence, Nat.add_assoc] using
      ShadowingTails.summable_shift hsummable (L.N + n)
  apply exists_paperFacingOutput_of_terminalStrictness F herr0 herrsum tube
    physical hH0 (half_pos hchord) physicalDefect hH0 hdirection
  · exact ConfiguredAlignedQGeometry.bounded_range A hQ 0
  · rw [ConfiguredAlignedQGeometry.width_zero_eq_model A hQ]
    exact hmodelWidth
  · rw [ConfiguredAlignedQGeometry.totalLength_eq A hQ 0]
  · intro O
    have htail : ShadowingTails.tail
        (FiniteSmoothRearFamilyMarkingAwarePresentedSlicedAssembly.ConstructionCore.depthError
          (rowError (shiftSequence diagonal L.N)) 0) 0 ≤
        ShadowingTails.tail (rowError (shiftSequence diagonal L.N) 0) 0 := by
      have hanti := ShadowingTails.tail_antitone (herrsum 0) (herr0 0)
        (Nat.zero_le 1)
      simpa [FiniteSmoothRearFamilyMarkingAwarePresentedSlicedAssembly.ConstructionCore.depthError,
        ShadowingTails.tail, Nat.add_assoc, Nat.add_comm] using hanti
    have hshadow : PaperFacingVariableTerminalOutput.shadowSize O ≤
        rowRadius (shiftSequence conversion L.N)
          (shiftSequence diagonal L.N) 0 := by
      change NormalPathC2IncrementVariableSpeed.c2ConstVar
          (P0 0) (P1 0) (khat 0) (G1 0) (Cg 0) *
          ShadowingTails.tail
            (FiniteSmoothRearFamilyMarkingAwarePresentedSlicedAssembly.ConstructionCore.depthError
              (rowError (shiftSequence diagonal L.N)) 0) 0 ≤ _
      calc
        _ ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
              (P0 0) (P1 0) (khat 0) (G1 0) (Cg 0) *
              ShadowingTails.tail
                (rowError (shiftSequence diagonal L.N) 0) 0 :=
          mul_le_mul_of_nonneg_left htail
            (NormalPathC2IncrementVariableSpeed.c2ConstVar_nonneg _ _ _ _ _)
        _ ≤ shiftSequence conversion L.N 0 *
              ShadowingTails.tail
                (rowError (shiftSequence diagonal L.N) 0) 0 :=
          mul_le_mul_of_nonneg_right (hpathConversion 0)
            (ShadowingTails.tail_nonneg (herr0 0) 0)
        _ = rowRadius (shiftSequence conversion L.N)
              (shiftSequence diagonal L.N) 0 := rfl
    have hleft : Cw + 2 * PaperFacingVariableTerminalOutput.shadowSize O ≤
        Cw + 2 * rowRadius (shiftSequence conversion L.N)
          (shiftSequence diagonal L.N) 0 := by linarith
    have hright :
        (2 * D'.Hs 0 - rowRadius (shiftSequence conversion L.N)
            (shiftSequence diagonal L.N) 0) / Real.pi ≤
        (2 * D'.Hs 0 - PaperFacingVariableTerminalOutput.shadowSize O) /
          Real.pi :=
      div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
    exact hleft.trans_lt (L.width_gap.trans_le hright)

/-- Direct ordinary-curve projection of the configured reachable output. -/
theorem paperMain_of_configuredClosing
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {conversion diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D conversion diagonal Cw)
    (hdiagonal : ∀ j, 0 ≤ diagonal j) (hsummable : Summable diagonal)
    {Qmodel : ℕ → Data} {kh0 C0 K : ℝ} {d : ℕ → ℝ}
    (A : ConfiguredCanonicalPairSource.Output
      (shift D L.N) Qmodel kh0 C0 K d)
    (hQ : ∀ n, perim (Qmodel n) = 2 * (shift D L.N).Hs n ∧
      ev (Qmodel n) = TwoCapPairsAssembly.front
        ((shift D L.N).kappas n) (shift D L.N).model.thetaBase
        ((shift D L.N).Hs n))
    {P0 P1 khat G1 Cg : ℕ → ℝ} {period : ℕ → ℕ → ℝ}
    {kh Qmax : ℕ → ℝ} {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : RecursivePresentedConstructionCore
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      (rowError (shiftSequence diagonal L.N))
      P0 P1 khat G1 Cg (outputUpper D L)
      ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2)
      period (shiftSequence diagonal L.N) kh Qmax a MA NA K0 K1 K2)
    (tube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      ((shift D L.N).Hs 0) (outputUpper D L n) 0
      (chordBase (shift D L.N).model / 2) (markedGrid F n k))
    (physical : PhysicalRowBounds (rearRows F) (markedGrid F)
      ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2))
    (physicalDefect : ∀ n, Tendsto
      (fun k => dist (rearRows F n k) (markedGrid F n k))
      atTop (nhds 0))
    (hpathConversion : ∀ n,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
        (P0 n) (P1 n) (khat n) (G1 n) (Cg n) ≤
          shiftSequence conversion L.N n)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    (hmodelWidth : Width.width
      (range (TwoCapPairsAssembly.front ((shift D L.N).kappas 0)
        (shift D L.N).model.thetaBase ((shift D L.N).Hs 0))) direction ≤ Cw) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L0 : ℝ,
      0 < L0 ∧ Function.Periodic (Gamma 0) L0 ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L0 := by
  apply paperMain_of_paperFacingOutput
  exact exists_paperFacingOutput_of_configuredClosing L hdiagonal hsummable A hQ
    F tube physical physicalDefect hpathConversion hdirection hmodelWidth

end ConfiguredRecursiveEdgePresentedCapstoneClosing
