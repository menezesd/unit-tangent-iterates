import UnitTangentIterates.ConfiguredRecursiveEdgePresentedCapstoneClosing
import UnitTangentIterates.ConfiguredRecursiveEdgePresentedCapstonePhysicalBounds

/-! # Row-budget closure for the reachable presented capstone -/

noncomputable section

open Function Set Filter MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePresentedCapstoneRowBudgetClosing

open ConfiguredAlignedQGeometry
  ConfiguredGaugeEndpointLinearRadius
  ConfiguredInductiveTubeBudget
  ConfiguredPhysicalDiagonalRowBudget
  ConfiguredRecursiveEdgePresentedCapstoneAdapter
  ConfiguredRecursiveEdgePresentedCapstoneAdapter.RecursiveConstruction
  ConfiguredRecursiveEdgePresentedCapstoneClosing
  ConfiguredRecursiveEdgePresentedCapstonePhysicalBounds
  ConstructedConfiguredInductiveTubeBudget
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGrid
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedSlicedInvariant
  VariableTerminalRowTubeAdapter

/-- Configured row budgets and the actual presented terminal caps discharge both
the uniform physical bounds and endpoint-defect convergence required by the
paper theorem.  The endpoint part of the radius is kept explicit; the equality
`hcombined` records that the configured diagonal budget already contains it. -/
theorem paperMain_of_configuredRowBudget_and_presentedCaps
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {conversion diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D conversion diagonal Cw)
    (hdiagonal : ∀ j, 0 ≤ diagonal j)
    (hsummable : Summable diagonal)
    {Qmodel : ℕ → Data} {kh0 C0 K : ℝ} {d : ℕ → ℝ}
    (A : ConfiguredCanonicalPairSource.Output (shift D L.N) Qmodel kh0 C0 K d)
    (hQ : ∀ n,
      perim (Qmodel n) = 2 * (shift D L.N).Hs n ∧
      ev (Qmodel n) = TwoCapPairsAssembly.front
        ((shift D L.N).kappas n) (shift D L.N).model.thetaBase
          ((shift D L.N).Hs n))
    {P0 P1 khat G1 Cg : ℕ → ℝ}
    {period : ℕ → ℕ → ℝ} {kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : RecursivePresentedConstructionCore
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      (rowError (shiftSequence diagonal L.N)) P0 P1 khat G1 Cg
      (outputUpper D L) ((shift D L.N).Hs 0)
      (chordBase (shift D L.N).model / 2) period
      (shiftSequence diagonal L.N) kh Qmax a MA NA K0 K1 K2)
    {baseConversion endpointConversion : ℕ → ℝ}
    (hbaseConversion : ∀ n, 0 ≤ baseConversion n)
    (hendpoint : ∀ n, 0 ≤ endpointConversion n)
    (hcombined : ∀ n,
      combinedConversion baseConversion endpointConversion n =
        shiftSequence conversion L.N n)
    (hpathConversion : ∀ n,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
        (P0 n) (P1 n) (khat n) (G1 n) (Cg n) ≤ baseConversion n)
    (B : RowBudget
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      P0 P1 khat G1 Cg
      (fun _ ↦ 2 * (shift D L.N).Hs 0)
      (fun _ ↦ chordBase (shift D L.N).model)
      (accBound (shift D L.N).model)
      (outputRadius D L) (outputRho D L) (outputUpper D L)
      ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2))
    (markedTube : ∀ n k,
      VariableMarkedTube.IsVariableTubeMember ((shift D L.N).Hs 0)
        (outputUpper D L n) 0 (chordBase (shift D L.N).model / 2)
        (markedGrid F n k))
    {M : ℝ} (hM : 0 ≤ M)
    (caps : ∀ n k, PresentedRowCap ((rowFamilyAt F k).row n) M
      (endpointConversion n) (shiftSequence diagonal L.N (n + (k + 1))))
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    (hmodelWidth : Width.width
      (range (TwoCapPairsAssembly.front ((shift D L.N).kappas 0)
        (shift D L.N).model.thetaBase ((shift D L.N).Hs 0))) direction ≤ Cw) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L0,
      0 < L0 ∧ Periodic (Gamma 0) L0 ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L0 := by
  let D' := shift D L.N
  let Q := ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ
  have hH0 : 0 < D'.Hs 0 := D'.separation_zero_pos
  have hkstar : 0 < D'.model.kstar := configured_kstar_pos D'.model
  have hchord : 0 < chordBase D'.model := by
    rw [chordBase_eq_min D'.model hkstar]
    exact lt_min hH0
      (div_pos Real.pi_pos (mul_pos (by norm_num) hkstar))
  have hsumShift : Summable (shiftSequence diagonal L.N) := by
    change Summable (fun n ↦ diagonal (L.N + n))
    convert (summable_nat_add_iff (f := diagonal) L.N).2 hsummable using 1
    funext n
    rw [Nat.add_comm]
  have hdiagShift : ∀ j, 0 ≤ shiftSequence diagonal L.N j := by
    intro j
    exact hdiagonal (L.N + j)
  have hbaseModel : ∀ n, IsTubeMember (2 * D'.Hs 0) 0
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
  have hbaseCommon : ∀ n, IsTubeMember (D'.Hs 0) 0
      (chordBase D'.model / 2) (Q n) := by
    intro n
    exact (hbaseModel n).mono (by linarith) (by linarith)
  have hbasePerim : ∀ n, 2 * D'.Hs 0 ≤ perim (Q n) := by
    intro n
    rw [ConfiguredAlignedQGeometry.perim_eq A hQ n]
    exact mul_le_mul_of_nonneg_left (D'.separation_lower n) (by norm_num)
  have hbaseAcc : ∀ n u, ‖(Q n).2.2 u‖ ≤ accBound D'.model n := by
    intro n u
    exact ConfiguredAlignedQGeometry.acceleration_le A hQ n u
  have herror : ∀ n k,
      rowError (shiftSequence diagonal L.N) n (k + 1) =
        shiftSequence diagonal L.N (n + (k + 1)) := by
    intro n k
    rfl
  have hradius : ∀ n, outputRadius D L n =
      rowRadius (combinedConversion baseConversion endpointConversion)
        (shiftSequence diagonal L.N) n := by
    intro n
    unfold outputRadius rowRadius
    rw [hcombined n]
  let physical := physicalRowBounds_of_rowBudget_and_caps F hsumShift
    hdiagShift hbaseConversion hpathConversion hendpoint herror B hradius
    hbaseModel hbaseCommon hbasePerim hbaseAcc markedTube hM caps
  have hsummableRows : ∀ n,
      Summable (rowError (shiftSequence diagonal L.N) n) := by
    intro n
    simpa [rowError, Nat.add_comm] using
      (summable_nat_add_iff (f := shiftSequence diagonal L.N) n).2 hsumShift
  have physicalDefect : ∀ n, Tendsto
      (fun k ↦ dist (rearRows F n k) (markedGrid F n k)) atTop (nhds 0) := by
    intro n
    exact physicalDefect_tendsto_of_summable_rowCaps F hM endpointConversion
      (fun i k ↦ by simpa [rowError] using caps i k) hsummableRows n
  have hpathTotal : ∀ n,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
        (P0 n) (P1 n) (khat n) (G1 n) (Cg n) ≤
          shiftSequence conversion L.N n := by
    intro n
    rw [← hcombined n]
    exact (hpathConversion n).trans
      (le_add_of_nonneg_right (hendpoint n))
  exact paperMain_of_configuredClosing L hdiagonal hsummable A hQ F markedTube
    physical physicalDefect hpathTotal hdirection hmodelWidth

/-- Final downstream specialization with the scalar row budget constructed
from the configured large-separation output.  The presented transition uses
the identity junction (`MA = 1`, `NA = 0`); no capstone estimate depends on
the remaining transition constants. -/
theorem paperMain_of_configuredPresentedCore
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {conversion diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D conversion diagonal Cw)
    (hconversion : ∀ j, 0 ≤ conversion j)
    (hdiagonal : ∀ j, 0 ≤ diagonal j)
    (hsummable : Summable diagonal)
    {Qmodel : ℕ → Data} {kh0 C0 K : ℝ} {d : ℕ → ℝ}
    (A : ConfiguredCanonicalPairSource.Output (shift D L.N) Qmodel kh0 C0 K d)
    (hQ : ∀ n,
      perim (Qmodel n) = 2 * (shift D L.N).Hs n ∧
      ev (Qmodel n) = TwoCapPairsAssembly.front
        ((shift D L.N).kappas n) (shift D L.N).model.thetaBase
          ((shift D L.N).Hs n))
    {P0 P1 khat G1 Cg : ℕ → ℝ}
    {period : ℕ → ℕ → ℝ} {kh Qmax : ℕ → ℝ}
    {a : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : RecursivePresentedConstructionCore
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      (rowError (shiftSequence diagonal L.N)) P0 P1 khat G1 Cg
      (outputUpper D L) ((shift D L.N).Hs 0)
      (chordBase (shift D L.N).model / 2) period
      (shiftSequence diagonal L.N) kh Qmax a
      (fun _ _ ↦ 1) (fun _ _ ↦ 0) K0 K1 K2)
    {baseConversion endpointConversion : ℕ → ℝ}
    (hbaseConversion : ∀ n, 0 ≤ baseConversion n)
    (hendpoint : ∀ n, 0 ≤ endpointConversion n)
    (hcombined : ∀ n,
      combinedConversion baseConversion endpointConversion n =
        shiftSequence conversion L.N n)
    (hpathConversion : ∀ n,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
        (P0 n) (P1 n) (khat n) (G1 n) (Cg n) ≤ baseConversion n)
    (markedTube : ∀ n k,
      VariableMarkedTube.IsVariableTubeMember ((shift D L.N).Hs 0)
        (outputUpper D L n) 0 (chordBase (shift D L.N).model / 2)
        (markedGrid F n k))
    {M : ℝ} (hM : 0 ≤ M)
    (caps : ∀ n k, PresentedRowCap ((rowFamilyAt F k).row n) M
      (endpointConversion n) (shiftSequence diagonal L.N (n + (k + 1))))
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    (hmodelWidth : Width.width
      (range (TwoCapPairsAssembly.front ((shift D L.N).kappas 0)
        (shift D L.N).model.thetaBase ((shift D L.N).Hs 0))) direction ≤ Cw) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L0,
      0 < L0 ∧ Periodic (Gamma 0) L0 ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L0 := by
  let B := Classical.choice (exists_rowBudget_of_output D L hconversion
    hdiagonal (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
    P1 G1 Cg (ConfiguredAlignedQGeometry.perim_eq A hQ)
    (P0 := P0) (khat := khat))
  exact paperMain_of_configuredRowBudget_and_presentedCaps L hdiagonal
    hsummable A hQ F hbaseConversion hendpoint hcombined hpathConversion B
    markedTube hM caps hdirection hmodelWidth

end ConfiguredRecursiveEdgePresentedCapstoneRowBudgetClosing
