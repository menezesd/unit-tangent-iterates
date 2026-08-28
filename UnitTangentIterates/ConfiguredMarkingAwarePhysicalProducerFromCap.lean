import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCapRowBounds
import UnitTangentIterates.ConfiguredPhysicalDiagonalRowBudget
import UnitTangentIterates.ConfiguredAlignedQGeometry
import UnitTangentIterates.VariableTerminalRowTubeStepAdapter

/-!
# Configured physical producer from actual correlated row caps

The large-separation output reserves the sum of the path-shadow conversion
and terminal marking conversion.  Consequently the actual selected
`CapFamily`, together with the exact physical edges, constructs the complete
`PhysicalProducer`; row bounds and convergence are no longer inputs.
-/

noncomputable section

open Set Filter MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed

namespace ConfiguredMarkingAwarePhysicalProducerFromCap

open ConfiguredApproximateDefectPathRowwise
  ConfiguredCanonicalPairSource
  ConfiguredGaugeEndpointLinearRadius
  ConfiguredInductiveTubeBudget
  ConfiguredPhysicalDiagonalRowBudget
  ConstructedConfiguredInductiveTubeBudget
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  EnrichedPhysicalChosenRichFamily
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwarePhysicalCore
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  VariableMarkedTube VariableTerminalRowTubeStepAdapter

/-- Construct the full physical package from only actual selected endpoint
caps and exact finite physical edges. -/
def physicalProducer_of_capFamily
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {pathConversion endpointConversion diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D (combinedConversion pathConversion endpointConversion)
      diagonal Cw)
    {Qmodel : ℕ → Data} {kh0 C0 K : ℝ} {d : ℕ → ℝ}
    (A : ConfiguredCanonicalPairSource.Output
      (shift D L.N) Qmodel kh0 C0 K d)
    (hQ : ∀ n,
      perim (Qmodel n) = 2 * (shift D L.N).Hs n ∧
      ev (Qmodel n) = TwoCapPairsAssembly.front
        ((shift D L.N).kappas n) (shift D L.N).model.thetaBase
        ((shift D L.N).Hs n))
    {P0 P1 khat G1 Cg : ℕ → ℝ} {period : ℕ → ℕ → ℝ}
    {sourceKh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : ConstructionCore
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      (rowError (shiftSequence diagonal L.N))
      P0 P1 khat
      G1 Cg (outputUpper D L)
      ((shift D L.N).Hs 0) (chordBase (shift D L.N).model / 2)
      period (shiftSequence diagonal L.N) sourceKh Qmax
      a MA NA K0 K1 K2)
    (R : CapFamily F (shiftSequence endpointConversion L.N)
      (shiftSequence diagonal L.N))
    (hpath0 : ∀ n, 0 ≤ pathConversion n)
    (hendpoint0 : ∀ n, 0 ≤ endpointConversion n)
    (hdiagonal0 : ∀ n, 0 ≤ diagonal n)
    (hpathConversion : ∀ n,
      c2ConstVar (P0 n) (P1 n)
        (khat n) (G1 n) (Cg n) ≤
          shiftSequence pathConversion L.N n)
    (hkh : ∀ n, sourceKh n = kh0)
    (hbasePhysical : ∀ n, Nonempty (PhysicalRearLimitKinematics kh0
      (F.base.column.step.richStage n).terminalBase
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ (n + 1)))) :
    PhysicalProducer F kh0 ((shift D L.N).Hs 0)
      (chordBase (shift D L.N).model / 2) := by
  let D' := shift D L.N
  let Q := ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ
  let RB := Classical.choice (exists_rowBudget_of_output D L
    (combinedConversion_nonneg hpath0 hendpoint0) hdiagonal0
    Q P1 G1 Cg (ConfiguredAlignedQGeometry.perim_eq A hQ) P0 khat)
  have hsum : Summable (shiftSequence diagonal L.N) := by
    have H := F.defect.summable 0
    change Summable (fun k => shiftSequence diagonal L.N (0 + k)) at H
    simpa only [Nat.zero_add] using H
  have hbaseModel : ∀ n, IsTubeMember (2 * D'.Hs 0) 0
      (chordBase D'.model) (Q n) := by
    intro n
    let hq := ConfiguredAlignedQGeometry.strict_model_tube A hQ n
    exact
      { hasDerivAt_curve := hq.hasDerivAt_curve
        hasDerivAt_vel := hq.hasDerivAt_vel
        periodic := hq.periodic
        speed_const := hq.speed_const
        speed_lb := fun u => by
          rw [norm_vel_eq_perim hq u,
            ConfiguredAlignedQGeometry.perim_eq A hQ n]
          exact mul_le_mul_of_nonneg_left (D'.separation_lower n) (by norm_num)
        curv_lb := hq.curv_lb
        chord := hq.chord }
  have hbaseCommon : ∀ n, IsTubeMember (D'.Hs 0) 0
      (chordBase D'.model / 2) (Q n) :=
    ConfiguredGaugeFirstPhysicalSequence.alignedQ_tube A.input hQ
  let stepPath : ∀ n k, NormalPath (F.columns k n) (F.columns (k + 1) n) :=
    fun n k => (F.chosenColumn k).column.step.richStage n |>.stage.increment
  have hPcurve : ∀ n k u,
      HasDerivAt (⇑(F.columns k n).1) ((F.columns k n).2.1 u) u := by
    intro n k u
    cases k with
    | zero => simpa using (hbaseModel n).hasDerivAt_curve u
    | succ k => exact (F.chosenColumn k).column.step.richStage n |>.stage.rear_curve_deriv u
  have hPvel : ∀ n k u,
      HasDerivAt (⇑(F.columns k n).2.1) ((F.columns k n).2.2 u) u := by
    intro n k u
    cases k with
    | zero => simpa using (hbaseModel n).hasDerivAt_vel u
    | succ k => exact (F.chosenColumn k).column.step.richStage n |>.stage.rear_vel_deriv u
  have hpartial : ∀ n k,
      (∑ j ∈ Finset.range k,
        rowError (shiftSequence diagonal L.N) n j) ≤
      ShadowingTails.tail (rowError (shiftSequence diagonal L.N) n) 0 := by
    intro n k
    simpa [ShadowingTails.tail] using
      (F.defect.summable n).sum_le_tsum (Finset.range k)
        (fun i _ => F.defect.nonnegative n i)
  have hpathRadius : ∀ n,
      c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) *
          ShadowingTails.tail (rowError (shiftSequence diagonal L.N) n) 0 ≤
        rowRadius (shiftSequence pathConversion L.N)
          (shiftSequence diagonal L.N) n := by
    intro n
    unfold rowRadius
    exact mul_le_mul_of_nonneg_right (hpathConversion n)
      (ShadowingTails.tail_nonneg
        (fun k => F.defect.nonnegative n k) 0)
  have hcolumn : ∀ n k, dist (Q n) (F.columns k n) ≤
      rowRadius (shiftSequence pathConversion L.N)
        (shiftSequence diagonal L.N) n :=
    markedDist_le_rowRadius_of_steps (fun _ => rfl) stepPath hPcurve hPvel
      (fun n k => (F.chosenColumn k).column.step.richStage n |>.stage.increment_geometry)
      (fun n k => (F.chosenColumn k).column.step.richStage n |>.stage.increment_cost)
      hpartial hpathRadius
  have hradius : ∀ n, outputRadius D L n =
      rowRadius
        (combinedConversion (shiftSequence pathConversion L.N)
          (shiftSequence endpointConversion L.N))
        (shiftSequence diagonal L.N) n := by
    intro n
    rfl
  let bounds := R.physicalBounds_of_rowBudget hsum
    (fun j => hdiagonal0 (L.N + j))
    (fun n => hpath0 (L.N + n)) (fun n => hendpoint0 (L.N + n))
    RB hradius hbaseModel hbaseCommon
    (fun n => by
      rw [ConfiguredAlignedQGeometry.perim_eq A hQ n]
      exact mul_le_mul_of_nonneg_left (D'.separation_lower n) (by norm_num))
    (ConfiguredAlignedQGeometry.acceleration_le A hQ) hcolumn
  exact R.toPhysicalProducer hsum bounds hkh hbasePhysical

end ConfiguredMarkingAwarePhysicalProducerFromCap

namespace ConfiguredMarkingAwarePhysicalProducerFromCap

open ConfiguredApproximateDefectPathRowwise
  ConfiguredCanonicalPairSource
  ConfiguredGaugeEndpointLinearRadius
  ConfiguredInductiveTubeBudget
  ConfiguredPhysicalDiagonalRowBudget
  ConstructedConfiguredInductiveTubeBudget
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  EnrichedPhysicalChosenRichFamily
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwareCappedProvider
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  VariableMarkedTube VariableTerminalRowTubeStepAdapter

/-- Configured physical producer for the invariant-indexed reachable
recursion. -/
def slicedPhysicalProducer_of_capFamily
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {pathConversion endpointConversion diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D (combinedConversion pathConversion endpointConversion)
      diagonal Cw)
    {Qmodel : ℕ → Data} {kh0 C0 K : ℝ} {d : ℕ → ℝ}
    (A : ConfiguredCanonicalPairSource.Output
      (shift D L.N) Qmodel kh0 C0 K d)
    (hQ : ∀ n, perim (Qmodel n) = 2 * (shift D L.N).Hs n ∧
      ev (Qmodel n) = TwoCapPairsAssembly.front
        ((shift D L.N).kappas n) (shift D L.N).model.thetaBase
        ((shift D L.N).Hs n))
    {P0 P1 khat G1 Cg : ℕ → ℝ} {period : ℕ → ℕ → ℝ}
    {sourceKh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : SlicedConstructionCore
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      (rowError (shiftSequence diagonal L.N)) P0 P1 khat G1 Cg
      (outputUpper D L) ((shift D L.N).Hs 0)
      (chordBase (shift D L.N).model / 2) period
      (shiftSequence diagonal L.N) sourceKh Qmax a MA NA K0 K1 K2)
    (R : SlicedCapFamily F (shiftSequence endpointConversion L.N)
      (shiftSequence diagonal L.N))
    (hpath0 : ∀ n, 0 ≤ pathConversion n)
    (hendpoint0 : ∀ n, 0 ≤ endpointConversion n)
    (hdiagonal0 : ∀ n, 0 ≤ diagonal n)
    (hpathConversion : ∀ n, c2ConstVar (P0 n) (P1 n)
      (khat n) (G1 n) (Cg n) ≤ shiftSequence pathConversion L.N n)
    (hkh : ∀ n, sourceKh n = kh0)
    (hbasePhysical : ∀ n, Nonempty (PhysicalRearLimitKinematics kh0
      (F.base.column.step.richStage n).terminalBase
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ (n + 1)))) :
    SlicedPhysicalProducer F kh0 ((shift D L.N).Hs 0)
      (chordBase (shift D L.N).model / 2) := by
  let D' := shift D L.N
  let Q := ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ
  let RB := Classical.choice (exists_rowBudget_of_output D L
    (combinedConversion_nonneg hpath0 hendpoint0) hdiagonal0
    Q P1 G1 Cg (ConfiguredAlignedQGeometry.perim_eq A hQ) P0 khat)
  have hsum : Summable (shiftSequence diagonal L.N) := by
    have H := F.defect.summable 0
    change Summable (fun k ↦ shiftSequence diagonal L.N (0 + k)) at H
    simpa only [Nat.zero_add] using H
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
          rw [norm_vel_eq_perim hq u, ConfiguredAlignedQGeometry.perim_eq A hQ n]
          exact mul_le_mul_of_nonneg_left (D'.separation_lower n) (by norm_num)
        curv_lb := hq.curv_lb
        chord := hq.chord }
  have hbaseCommon : ∀ n, IsTubeMember (D'.Hs 0) 0
      (chordBase D'.model / 2) (Q n) :=
    ConfiguredGaugeFirstPhysicalSequence.alignedQ_tube A.input hQ
  let stepPath : ∀ n k, NormalPath (F.columns k n) (F.columns (k + 1) n) :=
    fun n k ↦ (F.chosenColumn k).column.step.richStage n |>.stage.increment
  have hPcurve : ∀ n k u,
      HasDerivAt (⇑(F.columns k n).1) ((F.columns k n).2.1 u) u := by
    intro n k u
    cases k with
    | zero => simpa using (hbaseModel n).hasDerivAt_curve u
    | succ k => exact (F.chosenColumn k).column.step.richStage n |>.stage.rear_curve_deriv u
  have hPvel : ∀ n k u,
      HasDerivAt (⇑(F.columns k n).2.1) ((F.columns k n).2.2 u) u := by
    intro n k u
    cases k with
    | zero => simpa using (hbaseModel n).hasDerivAt_vel u
    | succ k => exact (F.chosenColumn k).column.step.richStage n |>.stage.rear_vel_deriv u
  have hpartial : ∀ n k, (∑ j ∈ Finset.range k,
      rowError (shiftSequence diagonal L.N) n j) ≤
      ShadowingTails.tail (rowError (shiftSequence diagonal L.N) n) 0 := by
    intro n k
    simpa [ShadowingTails.tail] using
      (F.defect.summable n).sum_le_tsum (Finset.range k)
        (fun i _ ↦ F.defect.nonnegative n i)
  have hpathRadius : ∀ n,
      c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) *
          ShadowingTails.tail (rowError (shiftSequence diagonal L.N) n) 0 ≤
        rowRadius (shiftSequence pathConversion L.N)
          (shiftSequence diagonal L.N) n := by
    intro n
    unfold rowRadius
    exact mul_le_mul_of_nonneg_right (hpathConversion n)
      (ShadowingTails.tail_nonneg (fun k ↦ F.defect.nonnegative n k) 0)
  have hcolumn : ∀ n k, dist (Q n) (F.columns k n) ≤
      rowRadius (shiftSequence pathConversion L.N)
        (shiftSequence diagonal L.N) n :=
    markedDist_le_rowRadius_of_steps (fun _ ↦ rfl) stepPath hPcurve hPvel
      (fun n k ↦ (F.chosenColumn k).column.step.richStage n |>.stage.increment_geometry)
      (fun n k ↦ (F.chosenColumn k).column.step.richStage n |>.stage.increment_cost)
      hpartial hpathRadius
  have hradius : ∀ n, outputRadius D L n =
      rowRadius (combinedConversion (shiftSequence pathConversion L.N)
        (shiftSequence endpointConversion L.N))
        (shiftSequence diagonal L.N) n := fun _ ↦ rfl
  let bounds := R.physicalBounds_of_rowBudget hsum
    (fun j ↦ hdiagonal0 (L.N + j))
    (fun n ↦ hpath0 (L.N + n)) (fun n ↦ hendpoint0 (L.N + n))
    RB hradius hbaseModel hbaseCommon
    (fun n ↦ by
      rw [ConfiguredAlignedQGeometry.perim_eq A hQ n]
      exact mul_le_mul_of_nonneg_left (D'.separation_lower n) (by norm_num))
    (ConfiguredAlignedQGeometry.acceleration_le A hQ) hcolumn
  exact R.toPhysicalProducer hsum bounds hkh hbasePhysical

end ConfiguredMarkingAwarePhysicalProducerFromCap
