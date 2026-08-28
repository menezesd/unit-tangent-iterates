import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0CappedRowProduction
import UnitTangentIterates.ConfiguredPhysicalDiagonalRowBudget

/-! # Row-fixed period ceiling for reachable edge recursion -/

noncomputable section

open MarkedSpace

namespace ConfiguredRecursiveEdgeReachableQmax

open ConfiguredAlignedQGeometry
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredPhysicalDiagonalRowBudget
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0Growth
  ExponentialDiagonalLargeSeparation
  VariableTerminalRowTubeAdapter

variable {MA NA : ℝ}

/-- The row-fixed recursive ceiling attached to any configured diagonal
output.  In particular this applies unchanged when the physical diagonal is
widened to retain composition-density coefficients. -/
def recursiveQmaxOfOutput
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {conversion diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D conversion diagonal Cw) (n : ℕ) : ℝ :=
  outputUpper D L (n + 2)

theorem outputRadius_nonnegative_of_output
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {conversion diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D conversion diagonal Cw)
    (hconversion : ∀ j, 0 ≤ conversion j)
    (hdiagonal : ∀ j, 0 ≤ diagonal j) (n : ℕ) :
    0 ≤ outputRadius D L n := by
  unfold outputRadius rowRadius
  exact mul_nonneg (hconversion (L.N + n))
    (ShadowingTails.tail_nonneg
      (fun k ↦ hdiagonal (L.N + (n + k))) 0)

theorem recursiveQmaxOfOutput_pos
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {conversion diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D conversion diagonal Cw)
    (hconversion : ∀ j, 0 ≤ conversion j)
    (hdiagonal : ∀ j, 0 ≤ diagonal j) (n : ℕ) :
    0 < recursiveQmaxOfOutput D L n := by
  unfold recursiveQmaxOfOutput outputUpper
  have hH := (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
    D L.N).model.separation_pos (n + 2)
  have hr := outputRadius_nonnegative_of_output D L hconversion hdiagonal (n + 2)
  nlinarith

/-- The analytic successor in row `n` consumes the old source in row `n+1`;
that source is carried by the physical rear row `n+2`.  Its row-budget ceiling
is therefore the configured upper speed at `n+2`.  This datum exists before
the recursive construction and introduces no circular dependency on its
eventual `PhysicalRowBounds`. -/
def recursiveQmax
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) : ℝ :=
  recursiveQmaxOfOutput O.E.data O.large n

@[simp] theorem recursiveQmax_eq_rowC
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    recursiveQmax O n = rowC O (n + 2) := rfl

private noncomputable def scalarRowBudget
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) :
    RowBudget
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ O.pair.input O.model_data)
      (ConfiguredApproximateDefectPathRowwise.rowP0
        (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
          O.E.data O.large.N))
      (fun _ ↦ 0) (fun _ ↦
        (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
          O.E.data O.large.N).kstar)
      (fun _ ↦ 0) (fun _ ↦ 0)
      (fun _ ↦ 2 *
        (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
          O.E.data O.large.N).Hs 0)
      (fun _ ↦ ConfiguredInductiveTubeBudget.chordBase
        (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
          O.E.data O.large.N).model)
      (ConfiguredInductiveTubeBudget.accBound
        (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
          O.E.data O.large.N).model)
      (outputRadius O.E.data O.large) (outputRho O.E.data O.large)
      (outputUpper O.E.data O.large)
      ((ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
        O.E.data O.large.N).Hs 0)
      (ConfiguredInductiveTubeBudget.chordBase
        (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
          O.E.data O.large.N).model / 2) :=
  Classical.choice (exists_rowBudget_of_output O.E.data O.large
    (edgeCombinedConversion_nonnegative O.E.data
      sourceKh_nonnegative sourceKh_lt_one)
    (edgePhysicalDefect_nonnegative O.E.data)
    (ConfiguredGaugeFirstPhysicalSequence.alignedQ O.pair.input O.model_data)
    (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0)
    (ConfiguredAlignedQGeometry.perim_eq O.pair O.model_data)
    (P0 := ConfiguredApproximateDefectPathRowwise.rowP0
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
        O.E.data O.large.N))
    (khat := fun _ ↦
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
        O.E.data O.large.N).kstar))

theorem outputRadius_nonnegative
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    0 ≤ outputRadius O.E.data O.large n :=
  (scalarRowBudget O).radius_nonnegative n

theorem recursiveQmax_pos
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    0 < recursiveQmax O n := by
  unfold recursiveQmax recursiveQmaxOfOutput outputUpper
  have hH := (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
    O.E.data O.large.N).model.separation_pos (n + 2)
  have hr := outputRadius_nonnegative O (n + 2)
  nlinarith

theorem model_perim_le_recursiveQmax
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    perim (ConfiguredGaugeFirstPhysicalSequence.alignedQ
      O.pair.input O.model_data (n + 2)) ≤ recursiveQmax O n := by
  rw [ConfiguredAlignedQGeometry.perim_eq O.pair O.model_data]
  unfold recursiveQmax recursiveQmaxOfOutput outputUpper
  exact le_add_of_nonneg_right (outputRadius_nonnegative O (n + 2))

end ConfiguredRecursiveEdgeReachableQmax
