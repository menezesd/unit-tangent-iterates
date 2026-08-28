import UnitTangentIterates.ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal
import UnitTangentIterates.ConfiguredRecursiveEdgeFinitePresentedPaperCapstone

/-!
# Paper capstone with the period-scaled recost diagonal

This adapter replaces every scalar closing premise by the canonical
period-scaled recost output.  The remaining input is one geometric record:
actual displayed cells, their physical sidecars, and the depth-zero model
identification.
-/

noncomputable section

open Function Set Filter Topology MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed VariableMarkedTube

namespace ConfiguredRecursiveEdgeRecostScaledPaperCapstone

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgeFinitePresentedPaperCapstone
  ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
  FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays

open FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays.GeometricArray

/-- Configured data after the row-jet prefix, before the new recost closing
shift is selected. -/
abbrev data
    (J : RowJetScalarOutput choice.MA0 choice.NA0) :
    ConstructedConfiguredSequenceWeighted.Data :=
  shift J.scalar.E.data J.scalar.large.N

/-- Canonical period-scaled closing output at the row-jet stage. -/
noncomputable def large
    (J : RowJetScalarOutput choice.MA0 choice.NA0) :
    ExponentialDiagonalLargeSeparation.Output (data J) (fun _ ↦ 1)
      (recostDirectDiagonal (data J) choice.MA0 choice.NA0 distortionTotal
        physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
        physicalTransitionCeilings.C2 J.scalar.Mend) J.scalar.Cw :=
  recostWeightedOutput (data J) choice.MA0 choice.NA0 distortionTotal
    physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
    physicalTransitionCeilings.C2 J.scalar.Mend J.scalar.Cw
    choice.MA0_nonnegative choice.NA0_nonnegative
    J.scalar.Mend_positive.le J.scalar.Cw_nonnegative

/-- Public row/depth error after the canonical recost closing shift. -/
def error (J : RowJetScalarOutput choice.MA0 choice.NA0)
    (n k : ℕ) : ℝ :=
  shiftSequence
    (recostDirectDiagonal (data J) choice.MA0 choice.NA0 distortionTotal
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2 J.scalar.Mend)
    (large J).N (n + k)

/-- The unshifted row-jet-data index represented by a displayed cell. -/
def publicIndex (J : RowJetScalarOutput choice.MA0 choice.NA0)
    (n k : ℕ) : ℕ :=
  (large J).N + n + k

theorem error_eq_directDiagonal
    (J : RowJetScalarOutput choice.MA0 choice.NA0) (n k : ℕ) :
    error J n k =
      recostDirectDiagonal (data J) choice.MA0 choice.NA0 distortionTotal
        physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
        physicalTransitionCeilings.C2 J.scalar.Mend (publicIndex J n k) := by
  simp [error, publicIndex, shiftSequence, Nat.add_assoc]

theorem error_nonnegative
    (J : RowJetScalarOutput choice.MA0 choice.NA0) :
    ∀ n k, 0 ≤ error J n k := by
  intro n k
  rw [error_eq_directDiagonal]
  exact recostDirectDiagonal_nonnegative (data J) _

theorem error_summable
    (J : RowJetScalarOutput choice.MA0 choice.NA0) :
    ∀ n, Summable (error J n) := by
  have hs := recostDirectDiagonal_summable (data J)
    (E0 := distortionTotal)
    (C0 := physicalTransitionCeilings.C0)
    (C1 := physicalTransitionCeilings.C1)
    (C2 := physicalTransitionCeilings.C2)
    choice.MA0_nonnegative choice.NA0_nonnegative
    J.scalar.Mend_positive.le
  intro n
  simpa [error, shiftSequence, Nat.add_assoc] using
    ShadowingTails.summable_shift hs ((large J).N + n)

/-- Recursive/geometric data before scalar fields are inserted into the
presented-array record. -/
structure GeometricCore
    (J : RowJetScalarOutput choice.MA0 choice.NA0) where
  Q : ℕ → Data
  P : ℕ → ℕ → Data
  B0 : ℕ → Data
  C : ℕ → ℝ
  c : ℝ
  dlt : ℝ
  cell : ∀ n k, Cell P n k
  base : ∀ n, P n 0 = Q n
  tube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (P n k)
  stepDistance : ∀ n k,
    dist (P n k) (P n (k + 1)) ≤ error J n k

namespace GeometricCore

/-- The actual presented array with all scalar fields discharged by the
recost diagonal.  The bookkeeping conversion is one because the conversion
has already been paid inside `error`. -/
def array {J : RowJetScalarOutput choice.MA0 choice.NA0}
    (G : GeometricCore J) :
    Array G.Q G.P (error J)
      ActualStageProvider.paperP0 ActualStageProvider.paperP1
      ActualStageProvider.paperKhat ActualStageProvider.paperG1
      ActualStageProvider.paperCg G.C G.c G.dlt where
  cell := G.cell
  base := G.base
  error_nonnegative := error_nonnegative J
  error_summable := error_summable J
  tube := G.tube
  stepDistance := by
    intro n k
    simpa [ActualStageProvider.paper_rowC] using G.stepDistance n k

end GeometricCore

/-- The single non-scalar input retained by the recost capstone. -/
structure DirectInput
    (J : RowJetScalarOutput choice.MA0 choice.NA0) where
  core : GeometricCore J
  kh0 : ℝ
  cb : ℝ
  db : ℝ
  cp : ℝ
  dp : ℝ
  physical :
    FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays.GeometricArray.Package
      core.array core.B0 kh0 cb db cp dp
  kh0_nonnegative : 0 ≤ kh0
  kh0_lt_one : kh0 < 1
  cb_pos : 0 < cb
  db_pos : 0 < db
  cp_pos : 0 < cp
  c_pos : 0 < core.c
  Q_zero : core.Q 0 = J.scalar.Q (large J).N

namespace DirectInput

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}

private theorem base_bounded (I : DirectInput J) :
    Bornology.IsBounded (range (⇑(I.core.Q 0).1)) := by
  rw [← I.core.base 0]
  apply CurveDistance.isBounded_range_of_periodic
  · exact continuous_iff_continuousAt.mpr fun u ↦
      ((I.core.tube 0 0).hasDerivAt_curve u).continuousAt
  · exact (I.core.tube 0 0).periodic
  · norm_num

private theorem base_width (I : DirectInput J) :
    Width.width (range (⇑(I.core.Q 0).1))
      (J.scalar.direction (J.scalar.large.N + (large J).N)) ≤
        J.scalar.Cw := by
  rw [I.Q_zero]
  have hper : perim (J.scalar.Q (large J).N) ≠ 0 := by
    rw [(J.scalar.model_data (large J).N).1]
    exact (mul_pos (by norm_num)
      ((shift J.scalar.E.data J.scalar.large.N).model.separation_pos
        (large J).N)).ne'
  rw [← MarkedSpace.range_ev_of_perim_ne_zero hper]
  rw [(J.scalar.model_data (large J).N).2]
  simpa [shift, Nat.add_assoc] using
    J.scalar.model_width (J.scalar.large.N + (large J).N)

private theorem base_length (I : DirectInput J) :
    2 * (shift (data J) (large J).N).Hs 0 ≤
      MarkedReparam.totalLength (fun u ↦ (I.core.Q 0).2.1 u) := by
  rw [I.Q_zero,
    VariableMarkedPhysicalLength.totalLength_eq_perim_of_tube
      (J.scalar.pair.input.front_tube (large J).N),
    (J.scalar.model_data (large J).N).1]
  simp [data, shift, Nat.add_assoc]

private theorem universal_gap (I : DirectInput J) :
    ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      I.core.Q I.core.P (error J)
      ActualStageProvider.paperP0 ActualStageProvider.paperP1
      ActualStageProvider.paperKhat ActualStageProvider.paperG1
      ActualStageProvider.paperCg I.core.C I.core.c I.core.dlt,
      J.scalar.Cw + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * (shift (data J) (large J).N).Hs 0 -
          PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi := by
  intro O
  have hshadow : PaperFacingVariableTerminalOutput.shadowSize O =
      rowRadius (shiftSequence (fun _ ↦ 1) (large J).N)
        (shiftSequence
          (recostDirectDiagonal (data J) choice.MA0 choice.NA0
            distortionTotal physicalTransitionCeilings.C0
            physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
            J.scalar.Mend) (large J).N) 0 := by
    simp [PaperFacingVariableTerminalOutput.shadowSize,
      ActualStageProvider.paper_rowC, error, rowRadius, rowError,
      ShadowingTails.tail, shiftSequence, Nat.add_assoc]
  rw [hshadow]
  exact (large J).width_gap

/-- Final paper theorem with all scalar, summability, tail, and closing-gap
hypotheses discharged by the canonical period-scaled recost output. -/
theorem paper (I : DirectInput J) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  apply GenericVariableTerminalDirectCapstoneExplicitFrontPaperMain.paperMainDistance
    I.core.array.toGeometricScheme I.physical.markings I.physical.physical
    I.kh0_nonnegative I.kh0_lt_one I.cb_pos I.db_pos I.cp_pos
    I.physical.frontTube I.physical.mixed I.physical.physicalDefect I.c_pos
    (direction := J.scalar.direction (J.scalar.large.N + (large J).N))
    (modelWidth := J.scalar.Cw)
    (H := (shift (data J) (large J).N).Hs 0)
  · exact J.scalar.direction_unit _
  · exact I.base_bounded
  · exact I.base_width
  · exact I.base_length
  · exact I.universal_gap

end DirectInput

end ConfiguredRecursiveEdgeRecostScaledPaperCapstone
