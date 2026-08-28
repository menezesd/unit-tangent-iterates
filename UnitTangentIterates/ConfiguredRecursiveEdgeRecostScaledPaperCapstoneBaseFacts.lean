import UnitTangentIterates.ConfiguredRecursiveEdgeRecostScaledPaperCapstone

/-!
# Recost-scaled paper capstone with truthful base facts

The reachable recost grid starts at the configured moved-rear representative,
not at the aligned model datum as complete marked `Data`.  The closing theorem
only uses boundedness, transverse width, and a lower bound for total length.
This module exposes exactly those invariant facts and retains all scalar
specialization from the recost-scaled capstone.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostScaledPaperCapstoneBaseFacts

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgeFinitePresentedPaperCapstone
  ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal
  ConfiguredRecursiveEdgeRecostScaledPaperCapstone
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
  FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays
  FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays.GeometricArray

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}

/-- The three parameterization-invariant facts about the actual displayed
base which are consumed by the final closing argument. -/
structure BaseFacts (G : GeometricCore J) where
  direction : ℂ
  direction_norm : ‖direction‖ = 1
  bounded : Bornology.IsBounded (range (⇑(G.Q 0).1))
  width : Width.width (range (⇑(G.Q 0).1)) direction ≤ J.scalar.Cw
  length : 2 * (shift (data J) (large J).N).Hs 0 ≤
    MarkedReparam.totalLength (fun u ↦ (G.Q 0).2.1 u)

/-- Recosted direct capstone input with the truthful moved-rear base facts in
place of an invalid marked equality with the aligned model. -/
structure DirectInput
    (J : RowJetScalarOutput choice.MA0 choice.NA0) where
  core : GeometricCore J
  kh0 : ℝ
  cb : ℝ
  db : ℝ
  cp : ℝ
  dp : ℝ
  physical : Package core.array core.B0 kh0 cb db cp dp
  kh0_nonnegative : 0 ≤ kh0
  kh0_lt_one : kh0 < 1
  cb_pos : 0 < cb
  db_pos : 0 < db
  cp_pos : 0 < cp
  c_pos : 0 < core.c
  baseFacts : BaseFacts core

namespace DirectInput

private theorem universal_gap (I : DirectInput J) :
    ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      I.core.Q I.core.P (error J)
      ConfiguredRecursiveEdgeFinitePresentedPaperCapstone.ActualStageProvider.paperP0
      ConfiguredRecursiveEdgeFinitePresentedPaperCapstone.ActualStageProvider.paperP1
      ConfiguredRecursiveEdgeFinitePresentedPaperCapstone.ActualStageProvider.paperKhat
      ConfiguredRecursiveEdgeFinitePresentedPaperCapstone.ActualStageProvider.paperG1
      ConfiguredRecursiveEdgeFinitePresentedPaperCapstone.ActualStageProvider.paperCg
      I.core.C I.core.c I.core.dlt,
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

/-- Final paper theorem with the canonical recost scalar stack and the actual
displayed base geometry kept separate. -/
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
    (direction := I.baseFacts.direction)
    (modelWidth := J.scalar.Cw)
    (H := (shift (data J) (large J).N).Hs 0)
  · exact I.baseFacts.direction_norm
  · exact I.baseFacts.bounded
  · exact I.baseFacts.width
  · exact I.baseFacts.length
  · exact I.universal_gap

end DirectInput

end ConfiguredRecursiveEdgeRecostScaledPaperCapstoneBaseFacts
