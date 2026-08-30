import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalBounds
import UnitTangentIterates.ConfiguredRecursiveEdgePresentedPhysicalSidecars
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPaperCapstone

/-!
# Physical-package facts for a chosen prepared chain

This module records the unconditional common-tube facts available from a
`ChosenChain`.  The remaining depth-zero physical-front tube is isolated as an
exact proposition: unlike the positive-depth front, its prepared geometric
phase provenance is not retained by `ChosenChain`.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalPackage

open ConfiguredCanonicalPairSource
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeRecostFinitePreparedChosenChain
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray
  FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
  FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays
  FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays.GeometricArray

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  {H : Output R}

/-- The exact configured row data used by the chosen chain's physical array. -/
abbrev rowData (H : Output R) : ConstructedConfiguredSequenceWeighted.Data :=
  H.toClosing.data

/-- Positivity of the exact configured common speed floor. -/
theorem rowData_commonC_pos (H : Output R) :
    0 < commonC (rowData H) := by
  change 0 < (rowData H).Hs 0
  exact (rowData H).separation_zero_pos

/-- Positivity of the exact configured common chord radius. -/
theorem rowData_commonDlt_pos (H : Output R) :
    0 < commonDlt (rowData H) := by
  let D := rowData H
  have hk :=
    ConstructedConfiguredInductiveTubeBudget.configured_kstar_pos D.model
  change 0 < ConfiguredInductiveTubeBudget.chordBase D.model / 2
  rw [ConstructedConfiguredInductiveTubeBudget.chordBase_eq_min D.model hk]
  exact half_pos (lt_min D.separation_zero_pos
    (div_pos Real.pi_pos (mul_pos (by norm_num) hk)))

/-- The truthful depth-zero row has the exact ordinary common tube. -/
theorem baseTube (C : ChosenChain H) (n : ℕ) :
    IsTubeMember (commonC (rowData H)) 0 (commonDlt (rowData H))
      (C.system.P n 0) := by
  rw [C.system.P_zero]
  apply
    (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainVariableTube.configuredBase_model_tube
      H.toClosing n).mono
  · change H.toClosing.data.Hs 0 ≤ 2 * H.toClosing.data.Hs 0
    linarith [H.toClosing.data.separation_zero_pos]
  · change
      ConfiguredInductiveTubeBudget.chordBase H.toClosing.data.model / 2 ≤
        ConfiguredInductiveTubeBudget.chordBase H.toClosing.data.model
    have hd := rowData_commonDlt_pos H
    change 0 < ConfiguredInductiveTubeBudget.chordBase H.toClosing.data.model / 2 at hd
    linarith

/-- Every displayed grid datum has the exact ordinary common tube.  The array
supplies the common variable tube, while its preceding cell supplies constant
physical-rear speed. -/
theorem ordinaryTube (C : ChosenChain H) (n k : ℕ) :
    IsTubeMember (commonC (rowData H)) 0 (commonDlt (rowData H))
      (C.system.P n k) := by
  change IsTubeMember (H.toClosing.data.Hs 0) 0
    (ConfiguredInductiveTubeBudget.chordBase H.toClosing.data.model / 2)
      (C.system.P n k)
  let A :=
    ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.array C
  let B0 : ℕ → Data := fun i => C.system.P i 0
  have h := physicalRearTube A B0 (fun _ => rfl) (baseTube C) n k
  simpa [physicalRear_eq_presented A B0 (fun _ => rfl)] using h

/-- Every positive-depth cell front has the exact ordinary common tube. -/
theorem physicalFront_succ_tube (C : ChosenChain H) (n k : ℕ) :
    IsTubeMember (commonC (rowData H)) 0 (commonDlt (rowData H))
      ((ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.array
        C).cell n (k + 1)).physicalFront := by
  change IsTubeMember (commonC (rowData H)) 0 (commonDlt (rowData H))
    (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell.physicalFront C n k)
  rw [ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell.physicalFront_eq_normalized_shift_P
    C n k]
  exact MarkedShift.isTubeMember_shiftData
    (ordinaryTube C (n + 1) (k + 1))
    (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell.normalizedPhysicalFrontPhase
      C n k : ℝ)

/-- Every physical-array cell uses the exact configured curvature cap. -/
@[simp] theorem cellKh (C : ChosenChain H) (n k : ℕ) :
    ((ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.array
      C).cell n k).state.kh = sourceKh := by
  change
    (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.cell
      C n k).state.kh = sourceKh
  exact
    ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.cell_state_kh C n k

/-- The exact proposition not retained by an arbitrary `ChosenChain`: common
tube membership for the physical fronts of its depth-zero cells. -/
def BasePhysicalFrontTube (C : ChosenChain H) : Prop :=
  ∀ n, IsTubeMember (commonC (rowData H)) 0 (commonDlt (rowData H))
    ((ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.array
      C).cell n 0).physicalFront

/-- The retained depth-zero prepared geometry identifies its physical front
with a marking shift of the next exact base display. -/
theorem basePhysicalFrontTube (C : ChosenChain H) :
    BasePhysicalFrontTube C := by
  intro n
  change IsTubeMember (commonC (rowData H)) 0 (commonDlt (rowData H))
    ((C.reachable 0).presented n).terminal.frontData
  rw [(C.geometry 0).terminalFront_eq_phase n,
    C.baseDisplayed (n + 1), ← C.system.P_zero (n + 1)]
  exact MarkedShift.isTubeMember_shiftData
    (ordinaryTube C (n + 1) 0) ((C.geometry 0).terminalFrontPhase n)

/-- Complete unconditional configured cell facts for the physical array. -/
def cellFacts (C : ChosenChain H) :
    ConfiguredRecursiveEdgePresentedPhysicalSidecars.CellFacts (rowData H)
      (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.array
        C) where
  baseTube := baseTube C
  cellKh := cellKh C
  cellFrontTube := by
    intro n k
    cases k with
    | zero => exact basePhysicalFrontTube C n
    | succ k =>
        simpa [Nat.succ_eq_add_one] using physicalFront_succ_tube C n k

/-- Callback-free physical sidecars, transported to the canonical base family
stored by `PhysicalArray.core C`. -/
noncomputable def sidecars (C : ChosenChain H) :
    PresentedPhysical.Sidecars
      (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.core
        C).array
      (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.core
        C).B0
      sourceKh (commonC (rowData H)) (commonDlt (rowData H))
      (commonC (rowData H)) (commonDlt (rowData H)) := by
  have hB0 :
      (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.core
        C).B0 = fun n => C.system.P n 0 := by
    funext n
    exact (C.system.P_zero n).symm
  rw [hB0]
  exact
    ConfiguredRecursiveEdgePresentedPhysicalSidecars.CellFacts.toSidecars
      (rowData H)
      (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.array
        C)
      (cellFacts C)

/-- The phase-normalized geometric package, definitionally indexed by the
array and canonical base family of `PhysicalArray.core C`. -/
noncomputable def presentedPackage (C : ChosenChain H) :
    Package
      (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.core
        C).array
      (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.core
        C).B0
      sourceKh (commonC (rowData H)) (commonDlt (rowData H))
      (commonC (rowData H)) (commonDlt (rowData H)) := by
  let S := sidecars C
  exact
    FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays.GeometricArray.presentedPackage
        (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.core
          C).array
        (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.core
          C).B0
        (fun n =>
          ((ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.core C).array.base
            n).symm)
        S.physical S.mixed S.frontTube

/-- Paper-facing name for the exact presented physical package. -/
noncomputable def physicalPackage (C : ChosenChain H) :
    Package
      (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.core
        C).array
      (ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.core
        C).B0
      sourceKh (commonC (rowData H)) (commonDlt (rowData H))
      (commonC (rowData H)) (commonDlt (rowData H)) :=
  presentedPackage C

/-- Final multiplier-capstone input with the exact chosen physical core. -/
noncomputable def physicalBaseInput (C : ChosenChain H) :
    ConfiguredRecursiveEdgeRecostMultiplierPaperCapstone.PhysicalBaseInput
      H.toClosing where
  core :=
    ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalArray.core C
  kh0 := sourceKh
  cb := commonC (rowData H)
  db := commonDlt (rowData H)
  cp := commonC (rowData H)
  dp := commonDlt (rowData H)
  physical := physicalPackage C
  kh0_nonnegative := sourceKh_nonnegative
  kh0_lt_one := sourceKh_lt_one
  cb_pos := rowData_commonC_pos H
  db_pos := rowData_commonDlt_pos H
  cp_pos := rowData_commonC_pos H
  c_pos := rowData_commonC_pos H
  P_zero := by
    intro n
    change C.system.P n 0 =
      ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing n
    exact C.system.P_zero n

end ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalPackage
