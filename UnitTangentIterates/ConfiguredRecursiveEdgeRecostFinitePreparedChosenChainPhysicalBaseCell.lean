import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell

/-!
# The physical base cell of a chosen prepared chain

At depth zero the coherent phase is zero.  Consequently the physical rear
`P n 1` is exactly the base retained by the depth-zero presented input, whose
terminal package already carries the required physical rear kinematics.
-/

noncomputable section

open Function Set MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed VariableMarkedTube

namespace ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalBaseCell

open CoherentPhaseReachableMetricRange
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeRecostFinitePreparedChosenChain
  ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  {H : Output R}

/-- The native presented boundary retained by the chosen depth-zero layer. -/
abbrev basePresented (C : ChosenChain H) (n : ℕ) :=
  (C.reachable 0).presented n

/-- The base prepared step uses the native pre-core of the chosen reachable
depth-zero layer. -/
theorem basePre_eq_reachablePre (C : ChosenChain H) (n : ℕ) :
    (C.stepData 0).input.pre n = (C.reachable 0).pre H n :=
  (C.stepData 0).pre_eq n

/-- The first coherent physical rear is exactly the base of the chosen
depth-zero presented boundary.  No marking shift remains at depth zero. -/
theorem physicalRear_eq_presentedBase (C : ChosenChain H) (n : ℕ) :
    C.system.P n 1 = (basePresented C n).base := by
  calc
    C.system.P n 1 =
        ((C.stepData 0).input.pre n).geometric.base := by
      rw [C.system.P_succ_eq_shift_canonical]
      change MarkedShift.shiftData 0
          ((C.stepData 0).input.pre n).geometric.base =
        ((C.stepData 0).input.pre n).geometric.base
      simp
    _ = ((C.reachable 0).pre H n).geometric.base := by
      rw [basePre_eq_reachablePre C n]
    _ = (basePresented C n).base := rfl

/-- The ordinary front paired with the physical base rear. -/
def physicalFront (C : ChosenChain H) (n : ℕ) : Data :=
  (basePresented C n).terminal.frontData

/-- Exact physical rear kinematics aligned with `C.system.P n 1`, obtained
from the chosen base presentation rather than from an added hypothesis. -/
noncomputable def physicalKinematics (C : ChosenChain H) (n : ℕ) :
    PhysicalRearLimitKinematics sourceKh (C.system.P n 1)
      (physicalFront C n) := by
  rw [physicalRear_eq_presentedBase C n]
  exact (basePresented C n).terminal.frontKinematics

/-- The aligned physical base rear retains its native zero-floor tube. -/
theorem physicalRear_tube (C : ChosenChain H) (n : ℕ) :
    IsTubeMember
      (basePresented C n).terminal.physical.cq 0
      (basePresented C n).terminal.physical.dlt
      (C.system.P n 1) := by
  rw [physicalRear_eq_presentedBase C n]
  exact (basePresented C n).terminal.zero_floor_tube

/-- Constant physical rear speed at depth zero follows from the retained
presented tube. -/
theorem physicalRear_speedConst (C : ChosenChain H) (n : ℕ) : ∀ u v,
    ‖(C.system.P n 1).2.1 u‖ = ‖(C.system.P n 1).2.1 v‖ :=
  (physicalRear_tube C n).speed_const

/-- Complete unconditional depth-zero physical cell of the chosen chain. -/
def cell (C : ChosenChain H) (n : ℕ) : Cell C.system.P n 0 where
  state :=
    ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell.state
      C n 0
  row :=
    ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell.row
      C n 0
  kh_nonnegative := sourceKh_nonnegative
  kh_lt_one := sourceKh_lt_one
  selectedStart := C.system.P n 1
  selectedEnd :=
    ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell.selectedRear
      C n 0
  path :=
    ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell.rowPath
      C n 0
  physicalFrontData := physicalFront C n
  physicalKinematics := ⟨physicalKinematics C n⟩
  physicalRearSpeedConst := physicalRear_speedConst C n
  range_edge := C.system.rangeEdge n 0

@[simp] theorem cell_state_kh (C : ChosenChain H) (n : ℕ) :
    (cell C n).state.kh = sourceKh := rfl

end ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalBaseCell
