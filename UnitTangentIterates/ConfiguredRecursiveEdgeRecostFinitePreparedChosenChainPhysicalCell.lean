import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedChosenChain
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedNextPhase
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
import UnitTangentIterates.PhysicalRearKinematicsShift

/-!
# Physical cells from a chosen prepared chain

One prepared step supplies the complete physical cell at the positive depth
which it creates.  The terminal front is first related to the coherent grid,
then normalized modulo one.  The rear and front markings are subsequently
shifted by the phase equation retained in `PhysicalRearLimitKinematics`.
-/

noncomputable section

open Function Set MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed VariableMarkedTube

namespace ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell

open CoherentPhaseReachableMetricRange
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostFiniteNativePresentedInput
  ConfiguredRecursiveEdgeRecostFinitePreparedChosenChain
  ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower
  FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  {H : Output R}

abbrev analyticGeometry
    (C : ChosenChain H) (n k : ℕ) :=
  ((C.stepData k).boundaryFacts H n).geometry

/-- The recursive package is rebuilt from the prepared source-tied sidecars,
not from an independent successor callback. -/
noncomputable def recursiveAnalytic
    (C : ChosenChain H) (n k : ℕ) :=
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input.recursive
    ((C.stepData k).input.analytic n) ((C.stepData k).recursiveFacts n)

/-- The rear phase used by the cell created by step `k`. -/
def rearPhase (C : ChosenChain H) (n k : ℕ) : ℝ :=
  (ChosenChain.system H C).coherentPhase n (k + 1)

/-- The unnormalized phase relating the analytic terminal front to the
coherent successor-row datum. -/
def terminalPhaseRaw (C : ChosenChain H) (n k : ℕ) : ℝ :=
  (C.stepData k).input.terminalFrontPhase n -
    (ChosenChain.system H C).coherentPhase (n + 1) (k + 1)

/-- Canonical representative of the terminal phase in `[0,1]`. -/
def normalizedTerminalPhase
    (C : ChosenChain H) (n k : ℕ) : Set.Icc (0 : ℝ) 1 :=
  MarkedShift.normalizedPhase (terminalPhaseRaw C n k)

/-- The prepared terminal reference is exactly the raw datum in the chosen
successor layer. -/
theorem terminalReference_eq_raw
    (C : ChosenChain H) (n k : ℕ) :
    ChosenChain.terminalReference H C n k =
      ChosenChain.raw H C (n + 1) (k + 1) := by
  change (C.stepData k).input.terminalFrontReference n =
    ((C.reachable (k + 1)).nodes (n + 1)).stage.displayed
  rw [ChosenChain.reachable_succ_nodes H C k]
  simpa [PreparedStepData.next] using
    (C.stepData k).terminalReference_eq n

/-- The coherent terminal-reference datum inherits the predecessor presented
rear tube. -/
theorem terminalReference_tube
    (C : ChosenChain H) (n k : ℕ) :
    IsTubeMember
      ((C.stepData k).input.pre (n + 1)).geometric.terminal.physical.cq 0
      ((C.stepData k).input.pre (n + 1)).geometric.terminal.physical.dlt
      ((ChosenChain.system H C).P (n + 1) (k + 1)) := by
  rw [(ChosenChain.system H C).P_succ_eq_shift_canonical]
  simpa [ChosenChain.canonical] using
    (MarkedShift.isTubeMember_shiftData
      ((C.stepData k).input.pre (n + 1)).geometric.terminal.zero_floor_tube
      ((ChosenChain.system H C).coherentPhase (n + 1) k))

/-- The analytic terminal front is the normalized phase shift of the
correctly indexed coherent physical front. -/
theorem analyticFront_eq_normalized_shift_P
    (C : ChosenChain H) (n k : ℕ) :
    (analyticGeometry C n k).frontData =
      MarkedShift.shiftData (normalizedTerminalPhase C n k : ℝ)
        ((ChosenChain.system H C).P (n + 1) (k + 1)) := by
  let I := C.stepData k
  let G := analyticGeometry C n k
  let q := terminalPhaseRaw C n k
  have hraw : G.frontData = MarkedShift.shiftData
      (I.input.terminalFrontPhase n)
      (ChosenChain.raw H C (n + 1) (k + 1)) := by
    calc
      G.frontData = unitTangentData (I.input.analytic n).source :=
        G.frontData_eq
      _ = MarkedShift.shiftData (I.input.terminalFrontPhase n)
          (I.input.terminalFrontReference n) :=
        I.input.terminalFront_eq_phase n
      _ = MarkedShift.shiftData (I.input.terminalFrontPhase n)
          (ChosenChain.terminalReference H C n k) := rfl
      _ = MarkedShift.shiftData (I.input.terminalFrontPhase n)
          (ChosenChain.raw H C (n + 1) (k + 1)) :=
        congrArg (MarkedShift.shiftData (I.input.terminalFrontPhase n))
          (terminalReference_eq_raw C n k)
  have hcoherent :
      MarkedShift.shiftData (I.input.terminalFrontPhase n)
          (ChosenChain.raw H C (n + 1) (k + 1)) =
        MarkedShift.shiftData q
          ((ChosenChain.system H C).P (n + 1) (k + 1)) := by
    change MarkedShift.shiftData (I.input.terminalFrontPhase n)
        (ChosenChain.raw H C (n + 1) (k + 1)) =
      MarkedShift.shiftData q
        (MarkedShift.shiftData
          ((ChosenChain.system H C).coherentPhase (n + 1) (k + 1))
          (ChosenChain.raw H C (n + 1) (k + 1)))
    rw [MarkedShift.shiftData_add]
    congr 1
    dsimp [q, terminalPhaseRaw]
    ring
  calc
    G.frontData = MarkedShift.shiftData q
        ((ChosenChain.system H C).P (n + 1) (k + 1)) := hraw.trans hcoherent
    _ = MarkedShift.shiftData (normalizedTerminalPhase C n k : ℝ)
        ((ChosenChain.system H C).P (n + 1) (k + 1)) := by
      simpa [normalizedTerminalPhase, q] using
        (MarkedShift.shiftData_normalizedPhase q
          ((ChosenChain.system H C).P (n + 1) (k + 1))
          (terminalReference_tube C n k)).symm

/-- The analytic front therefore has an ordinary tube without a front-tube
callback. -/
theorem analyticFront_tube
    (C : ChosenChain H) (n k : ℕ) :
    IsTubeMember
      ((C.stepData k).input.pre (n + 1)).geometric.terminal.physical.cq 0
      ((C.stepData k).input.pre (n + 1)).geometric.terminal.physical.dlt
      (analyticGeometry C n k).frontData := by
  rw [analyticFront_eq_normalized_shift_P C n k]
  exact MarkedShift.isTubeMember_shiftData
    (terminalReference_tube C n k) (normalizedTerminalPhase C n k : ℝ)

/-- The physical rear of the positive-depth cell is the coherent shift of
the presented rear built by the preceding prepared step. -/
theorem physicalRear_eq_shift_presented
    (C : ChosenChain H) (n k : ℕ) :
    (ChosenChain.system H C).P n (k + 2) =
      MarkedShift.shiftData (rearPhase C n k)
        (analyticGeometry C n k).presented := by
  rw [show k + 2 = (k + 1) + 1 by omega,
    (ChosenChain.system H C).P_succ_eq_shift_canonical]
  congr 1
  change ((C.stepData (k + 1)).input.pre n).geometric.base =
    (analyticGeometry C n k).presented
  rw [(C.stepData (k + 1)).pre_eq n, C.successorReachable k]
  rfl

/-- The coherent physical rear retains the ordinary presented tube. -/
theorem physicalRear_tube
    (C : ChosenChain H) (n k : ℕ) :
    IsTubeMember (analyticGeometry C n k).physical.cq 0
      (analyticGeometry C n k).physical.dlt
      ((ChosenChain.system H C).P n (k + 2)) := by
  rw [physicalRear_eq_shift_presented C n k]
  exact MarkedShift.isTubeMember_shiftData
    (analyticGeometry C n k).zero_floor_tube (rearPhase C n k)

/-- Constant physical rear speed follows from the retained presented rear
tube. -/
theorem physicalRear_speedConst
    (C : ChosenChain H) (n k : ℕ) : forall u v,
    ‖((ChosenChain.system H C).P n (k + 2)).2.1 u‖ =
      ‖((ChosenChain.system H C).P n (k + 2)).2.1 v‖ :=
  (physicalRear_tube C n k).speed_const

/-- Front phase forced by the coherent rear phase. -/
def physicalFrontPhase (C : ChosenChain H) (n k : ℕ) : ℝ :=
  (analyticGeometry C n k).frontKinematics.sf
      (perim (analyticGeometry C n k).presented * rearPhase C n k) /
    perim (analyticGeometry C n k).frontData

/-- The ordinary front after the phase forced by physical kinematics. -/
def physicalFront (C : ChosenChain H) (n k : ℕ) : Data :=
  MarkedShift.shiftData (physicalFrontPhase C n k)
    (analyticGeometry C n k).frontData

/-- Canonical coherent-grid phase of the final physical front. -/
def normalizedPhysicalFrontPhase
    (C : ChosenChain H) (n k : ℕ) : Set.Icc (0 : ℝ) 1 :=
  MarkedShift.normalizedPhase
    (physicalFrontPhase C n k + (normalizedTerminalPhase C n k : ℝ))

/-- The shifted analytic front is exactly a normalized shift of the coherent
front-row datum. -/
theorem physicalFront_eq_normalized_shift_P
    (C : ChosenChain H) (n k : ℕ) :
    physicalFront C n k =
      MarkedShift.shiftData (normalizedPhysicalFrontPhase C n k : ℝ)
        ((ChosenChain.system H C).P (n + 1) (k + 1)) := by
  unfold physicalFront
  rw [analyticFront_eq_normalized_shift_P C n k,
    MarkedShift.shiftData_add]
  simpa [normalizedPhysicalFrontPhase] using
    (MarkedShift.shiftData_normalizedPhase
      (physicalFrontPhase C n k + (normalizedTerminalPhase C n k : ℝ))
      ((ChosenChain.system H C).P (n + 1) (k + 1))
      (terminalReference_tube C n k)).symm

/-- The identified physical front inherits the coherent terminal-reference
tube. -/
theorem physicalFront_tube
    (C : ChosenChain H) (n k : ℕ) :
    IsTubeMember
      ((C.stepData k).input.pre (n + 1)).geometric.terminal.physical.cq 0
      ((C.stepData k).input.pre (n + 1)).geometric.terminal.physical.dlt
      (physicalFront C n k) := by
  rw [physicalFront_eq_normalized_shift_P C n k]
  exact MarkedShift.isTubeMember_shiftData
    (terminalReference_tube C n k)
    (normalizedPhysicalFrontPhase C n k : ℝ)

/-- Transport the analytic source kinematics to the coherent rear and the
correctly indexed physical front. -/
noncomputable def physicalKinematics
    (C : ChosenChain H) (n k : ℕ) :
    PhysicalRearLimitKinematics sourceKh
      ((ChosenChain.system H C).P n (k + 2))
      (physicalFront C n k) := by
  let G := analyticGeometry C n k
  let K := G.frontKinematics
  let r := rearPhase C n k
  let b := physicalFrontPhase C n k
  have hfrontPerim : perim G.frontData ≠ 0 :=
    (perim_pos
      ((C.stepData k).input.pre (n + 1)).geometric.terminal.physical.cq_pos
      (analyticFront_tube C n k)).ne'
  have hphase : K.sf (perim G.presented * r) =
      perim G.frontData * b := by
    simpa [b, physicalFrontPhase, r, K, G] using
      (mul_div_cancel₀ (K.sf (perim G.presented * r)) hfrontPerim).symm
  have Ks := K.shift
    ((C.stepData k).input.pre (n + 1)).geometric.terminal.physical.cq_pos
    (analyticFront_tube C n k) G.physical.cq_pos G.zero_floor_tube
    b r hphase
  rw [physicalRear_eq_shift_presented C n k]
  simpa [physicalFront, b, r, G, K] using Ks

/-- The coherent selected endpoint of the successor presentation. -/
def selectedRear (C : ChosenChain H) (n k : ℕ) : Data :=
  MarkedShift.shiftData (rearPhase C n k)
    (((C.stepData k).boundaryFacts H n).presentedInput.output.jets.rear)

/-- The coherent positive-depth display is the shifted selected initial of
the prepared successor. -/
theorem P_succ_eq_shift_nextDisplayed
    (C : ChosenChain H) (n k : ℕ) :
    (ChosenChain.system H C).P n (k + 1) =
      MarkedShift.shiftData (rearPhase C n k)
        ((C.stepData k).input.nextDisplayed n) := by
  change MarkedShift.shiftData
      ((ChosenChain.system H C).coherentPhase n (k + 1))
      (ChosenChain.raw H C n (k + 1)) =
    MarkedShift.shiftData
      ((ChosenChain.system H C).coherentPhase n (k + 1))
      ((C.stepData k).input.nextDisplayed n)
  congr 1
  change ((C.reachable (k + 1)).nodes n).stage.displayed =
    (C.stepData k).input.nextDisplayed n
  rw [ChosenChain.reachable_succ_nodes H C k]
  rfl

/-- The actual prepared chosen path, shifted to the coherent successor
display. -/
def rowPath (C : ChosenChain H) (n k : ℕ) :
    NormalPath ((ChosenChain.system H C).P n (k + 1))
      (selectedRear C n k) := by
  rw [P_succ_eq_shift_nextDisplayed C n k]
  simpa [selectedRear] using
    (MarkedShift.shiftPath (rearPhase C n k)
      (((C.stepData k).boundaryFacts H n).presentedInput.output.chosen.Delta))

/-- Analytic state of the positive-depth row, using the recursive package
assembled from the prepared sidecars. -/
def state (C : ChosenChain H) (n k : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower.State where
  start := ((C.reachable k).nodes (n + 1)).stage.displayed
  finish := ((C.stepData k).input.pre (n + 1)).geometric.output.jets.rear
  path := ((C.stepData k).input.pre (n + 1)).path
  P0 := (C.stepData k).input.step.targetP0 n
  kh := sourceKh
  khat := (C.stepData k).input.step.targetKhat n
  Qmax := (C.stepData k).input.step.targetQmax n
  source := (recursiveAnalytic C n k).source
  P1 := (recursiveAnalytic C n k).slice.periodUpper
  markingLower := (recursiveAnalytic C n k).slice.markingLower
  markingUpper := (recursiveAnalytic C n k).slice.markingUpper
  facts := Nonaffine.Facts.ofAnalytic (recursiveAnalytic C n k).slice le_rfl

/-- Presented row reconstructed by the prepared step, with its front tube
obtained from phase coherence. -/
def row (C : ChosenChain H) (n k : ℕ) :
    PresentedRow (state C n k).source := by
  let I := C.stepData k
  let B := I.boundaryFacts H n
  refine
    { applied := I.input.step.nextApplied n
      p := I.input.nextDisplayed n
      base := B.geometry.presented
      frontEndpoint := I.input.pre (n + 1) |>.geometric.output.jets.rear
      bound := H.error n (k + 1)
      terminalInput := B.terminal
      output := B.presentedInput.output
      cFront := I.input.pre (n + 1) |>.geometric.terminal.physical.cq
      kFront := 0
      dFront := I.input.pre (n + 1) |>.geometric.terminal.physical.dlt
      cFront_pos := I.input.pre (n + 1) |>.geometric.terminal.physical.cq_pos
      front_tube := by
        change IsTubeMember
          (I.input.pre (n + 1)).geometric.terminal.physical.cq 0
          (I.input.pre (n + 1)).geometric.terminal.physical.dlt
          (analyticGeometry C n k).frontData
        exact analyticFront_tube C n k
      frontData_eq := by
        change (analyticGeometry C n k).frontData =
          unitTangentData (I.input.analytic n).source
        exact (analyticGeometry C n k).frontData_eq }

/-- The retained unnormalized diagonal edge at the cell depth. -/
theorem rawDiagonalRangeEdge
    (C : ChosenChain H) (n k : ℕ) :
    GeometricUnitTangentRangeEdge
      (ChosenChain.raw H C (n + 1) (k + 1))
      (ChosenChain.canonical H C n (k + 1)) := by
  simpa [ChosenChain.raw, ChosenChain.canonical] using
    (C.stepData (k + 1)).rawDiagonalRangeEdge n

/-- Exact coherent diagonal range edge at the positive cell depth. -/
theorem rangeEdge (C : ChosenChain H) (n k : ℕ) :
    GeometricUnitTangentRangeEdge
      ((ChosenChain.system H C).P (n + 1) (k + 1))
      ((ChosenChain.system H C).P n (k + 2)) :=
  (ChosenChain.system H C).rangeEdge n (k + 1)

/-- Complete existing cell at every positive depth of the chosen chain. -/
def cell (C : ChosenChain H) (n k : ℕ) :
    Cell (ChosenChain.system H C).P n (k + 1) where
  state := state C n k
  row := row C n k
  kh_nonnegative := sourceKh_nonnegative
  kh_lt_one := sourceKh_lt_one
  selectedStart := (ChosenChain.system H C).P n (k + 1)
  selectedEnd := selectedRear C n k
  path := rowPath C n k
  physicalFrontData := physicalFront C n k
  physicalKinematics := ⟨physicalKinematics C n k⟩
  physicalRearSpeedConst := physicalRear_speedConst C n k
  range_edge := rangeEdge C n k

@[simp] theorem cell_state_kh
    (C : ChosenChain H) (n k : ℕ) :
    (cell C n k).state.kh = sourceKh := rfl

end ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainPhysicalCell
