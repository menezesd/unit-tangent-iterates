import UnitTangentIterates.ConfiguredModelPairSource
import UnitTangentIterates.RichStageDataPhaseRigidTransport
import UnitTangentIterates.ConfiguredRowDefectProvider

/-! # Gauge-first configured physical presentations -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredGaugeFirstPhysicalSequence

open ConfiguredModelPairPhaseCarrier ConfiguredModelPairSource
  ConfiguredPairSourceAdapter RichStageDataPhaseRigidTransport

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {Q : ℕ → Data} {kh c dlt : ℝ}

structure Presentation (S : Input D Q kh c dlt) (n : ℕ) where
  translation : ℂ
  rotation : ℂ
  phase : ℝ
  rotation_norm : ‖rotation‖ = 1

def Presentation.data (S : Input D Q kh c dlt) {n : ℕ}
    (A : Presentation S n) : Data :=
  move A.translation A.rotation A.phase (Q n)

def initial (S : Input D Q kh c dlt) : Presentation S 0 where
  translation := 0
  rotation := 1
  phase := 0
  rotation_norm := by simp

def transferRotation (S : Input D Q kh c dlt) {n : ℕ}
    (A : Presentation S n) : ℂ :=
  A.rotation * (S.identity n).rearRotation⁻¹

def transferTranslation (S : Input D Q kh c dlt) {n : ℕ}
    (A : Presentation S n) : ℂ :=
  A.translation - transferRotation S A * (S.identity n).rearTranslation

def next (S : Input D Q kh c dlt) {n : ℕ}
    (A : Presentation S n) (r : ℝ) : Presentation S (n + 1) where
  translation := transferTranslation S A +
    transferRotation S A * (S.identity n).frontTranslation
  rotation := transferRotation S A * (S.identity n).frontRotation
  phase := S.frontPhase n r
  rotation_norm := by
    simp [transferRotation, norm_mul, A.rotation_norm,
      (S.identity n).rearRotation_norm,
      (S.identity n).frontRotation_norm]

theorem shiftData_rigidData (a w : ℂ) (q : ℝ) (p : Data) :
    MarkedShift.shiftData q (MarkedRigid.rigidData a w p) =
      MarkedRigid.rigidData a w (MarkedShift.shiftData q p) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ext u <;> rfl

theorem physicalStep (S : Input D Q kh c dlt) {n : ℕ}
    (A : Presentation S n) (r : ℝ) : Nonempty
    (PhysicalRearLimitKinematics kh
      (move A.translation A.rotation r (S.carrier n).data)
      (next S A r).data) := by
  let I := S.identity n
  let tw := transferRotation S A
  let ta := transferTranslation S A
  have hwR : I.rearRotation ≠ 0 := by
    intro h
    have : ‖I.rearRotation‖ = 0 := by rw [h, norm_zero]
    linarith [I.rearRotation_norm]
  have htw : ‖tw‖ = 1 := by
    change ‖A.rotation * I.rearRotation⁻¹‖ = 1
    rw [norm_mul, norm_inv, A.rotation_norm, I.rearRotation_norm]
    norm_num
  let K := Nonempty.some (S.physicalAtPhase n r)
  let KR := physicalRearLimitKinematics_rigid K ta tw htw
  have hrot : tw * I.rearRotation = A.rotation := by
    dsimp [tw, transferRotation, I]
    rw [mul_assoc, inv_mul_cancel₀ hwR, mul_one]
  have hreareq : MarkedRigid.rigidData ta tw
      (MarkedShift.shiftData r (S.rear n)) =
      move A.translation A.rotation r (S.carrier n).data := by
    unfold Input.rear
    rw [shiftData_rigidData, MarkedRigid.rigidData_comp]
    rw [hrot]
    congr 2
    dsimp [ta, transferTranslation]
    ring
  have hfronteq : MarkedRigid.rigidData ta tw
      (MarkedShift.shiftData (S.frontRelativePhase n r) (S.front n)) =
      (next S A r).data := by
    unfold Input.front
    rw [shiftData_rigidData, MarkedRigid.rigidData_comp,
      MarkedShift.shiftData_add]
    change MarkedRigid.rigidData
        (ta + tw * I.frontTranslation) (tw * I.frontRotation)
        (MarkedShift.shiftData
          (S.frontRelativePhase n r + S.frontShift n) (Q (n + 1))) =
      MarkedRigid.rigidData
        (ta + tw * I.frontTranslation) (tw * I.frontRotation)
        (MarkedShift.shiftData (S.frontPhase n r) (Q (n + 1)))
    congr 3
    unfold Input.frontRelativePhase Input.frontShift Input.frontPhase
    field_simp [ne_of_gt (D.model.separation_pos (n + 1))]
  rw [← hreareq, ← hfronteq]
  exact ⟨KR⟩

variable (S : Input D Q kh c dlt)
  (hQ : ∀ n, perim (Q n) = 2 * D.Hs n ∧
    ev (Q n) = TwoCapPairsAssembly.front
      (D.kappas n) D.model.thetaBase (D.Hs n))

def output (n : ℕ) :
    ConfiguredApproximateDefectPathActualTerminal.Output D Q n (S.carrier n) :=
  Classical.choice
    (ConfiguredApproximateDefectPathActualTerminal.exists_output
      D hQ n (S.carrier n))

def rearPhase {n : ℕ} (A : Presentation S n) : ℝ :=
  (output S hQ n).baseShift +
    (output S hQ n).marking.marking.psi A.phase

def presentations : ∀ n, Presentation S n
  | 0 => initial S
  | n + 1 => next S (presentations n)
      (rearPhase S hQ (presentations n))

def alignedQ (n : ℕ) : Data :=
  (presentations (S := S) (hQ := hQ) n).data

theorem alignedQ_tube (n : ℕ) : IsTubeMember c 0 dlt (alignedQ S hQ n) := by
  unfold alignedQ Presentation.data move
  exact MarkedRigid.isTubeMember_rigidData
    (presentations (S := S) (hQ := hQ) n).rotation_norm
    (MarkedShift.isTubeMember_shiftData (S.front_tube n)
      (presentations (S := S) (hQ := hQ) n).phase)

def movedRear (n : ℕ) : Data :=
  let A := presentations (S := S) (hQ := hQ) n
  move A.translation A.rotation A.phase (output S hQ n).rear

theorem terminalBase_eq_physicalRear (n : ℕ) :
    move (presentations (S := S) (hQ := hQ) n).translation
        (presentations (S := S) (hQ := hQ) n).rotation
        ((output S hQ n).marking.marking.psi
          (presentations (S := S) (hQ := hQ) n).phase)
        (output S hQ n).terminalBase =
      move (presentations (S := S) (hQ := hQ) n).translation
        (presentations (S := S) (hQ := hQ) n).rotation
        (rearPhase S hQ (presentations (S := S) (hQ := hQ) n))
          (S.carrier n).data := by
  unfold move rearPhase
  apply congrArg (MarkedRigid.rigidData
    (presentations (S := S) (hQ := hQ) n).translation
    (presentations (S := S) (hQ := hQ) n).rotation)
  let q := (output S hQ n).marking.marking.psi
    (presentations (S := S) (hQ := hQ) n).phase
  change MarkedShift.shiftData q (output S hQ n).terminalBase =
    MarkedShift.shiftData ((output S hQ n).baseShift + q) (S.carrier n).data
  rw [(output S hQ n).terminalBase_eq, MarkedShift.shiftData_add]
  congr 1
  ring

def richStagePackage (Krow : ℝ) (C : ℕ → ℝ) (n : ℕ) :
    {R : TriangularMarkedRecursiveChoiceVariableTerminalConstructor.RichStageData
      (alignedQ S hQ n) (alignedQ S hQ (n + 1)) (movedRear S hQ n)
      (ConfiguredRowDefectProvider.error D Krow n 0)
      (ConfiguredApproximateDefectPathRowwise.rowP0 D n)
      (ConfiguredApproximateDefectPathRowwise.rowP1 D n) D.kstar
      (ConfiguredApproximateDefectPathRowwise.rowG1 D n)
      (ConfiguredApproximateDefectPathRowwise.rowCg D n) c (C n) dlt //
      R.terminalBase = move
        (presentations (S := S) (hQ := hQ) n).translation
        (presentations (S := S) (hQ := hQ) n).rotation
        (rearPhase S hQ (presentations (S := S) (hQ := hQ) n))
        (S.carrier n).data ∧
      R.stage.increment.T = 1 ∧
      ControlledJunctionPathFunctionalBounds.FunctionalIntegrable
        R.stage.increment.eta} := by
  let A := presentations (S := S) (hQ := hQ) n
  let W := output S hQ n
  let r := rearPhase S hQ A
  let P := Nonempty.some (physicalStep S A r)
  have hnext : alignedQ S hQ (n + 1) = (next S A r).data := by
    simp [alignedQ, presentations, A, r, rearPhase]
  have hfront : IsTubeMember c 0 dlt (alignedQ S hQ (n + 1)) :=
    alignedQ_tube S hQ (n + 1)
  let PC := P.toStageComponents S.kh_nonneg S.kh_lt_one S.c_pos
    (hnext ▸ hfront)
  let H := (PC.limitStrictness S.c_pos hfront).toH
    (fun s => ((PC.limitStrictness S.c_pos hfront).curvature_deriv s).differentiableAt)
  let base := move A.translation A.rotation
    (W.marking.marking.psi A.phase) W.terminalBase
  have hbaseeq : base = move A.translation A.rotation r (S.carrier n).data := by
    exact terminalBase_eq_physicalRear S hQ n
  have hbase : IsTubeMember (S.carrier n).c 0 (S.carrier n).dlt base := by
    rw [hbaseeq]
    exact MarkedRigid.isTubeMember_rigidData A.rotation_norm
      (MarkedShift.isTubeMember_shiftData (S.carrier n).tube r)
  let M := (W.marking.rephase A.phase).rigid A.translation A.rotation
    A.rotation_norm
  have hcont : Continuous M.marking.psi :=
    continuous_iff_continuousAt.2 fun u => (M.psi_deriv u).continuousAt
  have hmono : StrictMono M.marking.psi := by
    refine strictMono_of_deriv_pos fun u => ?_
    rw [(M.psi_deriv u).deriv]
    exact lt_of_lt_of_le M.lambda_pos (M.marking.lower u)
  have hsurj : Surjective M.marking.psi :=
    GaugeMarkedSelectedInverseEndpoint.surjective_of_continuous_strictMono_quasiPeriodic
      one_pos hcont hmono M.marking.translate M.psi_zero
  have hcanonical : range (⇑(alignedQ S hQ (n + 1)).1) =
      range (UnitTangent.unitTangentMap (ev base)) := by
    rw [hbaseeq]
    rw [← range_ev_of_perim_ne_zero
      (ne_of_gt (perim_pos S.c_pos hfront))]
    rw [hnext]
    exact PC.range_front_eq_unitTangent_rear
  have hstrict : UnconditionalAssembly.LimitStrictnessDataH base := by
    rw [hbaseeq]
    exact H
  have hRange := GaugeRearFamilyVariableTerminal.geometricRangeEdge_of_orientedReparametrization
    (S.carrier n).c_pos M.lambda_pos hbase M.marking hsurj hcanonical
  have hHarnack := GaugeRearFamilyVariableTerminal.arclengthHarnack_of_orientedReparametrization
    (S.carrier n).c_pos (S.carrier n).dlt_pos hbase M.marking hsurj hstrict
  have hbound : PathMetric.NormalPath.cost W.increment ≤
      ConfiguredRowDefectProvider.error D Krow n 0 := by
    simpa [ConfiguredRowDefectProvider.error,
      PathMetric.WeightedRecursiveDefect.pullbackError] using W.increment_cost
  let Rout := RichStageDataPhaseRigidTransport.transportOutput
    (c := c) (C := C n) (dlt := dlt) W hbound
    A.phase (alignedQ S hQ (n + 1)) A.translation A.rotation A.rotation_norm
    hRange hHarnack
  refine ⟨Rout, ?_, ?_, ?_⟩
  · exact terminalBase_eq_physicalRear S hQ n
  · exact RichStageDataPhaseRigidTransport.transportOutput_time_one
      (c := c) (C := C n) (dlt := dlt) W hbound
      A.phase (alignedQ S hQ (n + 1)) A.translation A.rotation A.rotation_norm
      hRange hHarnack
  · exact RichStageDataPhaseRigidTransport.transportOutput_functional
      (c := c) (C := C n) (dlt := dlt) W hbound
      A.phase (alignedQ S hQ (n + 1)) A.translation A.rotation A.rotation_norm
      hRange hHarnack

/-- The deterministic rich stage retained before existential packaging. -/
def richStage (Krow : ℝ) (C : ℕ → ℝ) (n : ℕ) :=
  (richStagePackage S hQ Krow C n).val

theorem richStage_spec (Krow : ℝ) (C : ℕ → ℝ) (n : ℕ) :
    (richStage S hQ Krow C n).terminalBase = move
        (presentations (S := S) (hQ := hQ) n).translation
        (presentations (S := S) (hQ := hQ) n).rotation
        (rearPhase S hQ (presentations (S := S) (hQ := hQ) n))
        (S.carrier n).data ∧
      (richStage S hQ Krow C n).stage.increment.T = 1 ∧
      ControlledJunctionPathFunctionalBounds.FunctionalIntegrable
        (richStage S hQ Krow C n).stage.increment.eta :=
  (richStagePackage S hQ Krow C n).property

theorem exists_richStage (Krow : ℝ) (C : ℕ → ℝ) (n : ℕ) :
    ∃ R : TriangularMarkedRecursiveChoiceVariableTerminalConstructor.RichStageData
      (alignedQ S hQ n) (alignedQ S hQ (n + 1)) (movedRear S hQ n)
      (ConfiguredRowDefectProvider.error D Krow n 0)
      (ConfiguredApproximateDefectPathRowwise.rowP0 D n)
      (ConfiguredApproximateDefectPathRowwise.rowP1 D n) D.kstar
      (ConfiguredApproximateDefectPathRowwise.rowG1 D n)
      (ConfiguredApproximateDefectPathRowwise.rowCg D n) c (C n) dlt,
      R.terminalBase = move
        (presentations (S := S) (hQ := hQ) n).translation
        (presentations (S := S) (hQ := hQ) n).rotation
        (rearPhase S hQ (presentations (S := S) (hQ := hQ) n))
        (S.carrier n).data ∧
      R.stage.increment.T = 1 ∧
      ControlledJunctionPathFunctionalBounds.FunctionalIntegrable
        R.stage.increment.eta :=
  ⟨richStage S hQ Krow C n, richStage_spec S hQ Krow C n⟩

def provider (Krow : ℝ) (C : ℕ → ℝ) :
    TriangularMarkedRecursiveChoiceVariableTerminalConstructor.BaseStageProvider
      (alignedQ S hQ) (ConfiguredRowDefectProvider.error D Krow)
      (ConfiguredApproximateDefectPathRowwise.rowP0 D)
      (ConfiguredApproximateDefectPathRowwise.rowP1 D) (fun _ => D.kstar)
      (ConfiguredApproximateDefectPathRowwise.rowG1 D)
      (ConfiguredApproximateDefectPathRowwise.rowCg D) C c dlt :=
  ⟨⟨{
    next := movedRear S hQ
    richStage := fun n => Classical.choose (exists_richStage S hQ Krow C n) }⟩⟩

theorem retainedPhysical (Krow : ℝ) (C : ℕ → ℝ) (n : ℕ) : Nonempty
    (PhysicalRearLimitKinematics kh
      (Classical.choose (exists_richStage S hQ Krow C n)).terminalBase
      (alignedQ S hQ (n + 1))) := by
  let A := presentations (S := S) (hQ := hQ) n
  let r := rearPhase S hQ A
  let P := Nonempty.some (physicalStep S A r)
  have heq : (Classical.choose (exists_richStage S hQ Krow C n)).terminalBase =
      move A.translation A.rotation r (S.carrier n).data := by
    exact (Classical.choose_spec (exists_richStage S hQ Krow C n)).1
  have hnext : alignedQ S hQ (n + 1) = (next S A r).data := by
    simp [alignedQ, presentations, A, r, rearPhase]
  rw [heq]
  rw [hnext]
  exact ⟨P⟩

end ConfiguredGaugeFirstPhysicalSequence
