import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter
import UnitTangentIterates.PhysicalRearKinematicsShift
import UnitTangentIterates.MarkingAwareSourceSelectedRearData

/-! # Phase-insensitive physical initial data for the recursive edge source -/

noncomputable section

open Function Set MarkedSpace PathMetric RearTrack RearOwnArclength

namespace ConfiguredRecursiveEdgePhysicalInitialData

open ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  ConfiguredGaugeFirstPhysicalSequence

variable {MA NA : ℝ}

def previousPresentation
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :=
  ConfiguredGaugeFirstPhysicalSequence.presentations
    O.pair.input O.model_data n

/-- The constant-speed rear carried by the physical pair step whose front is
the displayed source front before its explicit marking shift. -/
def unshiftedRear
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) : Data :=
  let A := previousPresentation O n
  RichStageDataPhaseRigidTransport.move A.translation A.rotation
    (ConfiguredGaugeFirstPhysicalSequence.rearPhase O.pair.input O.model_data A)
    (O.pair.input.carrier n).data

def frontData
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) : Data :=
  (ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.presentation O n).data

/-- The configured physical pair step, rewritten to the source's displayed
front presentation. -/
noncomputable def unshiftedKinematics
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    PhysicalRearLimitKinematics sourceKh (unshiftedRear O n) (frontData O n) := by
  let A := previousPresentation O n
  let r := ConfiguredGaugeFirstPhysicalSequence.rearPhase
    O.pair.input O.model_data A
  simpa [unshiftedRear, frontData, previousPresentation,
    ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.presentation,
    ConfiguredGaugeFirstPhysicalSequence.presentations, A, r] using
    Classical.choice (ConfiguredGaugeFirstPhysicalSequence.physicalStep
      O.pair.input A r)

theorem front_tube
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    IsTubeMember (ConfiguredCanonicalPairSource.commonC (data O)) 0
      (ConfiguredCanonicalPairSource.commonDlt (data O)) (frontData O n) := by
  simpa [frontData,
    ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.presentation,
    ConfiguredGaugeFirstPhysicalSequence.alignedQ] using
    (ConfiguredGaugeFirstPhysicalSequence.alignedQ_tube
      O.pair.input O.model_data (n + 1))

theorem unshiftedRear_tube
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    IsTubeMember (ConfiguredCanonicalPairSource.commonC (data O)) 0
      (ConfiguredCanonicalPairSource.commonDlt (data O)) (unshiftedRear O n) := by
  let A := previousPresentation O n
  let r := ConfiguredGaugeFirstPhysicalSequence.rearPhase
    O.pair.input O.model_data A
  rw [show unshiftedRear O n = RichStageDataPhaseRigidTransport.move
      A.translation A.rotation r (O.pair.input.carrier n).data by
    rfl]
  rw [O.pair.input_carrier n]
  exact MarkedRigid.isTubeMember_rigidData A.rotation_norm
    (MarkedShift.isTubeMember_shiftData (O.pair.carrier_common n) r)

/-- Rear marking shift uniquely corresponding to the explicit source-front
shift.  No identification of it with the displayed phase is made. -/
def rearShift
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) : ℝ :=
  let K := unshiftedKinematics O n
  rearArclength
      (NormalizedSteeringPhysicalRescaling.deltaPhys K.steering
        (perim (frontData O n)))
      (perim (frontData O n) * sourceFrontShift O n) /
    perim (unshiftedRear O n)

theorem rearShift_phase
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    (unshiftedKinematics O n).sf
        (perim (unshiftedRear O n) * rearShift O n) =
      perim (frontData O n) * sourceFrontShift O n := by
  let K := unshiftedKinematics O n
  let dl := NormalizedSteeringPhysicalRescaling.deltaPhys K.steering
    (perim (frontData O n))
  have hrearPos : 0 < perim (unshiftedRear O n) :=
    perim_pos (data O).separation_zero_pos (unshiftedRear_tube O n)
  have hmul : perim (unshiftedRear O n) * rearShift O n =
      rearArclength dl (perim (frontData O n) * sourceFrontShift O n) := by
    simpa [rearShift, K, dl] using
      (mul_div_cancel₀
        (rearArclength dl (perim (frontData O n) * sourceFrontShift O n))
        hrearPos.ne')
  rw [hmul]
  have hdlC : Continuous dl := by
    unfold dl NormalizedSteeringPhysicalRescaling.deltaPhys
    exact (Differentiable.continuous fun u =>
      K.steering.steering u |>.differentiableAt).comp
        (continuous_id.div_const _)
  have hmono : StrictMono (rearArclength dl) :=
    RearTrack.strictMono_rearArclength hdlC sourceKh_lt_one sourceKh_nonnegative
      (fun s => (NormalizedSteeringPhysicalRescaling.deltaPhys_mem
        K.steering (P := perim (frontData O n)) s).1)
      (fun s => (NormalizedSteeringPhysicalRescaling.deltaPhys_mem
        K.steering (P := perim (frontData O n)) s).2)
  apply hmono.injective
  exact K.arclength_rightInverse _

/-- The actual initial datum used by the geometric recursion. -/
def initial
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) : Data :=
  MarkedShift.shiftData (rearShift O n) (unshiftedRear O n)

theorem initial_tube
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    IsTubeMember (ConfiguredCanonicalPairSource.commonC (data O)) 0
      (ConfiguredCanonicalPairSource.commonDlt (data O)) (initial O n) :=
  MarkedShift.isTubeMember_shiftData (unshiftedRear_tube O n) (rearShift O n)

/-- The shifted physical initial rear retains the model carrier perimeter. -/
theorem initial_perim_eq
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    perim (initial O n) = 2 * (data O).Hs n := by
  rw [initial, SelectedInverseShiftEquivariance.perim_shiftData
    (unshiftedRear_tube O n)]
  let A := previousPresentation O n
  let r := ConfiguredGaugeFirstPhysicalSequence.rearPhase
    O.pair.input O.model_data A
  change perim (RichStageDataPhaseRigidTransport.move
    A.translation A.rotation r (O.pair.input.carrier n).data) =
      2 * (data O).Hs n
  rw [O.pair.input_carrier n]
  unfold RichStageDataPhaseRigidTransport.move
  calc
    perim (MarkedRigid.rigidData A.translation A.rotation
      (MarkedShift.shiftData r (O.pair.carriers n).data)) =
        perim (MarkedShift.shiftData r (O.pair.carriers n).data) := by
        simp [perim, A.rotation_norm]
    _ = perim (O.pair.carriers n).data :=
      SelectedInverseShiftEquivariance.perim_shiftData
        (O.pair.carrier_common n) r
    _ = 2 * (data O).Hs n := (O.pair.carriers n).perim_eq

/-- Physical kinematics with exactly the source's shifted front and the
corresponding shifted initial rear. -/
noncomputable def initialKinematics
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    PhysicalRearLimitKinematics sourceKh (initial O n)
      (MarkedShift.shiftData (sourceFrontShift O n) (frontData O n)) :=
  (unshiftedKinematics O n).shift
    (data O).separation_zero_pos (front_tube O n)
    (data O).separation_zero_pos (unshiftedRear_tube O n)
    (sourceFrontShift O n) (rearShift O n) (rearShift_phase O n)

theorem source_period_zero_eq_frontData
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    (source O C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n).P 0 =
      perim (frontData O n) := by
  have hp : perim (frontData O n) = 2 * (data O).Hs (n + 1) := by
    simpa [frontData,
      ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.presentation,
      ConfiguredGaugeFirstPhysicalSequence.alignedQ] using
      (ConfiguredAlignedQGeometry.perim_eq O.pair O.model_data (n + 1))
  rw [hp]
  change
    (ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily.edgeSourceAt O n
      (initialRearPhase O n)).P 0 = 2 * (data O).Hs (n + 1)
  rw [ConfiguredBaseProfiledEdgeInitialGaugeRecursiveAnalyticSuccessorFamily.edgeSourceAt_period_eq]
  rfl

theorem rearOwn_zero_eq_initial_ev
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) (x : ℝ) :
    rearOwn
        (source O C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) n).F
        (source O C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) n).Theta
        (source O C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) n).delta
        (source O C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) n).sf 0 x =
      ev (initial O n) x := by
  apply rearOwn_zero_eq_physicalRear
    (source O C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n)
    (initialKinematics O n)
  · exact source_front_zero_eq_shift O C n
  · simpa [SelectedInverseShiftEquivariance.perim_shiftData (front_tube O n)] using
      source_period_zero_eq_frontData O C n

theorem rearPeriod_zero_eq_initial_perim
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    rearPeriod (source O C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n) 0 = perim (initial O n) := by
  apply rearPeriod_zero_eq_physicalRear_perim
    (source O C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n)
    (initialKinematics O n)
  · exact source_front_zero_eq_shift O C n
  · simpa [SelectedInverseShiftEquivariance.perim_shiftData (front_tube O n)] using
      source_period_zero_eq_frontData O C n

/-- Exact curve identity required by the geometric recursion. -/
theorem initial_eq
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) (u : ℝ) :
    (initial O n).1 u =
      rearOwn
        (source O C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) n).F
        (source O C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) n).Theta
        (source O C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) n).delta
        (source O C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) n).sf 0
        (rearPeriod (source O C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) n) 0 * u) := by
  rw [rearOwn_zero_eq_initial_ev O C n,
    rearPeriod_zero_eq_initial_perim O C n]
  simp [ev, (perim_pos (data O).separation_zero_pos (initial_tube O n)).ne']

theorem initial_range
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    range (initial O n).1 = range (unshiftedRear O n).1 := by
  exact ConfiguredBaseProfiledEdgeInitialGaugeRecursiveAnalyticSuccessorFamily.range_shiftData
    (unshiftedRear O n) (rearShift O n)

end ConfiguredRecursiveEdgePhysicalInitialData
