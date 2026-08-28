import UnitTangentIterates.MarkedShiftCompactContinuity
import UnitTangentIterates.PhysicalRearLocalPhaseCompactness
import UnitTangentIterates.PhysicalRearTrackLimitClosure

/-!
# Rowwise closure of phase-shifted physical rear stages

This is the honest adapter between a concrete finite-row sidecar and the local
shifted-stage hypothesis used by the all-orders regularity bootstrap.  Compact
phase extraction and convergence of the shifted front are proved here.  The
remaining synchronized inverse/steering convergence is kept as an explicit
sidecar rather than inferred from tube boundedness.
-/

noncomputable section

open Filter Set Topology MarkedSpace

namespace PhysicalRearLocalShiftedStageClosure

open PathMetric NormalizedSteeringPhysicalRescaling

/-- The exact synchronized analytic limit needed after a phase subsequence has
been selected.  These two convergence fields are precisely what closes the
rear-track identity. -/
structure SynchronizedKinematicLimit
    (kh : ℝ) (rearN frontN : ℕ → Data) (rear front : Data)
    (K : ∀ k, PhysicalRearLimitKinematics kh (rearN k) (frontN k)) where
  limit : PhysicalRearLimitKinematicsWithoutTrack kh rear front
  sf_tendsto : ∀ x,
    Tendsto (fun k => (K k).sf x) atTop (nhds (limit.sf x))
  delta_tendsto : ∀ x, Tendsto
    (fun k => deltaPhys (K k).steering (perim (frontN k)) ((K k).sf x))
    atTop
    (nhds (deltaPhys limit.steering (perim front) (limit.sf x)))

/-- Explicit fixed-row finite data.  The `synchronized` callback is invoked
only after compactness has chosen a convergent normalized phase subsequence. -/
structure FixedRowInput (kh c dlt : ℝ) (rear front : Data) where
  rearN : ℕ → Data
  baseFrontN : ℕ → Data
  physicalFrontN : ℕ → Data
  phaseSidecar :
    PhysicalRearLocalPhaseCompactness.NormalizedPhaseSidecar
      baseFrontN physicalFrontN
  kinematics : ∀ k,
    PhysicalRearLimitKinematics kh (rearN k) (physicalFrontN k)
  physicalFront_tube : ∀ k,
    IsTubeMember c 0 dlt (physicalFrontN k)
  rear_tendsto : Tendsto rearN atTop (nhds rear)
  baseFront_tendsto : Tendsto baseFrontN atTop (nhds front)
  synchronized : ∀ (q : Set.Icc (0 : ℝ) 1) (phi : ℕ → ℕ),
    StrictMono phi →
    Tendsto (fun k => phaseSidecar.phase (phi k)) atTop (nhds q) →
    Nonempty (SynchronizedKinematicLimit kh
      (fun k => rearN (phi k))
      (fun k => physicalFrontN (phi k))
      rear (MarkedShift.shiftData (q : ℝ) front)
      (fun k => kinematics (phi k)))

/-- Compact phase extraction plus the synchronized kinematic sidecar closes a
single limiting adjacent stage, with the successor shifted by the limiting
phase. -/
theorem exists_shifted_stage_of_fixedRowInput
    {kh c dlt : ℝ} {rear front : Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front)
    (I : FixedRowInput kh c dlt rear front) :
    ∃ q : ℝ, Nonempty
      (PhysicalRearLimitStageComponents rear
        (MarkedShift.shiftData q front)) := by
  obtain ⟨q, phi, hphi, hq⟩ :=
    PhysicalRearLocalPhaseCompactness.exists_phase_subseq I.phaseSidecar
  let rearS : ℕ → Data := fun k => I.rearN (phi k)
  let frontS : ℕ → Data := fun k => I.physicalFrontN (phi k)
  let KS : ∀ k, PhysicalRearLimitKinematics kh (rearS k) (frontS k) :=
    fun k => I.kinematics (phi k)
  have hrearS : Tendsto rearS atTop (nhds rear) := by
    simpa [rearS, Function.comp_def] using
      I.rear_tendsto.comp hphi.tendsto_atTop
  have hbaseS : Tendsto (fun k => I.baseFrontN (phi k)) atTop
      (nhds front) := by
    simpa [Function.comp_def] using
      I.baseFront_tendsto.comp hphi.tendsto_atTop
  have hqReal : Tendsto (fun k => (I.phaseSidecar.phase (phi k) : ℝ))
      atTop (nhds (q : ℝ)) := by
    exact continuous_subtype_val.continuousAt.tendsto.comp hq
  have hshifted : Tendsto
      (fun k => MarkedShift.shiftData
        (I.phaseSidecar.phase (phi k) : ℝ) (I.baseFrontN (phi k)))
      atTop (nhds (MarkedShift.shiftData (q : ℝ) front)) :=
    MarkedShiftCompactContinuity.tendsto_shiftData hfront hbaseS hqReal
  have hfrontS : Tendsto frontS atTop
      (nhds (MarkedShift.shiftData (q : ℝ) front)) := by
    apply hshifted.congr'
    exact Eventually.of_forall fun k => by
      simpa [frontS] using (I.phaseSidecar.front_eq (phi k)).symm
  let L := Nonempty.some (I.synchronized q phi hphi hq)
  have hfrontSTube : ∀ k, IsTubeMember c 0 dlt (frontS k) :=
    fun k => I.physicalFront_tube (phi k)
  let hfrontShift : IsTubeMember c 0 dlt
      (MarkedShift.shiftData (q : ℝ) front) :=
    MarkedShift.isTubeMember_shiftData hfront (q : ℝ)
  refine ⟨q, ⟨limitStageComponents_of_paired_tendsto
    KS L.limit hkh0 hkh1 hc hfrontSTube hrear hfrontShift
    hrearS hfrontS ?_ ?_⟩⟩
  · exact L.sf_tendsto
  · exact L.delta_tendsto

/-- Rowwise explicit finite inputs produce exactly the local shifted-stage
family consumed by `SelectedRearAllOrdersRegularity`. -/
theorem localShiftedStages_of_fixedRowInputs
    {kh c dlt : ℝ} {X : ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hX : ∀ n, IsTubeMember c 0 dlt (X n))
    (I : ∀ n, FixedRowInput kh c dlt (X n) (X (n + 1))) :
    ∀ n, ∃ q : ℝ, Nonempty
      (PhysicalRearLimitStageComponents (X n)
        (MarkedShift.shiftData q (X (n + 1)))) := by
  intro n
  exact exists_shifted_stage_of_fixedRowInput hkh0 hkh1 hc
    (hX n) (hX (n + 1)) (I n)

end PhysicalRearLocalShiftedStageClosure
