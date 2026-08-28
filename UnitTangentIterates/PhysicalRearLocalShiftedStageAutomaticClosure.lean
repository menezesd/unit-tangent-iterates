import UnitTangentIterates.PhysicalRearLimitSynchronizedExtraction

/-!
# Automatic rowwise closure of phase-shifted physical rear stages

This module removes the explicit synchronized-limit callback from the older
fixed-row adapter.  A common normalized-steering Lipschitz bound supplies the
second compact extraction, whose exact index map remains exposed by
`ExtractedKinematicLimit`.
-/

noncomputable section

open Filter Set Topology MarkedSpace

namespace PhysicalRearLocalShiftedStageAutomaticClosure

open PathMetric NormalizedSteeringPhysicalRescaling CurvatureFromMarkedDistance

/-- Concrete fixed-row input sufficient for automatic phase and steering
compactness. -/
structure FixedRowInput (kh c dlt : ℝ) (rear front : Data) where
  rearN : ℕ → Data
  baseFrontN : ℕ → Data
  physicalFrontN : ℕ → Data
  phaseSidecar :
    PhysicalRearLocalPhaseCompactness.NormalizedPhaseSidecar
      baseFrontN physicalFrontN
  kinematics : ∀ k,
    PhysicalRearLimitKinematics kh (rearN k) (physicalFrontN k)
  rear_tube : ∀ k, IsTubeMember c 0 dlt (rearN k)
  physicalFront_tube : ∀ k,
    IsTubeMember c 0 dlt (physicalFrontN k)
  rear_tendsto : Tendsto rearN atTop (nhds rear)
  baseFront_tendsto : Tendsto baseFrontN atTop (nhds front)
  steeringLip : ∃ C : NNReal,
    ∀ k, LipschitzWith C (kinematics k).steering.delta

/-- The common steering modulus required by `FixedRowInput` follows from the
usual common front-perimeter and intrinsic-curvature bounds. -/
theorem exists_steeringLip_of_curvatureBounds
    {kh c dlt C Pmax : ℝ}
    {rearN frontN : ℕ → Data}
    (K : ∀ k, PhysicalRearLimitKinematics kh (rearN k) (frontN k))
    (hc : 0 < c)
    (hfront : ∀ k, IsTubeMember c 0 dlt (frontN k))
    (hC : 0 ≤ C)
    (hPmax : ∀ k, perim (frontN k) ≤ Pmax)
    (hcurv : ∀ k u, |dataCurv (frontN k) u| ≤ C) :
    ∃ L : NNReal, ∀ k, LipschitzWith L (K k).steering.delta := by
  refine ⟨Real.toNNReal (Pmax * (C + 1)), fun k => ?_⟩
  exact (K k).normalizedSteering_lipschitz hc (hfront k) hC
    (hPmax k) (hcurv k)

/-- Compact phase extraction followed by automatic synchronized steering and
inverse extraction closes one limiting shifted physical stage. -/
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
      atTop (nhds (q : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp hq
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
  have hrearSTube : ∀ k, IsTubeMember c 0 dlt (rearS k) :=
    fun k => I.rear_tube (phi k)
  have hfrontSTube : ∀ k, IsTubeMember c 0 dlt (frontS k) :=
    fun k => I.physicalFront_tube (phi k)
  let hfrontShift : IsTubeMember c 0 dlt
      (MarkedShift.shiftData (q : ℝ) front) :=
    MarkedShift.isTubeMember_shiftData hfront (q : ℝ)
  obtain ⟨C, hLip⟩ := I.steeringLip
  let E := Nonempty.some (exists_extractedKinematicLimit_of_lipschitz
    KS hkh0 hkh1 hc hfrontSTube hfrontShift hrearS hfrontS
      (fun k => hLip (phi k)))
  let Sync := E.toSynchronizedKinematicLimit hkh0 hkh1 hc
    hrearSTube hfrontSTube hrear hfrontShift hrearS hfrontS
  let rearSS : ℕ → Data := fun k => rearS (E.phi k)
  let frontSS : ℕ → Data := fun k => frontS (E.phi k)
  let KSS : ∀ k, PhysicalRearLimitKinematics kh (rearSS k) (frontSS k) :=
    fun k => KS (E.phi k)
  have hrearSS : Tendsto rearSS atTop (nhds rear) := by
    simpa [rearSS, Function.comp_def] using
      hrearS.comp E.phi_strictMono.tendsto_atTop
  have hfrontSS : Tendsto frontSS atTop
      (nhds (MarkedShift.shiftData (q : ℝ) front)) := by
    simpa [frontSS, Function.comp_def] using
      hfrontS.comp E.phi_strictMono.tendsto_atTop
  refine ⟨q, ⟨limitStageComponents_of_paired_tendsto
    KSS Sync.limit hkh0 hkh1 hc
    (fun k => hfrontSTube (E.phi k)) hrear hfrontShift
    hrearSS hfrontSS ?_ ?_⟩⟩
  · exact Sync.sf_tendsto
  · exact Sync.delta_tendsto

/-- Rowwise automatic inputs produce the local shifted stages used by the
all-orders regularity bootstrap. -/
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

end PhysicalRearLocalShiftedStageAutomaticClosure
