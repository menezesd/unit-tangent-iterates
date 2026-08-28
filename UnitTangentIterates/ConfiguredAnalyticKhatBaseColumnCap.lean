import UnitTangentIterates.ConfiguredCorrelatedBaseColumnCap
import UnitTangentIterates.ConfiguredAnalyticKhatConstructionCoreProvider

/-!
# The configured base cap with an independent analytic curvature ceiling

The analytic construction widens the coarse path-curvature ceiling from
`D.kstar` to an independently supplied `khat`.  This does not change the
chosen interpolation path, its terminal base, or the quantitative endpoint
estimate.  The theorem below records that the configured base-column cap is
therefore available for the analytic construction core as well.
-/

noncomputable section

open Set MarkedSpace

namespace ConfiguredAnalyticKhatBaseColumnCap

open ConfiguredPolynomialDiagonalStableRowDefectProvider
open ConfiguredApproximateDefectPathRowwise
open ConfiguredCorrelatedBaseColumnCap
open FiniteSmoothRearFamilyAnalyticSource
open FiniteSmoothRearFamilyCorrelatedPhysicalCore

variable
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {Q : ℕ → Data} {kh c dlt khat : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) (hH : 1 ≤ D.Hs 0) (hkhat : D.kstar ≤ khat)
    {MA0 NA0 K0 K1 K2 : ℝ}
    (khRow Qmax : ℕ → ℝ)
    (source : ∀ n, Source
      (((ConfiguredAnalyticKhatConstructionCoreProvider.baseProvider
        S hQ C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1)
          (K2 := K2) hH hkhat).base.step.richStage (n + 1)).stage.increment)
      (rowP0 D n) (khRow n) khat (Qmax n))

/-- The exact configured base cap, transported to the analytic-`khat`
construction.  The sole scalar input is the already constructed uniform
upper bound for the diagonal defect. -/
theorem baseColumnCap
    {M : ℝ}
    (hM : ∀ n, rowDefect D n ≤ M) :
    ColumnCap
      (ConfiguredAnalyticKhatConstructionCoreProvider.baseCorrelated
        S hQ C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1)
          (K2 := K2) hH hkhat khRow Qmax source)
      (baseEndpointConversion D M) (physicalDefect D) := by
  refine ⟨?_, ?_⟩
  · intro n
    let A := ConfiguredGaugeFirstPhysicalSequence.presentations
      (S := S) (hQ := hQ) n
    let W := ConfiguredGaugeFirstPhysicalSequence.output S hQ n
    let R := Classical.choose
      (ConfiguredGaugeFirstPhysicalSequence.exists_richStage S hQ 1 C n)
    have hR := Classical.choose_spec
      (ConfiguredGaugeFirstPhysicalSequence.exists_richStage S hQ 1 C n)
    have hterminal :
        ((ConfiguredAnalyticKhatConstructionCoreProvider.baseCorrelated
          S hQ C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1)
            (K2 := K2) hH hkhat khRow Qmax source).column.step.richStage n).terminalBase =
          RichStageDataPhaseRigidTransport.move A.translation A.rotation
            (W.marking.marking.psi A.phase) W.terminalBase := by
      calc
        _ = R.terminalBase := by rfl
        _ = RichStageDataPhaseRigidTransport.move A.translation A.rotation
            (ConfiguredGaugeFirstPhysicalSequence.rearPhase S hQ A)
            (S.carrier n).data := hR.1
        _ = RichStageDataPhaseRigidTransport.move A.translation A.rotation
            (W.marking.marking.psi A.phase) W.terminalBase := by
          exact (ConfiguredGaugeFirstPhysicalSequence.terminalBase_eq_physicalRear
            S hQ n).symm
    have hend := W.transported_endpoint_dist A.phase A.translation A.rotation
      A.rotation_norm
    change dist (ConfiguredGaugeFirstPhysicalSequence.movedRear S hQ n)
      ((ConfiguredAnalyticKhatConstructionCoreProvider.baseCorrelated
        S hQ C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1)
          (K2 := K2) hH hkhat khRow Qmax source).column.step.richStage n).terminalBase ≤ _
    rw [hterminal]
    exact hend.trans (baseTransportMarkingBound_le_physicalDefect D hH hM n)
  · intro n u
    let A := ConfiguredGaugeFirstPhysicalSequence.presentations
      (S := S) (hQ := hQ) n
    let R := Classical.choose
      (ConfiguredGaugeFirstPhysicalSequence.exists_richStage S hQ 1 C n)
    have hR := Classical.choose_spec
      (ConfiguredGaugeFirstPhysicalSequence.exists_richStage S hQ 1 C n)
    have hterminal :
        ((ConfiguredAnalyticKhatConstructionCoreProvider.baseCorrelated
          S hQ C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1)
            (K2 := K2) hH hkhat khRow Qmax source).column.step.richStage n).terminalBase =
          RichStageDataPhaseRigidTransport.move A.translation A.rotation
            (ConfiguredGaugeFirstPhysicalSequence.rearPhase S hQ A)
            (S.carrier n).data := by
      calc
        _ = R.terminalBase := by rfl
        _ = _ := hR.1
    rw [hterminal]
    have htube := MarkedRigid.isTubeMember_rigidData (a := A.translation)
      A.rotation_norm
      (MarkedShift.isTubeMember_shiftData (S.carrier n).tube
        (ConfiguredGaugeFirstPhysicalSequence.rearPhase S hQ A))
    change 0 ≤ ((starRingEnd ℂ)
      ((RichStageDataPhaseRigidTransport.move A.translation A.rotation
        (ConfiguredGaugeFirstPhysicalSequence.rearPhase S hQ A)
        (S.carrier n).data).2.1 u) *
      (RichStageDataPhaseRigidTransport.move A.translation A.rotation
        (ConfiguredGaugeFirstPhysicalSequence.rearPhase S hQ A)
        (S.carrier n).data).2.2 u).im
    simpa [RichStageDataPhaseRigidTransport.move] using htube.curv_lb u

end ConfiguredAnalyticKhatBaseColumnCap
