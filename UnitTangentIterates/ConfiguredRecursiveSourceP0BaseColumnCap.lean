import UnitTangentIterates.ConfiguredMarkingAwareAnalyticKhatBaseColumnCap
import UnitTangentIterates.ConfiguredRecursiveSourceP0ConstructionCoreProvider

/-! # Configured base cap at the recursive speed floor -/

noncomputable section

open Set MarkedSpace

namespace ConfiguredRecursiveSourceP0BaseColumnCap

open ConfiguredApproximateDefectPathRowwise
  ConfiguredCorrelatedBaseColumnCap
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredRecursiveSourceP0
  FiniteSmoothRearFamilyMarkingAwarePhysicalCore
  FiniteSmoothRearFamilyMarkingAwareSource

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
    (source : ∀ n, MarkingAwareSource
      (((ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseProvider
        S hQ C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1)
          (K2 := K2) hH hkhat).base.step.richStage (n + 1)).stage.increment)
      (sourceP0 D n) (khRow n) khat (Qmax n))

/-- The configured endpoint and terminal-curvature cap is independent of the
weakened analytic speed-floor parameter. -/
theorem baseColumnCap
    {M : ℝ}
    (hM : ∀ n, rowDefect D n ≤ M) :
    ColumnCap
      (ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseCorrelated
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
    have hstage := (ConfiguredGaugeFirstPhysicalSequence.richStage_spec
      S hQ 1 C n).1
    have hterminal :
        ((ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseCorrelated
          S hQ C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1)
            (K2 := K2) hH hkhat khRow Qmax source).column.step.richStage n).terminalBase =
          RichStageDataPhaseRigidTransport.move A.translation A.rotation
            (W.marking.marking.psi A.phase) W.terminalBase := by
      calc
        _ = RichStageDataPhaseRigidTransport.move A.translation A.rotation
            (ConfiguredGaugeFirstPhysicalSequence.rearPhase S hQ A)
            (S.carrier n).data := by
          simpa [ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseCorrelated,
            ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseProvider,
            ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseColumnStep,
            ConfiguredRecursiveSourceP0ConstructionCoreProvider.lowerRichStageP0,
            R, A] using hstage
        _ = RichStageDataPhaseRigidTransport.move A.translation A.rotation
            (W.marking.marking.psi A.phase) W.terminalBase := by
          exact (ConfiguredGaugeFirstPhysicalSequence.terminalBase_eq_physicalRear
            S hQ n).symm
    have hend := W.transported_endpoint_dist A.phase A.translation A.rotation
      A.rotation_norm
    change dist (ConfiguredGaugeFirstPhysicalSequence.movedRear S hQ n)
      ((ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseCorrelated
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
    have hstage := (ConfiguredGaugeFirstPhysicalSequence.richStage_spec
      S hQ 1 C n).1
    have hterminal :
        ((ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseCorrelated
          S hQ C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1)
            (K2 := K2) hH hkhat khRow Qmax source).column.step.richStage n).terminalBase =
          RichStageDataPhaseRigidTransport.move A.translation A.rotation
            (ConfiguredGaugeFirstPhysicalSequence.rearPhase S hQ A)
            (S.carrier n).data := by
      simpa [ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseCorrelated,
        ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseProvider,
        ConfiguredRecursiveSourceP0ConstructionCoreProvider.baseColumnStep,
        ConfiguredRecursiveSourceP0ConstructionCoreProvider.lowerRichStageP0,
        R, A] using hstage
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

end ConfiguredRecursiveSourceP0BaseColumnCap
