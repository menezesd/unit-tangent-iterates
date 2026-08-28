import UnitTangentIterates.ConfiguredAnalyticKhatConstructionCoreProvider
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePhysicalCore

/-!
# Configured marking-aware core with the independent analytic ceiling

The widened gauge-first base column is shared with the legacy construction.
Only the analytic source and recursive provider are replaced here.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredMarkingAwareAnalyticKhatConstructionCoreProvider

open ConfiguredApproximateDefectPathRowwise
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredRowCeilingPolynomialEnvelopes
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredDiagonalStableRowDefectProvider
  ConfiguredEnrichedConstructionCoreProvider
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwarePhysicalCore
  FiniteSmoothRearFamilyMarkingAwareSource

/-- Attach the genuine nonaffine source to the configured widened base. -/
def baseCorrelated
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt khat : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (hH : 1 ≤ D.Hs 0)
    (hkhat : D.kstar ≤ khat) (khRow Qmax : ℕ → ℝ)
    (source : ∀ n, MarkingAwareSource
      (((ConfiguredAnalyticKhatConstructionCoreProvider.baseProvider
          S hQ C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) hH hkhat).base.step.richStage
          (n + 1)).stage.increment)
      (rowP0 D n) (khRow n) khat (Qmax n)) :
    CorrelatedColumn (alignedQ S hQ) (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D)) 0
      (rowP0 D) (wideP1 D MA0) (fun _ ↦ khat)
      (wideG1 D MA0 NA0) (wideCgWithKhat D khat MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax K0 K1 K2 where
  column := (ConfiguredAnalyticKhatConstructionCoreProvider.baseProvider
    S hQ C (MA0 := MA0) (NA0 := NA0)
    (K0 := K0) (K1 := K1) (K2 := K2) hH hkhat).base
  source := source

/-- Sound configured construction core.  Its only analytic inputs are the
actual base sources and the concrete marking-aware successor provider. -/
def constructionCore
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt khat : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 : ℝ} (hH : 1 ≤ D.Hs 0)
    (hkhat : D.kstar ≤ khat)
    (khRow Qmax : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (source : ∀ n, MarkingAwareSource
      (((ConfiguredAnalyticKhatConstructionCoreProvider.baseProvider
          S hQ C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) hH hkhat).base.step.richStage
          (n + 1)).stage.increment)
      (rowP0 D n) (khRow n) khat (Qmax n))
    (G : Provider (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (rowP0 D) (wideP1 D MA0) (fun _ ↦ khat)
      (wideG1 D MA0 NA0) (wideCgWithKhat D khat MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax a MA NA K0 K1 K2) :
    ConstructionCore (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (rowP0 D) (wideP1 D MA0) (fun _ ↦ khat)
      (wideG1 D MA0 NA0) (wideCgWithKhat D khat MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax a MA NA K0 K1 K2 where
  defect := ConfiguredDiagonalStableRowDefectProvider.provider D
    (physicalCertificate D)
  base := baseCorrelated S hQ C hH hkhat khRow Qmax source
  provider := G

/-- The base physical edge is inherited from the exact same widened base
column used in `constructionCore`. -/
theorem basePhysical
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt khat : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (hH : 1 ≤ D.Hs 0)
    (hkhat : D.kstar ≤ khat) (n : ℕ) :
    Nonempty (PhysicalRearLimitKinematics kh
      ((ConfiguredAnalyticKhatConstructionCoreProvider.baseProvider
        S hQ C (MA0 := MA0) (NA0 := NA0)
        (K0 := K0) (K1 := K1) (K2 := K2) hH hkhat).base.step.richStage n).terminalBase
      (alignedQ S hQ (n + 1))) :=
  ConfiguredAnalyticKhatConstructionCoreProvider.basePhysical
    S hQ C hH hkhat n

end ConfiguredMarkingAwareAnalyticKhatConstructionCoreProvider

