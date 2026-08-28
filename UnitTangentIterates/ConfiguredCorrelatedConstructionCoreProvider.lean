import UnitTangentIterates.ConfiguredEnrichedConstructionCoreProvider
import UnitTangentIterates.FiniteSmoothRearFamilyCorrelatedPhysicalCore

/-!
# Configured source-preserving correlated construction core

This is the configured base-side adapter for the non-erasing correlated
recursion.  It uses the already selected gauge-first physical base column and
attaches only the analytic sources belonging to that exact column.  No map on
arbitrary erased columns is introduced.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredCorrelatedConstructionCoreProvider

open ConfiguredApproximateDefectPathRowwise
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredRowCeilingPolynomialEnvelopes
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredDiagonalStableRowDefectProvider
  ConfiguredEnrichedConstructionCoreProvider
  FiniteSmoothRearFamilyAnalyticSource
  FiniteSmoothRearFamilyCorrelatedPhysicalCore
  FiniteSmoothRearFamilyCorrelatedRecursion

/-- Attach the rowwise analytic sources to the exact configured physical base
column.  The source family is the remaining front/rear analytic construction,
not an output callback. -/
def baseCorrelated
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (hH : 1 ≤ D.Hs 0)
    (khRow Qmax : ℕ → ℝ)
    (source : ∀ n, Source
      (((ConfiguredEnrichedConstructionCoreProvider.baseProvider S hQ C
          (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
          hH).base.step.richStage (n + 1)).stage.increment)
      (rowP0 D n) (khRow n) D.kstar (Qmax n)) :
    CorrelatedColumn
      (alignedQ S hQ) (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D)) 0
      (rowP0 D) (wideP1 D MA0) (fun _ => D.kstar)
      (wideG1 D MA0 NA0) (wideCg D MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax K0 K1 K2 where
  column := (ConfiguredEnrichedConstructionCoreProvider.baseProvider S hQ C
    (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2) hH).base
  source := source

/-- Assemble the configured diagonal defect, exact correlated base column,
and the source-preserving row constructor into the selected recursion core. -/
def constructionCore
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 : ℝ} (hH : 1 ≤ D.Hs 0)
    (khRow Qmax Mtotal : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (source : ∀ n, Source
      (((ConfiguredEnrichedConstructionCoreProvider.baseProvider S hQ C
          (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
          hH).base.step.richStage (n + 1)).stage.increment)
      (rowP0 D n) (khRow n) D.kstar (Qmax n))
    (G : FiniteSmoothRearFamilyCorrelatedRecursion.Provider
      (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (rowP0 D) (wideP1 D MA0) (fun _ => D.kstar)
      (wideG1 D MA0 NA0) (wideCg D MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax Mtotal a MA NA K0 K1 K2) :
    FiniteSmoothRearFamilyCorrelatedPhysicalCore.ConstructionCore
      (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (rowP0 D) (wideP1 D MA0) (fun _ => D.kstar)
      (wideG1 D MA0 NA0) (wideCg D MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax Mtotal a MA NA K0 K1 K2 where
  defect := ConfiguredDiagonalStableRowDefectProvider.provider D
    (physicalCertificate D)
  base := baseCorrelated S hQ C hH khRow Qmax source
  provider := G

end ConfiguredCorrelatedConstructionCoreProvider
