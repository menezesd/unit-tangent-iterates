import UnitTangentIterates.ConfiguredAnalyticKhatConstructionCoreProvider
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareOfLegacy

/-!
# Sound marking-aware configured base column

The initial interpolation has an affine marking, so its legacy analytic source
embeds into the marking-aware recursion.  This definition retains that source
on the exact widened gauge-first base column; no successor marking is treated
as affine.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredMarkingAwareBaseCorrelated

open ConfiguredApproximateDefectPathRowwise
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredRowCeilingPolynomialEnvelopes
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredDiagonalStableRowDefectProvider
  ConfiguredEnrichedConstructionCoreProvider
  EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyAnalyticSource
  FiniteSmoothRearFamilyEnrichedMapProvider

/-- Attach an affine initial analytic source to the sound marking-aware base
column.  The column and terminal physical data are exactly those selected by
`ConfiguredAnalyticKhatConstructionCoreProvider.baseProvider`. -/
def baseCorrelatedOfLegacy
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt khat : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (hH : 1 ≤ D.Hs 0)
    (hkhat : D.kstar ≤ khat) (khRow Qmax : ℕ → ℝ)
    (source : ∀ n, Source
      (((ConfiguredAnalyticKhatConstructionCoreProvider.baseProvider
        S hQ C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1)
          (K2 := K2) hH hkhat).base.step.richStage (n + 1)).stage.increment)
      (rowP0 D n) (khRow n) khat (Qmax n)) :
    FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.CorrelatedColumn
      (alignedQ S hQ) (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D)) 0
      (rowP0 D) (wideP1 D MA0) (fun _ ↦ khat)
      (wideG1 D MA0 NA0) (wideCgWithKhat D khat MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax K0 K1 K2 where
  column := (ConfiguredAnalyticKhatConstructionCoreProvider.baseProvider
    S hQ C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1)
      (K2 := K2) hH hkhat).base
  source := fun n ↦
    FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.ofLegacy
      (source n)

end ConfiguredMarkingAwareBaseCorrelated
