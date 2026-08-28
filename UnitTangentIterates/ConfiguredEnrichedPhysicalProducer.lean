import UnitTangentIterates.ConfiguredEnrichedConstructionCoreProvider
import UnitTangentIterates.FiniteSmoothRearFamilyEnrichedPhysicalTransition
import UnitTangentIterates.EnrichedGaugeFirstFinitePhysicalCertificate

/-!
# Physical output of the deterministic configured enriched recursion

This module projects the physical certificates retained by the exact base and
successor columns.  No second column choice is made.
-/

noncomputable section

open MarkedSpace PathMetric Filter

namespace ConfiguredEnrichedPhysicalProducer

open ConfiguredApproximateDefectPathRowwise
  ConfiguredRowCeilingPolynomialEnvelopes
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConfiguredDiagonalStableRowDefectProvider
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredEnrichedConstructionCoreProvider
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyEnrichedMapProvider

/-- The actual selected base column has the configured physical rear
kinematics. -/
theorem base_physical
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (hH : 1 ≤ D.Hs 0)
    (n : ℕ) : Nonempty
      (PhysicalRearLimitKinematics kh
        ((baseProvider S hQ C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) hH).base.step.richStage n).terminalBase
        (alignedQ S hQ (n + 1))) := by
  simpa [baseProvider, baseColumnStep] using
    (ConfiguredGaugeFirstPhysicalSequence.retainedPhysical
      (S := S) (hQ := hQ) 1 C n)

/-- Every actual selected successor of the configured construction core
retains its corrected physical transition. -/
theorem constructionCore_physicalTransition
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
    (G : Provider (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (rowP0 D) (wideP1 D MA0) (fun _ => D.kstar)
      (wideG1 D MA0 NA0) (wideCg D MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax Mtotal a MA NA K0 K1 K2)
    (hkh : ∀ n, khRow n = kh0) (k : ℕ) :
    EnrichedGaugeFirstFinitePhysicalCertificate.PhysicalTransitionCertificate
      ((constructionCore S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G).chosenColumn k)
      ((constructionCore S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G).mapProvider.map k
        ((constructionCore S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G).chosenColumn k)).val
      kh0 := by
  simpa [constructionCore, FiniteSmoothRearFamilyEnrichedMapProvider.mapProvider] using
    (mappedColumn_physicalTransition G hkh k
      ((constructionCore S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G).chosenColumn k))

/-- The exact base and deterministic successor certificates assemble finite
physical kinematics on every retained row of the construction core. -/
theorem constructionCore_finite
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {kh c dlt kh0 : ℝ}
    (S : ConfiguredModelPairSource.Input D Q kh c dlt)
    (hQ : ∀ n,
      perim (Q n) = 2 * D.Hs n ∧
      ev (Q n) = TwoCapPairsAssembly.front
        (D.kappas n) D.model.thetaBase (D.Hs n))
    (C : ℕ → ℝ) {MA0 NA0 : ℝ} (hH : 1 ≤ D.Hs 0)
    (khRow Qmax Mtotal : ℕ → ℝ)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ)
    (G : Provider (alignedQ S hQ)
      (ConfiguredDiagonalStableRowDefectProvider.error D (physicalCoeff D))
      (rowP0 D) (wideP1 D MA0) (fun _ => D.kstar)
      (wideG1 D MA0 NA0) (wideCg D MA0 NA0) C c dlt
      (period D) (diagonal D) khRow Qmax Mtotal a MA NA K0 K1 K2)
    (hkh : ∀ n, khRow n = kh) :
    FinitePullbackPhysicalRearKinematics kh
      (EnrichedPhysicalHarnackClosure.retainedRows
        (constructionCore S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G).baseProvider
        (constructionCore S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G).mapProvider) := by
  let F := constructionCore S hQ C hH khRow Qmax Mtotal a MA NA K0 K1 K2 G
  refine ⟨?_⟩
  intro n k
  cases k with
  | zero =>
      simpa [F, EnrichedPhysicalHarnackClosure.retainedRows,
        ConstructionCore.chosenColumn,
        EnrichedPhysicalChosenRichFamily.columns_zero] using
        (base_physical S hQ C (MA0 := MA0) (NA0 := NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) hH n)
  | succ k =>
      have H := constructionCore_physicalTransition S hQ C hH khRow Qmax
        Mtotal a MA NA K0 K1 K2 G hkh k
      simpa [F, EnrichedPhysicalHarnackClosure.retainedRows] using
        H.physical n

end ConfiguredEnrichedPhysicalProducer
