import UnitTangentIterates.ConfiguredActualHalfAnalyticRowProduction
import UnitTangentIterates.ConfiguredAnalyticKhatBaseColumnCap

/-!
# Depth-zero cap for the shifted analytic construction

This is an auxiliary adapter for the legacy analytic core.  It is deliberately
kept separate from the marking-aware paper-facing recursion: the estimate is
useful there as well, but no identification of the two recursive providers is
made.
-/

noncomputable section

open Set MarkedSpace PathMetric

namespace ConfiguredActualHalfAnalyticBaseCap

open ConfiguredActualHalfAnalyticRowProduction
  ConfiguredActualHalfScalarStart
  ConfiguredApproximateDefectPathRowwise
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredCorrelatedBaseColumnCap
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  FiniteSmoothRearFamilyCorrelatedPhysicalCore

variable {MA0 NA0 : ℝ} (O : ConfiguredActualHalfScalarStart.Output MA0 NA0)

/-- The shifted row defect is bounded by the scalar cap already selected by
the epsilon-level large-separation construction. -/
theorem rowDefect_le_Mend (n : ℕ) : rowDefect (D O) n ≤ O.Mend := by
  have hscale : rowDefect (D O) n ≤ physicalDefect (D O) n := by
    unfold physicalDefect physicalCoeff
    have hrow0 := ConfiguredRowDefectProvider.rowDefect_nonneg (D O) n
    have hH : 1 ≤ 2 * (D O).Hs n := by
      have hs := (separation_one O).trans ((D O).separation_lower n)
      linarith
    nlinarith
  have hstrict : physicalDefect (D O) n < O.Mend := by
    simpa [D, ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
      physicalDefect, physicalCoeff,
      ConfiguredApproximateDefectPathRowwise.rowDefect] using
      O.physicalDefect_lt (O.large.N + n)
  exact hscale.trans hstrict.le

/-- The exact cap on the base column of `LegacyPackage.core`.  This theorem is
coefficient-exact: the base interpolation has its own explicit conversion,
which should later be combined with the successor conversion by `max` rather
than silently identified with it. -/
theorem baseCap (P : LegacyPackage O) :
    ColumnCap (LegacyPackage.core O P).base
      (baseEndpointConversion (D O) O.Mend) (physicalDefect (D O)) := by
  simpa [LegacyPackage.core] using
    (ConfiguredAnalyticKhatBaseColumnCap.baseColumnCap
      (S := O.pair.input) (hQ := O.model_data) (C := rowC O)
      (hH := separation_one O) (hkhat := kstar_le_pathKhat O)
      (MA0 := MA0) (NA0 := NA0) (K0 := P.K0) (K1 := P.K1) (K2 := P.K2)
      (khRow := khRow) (Qmax := Qmax O) (source := P.source)
      (M := O.Mend) (rowDefect_le_Mend O))

end ConfiguredActualHalfAnalyticBaseCap
