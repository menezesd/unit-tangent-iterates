import UnitTangentIterates.ConstructedPulseWidth
import UnitTangentIterates.ConstructedConfiguredInductiveTubeBudget

/-! # Shift transport for the canonical endpoint regularity certificate -/

noncomputable section

namespace ConstructedPulseWidth

/-- Discarding a finite prefix preserves the retained endpoint regularity. -/
def C3Certificate.shift
    {D : ConstructedConfiguredSequenceWeighted.Data} (H : C3Certificate D)
    (N : ℕ) : C3Certificate
      (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift D N) where
  model_KP_C3 := by
    intro n
    simpa [ConstructedConfiguredInductiveTubeBudget.WeightedData.shift] using
      H.model_KP_C3 (N + n)
  model_kH_C3 := by
    intro n
    simpa [ConstructedConfiguredInductiveTubeBudget.WeightedData.shift] using
      H.model_kH_C3 (N + n)

end ConstructedPulseWidth

