import UnitTangentIterates.ConfiguredActualHalfCappedMarkingAwareRowProduction

/-!
# Noncircular assembly of the final marking-aware package

The analytic envelope ceilings are fixed before diagonal large separation is
chosen.  A `RowBuilder` is correspondingly quantified over every scalar
output at those fixed ceilings: it may use the shift selected by that output
to construct the base sources and capped successor provider, but it cannot
change the ceilings after seeing the shift.

This is the strongest automatic assembly available without a theorem giving
uniform bounds for the intrinsic successor coefficients.  In particular,
the scalar-only zero choice is not used as an analytic bound.
-/

noncomputable section

namespace ConfiguredActualHalfCappedRowProductionBuilder

open ConfiguredActualHalfCappedMarkingAwareRowProduction

/-- Analytic row construction at envelope ceilings fixed before scalar tail
selection.  The universal quantifier is the dependency-order invariant: the
builder is supplied first and must work for the subsequently selected scalar
output and its shifted configured data. -/
structure RowBuilder (MA0 NA0 : ℝ) where
  build : ∀ O : ConfiguredActualHalfMergedScalarStart.Output MA0 NA0,
    Nonempty (RowPackage O)

/-- A complete pre-tail input: fixed nonnegative envelope ceilings together
with construction of the base marking-aware sources and capped successor
provider for every scalar output at those ceilings. -/
structure PreTailBuilder where
  choice : ConfiguredActualHalfScalarChoice.Choice
  rows : RowBuilder choice.MA0 choice.NA0

/-- Choose scalar/model data and the large-separation tail first, then invoke
the already-fixed analytic row builder on exactly that shifted output. -/
theorem exists_finalPackage_of_rowBuilder
    {eps MA0 NA0 : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10)
    (hMA0 : 0 ≤ MA0) (hNA0 : 0 ≤ NA0)
    (B : RowBuilder MA0 NA0) :
    Nonempty FinalPackage := by
  obtain ⟨O⟩ := ConfiguredActualHalfMergedScalarStart.exists_output_of_eps
    heps heps10 hMA0 hNA0
  obtain ⟨R⟩ := B.build O
  exact ⟨{
    choice := {
      MA0 := MA0
      NA0 := NA0
      MA0_nonnegative := hMA0
      NA0_nonnegative := hNA0
    }
    coherent := {
      scalar := O
      row := R
    }
  }⟩

/-- Record-level version of `exists_finalPackage_of_rowBuilder`. -/
theorem exists_finalPackage_of_preTailBuilder
    {eps : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10)
    (B : PreTailBuilder) :
    Nonempty FinalPackage :=
  exists_finalPackage_of_rowBuilder heps heps10
    B.choice.MA0_nonnegative B.choice.NA0_nonnegative B.rows

/-- Paper-facing projection from one pre-tail analytic builder. -/
theorem paperMain_of_preTailBuilder
    {eps : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10)
    (B : PreTailBuilder) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, Set.range (Gamma (n + 1)) =
        Set.range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (Set.range (Gamma 0)) L :=
  paperMain_of_nonempty_finalPackage
    (exists_finalPackage_of_preTailBuilder heps heps10 B)

end ConfiguredActualHalfCappedRowProductionBuilder
