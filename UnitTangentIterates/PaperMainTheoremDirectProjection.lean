import UnitTangentIterates.DiagonalEnrichedConstructionCoreDirectCapstone

/-!
# Final paper-statement projection

This forgets all marked-data and compactness witnesses from the paper-facing
output and exposes only the geometric curve sequence, its positive physical
period, ovality, the unit-tangent range orbit, and noncircularity.
-/

open Set

namespace PaperMainTheoremDirectProjection

theorem of_output
    {Q : ℕ → MarkedSpace.Data} {P : ℕ → ℕ → MarkedSpace.Data}
    {e : ℕ → ℕ → ℝ} {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt}
    {direction : ℂ} {modelWidth H : ℝ}
    (A : PaperFacingVariableTerminalOutput.Output O direction modelWidth H) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  exact ⟨A.Gamma,
    MarkedReparam.totalLength (fun u => (O.X 0).2.1 u),
    A.physical_length_pos, A.physical_periodic, A.oval, A.range_orbit,
    A.noncircle⟩

end PaperMainTheoremDirectProjection
