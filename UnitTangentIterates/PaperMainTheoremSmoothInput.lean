import UnitTangentIterates.PaperMainTheoremSmoothProjection

/-!
# Honest input boundary for the smooth paper projection
-/

noncomputable section

open Set MarkedSpace

namespace PaperMainTheoremSmoothInput

/-- The exact additional data which a configured physical branch must retain
to upgrade its existing paper output to the smooth theorem. -/
structure Input
    {Q : ℕ → Data} {P : ℕ → ℕ → Data}
    {e : ℕ → ℕ → ℝ} {P0 P1 khat G1 Cg C : ℕ → ℝ}
    {c dlt : ℝ}
    (O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt)
    (direction : ℂ) (modelWidth H : ℝ) where
  representatives : ∀ n,
    VariableMarkedTube.OrientedArclengthRepresentative (O.X n)
  paperOutput : PaperFacingVariableTerminalOutput.Output O direction modelWidth H
  gamma_eq : paperOutput.Gamma = fun n => ev (representatives n).q
  localShiftedStages : ∀ n, ∃ q : ℝ, Nonempty
    (PathMetric.PhysicalRearLimitStageComponents
      (representatives n).q
      (MarkedShift.shiftData q (representatives (n + 1)).q))

/-- The strongest smooth paper-facing conclusion available from the exact
retained local-stage input. -/
theorem paperSmooth
    {Q : ℕ → Data} {P : ℕ → ℕ → Data}
    {e : ℕ → ℕ → ℝ} {P0 P1 khat G1 Cg C : ℕ → ℝ}
    {c dlt : ℝ}
    {O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt}
    {direction : ℂ} {modelWidth H : ℝ}
    (I : Input O direction modelWidth H) :
    ∃ (Gamma : ℕ → ℝ → ℂ) (L : ℝ),
      0 < L ∧
      Function.Periodic (Gamma 0) L ∧
      InjOn (Gamma 0) (Ico 0 L) ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L :=
  PaperMainTheoremSmoothProjection.of_output_of_representatives
    I.representatives I.paperOutput I.gamma_eq I.localShiftedStages

end PaperMainTheoremSmoothInput

