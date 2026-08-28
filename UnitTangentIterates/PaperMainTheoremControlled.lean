import Mathlib
import UnitTangentIterates.UnconditionalAssemblyRemainder
import UnitTangentIterates.PaperControlledJunctionInputs

/-!
# Paper-facing main theorem from controlled junction data

`UnconditionalAssembly.ConfiguredModelSequence` is the existing output of the
hairpin/configuration part of the construction.  The remaining analytic and
geometric pullback work is represented once, without duplicated hypotheses,
by `PathMetric.PaperControlledJunctionInputs`.
-/

open Function Set MainTheoremConditional

/-- Paper-facing form of the main theorem.  After a configured model sequence
and its controlled-junction realization are supplied, there is a noncircular
initial oval with an infinite forward unit-tangent range orbit consisting
entirely of ovals.  Thus the conclusion directly expresses that every
nonnegative iterate in the statement of the TeX theorem remains strictly
convex and embedded (through `IsOval`). -/
theorem paper_main_theorem_of_configured_controlledJunctions
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (_model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps)
    {Q : ℕ → ℕ → MarkedSpace.Data} {R : ℕ → ℝ → ℂ} {M : ℝ → ℂ}
    (I : PathMetric.PaperControlledJunctionInputs Q R M) :
    ∃ (Γ : ℕ → ℝ → ℂ) (L : ℝ),
      IsOval (Γ 0) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Γ 0)) L ∧
      (∀ n, IsOval (Γ n)) ∧
      (∀ n,
        range (Γ (n + 1)) =
          range (UnitTangent.unitTangentMap (Γ n))) ∧
      0 < L ∧ Periodic (Γ 0) L := by
  obtain ⟨Γ, L, hoval, horbit, hL, hperiodic, hnoncircle⟩ :=
    I.exists_noncircular_rangeOrbit
  exact ⟨Γ, L, hoval 0, hnoncircle, hoval, horbit, hL, hperiodic⟩
