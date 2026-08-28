import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPaperSmoothCapstone

/-!
# Stable paper-facing main theorem statement

The constructed curves are independently marked arclength representatives.
Accordingly, the honest forward unit-tangent iteration statement is equality
of successive geometric ranges, rather than equality of parametrized maps.
-/

noncomputable section

open Function Set

namespace PaperMainTheoremFinalStatement

/-- A smooth oval in the paper's sense.  The explicit `ℕ∞` annotation makes
`⊤` mean smooth of every finite order, rather than analytic. -/
def IsSmoothOval (gamma : ℝ → ℂ) : Prop :=
  MainTheoremConditional.IsOval gamma ∧ ContDiff ℝ (⊤ : ℕ∞) gamma

/-- An exact geometric forward orbit of the unit-tangent operation, with all
stages retained as smooth oval representatives. -/
structure SmoothForwardUnitTangentOrbit (gamma0 : ℝ → ℂ) where
  gamma : ℕ → ℝ → ℂ
  gamma_zero : gamma 0 = gamma0
  smooth_oval : ∀ n, IsSmoothOval (gamma n)
  range_step : ∀ n,
    range (gamma (n + 1)) =
      range (UnitTangent.unitTangentMap (gamma n))

/-- Stable final proposition matching the paper wording as closely as the
current formal APIs permit: there exists a noncircular smooth oval whose
entire forward unit-tangent range orbit consists of smooth ovals.

The displayed `L` is a positive simple arclength period.  Noncircularity is
therefore stated using the repository's perimeter-aware circle predicate,
which is exactly the closing conclusion proved by the construction. -/
def MainConclusion : Prop :=
  ∃ (gamma0 : ℝ → ℂ) (L : ℝ),
    0 < L ∧
    Periodic gamma0 L ∧
    InjOn gamma0 (Ico 0 L) ∧
    IsSmoothOval gamma0 ∧
    ¬ ClosingArgument.IsCircleOfPerimeter (range gamma0) L ∧
    Nonempty (SmoothForwardUnitTangentOrbit gamma0)

/-- Projection of the configured smooth physical capstone onto the stable
paper-facing main proposition.  The exact range-orbit evidence remains inside
`SmoothForwardUnitTangentOrbit.range_step`. -/
theorem of_smoothPhysicalBaseInput
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {GO : ConfiguredRecursiveEdgeRecostMultiplierClosing.GaugeOutput J}
    (R : ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput J GO)
    (I : ConfiguredRecursiveEdgeRecostMultiplierPaperSmoothCapstone.SmoothPhysicalBaseInput R) :
    MainConclusion := by
  obtain ⟨Gamma, L, hL, hperiod, hinj, hoval, hsmooth, horbit, hnoncircle⟩ :=
    ConfiguredRecursiveEdgeRecostMultiplierPaperSmoothCapstone.paperSmooth R I
  refine ⟨Gamma 0, L, hL, hperiod, hinj, ⟨hoval 0, hsmooth 0⟩,
    hnoncircle, ?_⟩
  exact ⟨{
    gamma := Gamma
    gamma_zero := rfl
    smooth_oval := fun n => ⟨hoval n, hsmooth n⟩
    range_step := horbit }⟩

end PaperMainTheoremFinalStatement
