import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareConfiguredTransition
import UnitTangentIterates.PeriodicSupNormFunctionalIntegrable
import UnitTangentIterates.EnrichedPhysicalChosenTransitionAdapter
import UnitTangentIterates.ArclengthInverse

/-!
# Automatic analytic and scalar facts for marking-aware recursive rows

This module isolates the row fields that follow from the retained source and
chosen terminal output.  It also makes explicit the two pieces not stored by
those records: joint time continuity for functional integrability, and the
scalar comparison between path cost and the recursive diagonal ceiling.
-/

noncomputable section

open Set Function MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareAutomaticRowFacts

open ControlledJunctionPathFunctionalBounds
  EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareConfiguredTransition
  FiniteSmoothRearFamilyMarkingAwareSource
  PhysicalArclengthJacobiTransition

/-- Joint continuity of the source and chosen normal rates and their first two
spatial derivatives supplies the formerly separate functional-integrability
row field. -/
def functionalFacts_of_jointC2
    {p q a base : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := a) (base := base) (bound := bound) E}
    (O : Output E B)
    (frontC2 : C2NormalPathData Gamma)
    (front0 : Continuous (Function.uncurry Gamma.eta))
    (front1 : Continuous (Function.uncurry frontC2.eta1))
    (front2 : Continuous (Function.uncurry frontC2.eta2))
    (rear0 : Continuous (Function.uncurry O.chosen.Delta.eta))
    (rear1 : Continuous (Function.uncurry O.chosen.c2.eta1))
    (rear2 : Continuous (Function.uncurry O.chosen.c2.eta2)) :
    FunctionalFacts O where
  front :=
    PeriodicSupNormFunctionalIntegrable.functionalIntegrable_of_jointC2
      frontC2 front0 front1 front2
  rear :=
    PeriodicSupNormFunctionalIntegrable.functionalIntegrable_of_jointC2
      O.chosen.c2 rear0 rear1 rear2

/-- If source functional integrability is already retained by the configured
path, only joint continuity of the chosen path's `C²` data remains. -/
def functionalFacts_of_front_and_rear_jointC2
    {p q a base : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := a) (base := base) (bound := bound) E}
    (O : Output E B) (front : FunctionalIntegrable Gamma.eta)
    (rear0 : Continuous (Function.uncurry O.chosen.Delta.eta))
    (rear1 : Continuous (Function.uncurry O.chosen.c2.eta1))
    (rear2 : Continuous (Function.uncurry O.chosen.c2.eta2)) :
    FunctionalFacts O where
  front := front
  rear :=
    PeriodicSupNormFunctionalIntegrable.functionalIntegrable_of_jointC2
      O.chosen.c2 rear0 rear1 rear2

/-- The strip estimate turns a lower bound on `sqrt(1-kh²) * P(T)` into the
required terminal physical perimeter bound. -/
theorem terminal_perim_ge_one_of_front_period
    {p q a base : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (B : TerminalInput (p := a) (base := base) (bound := bound) E)
    (hperiod : 1 ≤ Real.sqrt (1 - kh ^ 2) * A.P Gamma.T) :
    1 ≤ perim base := by
  have hdelta : Continuous (A.delta Gamma.T) :=
    Differentiable.continuous fun s =>
      (A.steering Gamma.T s).differentiableAt
  have hcos : ∀ s, Real.sqrt (1 - kh ^ 2) ≤
      Real.cos (A.delta Gamma.T s) := fun s =>
    Shadowing.cos_ge_of_mem_strip
      (A.strip_nonnegative Gamma.T s) (A.strip_le Gamma.T s)
  have hrear : Real.sqrt (1 - kh ^ 2) * A.P Gamma.T ≤
      rearPeriod A Gamma.T := by
    exact ArclengthInverse.rearArclength_ge hdelta hcos
      (A.period_pos Gamma.T).le
  rw [← B.rearPeriod_terminal]
  exact hperiod.trans hrear

/-- A reusable period-floor version of `terminal_perim_ge_one_of_front_period`.
This is the form consumed by configured slice or model-period certificates. -/
theorem terminal_perim_ge_one_of_period_floor
    {p q a base : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax bound periodFloor : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (B : TerminalInput (p := a) (base := base) (bound := bound) E)
    (hfloor : periodFloor ≤ A.P Gamma.T)
    (hscale : 1 ≤ Real.sqrt (1 - kh ^ 2) * periodFloor) :
    1 ≤ perim base := by
  apply terminal_perim_ge_one_of_front_period B
  exact hscale.trans (mul_le_mul_of_nonneg_left hfloor (Real.sqrt_nonneg _))

/-- Physical Jacobi components are automatically nonnegative once the
physical period is at least one. -/
def components_nonnegative_of_period_ge_one
    {P : ℝ} (hP : 1 ≤ P) (eta : ℝ → ℝ → ℝ) :
    (components P eta).Nonnegative :=
  components_nonnegative (zero_lt_one.trans_le hP) eta

/-- Widen a common component ceiling. -/
def componentBound_mono
    {x : AnchoredJacobiStableTransition.Components} {d D : ℝ}
    (H : ComponentBound x d) (h : d ≤ D) : ComponentBound x D where
  w := H.w.trans h
  s0 := H.s0.trans h
  s1 := H.s1.trans h
  s2 := H.s2.trans h

/-- The chosen output already stores the relevant path cost.  Thus its four
physical components satisfy the recursive diagonal bound as soon as the row
period is at least one, the source path has unit time, functional integrability
is available, and `P * bound` is below the selected diagonal ceiling. -/
def components_bound_of_output
    {p q a base : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := a) (base := base) (bound := bound) E}
    (O : Output E B) (F : FunctionalFacts O)
    {P diagonal : ℝ} (hGammaT : Gamma.T = 1) (hP : 1 ≤ P)
    (hdiagonal : P * bound ≤ diagonal) :
    ComponentBound (components P O.chosen.Delta.eta) diagonal := by
  have hDeltaT : O.chosen.Delta.T = 1 := O.chosen.time_eq.trans hGammaT
  have hcost : O.chosen.Delta.cost ≤ bound := by
    rw [← O.stage_eq]
    exact O.stage.increment_cost
  exact componentBound_mono
    (ComponentBound.of_cost O.chosen.Delta hDeltaT F.rear hP hcost)
    hdiagonal

end FiniteSmoothRearFamilyMarkingAwareAutomaticRowFacts
