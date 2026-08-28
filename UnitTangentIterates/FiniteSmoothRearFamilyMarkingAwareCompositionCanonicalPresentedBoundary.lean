import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedSlicedInvariant
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedTerminalGeometry
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalInputCore
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedConfiguredTransition
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareAutomaticRowFacts

/-!
# Canonical presented boundary for a reachable composition row

This file fixes one theorem-produced application at each reachable row and
constructs its independently presented terminal input and chosen output.  In
particular, it does not quantify over all possible `Applied` witnesses.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareCompositionCanonicalPresentedBoundary

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareAutomaticRowFacts
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedSlicedInvariant
  FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareConfiguredTransition
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwarePresentedConfiguredTransition
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalInputCore
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily
  EnrichedPhysicalChosenRichFamily
  PhysicalArclengthJacobiTransition

variable {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {K0 K1 K2 : ℝ}
  {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
    period diagonal kh Qmax K0 K1 K2}

/-- Repackage the current invariant source as a composition-recursive
successor.  The predecessor source is a phantom index of this record. -/
def currentAnalytic
    (H : CompositionRecursiveSlicedCorrelatedColumn S) (n : ℕ) :
    CompositionRecursiveAnalyticSuccessor
      (S.column.step.richStage (n + 1)).stage.increment (S.source n)
      (P0 n) (kh n) (khat n) (Qmax n) where
  source := S.source n
  slice := H.slice n
  sidecars := H.sidecars n
  spatial := H.spatial n
  terminalCurvature_nonnegative := H.terminalCurvature_nonnegative n
  terminalRange := H.terminalRange n
  composition_d1 := H.composition_d1 n
  composition_d2 := H.composition_d2 n

/-- The single canonical long application used by the row. -/
noncomputable def applied
    (H : CompositionRecursiveSlicedCorrelatedColumn S) (n : ℕ) :
    Applied (S.column.step.richStage (n + 1)).stage.increment (S.source n) :=
  Classical.choice (exists_applied (S.source n))

/-- Automatic independently presented terminal geometry for the canonical
application. -/
noncomputable def geometry
    (H : CompositionRecursiveSlicedCorrelatedColumn S) (n : ℕ) :
    PresentedTerminalGeometry (S.source n) (applied H n) :=
  Classical.choice
    (FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedTerminalGeometry.CompositionRecursiveAnalyticSuccessor.exists_presentedTerminalGeometry
      (currentAnalytic H n) (applied H n) (Qmax n)
      (S.source n).rear_period_le)

private theorem frame_speed_one_zero
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A) : ∀ t x, E.frame.frame.v1 t x = 0 := by
  intro t x
  have heq : E.frame.frame.v t = fun _ ↦ (1 : ℝ) :=
    funext fun y ↦ E.frame.v_eq_one t y
  have hv := E.frame.frame.hv t x
  rw [heq] at hv
  exact hv.unique (hasDerivAt_const x 1)

private theorem neg_xi1_le_rateLip
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A) (t x : ℝ) :
    |-E.frame.frame.xi1 t x| ≤ E.frame.frame.rateLip := by
  have hr := E.frame.frame.hrate1 t x
  simpa [GaugeRate.gaugeRate1, E.frame.v_eq_one, frame_speed_one_zero E]
    using hr

/-- Application-specific flow and cost inputs, with the two-sided derivative
bounds obtained directly from the retained frame Lipschitz constant. -/
def inputs
    (H : CompositionRecursiveSlicedCorrelatedColumn S) (n : ℕ) :
    Inputs (bound := e n (k + 1)) (currentAnalytic H n).toRecursiveAnalyticSuccessor
      (applied H n) (geometry H n) (S.column.step.next n) := by
  let E := applied H n
  let G := geometry H n
  let ell := rearPeriod (S.source n) 0
  let L := perim G.presented
  let r := E.frame.frame.rateLip
  have hL : 0 < L := perim_pos G.physical.cq_pos G.zero_floor_tube
  have hell : 0 < ell := (S.source n).rear_period_pos 0
  have hr0 : 0 ≤ r := E.frame.frame.rateLip_nonneg
  refine
    { initial_alignment := ?_
      cost_le := H.source_cost_le n
      lambda := ell * Real.exp
        (-(r * |(S.column.step.richStage (n + 1)).stage.increment.T|)) / L
      Lambda := ell * Real.exp
        (r * |(S.column.step.richStage (n + 1)).stage.increment.T|) / L
      lambda_pos := div_pos (mul_pos hell (Real.exp_pos _)) hL
      flow_lower := ?_
      flow_upper := ?_ }
  · intro u
    change RearOwnArclength.rearOwn (S.source n).F (S.source n).Theta
      (S.source n).delta (S.source n).sf 0 (E.Phi 0 u) = _
    rw [E.initial]
    exact H.initialAlignment n u
  · intro u
    apply (div_le_div_iff_of_pos_right hL).2
    have hb := (FlowDerivative.flowDeriv_bounds
      (K := Real.toNNReal r)
      (hx := fun t x ↦ -E.frame.frame.xi1 t x)
      (Phi := E.Phi) hell
      (fun t x ↦ by
        rw [Real.coe_toNNReal _ hr0]
        exact neg_xi1_le_rateLip E t x)
      (S.column.step.richStage (n + 1)).stage.increment.T u).1
    simpa [ell, r, Real.coe_toNNReal _ hr0] using hb
  · intro u
    apply (div_le_div_iff_of_pos_right hL).2
    have hb := (FlowDerivative.flowDeriv_bounds
      (K := Real.toNNReal r)
      (hx := fun t x ↦ -E.frame.frame.xi1 t x)
      (Phi := E.Phi) hell
      (fun t x ↦ by
        rw [Real.coe_toNNReal _ hr0]
        exact neg_xi1_le_rateLip E t x)
      (S.column.step.richStage (n + 1)).stage.increment.T u).2
    simpa [ell, r, Real.coe_toNNReal _ hr0] using hb

/-- Sound presented terminal input for the canonical application. -/
def terminalInput
    (H : CompositionRecursiveSlicedCorrelatedColumn S) (n : ℕ) :
    PresentedTerminalInputCore (p := S.column.step.next n)
      (base := (geometry H n).presented) (bound := e n (k + 1))
      (applied H n) :=
  (inputs H n).toPresentedTerminalInputCore

/-- The canonical chosen presented output. -/
noncomputable def output
    (H : CompositionRecursiveSlicedCorrelatedColumn S) (n : ℕ) :
    PresentedOutputCore (applied H n) (terminalInput H n) :=
  Classical.choice (exists_presentedOutputCore (applied H n) (terminalInput H n))

theorem front_range
    (H : CompositionRecursiveSlicedCorrelatedColumn S) (n : ℕ) :
    range (ev (terminalInput H n).frontData) =
      range (S.column.step.next (n + 1)).1 :=
  by
    change range (ev (geometry H n).frontData) = _
    exact front_range_endpoint
      (X := (currentAnalytic H n).toRecursiveAnalyticSuccessor) (geometry H n)

theorem chosen_cost_le
    (H : CompositionRecursiveSlicedCorrelatedColumn S) (n : ℕ) :
    (output H n).chosen.Delta.cost ≤ e n (k + 1) := by
  rw [(output H n).chosen.cost_eq]
  exact (terminalInput H n).cost_le

def functionalFacts
    (H : CompositionRecursiveSlicedCorrelatedColumn S) (n : ℕ)
    (front : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable
      (S.column.step.richStage (n + 1)).stage.increment.eta) :
    PresentedFunctionalFacts (output H n) :=
  PresentedFunctionalFacts.ofExactSource (output H n) front

/-- Presented version of the automatic terminal-perimeter estimate. -/
theorem terminal_perim_ge_one
    (H : CompositionRecursiveSlicedCorrelatedColumn S) (n : ℕ)
    (hscale : 1 ≤ Real.sqrt (1 - (kh n) ^ 2) * (P0 n)) :
    1 ≤ perim (geometry H n).presented := by
  have hfloor := (H.slice n).period_lower
  have hdelta : Continuous ((S.source n).delta
      (S.column.step.richStage (n + 1)).stage.increment.T) :=
    Differentiable.continuous fun s ↦
      ((S.source n).steering
        (S.column.step.richStage (n + 1)).stage.increment.T s).differentiableAt
  have hcos : ∀ s, Real.sqrt (1 - (kh n) ^ 2) ≤
      Real.cos ((S.source n).delta
        (S.column.step.richStage (n + 1)).stage.increment.T s) := fun s ↦
    Shadowing.cos_ge_of_mem_strip
      ((S.source n).strip_nonnegative _ s) ((S.source n).strip_le _ s)
  have hrear : Real.sqrt (1 - (kh n) ^ 2) * (P0 n) ≤
      rearPeriod (S.source n)
        (S.column.step.richStage (n + 1)).stage.increment.T := by
    apply (mul_le_mul_of_nonneg_left
      (hfloor (S.column.step.richStage (n + 1)).stage.increment.T)
      (Real.sqrt_nonneg _)).trans
    exact ArclengthInverse.rearArclength_ge hdelta hcos
      ((S.source n).period_pos _).le
  rw [← (terminalInput H n).rearPeriod_terminal]
  exact hscale.trans hrear

def components_nonnegative
    (H : CompositionRecursiveSlicedCorrelatedColumn S) (n : ℕ)
    (hperiod : 1 ≤ period n (k + 1)) :
    (PhysicalArclengthJacobiTransition.components (period n (k + 1))
      (output H n).chosen.Delta.eta).Nonnegative :=
  components_nonnegative_of_period_ge_one hperiod _

/-- Cost-based component bound for the actual presented chosen path. -/
def components_bound
    (H : CompositionRecursiveSlicedCorrelatedColumn S) (n : ℕ)
    (front : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable
      (S.column.step.richStage (n + 1)).stage.increment.eta)
    (hGammaT : (S.column.step.richStage (n + 1)).stage.increment.T = 1)
    (hperiod : 1 ≤ period n (k + 1))
    (hcost : period n (k + 1) * (output H n).chosen.Delta.cost ≤
      diagonal (n + (k + 1))) :
    ComponentBound
      (PhysicalArclengthJacobiTransition.components (period n (k + 1))
        (output H n).chosen.Delta.eta)
      (diagonal (n + (k + 1))) := by
  apply componentBound_mono
    (ComponentBound.of_cost (output H n).chosen.Delta
      ((output H n).chosen.time_eq.trans hGammaT)
      (functionalFacts H n front).rear hperiod le_rfl)
  exact hcost

end FiniteSmoothRearFamilyMarkingAwareCompositionCanonicalPresentedBoundary
