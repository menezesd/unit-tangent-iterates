import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedTerminalGeometry
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalInputCore

/-! # Canonical theorem-produced transition-free presented row -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
  FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalInputCore
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily
  NormalPathC2IncrementVariableSpeed

variable {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
  {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
  {S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
    kh Qmax}

def currentAnalytic (H : GeometricCompositionInvariant S) (n : ℕ) :
    CompositionRecursiveAnalyticSuccessor
      (S.path n) (S.source n)
      (P0 (n + k)) (kh n) (khat n) (Qmax (n + k)) where
  source := S.source n
  slice := H.slice n
  sidecars := H.sidecars n
  spatial := H.spatial n
  terminalCurvature_nonnegative := H.terminalCurvature_nonnegative n
  terminalRange := H.terminalRange n
  composition_d1 := H.composition_d1 n
  composition_d2 := H.composition_d2 n

noncomputable def applied (H : GeometricCompositionInvariant S) (n : ℕ) :
    Applied (S.path n) (S.source n) :=
  Classical.choice (exists_applied (S.source n))

noncomputable def geometry (H : GeometricCompositionInvariant S) (n : ℕ) :
    PresentedTerminalGeometry (S.source n) (applied H n) :=
  { Classical.choice
      (FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedTerminalGeometry.CompositionRecursiveAnalyticSuccessor.exists_presentedTerminalGeometry
        (currentAnalytic H n) (applied H n) (Qmax (n + k))
        (S.source n).rear_period_le) with
    Lmax := Qmax (n + k)
    period_le := (S.source n).rear_period_le }

@[simp] theorem geometry_Lmax (H : GeometricCompositionInvariant S) (n : ℕ) :
    (geometry H n).Lmax = Qmax (n + k) := rfl

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

def inputs (H : GeometricCompositionInvariant S) (n : ℕ) :
    Inputs (bound := e n (k + 1))
      (currentAnalytic H n).toRecursiveAnalyticSuccessor
      (applied H n) (geometry H n) (S.initial n) := by
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
        (-(r * |(S.path n).T|)) / L
      Lambda := ell * Real.exp
        (r * |(S.path n).T|) / L
      lambda_pos := div_pos (mul_pos hell (Real.exp_pos _)) hL
      flow_lower := ?_
      flow_upper := ?_ }
  · intro u
    change RearOwnArclength.rearOwn (S.source n).F (S.source n).Theta
      (S.source n).delta (S.source n).sf 0 (E.Phi 0 u) = (S.initial n).1 u
    rw [E.initial]
    exact (S.initial_eq n u).symm
  · intro u
    apply (div_le_div_iff_of_pos_right hL).2
    have hb := (FlowDerivative.flowDeriv_bounds
      (K := Real.toNNReal r) (hx := fun t x ↦ -E.frame.frame.xi1 t x)
      (Phi := E.Phi) hell
      (fun t x ↦ by
        rw [Real.coe_toNNReal _ hr0]
        exact neg_xi1_le_rateLip E t x)
      (S.path n).T u).1
    simpa [ell, r, Real.coe_toNNReal _ hr0] using hb
  · intro u
    apply (div_le_div_iff_of_pos_right hL).2
    have hb := (FlowDerivative.flowDeriv_bounds
      (K := Real.toNNReal r) (hx := fun t x ↦ -E.frame.frame.xi1 t x)
      (Phi := E.Phi) hell
      (fun t x ↦ by
        rw [Real.coe_toNNReal _ hr0]
        exact neg_xi1_le_rateLip E t x)
      (S.path n).T u).2
    simpa [ell, r, Real.coe_toNNReal _ hr0] using hb

def terminalInput (H : GeometricCompositionInvariant S) (n : ℕ) :
    PresentedTerminalInputCore (p := S.initial n)
      (base := (geometry H n).presented) (bound := e n (k + 1))
      (applied H n) := (inputs H n).toPresentedTerminalInputCore

noncomputable def output (H : GeometricCompositionInvariant S) (n : ℕ) :
    PresentedOutputCore (applied H n) (terminalInput H n) :=
  Classical.choice (exists_presentedOutputCore (applied H n) (terminalInput H n))

theorem front_range (H : GeometricCompositionInvariant S) (n : ℕ) :
    range (ev (terminalInput H n).frontData) = range (S.pathEnd n).1 := by
  change range (ev (geometry H n).frontData) = _
  exact front_range_endpoint
    (X := (currentAnalytic H n).toRecursiveAnalyticSuccessor) (geometry H n)

theorem chosen_cost_le (H : GeometricCompositionInvariant S) (n : ℕ) :
    (output H n).chosen.Delta.cost ≤ e n (k + 1) := by
  rw [(output H n).chosen.cost_eq]
  exact (terminalInput H n).cost_le

theorem terminal_perim_ge_one
    (H : GeometricCompositionInvariant S) (n : ℕ) :
    1 ≤ perim (geometry H n).presented := by
  have hdelta : Continuous ((S.source n).delta
      (S.path n).T) :=
    Differentiable.continuous fun s ↦
      ((S.source n).steering
        (S.path n).T s).differentiableAt
  have hcos : ∀ s, Real.sqrt (1 - (kh n) ^ 2) ≤
      Real.cos ((S.source n).delta
        (S.path n).T s) := fun s ↦
    Shadowing.cos_ge_of_mem_strip
      ((S.source n).strip_nonnegative _ s) ((S.source n).strip_le _ s)
  have hrear : Real.sqrt (1 - (kh n) ^ 2) * (S.source n).P (S.path n).T ≤
      rearPeriod (S.source n) (S.path n).T := by
    exact ArclengthInverse.rearArclength_ge hdelta hcos
      ((S.source n).period_pos _).le
  rw [← (terminalInput H n).rearPeriod_terminal]
  exact (H.frontPeriodScaleOne n (S.path n).T).trans hrear

/-- Assemble the canonical row once the configured source supplies its three
ordinary flow ceilings and fixed terminal period scale. -/
noncomputable def row
    (H : GeometricCompositionInvariant S) (n : ℕ)
    (hP1 : GaugeFlowDerivCost.costP1 (rearPeriod (S.source n) 0) (khat n)
      (∫ t in (0 : ℝ)..(S.path n).T,
        (S.source n).m t) ≤ P1 n)
    (hG1 : GaugeFlowDerivCost.costG1 (rearPeriod (S.source n) 0) (khat n)
      (rearKappa2 (kh n))
      (∫ t in (0 : ℝ)..(S.path n).T,
        (S.source n).m t) ≤ G1 n)
    (hCg : khat n * GaugeFlowDerivCost.costG1
        (rearPeriod (S.source n) 0) (khat n) (rearKappa2 (kh n))
        (∫ t in (0 : ℝ)..(S.path n).T,
          (S.source n).m t) +
      rearKappa2 (kh n) * GaugeFlowDerivCost.costP1
        (rearPeriod (S.source n) 0) (khat n)
        (∫ t in (0 : ℝ)..(S.path n).T,
          (S.source n).m t) ^ 2 ≤ Cg n)
    : GeometricPresentedRowSelection (n := n) S where
  presented := (geometry H n).presented
  applied := applied H n
  terminalInput := terminalInput H n
  output := output H n
  front_range := front_range H n
  increment_geometry := by
    let O := output H n
    apply IsVariableSpeedNormalPath.mono O.chosen.Delta
      (by simpa only [O.stage_eq] using O.stage.increment_geometry)
      ((rearKappa1_nonneg (S.source n).kh_nonnegative
        (S.source n).kh_lt_one).trans (S.source n).rearKappa1_le)
      hP1 hG1 hCg
  terminal_perim_ge_one := terminal_perim_ge_one H n

end FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow
