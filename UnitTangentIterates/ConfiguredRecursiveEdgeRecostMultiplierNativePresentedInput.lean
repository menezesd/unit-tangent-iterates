import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNativeCore
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalGeometry
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalInputCore

/-!
# Native presented inputs for intrinsic multiplier successors

The scaled analytic source already proves the two composition inequalities.
After retaining its source-tied `RecursiveFacts`, its marked initial datum,
and the intended source-cost bound, all remaining terminal geometry, tube,
strictness, and flow fields are theorem-produced.  This module performs that
construction directly on the intrinsic successor stage, without transporting
a correlated-column stage through dependent profile equalities.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierNativePresentedInput

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostMultiplierNativeCore
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalInputCore
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily
  NormalPathC2IncrementVariableSpeed

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  {k : ℕ} {S : ℕ → Node} {L : Layer R k S}

/-- The three source-specific facts not carried by `InputData`.  In the
coherent intrinsic construction `displayed_eq` is definitional, since the
next displayed datum is chosen to be `selectedRearData 0`. -/
structure BoundaryFacts (I : InputData R L) (n : ℕ) (bound : ℝ) where
  recursiveFacts : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input.RecursiveFacts
    (I.analytic n)
  displayed_eq : I.nextDisplayed n = (I.analytic n).source.selectedRearData 0
  cost_le : (∫ t in (0 : ℝ)..(I.pre (n + 1)).path.T,
    (I.analytic n).source.m t) ≤ bound

namespace BoundaryFacts

variable {I : InputData R L} {n : ℕ} {bound : ℝ}

/-- The exact recursive successor attached to the already-selected scaled
source. -/
def recursive (B : BoundaryFacts I n bound) :=
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input.recursive
    (I.analytic n) B.recursiveFacts

/-- Choose terminal physical geometry from the scaled composition estimates
and the retained recursive sidecars. -/
noncomputable def geometry (B : BoundaryFacts I n bound) :
    PresentedTerminalGeometry (I.analytic n).source (I.step.nextApplied n) :=
  Classical.choice
    (FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalGeometry.RecursiveAnalyticSuccessor.exists_presentedTerminalGeometry_of_spatial
      B.recursive
      (I.step.nextApplied n)
      ((I.analytic n).composition_d1
        ((I.analytic n).source.rear_period_le 0))
      ((I.analytic n).composition_d2
        ((I.analytic n).source.rear_period_le 0))
      (I.step.targetQmax n)
      (I.analytic n).source.rear_period_le)

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

/-- The application-specific scalar and flow package.  Flow bounds use only
the canonical applied frame's Lipschitz estimate; they are not readiness
callbacks. -/
def inputs (B : BoundaryFacts I n bound) :
    Inputs (bound := bound) B.recursive (I.step.nextApplied n) B.geometry
      (I.nextDisplayed n) := by
  let E := I.step.nextApplied n
  let G := B.geometry
  let ell := rearPeriod (I.analytic n).source 0
  let per := perim G.presented
  let r := E.frame.frame.rateLip
  have hper : 0 < per := perim_pos G.physical.cq_pos G.zero_floor_tube
  have hell : 0 < ell := (I.analytic n).source.rear_period_pos 0
  have hr0 : 0 ≤ r := E.frame.frame.rateLip_nonneg
  refine
    { initial_alignment := ?_
      cost_le := B.cost_le
      lambda := ell * Real.exp (-(r * |(I.pre (n + 1)).path.T|)) / per
      Lambda := ell * Real.exp (r * |(I.pre (n + 1)).path.T|) / per
      lambda_pos := div_pos (mul_pos hell (Real.exp_pos _)) hper
      flow_lower := ?_
      flow_upper := ?_ }
  · intro u
    rw [B.displayed_eq]
    change RearOwnArclength.rearOwn (I.analytic n).source.F
      (I.analytic n).source.Theta (I.analytic n).source.delta
      (I.analytic n).source.sf 0 (E.Phi 0 u) = _
    rw [E.initial]
    rfl
  · intro u
    apply (div_le_div_iff_of_pos_right hper).2
    have hb := (FlowDerivative.flowDeriv_bounds
      (K := Real.toNNReal r) (hx := fun t x ↦ -E.frame.frame.xi1 t x)
      (Phi := E.Phi) hell
      (fun t x ↦ by
        rw [Real.coe_toNNReal _ hr0]
        exact neg_xi1_le_rateLip E t x)
      (I.pre (n + 1)).path.T u).1
    simpa [ell, r, Real.coe_toNNReal _ hr0] using hb
  · intro u
    apply (div_le_div_iff_of_pos_right hper).2
    have hb := (FlowDerivative.flowDeriv_bounds
      (K := Real.toNNReal r) (hx := fun t x ↦ -E.frame.frame.xi1 t x)
      (Phi := E.Phi) hell
      (fun t x ↦ by
        rw [Real.coe_toNNReal _ hr0]
        exact neg_xi1_le_rateLip E t x)
      (I.pre (n + 1)).path.T u).2
    simpa [ell, r, Real.coe_toNNReal _ hr0] using hb

/-- Exact native terminal input on the intrinsic successor stage. -/
def terminal (B : BoundaryFacts I n bound) :=
  B.inputs.toPresentedTerminalInputCore

/-- The callback-free native pre-carrier boundary consumed by
`NativeCore.PresentedInput.core`. -/
def presentedInput (B : BoundaryFacts I n bound) :
    PresentedInput (I.step.next n).stage where
  base := B.geometry.presented
  bound := bound
  terminal := B.terminal
  path_time_one := (I.pre (n + 1)).time_one

/-- The resulting native successor pre-carrier. -/
noncomputable def core (B : BoundaryFacts I n bound) :
    Core (I.step.next n).stage :=
  B.presentedInput.core

end BoundaryFacts

end ConfiguredRecursiveEdgeRecostMultiplierNativePresentedInput
