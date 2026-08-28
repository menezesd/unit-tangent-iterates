import UnitTangentIterates.ConfiguredRecursiveSourceP0FixedDistortion
import UnitTangentIterates.ConfiguredGaugeJetUniformShift
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenTerminal

/-!
# Chosen terminal jets and fixed recursive majorants

The marking-aware chosen terminal retains exactly the same normalized marking
and spatial flow jets as `GaugeRearFamilyRichTerminalStage.RichStageOutput`.
This adapter exposes its exact jet error, bounds it by the configured stable
row defect, and feeds the resulting half-error estimate into the fixed
recursive analytic ceilings.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
  RearOwnArclength RearFamilyFrame

namespace ConfiguredRecursiveSourceP0ChosenJetMajorants

open ConfiguredApproximateDefectPathRowwise
  ConfiguredGaugeJetDistortion
  ConfiguredRecursiveSourceP0FixedDistortion
  ConfiguredRowCeilingPolynomialEnvelopes
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeFlowMarkedTerminalJets
  GaugeMarkedDataOfRearFamily
  GaugeRearFamilyRichTerminalStage
  GaugeTerminalNearIdentityJets

/-- Forget only the endpoint estimate and ordinary physical-front witness from
a marking-aware chosen terminal.  Its path, marking, and terminal jets are
unchanged. -/
def _root_.FiniteSmoothRearFamilyMarkingAwareChosenTerminal.Output.toRichStageOutput
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := p) (base := base) (bound := bound) E}
    (O : Output E B) :
    RichStageOutput O.jets p b bound P0 kh khat
      (∫ t in (0 : ℝ)..Gamma.T, A.m t) 0 0 0 where
  stage := O.stage
  lambda := B.lambda
  Lambda := B.Lambda
  lambda_pos := B.lambda_pos
  marking := O.marking
  ddpsi := O.ddpsi
  psi_eq := O.psi_eq
  dpsi_eq := O.dpsi_eq
  ddpsi_eq := O.ddpsi_eq
  psi_deriv := O.psi_deriv
  dpsi_deriv := O.dpsi_deriv
  ddpsi_cont := O.ddpsi_cont
  psi_zero := O.psi_zero
  oriented_curvature := O.oriented_curvature

/-- Exact near-identity error attached to the actual selected terminal
marking. -/
def _root_.FiniteSmoothRearFamilyMarkingAwareChosenTerminal.Output.jetError
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := p) (base := base) (bound := bound) E}
    (O : Output E B) : ℝ :=
  GaugeTerminalNearIdentityJets.jetError (rearPeriod A 0) (perim base)
    (rearKappa1 kh * (∫ t in (0 : ℝ)..Gamma.T, A.m t))
    (rearKappa2 kh * (∫ t in (0 : ℝ)..Gamma.T, A.m t))

/-- The exact chosen marking jets are bounded by its retained flow error. -/
theorem _root_.FiniteSmoothRearFamilyMarkingAwareChosenTerminal.Output.jetBounds
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := p) (base := base) (bound := bound) E}
    (O : Output E B) :
    JetBounds O.jets O.toRichStageOutput O.jetError := by
  have hv1 : ∀ t x, E.frame.frame.v1 t x = 0 := by
    intro t x
    have heq : E.frame.frame.v t = fun _ ↦ (1 : ℝ) :=
      funext fun y ↦ E.frame.v_eq_one t y
    have H := E.frame.frame.hv t x
    rw [heq] at H
    exact H.unique (hasDerivAt_const x 1)
  have hv2 : ∀ t x, E.frame.frame.v2 t x = 0 := by
    intro t x
    have heq : E.frame.frame.v1 t = fun _ ↦ (0 : ℝ) :=
      funext fun y ↦ hv1 t y
    have H := E.frame.frame.hv1 t x
    rw [heq] at H
    exact H.unique (hasDerivAt_const x 0)
  have hC : ∀ t x, |E.frame.frame.xi1 t x| ≤ rearKappa1 kh * A.m t := by
    intro t x
    have H := E.frame.rate1_bound t x
    simpa [GaugeRate.gaugeRate1, E.frame.v_eq_one, hv1] using H
  have hC2 : ∀ t x, |E.frame.frame.xi2 t x| ≤ rearKappa2 kh * A.m t := by
    intro t x
    have H := E.frame.rate2_bound t x
    simpa [GaugeRate.gaugeRate2, E.frame.v_eq_one, hv1, hv2] using H
  let m1 : ℝ → ℝ := fun t ↦ rearKappa1 kh * A.m t
  let m2 : ℝ → ℝ := fun t ↦ rearKappa2 kh * A.m t
  have H := jetBounds_of_flow O.jets O.toRichStageOutput
    (A.rear_period_pos 0) (perim_pos B.physical.cq_pos B.zero_floor_tube)
    Gamma.T_pos.le (continuous_const.mul A.density_continuous)
    (continuous_const.mul A.density_continuous)
    (fun t x ↦ by simpa [m1] using hC t x)
    (fun t x ↦ by simpa [m2] using hC2 t x)
  simpa [Output.jetError, m1, m2,
    intervalIntegral.integral_const_mul] using H

/-- The selected terminal's exact jet error is controlled by the configured
stable row defect.  All geometric quantities in the coefficient belong to
this same selected output. -/
theorem _root_.FiniteSmoothRearFamilyMarkingAwareChosenTerminal.Output.jetError_le_configured_eps
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := p) (base := base) (bound := bound) E}
    (O : Output E B)
    (D : ConstructedConfiguredSequenceWeighted.Data) (n k : ℕ)
    {M Cjet : ℝ}
    (hcost : O.chosen.Delta.cost ≤ rowDefect D (n + k))
    (hcap : rowDefect D (n + k) ≤ M)
    (hCjet : jetLinearConst (rearPeriod A 0) (perim base)
      (rearKappa1 kh) (rearKappa2 kh) M ≤ Cjet) :
    O.jetError ≤ eps D Cjet n k := by
  have hx : 0 ≤ ∫ t in (0 : ℝ)..Gamma.T, A.m t := by
    rw [← O.chosen.cost_eq]
    exact O.chosen.Delta.cost_nonneg
  have hxM : (∫ t in (0 : ℝ)..Gamma.T, A.m t) ≤ M := by
    rw [← O.chosen.cost_eq]
    exact hcost.trans hcap
  have hk1 : 0 ≤ rearKappa1 kh :=
    rearKappa1_nonneg A.kh_nonnegative A.kh_lt_one
  have hk2 : 0 ≤ rearKappa2 kh :=
    rearKappa2_nonneg A.kh_nonnegative A.kh_lt_one
  have hlinear := GaugeTerminalNearIdentityJets.jetError_le_linear
    (A.rear_period_pos 0).le
    (perim_pos B.physical.cq_pos B.zero_floor_tube)
    hk1 hk2 hx hxM
  have hcoefficient : 0 ≤ jetLinearConst (rearPeriod A 0) (perim base)
      (rearKappa1 kh) (rearKappa2 kh) M := by
    apply le_max_of_le_left
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (A.rear_period_pos 0).le
          (rearKappa1_nonneg A.kh_nonnegative A.kh_lt_one))
        (add_nonneg (Real.exp_pos _).le zero_le_one))
      (perim_pos B.physical.cq_pos B.zero_floor_tube).le
  calc
    O.jetError ≤
        jetLinearConst (rearPeriod A 0) (perim base)
          (rearKappa1 kh) (rearKappa2 kh) M *
            (∫ t in (0 : ℝ)..Gamma.T, A.m t) := by
      simpa [Output.jetError] using hlinear
    _ = jetLinearConst (rearPeriod A 0) (perim base)
          (rearKappa1 kh) (rearKappa2 kh) M * O.chosen.Delta.cost := by
      rw [O.chosen.cost_eq]
    _ ≤ jetLinearConst (rearPeriod A 0) (perim base)
          (rearKappa1 kh) (rearKappa2 kh) M * rowDefect D (n + k) :=
      mul_le_mul_of_nonneg_left hcost hcoefficient
    _ ≤ Cjet * rowDefect D (n + k) :=
      mul_le_mul_of_nonneg_right hCjet
        ((ConfiguredStableRowDefectProvider.provider D).nonnegative n k)
    _ = eps D Cjet n k := rfl

/-- A configured common-tail half estimate proves the half bound for the
actual selected terminal, not merely for an independently chosen marking. -/
theorem _root_.FiniteSmoothRearFamilyMarkingAwareChosenTerminal.Output.jetError_le_half
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := p) (base := base) (bound := bound) E}
    (O : Output E B)
    (D : ConstructedConfiguredSequenceWeighted.Data) (n k : ℕ)
    {M Cjet : ℝ}
    (hcost : O.chosen.Delta.cost ≤ rowDefect D (n + k))
    (hcap : rowDefect D (n + k) ≤ M)
    (hCjet : jetLinearConst (rearPeriod A 0) (perim base)
      (rearKappa1 kh) (rearKappa2 kh) M ≤ Cjet)
    (hhalf : eps D Cjet n k ≤ 1 / 2) :
    O.jetError ≤ 1 / 2 :=
  (O.jetError_le_configured_eps D n k hcost hcap hCjet).trans hhalf

/-- Composite bridge from one actual chosen terminal and its configured
half-error estimate to all three fixed recursive analytic ceilings. -/
theorem _root_.FiniteSmoothRearFamilyMarkingAwareChosenTerminal.Output.nearIdentity_majorants
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := p) (base := base) (bound := bound) E}
    (O : Output E B)
    (D : ConstructedConfiguredSequenceWeighted.Data) (n k : ℕ)
    {M Cjet rawP1 rawG1 rawCg : ℝ}
    (hkhat : 0 ≤ khat)
    (hcost : O.chosen.Delta.cost ≤ rowDefect D (n + k))
    (hcap : rowDefect D (n + k) ≤ M)
    (hCjet : jetLinearConst (rearPeriod A 0) (perim base)
      (rearKappa1 kh) (rearKappa2 kh) M ≤ Cjet)
    (hhalf : eps D Cjet n k ≤ 1 / 2)
    (hP0 : 0 ≤ rawP1) (hG0 : 0 ≤ rawG1) (hCg0 : 0 ≤ rawCg)
    (hP : rawP1 ≤ rowP1 D n)
    (hG : rawG1 ≤ rowG1 D n)
    (hCg : rawCg ≤ rowCg D n) :
    rawP1 * (1 + O.jetError) ≤ wideP1 D choice.MA0 n ∧
      rawG1 * (1 + O.jetError) ^ 2 + rawP1 * O.jetError ≤
        wideG1 D choice.MA0 choice.NA0 n ∧
      rawCg * (1 + O.jetError) ^ 2 + khat * rawP1 * O.jetError ≤
        wideCgWithKhat D khat choice.MA0 choice.NA0 n := by
  exact ConfiguredRecursiveSourceP0FixedDistortion.nearIdentity_majorants
    D n hkhat O.jetBounds.eps_nonnegative
    (O.jetError_le_half D n k hcost hcap hCjet hhalf)
    hP0 hG0 hCg0 hP hG hCg

end ConfiguredRecursiveSourceP0ChosenJetMajorants
