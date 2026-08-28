import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
import UnitTangentIterates.ConfiguredGaugeJetDistortion
import UnitTangentIterates.ConfiguredRecursiveSourceP0ChosenJetMajorants

/-!
# Jet bounds on the exact presented chosen output

`ChosenTerminal.Output` retains all fields of a rich terminal stage, but did
not bundle them as `GaugeRearFamilyRichTerminalStage.RichStageOutput`.  This
adapter is definitional and lets the established configured flow-jet theorem
act on the exact selected output.  Its result fills the non-erasing presented
near-identity sidecar.
-/

noncomputable section

open MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwarePresentedJetBounds

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily
  GaugeRearFamilyRichTerminalStage
  GaugeTerminalNearIdentityJets

private theorem frame_speed_jets_zero
    {a b : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A) :
    (∀ t x, E.frame.frame.v1 t x = 0) ∧
      ∀ t x, E.frame.frame.v2 t x = 0 := by
  have hv1 : ∀ t x, E.frame.frame.v1 t x = 0 := by
    intro t x
    have heq : E.frame.frame.v t = fun _ => (1 : ℝ) :=
      funext fun y => E.frame.v_eq_one t y
    have H := E.frame.frame.hv t x
    rw [heq] at H
    exact H.unique (hasDerivAt_const x 1)
  refine ⟨hv1, ?_⟩
  intro t x
  have heq : E.frame.frame.v1 t = fun _ => (0 : ℝ) :=
    funext fun y => hv1 t y
  have H := E.frame.frame.hv1 t x
  rw [heq] at H
  exact H.unique (hasDerivAt_const x 0)

/-- Rebundle the exact chosen output as the rich stage consumed by terminal
flow-jet estimates.  The final three scalar parameters are phantom in the raw
stage and may be supplied by the caller's row tube. -/
def PresentedOutputCore.richStage
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := p) (base := base) (bound := bound) E}
    (O : PresentedOutputCore E B) (c C dlt : ℝ) :
    RichStageOutput O.jets p b bound P0 kh khat
      (∫ t in (0 : ℝ)..Gamma.T, A.m t) c C dlt where
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

/-- The retained applied frame proves the actual terminal marking jets.  The
only scalar input is an upper bound on the same source-density integral; the
result is linear in the actual integral and is ready for comparison with a
configured row error. -/
theorem PresentedOutputCore.jetBounds_linear
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound Mcap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := p) (base := base) (bound := bound) E}
    (O : PresentedOutputCore E B) {c C dlt : ℝ}
    (hMcap : (∫ t in (0 : ℝ)..Gamma.T, A.m t) ≤ Mcap) :
    JetBounds O.jets
      (FiniteSmoothRearFamilyMarkingAwarePresentedJetBounds.PresentedOutputCore.richStage
        O c C dlt)
      (GaugeTerminalNearIdentityJets.jetLinearConst
        (rearPeriod A 0) (perim base) (rearKappa1 kh) (rearKappa2 kh) Mcap *
        (∫ t in (0 : ℝ)..Gamma.T, A.m t)) := by
  obtain ⟨hv1, hv2⟩ := frame_speed_jets_zero E
  have hxi1 : ∀ t x, |-E.frame.frame.xi1 t x| ≤ rearKappa1 kh * A.m t := by
    intro t x
    have H := E.frame.rate1_bound t x
    simpa [GaugeRate.gaugeRate1, E.frame.v_eq_one, hv1] using H
  have hxi2 : ∀ t x, |-E.frame.frame.xi2 t x| ≤ rearKappa2 kh * A.m t := by
    intro t x
    have H := E.frame.rate2_bound t x
    simpa [GaugeRate.gaugeRate2, E.frame.v_eq_one, hv1, hv2] using H
  obtain ⟨J, hJ⟩ := ConfiguredGaugeJetDistortion.stage_jetBounds O.jets
    (FiniteSmoothRearFamilyMarkingAwarePresentedJetBounds.PresentedOutputCore.richStage
      O c C dlt)
    (A.rear_period_pos 0) (perim_pos B.physical.cq_pos B.zero_floor_tube)
    Gamma.T_pos.le A.density_continuous A.density_nonnegative
    hxi1 hxi2
    (rearKappa1_nonneg A.kh_nonnegative A.kh_lt_one)
    (rearKappa2_nonneg A.kh_nonnegative A.kh_lt_one) hMcap
  exact ConfiguredGaugeJetDistortion.jetBounds_mono J hJ

/-- Jet bounds on the exact rebundled output are exactly the two inequalities
retained by a presented near-identity selection. -/
def PresentedNearIdentitySelection.ofJetBounds
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 eps : ℝ}
    {S : FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.CorrelatedColumn
      Q current e k P0 P1 khat G1 Cg C c dlt period diagonal kh Qmax K0 K1 K2}
    (R : PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S)
    {c' C' dlt' : ℝ}
    (J : JetBounds R.output.jets
      (FiniteSmoothRearFamilyMarkingAwarePresentedJetBounds.PresentedOutputCore.richStage
        R.output c' C' dlt') eps) :
    PresentedNearIdentitySelection (eps := eps) R where
  eps_nonnegative := J.eps_nonnegative
  dpsi := J.dpsi
  ddpsi := J.ddpsi

/-- Weaken the exact jet error already proved for `ChosenTerminal.Output` to
any configured common-tail ceiling. -/
def PresentedNearIdentitySelection.ofChosenJetBounds
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 eps : ℝ}
    {S : FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.CorrelatedColumn
      Q current e k P0 P1 khat G1 Cg C c dlt period diagonal kh Qmax K0 K1 K2}
    (R : PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S)
    {c' C' dlt' : ℝ}
    (J : JetBounds R.output.jets
      (PresentedOutputCore.richStage R.output c' C' dlt') eps) :
    PresentedNearIdentitySelection (eps := eps) R :=
  PresentedNearIdentitySelection.ofJetBounds R J

end FiniteSmoothRearFamilyMarkingAwarePresentedJetBounds
