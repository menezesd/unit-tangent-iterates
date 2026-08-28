import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareAppliedSource
import UnitTangentIterates.FiniteSmoothRearFamilyPhysicalFront
import UnitTangentIterates.GaugeRearFamilyRichTerminalStage
import UnitTangentIterates.EnrichedPhysicalGaugeStage

/-!
# A sound chosen terminal for a marking-aware rear-family source

This package retains one actual long-theorem path and its actual terminal
gauge jets.  Its ordinary physical front is explicit and may have a different
marking from the endpoint of the input path.  No affine density identity and
no identification of these two markings is asserted.
-/

noncomputable section

open Set Function MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
  RearOwnArclength RearFamilyFrame NormalPathC2IncrementVariableSpeed

namespace FiniteSmoothRearFamilyMarkingAwareChosenTerminal

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyPhysicalFront
  GaugeFlowMarkedTerminalJets
  GaugeMarkedDataOfRearFamily
  GaugeRearFamilyRichTerminalStage
  GaugeRearFamilyTriangularStageAdapter
  GaugeRearFamilyVariableTerminal

/-- Sound terminal boundary shared by genuinely presented outputs.  The
ordinary physical front is retained explicitly and is not identified with the
selected rear presentation `base`. -/
structure PresentedTerminalInputCore
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A) where
  initial : ∀ u,
    rearOwn A.F A.Theta A.delta A.sf 0 (E.Phi 0 u) = p.1 u
  physical : ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts base
  zero_floor_tube : IsTubeMember physical.cq 0 physical.dlt base
  dlt_pos : 0 < physical.dlt
  terminal_carrier : ∀ x,
    base.1 (x / perim base) =
      rearOwn A.F A.Theta A.delta A.sf Gamma.T x
  canonical_range : range (⇑b.1) =
    range (UnitTangent.unitTangentMap (ev base))
  strict : UnconditionalAssembly.LimitStrictnessDataH base
  normal_sup : ∀ t, ∀ j ≤ 2, supNorm
    (iteratedDeriv j (fun u => rearNormal A t (E.Phi t u))) ≤ A.m t
  cost_le : (∫ t in (0 : ℝ)..Gamma.T, A.m t) ≤ bound
  lambda : ℝ
  Lambda : ℝ
  lambda_pos : 0 < lambda
  flow_lower : ∀ u, lambda ≤
    FlowDerivative.flowDeriv (fun t x => -E.frame.frame.xi1 t x)
      E.Phi (rearPeriod A 0) Gamma.T u / perim base
  flow_upper : ∀ u,
    FlowDerivative.flowDeriv (fun t x => -E.frame.frame.xi1 t x)
      E.Phi (rearPeriod A 0) Gamma.T u / perim base ≤ Lambda
  Lmax : ℝ
  rearPeriod_le : ∀ t, rearPeriod A t ≤ Lmax
  rearPeriod_terminal : rearPeriod A Gamma.T = perim base
  frontData : Data
  frontKinematics : PhysicalRearLimitKinematics kh base frontData
  physicalFront : Certificate kh base frontData

/-- Endpoint facts not produced by the intrinsic long theorem.  The physical
front is deliberately separated from the marked input endpoint `b`. -/
structure TerminalInput
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A) where
  initial : ∀ u,
    rearOwn A.F A.Theta A.delta A.sf 0 (E.Phi 0 u) = p.1 u
  physical : ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts base
  zero_floor_tube : IsTubeMember physical.cq 0 physical.dlt base
  dlt_pos : 0 < physical.dlt
  terminal_carrier : ∀ x,
    base.1 (x / perim base) =
      rearOwn A.F A.Theta A.delta A.sf Gamma.T x
  canonical_range : range (⇑b.1) =
    range (UnitTangent.unitTangentMap (ev base))
  strict : UnconditionalAssembly.LimitStrictnessDataH base
  normal_sup : ∀ t, ∀ j ≤ 2, supNorm
    (iteratedDeriv j (fun u => rearNormal A t (E.Phi t u))) ≤ A.m t
  cost_le : (∫ t in (0 : ℝ)..Gamma.T, A.m t) ≤ bound
  lambda : ℝ
  Lambda : ℝ
  lambda_pos : 0 < lambda
  flow_lower : ∀ u, lambda ≤
    FlowDerivative.flowDeriv (fun t x => -E.frame.frame.xi1 t x)
      E.Phi (rearPeriod A 0) Gamma.T u / perim base
  flow_upper : ∀ u,
    FlowDerivative.flowDeriv (fun t x => -E.frame.frame.xi1 t x)
      E.Phi (rearPeriod A 0) Gamma.T u / perim base ≤ Lambda
  Lmax : ℝ
  rearPeriod_le : ∀ t, rearPeriod A t ≤ Lmax
  rearPeriod_terminal : rearPeriod A Gamma.T = perim base
  physicalFront : Certificate kh base b
  physicalFront_eq : physicalFront.physicalFront = base

def TerminalInput.toPresentedCore
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (B : TerminalInput (p := p) (base := base) (bound := bound) E) :
    PresentedTerminalInputCore (p := p) (base := base) (bound := bound) E where
  initial := B.initial
  physical := B.physical
  zero_floor_tube := B.zero_floor_tube
  dlt_pos := B.dlt_pos
  terminal_carrier := B.terminal_carrier
  canonical_range := B.canonical_range
  strict := B.strict
  normal_sup := B.normal_sup
  cost_le := B.cost_le
  lambda := B.lambda
  Lambda := B.Lambda
  lambda_pos := B.lambda_pos
  flow_lower := B.flow_lower
  flow_upper := B.flow_upper
  Lmax := B.Lmax
  rearPeriod_le := B.rearPeriod_le
  rearPeriod_terminal := B.rearPeriod_terminal
  frontData := base
  frontKinematics := by
    have FK := B.physicalFront.kinematics
    rw [B.physicalFront_eq] at FK
    exact FK
  physicalFront := Certificate.ofSame (by
    have FK := B.physicalFront.kinematics
    rw [B.physicalFront_eq] at FK
    exact FK)

/-- The retained unit-speed frame has zero first and second speed jets. -/
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

/-- Terminal spatial jets for the same marking-aware gauge flow. -/
theorem Applied.exists_terminalJets
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A)
    (B : PresentedTerminalInputCore (p := p) (base := base)
      (bound := bound) E) :
    Nonempty (TerminalJets E.frame.frame.xi E.frame.frame.xi1
      E.frame.frame.xi2 E.Phi (rearPeriod A 0) (perim base) Gamma.T base) := by
  have hxiC : Continuous (uncurry E.frame.frame.xi) :=
    E.frame.frame.hxic
  obtain ⟨hv1, hv2⟩ := frame_speed_jets_zero E
  have hC : ∀ t x, |E.frame.frame.xi1 t x| ≤ rearKappa1 kh * A.m t := by
    intro t x
    have H := E.frame.rate1_bound t x
    simpa [GaugeRate.gaugeRate1, E.frame.v_eq_one, hv1] using H
  have hC2 : ∀ t x, |E.frame.frame.xi2 t x| ≤ rearKappa2 kh * A.m t := by
    intro t x
    have H := E.frame.rate2_bound t x
    simpa [GaugeRate.gaugeRate2, E.frame.v_eq_one, hv1, hv2] using H
  have hflow : ∀ u t, HasDerivAt (fun r => E.Phi r u)
      (-E.frame.frame.xi t (E.Phi t u)) t := by
    intro u t
    simpa [GaugeRate.gaugeRate, E.frame.v_eq_one] using E.frame.flow u t
  have hL : 0 < perim base :=
    perim_pos B.physical.cq_pos B.zero_floor_tube
  exact GaugeFlowMarkedTerminalJets.exists_terminalJets Gamma.T_pos
    (A.rear_period_pos 0) hL hxiC
    E.frame.frame.hxi E.frame.frame.hxi1c E.frame.frame.hxi1
    E.frame.frame.hxi2c hC hC2
    (rearKappa1_nonneg A.kh_nonnegative A.kh_lt_one)
    (rearKappa2_nonneg A.kh_nonnegative A.kh_lt_one)
    A.density_continuous A.density_nonnegative A.density_support
    E.initial hflow B.zero_floor_tube.hasDerivAt_curve
    B.zero_floor_tube.hasDerivAt_vel

/-- A selected terminal row over the sound presented boundary. -/
structure PresentedOutputCore
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A)
    (B : PresentedTerminalInputCore (p := p) (base := base)
      (bound := bound) E) where
  jets : TerminalJets E.frame.frame.xi E.frame.frame.xi1
    E.frame.frame.xi2 E.Phi (rearPeriod A 0) (perim base) Gamma.T base
  chosen : ChosenPath Gamma A E.Phi p jets.rear
  stage : GaugeRearFamilyVariableTerminal.RawStageOutput p b jets.rear bound
    P0 (GaugeFlowDerivCost.costP1 (rearPeriod A 0) khat
      (∫ t in (0 : ℝ)..Gamma.T, A.m t)) khat
    (GaugeFlowDerivCost.costG1 (rearPeriod A 0) khat (rearKappa2 kh)
      (∫ t in (0 : ℝ)..Gamma.T, A.m t))
    (khat * GaugeFlowDerivCost.costG1 (rearPeriod A 0) khat (rearKappa2 kh)
        (∫ t in (0 : ℝ)..Gamma.T, A.m t) +
      rearKappa2 kh * GaugeFlowDerivCost.costP1 (rearPeriod A 0) khat
        (∫ t in (0 : ℝ)..Gamma.T, A.m t) ^ 2)
  stage_eq : stage.increment = chosen.Delta
  c2 : C2NormalPathData stage.increment
  marking : OrientedReparametrization base jets.rear B.lambda B.Lambda
  ddpsi : ℝ → ℝ
  psi_eq : ∀ u, marking.psi u = E.Phi Gamma.T u / perim base
  dpsi_eq : ∀ u, marking.dpsi u = jets.flow1 u / perim base
  ddpsi_eq : ∀ u, ddpsi u = jets.flow2 u / perim base
  psi_deriv : ∀ u, HasDerivAt marking.psi (marking.dpsi u) u
  dpsi_deriv : ∀ u, HasDerivAt marking.dpsi (ddpsi u) u
  ddpsi_cont : Continuous ddpsi
  psi_zero : marking.psi 0 = 0
  oriented_curvature : ∀ u, 0 ≤
    ((starRingEnd ℂ) (jets.rear.2.1 u) * jets.rear.2.2 u).im
  endpoint_dist : dist jets.rear base ≤
    MarkingDeviationC2.markingC2Bound
      (2 * B.Lmax * rearKappa1 kh * chosen.Delta.cost)
      (MarkingFlowDefectC2.flowDefectC1Int (rearPeriod A 0)
        (rearKappa1 kh * chosen.Delta.cost))
      (MarkingFlowDefectC2.flowDefectC2Int (rearPeriod A 0)
        (rearKappa1 kh * chosen.Delta.cost)
        (rearKappa2 kh * chosen.Delta.cost))
      B.physical.L B.physical.kb B.physical.kL
  frontKinematics : PhysicalRearLimitKinematics kh base B.frontData
  physicalFront : Certificate kh base B.frontData

/-- One sound, non-erased terminal row. -/
structure Output
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A)
    (B : TerminalInput (p := p) (base := base) (bound := bound) E) where
  jets : TerminalJets E.frame.frame.xi E.frame.frame.xi1
    E.frame.frame.xi2 E.Phi (rearPeriod A 0) (perim base) Gamma.T base
  chosen : ChosenPath Gamma A E.Phi p jets.rear
  stage : GaugeRearFamilyVariableTerminal.RawStageOutput p b jets.rear bound
    P0 (GaugeFlowDerivCost.costP1 (rearPeriod A 0) khat
      (∫ t in (0 : ℝ)..Gamma.T, A.m t)) khat
    (GaugeFlowDerivCost.costG1 (rearPeriod A 0) khat (rearKappa2 kh)
      (∫ t in (0 : ℝ)..Gamma.T, A.m t))
    (khat * GaugeFlowDerivCost.costG1 (rearPeriod A 0) khat (rearKappa2 kh)
        (∫ t in (0 : ℝ)..Gamma.T, A.m t) +
      rearKappa2 kh * GaugeFlowDerivCost.costP1 (rearPeriod A 0) khat
        (∫ t in (0 : ℝ)..Gamma.T, A.m t) ^ 2)
  stage_eq : stage.increment = chosen.Delta
  c2 : C2NormalPathData stage.increment
  marking : OrientedReparametrization base jets.rear B.lambda B.Lambda
  ddpsi : ℝ → ℝ
  psi_eq : ∀ u, marking.psi u = E.Phi Gamma.T u / perim base
  dpsi_eq : ∀ u, marking.dpsi u = jets.flow1 u / perim base
  ddpsi_eq : ∀ u, ddpsi u = jets.flow2 u / perim base
  psi_deriv : ∀ u, HasDerivAt marking.psi (marking.dpsi u) u
  dpsi_deriv : ∀ u, HasDerivAt marking.dpsi (ddpsi u) u
  ddpsi_cont : Continuous ddpsi
  psi_zero : marking.psi 0 = 0
  oriented_curvature : ∀ u, 0 ≤
    ((starRingEnd ℂ) (jets.rear.2.1 u) * jets.rear.2.2 u).im
  endpoint_dist : dist jets.rear base ≤
    MarkingDeviationC2.markingC2Bound
      (2 * B.Lmax * rearKappa1 kh * chosen.Delta.cost)
      (MarkingFlowDefectC2.flowDefectC1Int (rearPeriod A 0)
        (rearKappa1 kh * chosen.Delta.cost))
      (MarkingFlowDefectC2.flowDefectC2Int (rearPeriod A 0)
        (rearKappa1 kh * chosen.Delta.cost)
        (rearKappa2 kh * chosen.Delta.cost))
      B.physical.L B.physical.kb B.physical.kL
  physicalFront : Certificate kh base b
  physicalFront_eq : physicalFront.physicalFront = base

/-- An optional component certificate is attached only after the sound
terminal row exists.  This avoids treating an affine separated estimate as a
consequence of the intrinsic long theorem. -/
structure WithTransition
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := p) (base := base) (bound := bound) E}
    (O : Output E B) (PF PR a0 MA NA K0 K1 K2 : ℝ) : Prop where
  transition : AnchoredJacobiStableTransition.Transition
    (PhysicalArclengthJacobiTransition.components PF Gamma.eta)
    (PhysicalArclengthJacobiTransition.components PR O.chosen.Delta.eta)
    a0 MA NA K0 K1 K2

set_option maxHeartbeats 2000000

/-- Construct the exact chosen terminal row from the intrinsic long output.
No separated-density or affine-marking premise occurs. -/
theorem exists_presentedOutputCore
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A)
    (B : PresentedTerminalInputCore (p := p) (base := base)
      (bound := bound) E) :
    Nonempty (PresentedOutputCore E B) := by
  obtain ⟨J⟩ :=
    FiniteSmoothRearFamilyMarkingAwareChosenTerminal.Applied.exists_terminalJets E B
  have hterminal : ∀ u, J.rear.1 u =
      rearOwn A.F A.Theta A.delta A.sf Gamma.T (E.Phi Gamma.T u) := by
    intro u
    exact (J.position u).trans (B.terminal_carrier (E.Phi Gamma.T u))
  obtain ⟨W⟩ := E.chosen p J.rear B.initial
    (fun u => (hterminal u).symm) B.normal_sup
  have hL : 0 < perim base :=
    perim_pos B.physical.cq_pos B.zero_floor_tube
  have hlower : ∀ u, B.lambda ≤ J.flow1 u / perim base := by
    intro u
    rw [J.flow1_eq]
    exact B.flow_lower u
  have hupper : ∀ u, J.flow1 u / perim base ≤ B.Lambda := by
    intro u
    rw [J.flow1_eq]
    exact B.flow_upper u
  have hshiftTerminal : ∀ u, E.Phi Gamma.T (u + 1) =
      E.Phi Gamma.T u + perim base := by
    intro u
    rw [W.shift Gamma.T u, B.rearPeriod_terminal]
  let psi : ℝ → ℝ := fun u => E.Phi Gamma.T u / perim base
  let dpsi : ℝ → ℝ := fun u => J.flow1 u / perim base
  let ddpsi : ℝ → ℝ := fun u => J.flow2 u / perim base
  have hpsi : ∀ u, HasDerivAt psi (dpsi u) u :=
    fun u => (J.flow_deriv u).div_const (perim base)
  have hdpsi : ∀ u, HasDerivAt dpsi (ddpsi u) u :=
    fun u => (J.flow1_deriv u).div_const (perim base)
  have hvelocity : ∀ u, J.rear.2.1 u =
      (dpsi u : ℂ) * base.2.1 (psi u) := by
    intro u
    have hchain := (B.zero_floor_tube.hasDerivAt_curve (psi u)).scomp u (hpsi u)
    have heq : (⇑base.1 ∘ psi) = ⇑J.rear.1 :=
      funext fun x => (J.position x).symm
    rw [heq] at hchain
    have hu := (J.curve_deriv u).unique hchain
    simpa [Complex.real_smul] using hu
  have htranslate : ∀ u, psi (u + 1) = psi u + 1 := by
    intro u
    dsimp [psi]
    rw [hshiftTerminal u]
    field_simp [hL.ne']
  let orient : OrientedReparametrization base J.rear B.lambda B.Lambda :=
    { psi := psi
      dpsi := dpsi
      position := J.position
      velocity := hvelocity
      translate := htranslate
      lower := hlower
      upper := hupper }
  have hcont : Continuous orient.psi :=
    continuous_iff_continuousAt.2 fun u => (hpsi u).continuousAt
  have hmono : StrictMono orient.psi := by
    refine strictMono_of_deriv_pos fun u => ?_
    rw [(hpsi u).deriv]
    exact lt_of_lt_of_le B.lambda_pos (hlower u)
  have hzero : orient.psi 0 = 0 := by
    dsimp [orient, psi]
    rw [E.base Gamma.T, zero_div]
  have hsurj : Surjective orient.psi :=
    GaugeMarkedSelectedInverseEndpoint.surjective_of_continuous_strictMono_quasiPeriodic
      one_pos hcont hmono orient.translate hzero
  have hcurv := rear_orientedCurvature_nonnegative J
    A.kh_nonnegative A.kh_lt_one (A.strip_nonnegative Gamma.T)
    (A.strip_le Gamma.T) A.front_frenet A.angle_frenet A.steering
    A.sf_deriv A.cos_ne_zero rfl hterminal
  let residual : RawTerminalResidual b J.rear :=
    rawTerminalResidual_of_orientedReparametrization B.physical.cq_pos
      B.dlt_pos B.lambda_pos B.zero_floor_tube orient J.curve_deriv
      J.vel_deriv hcurv hsurj B.canonical_range B.strict
  let stage : GaugeRearFamilyVariableTerminal.RawStageOutput p b J.rear bound
      P0 (GaugeFlowDerivCost.costP1 (rearPeriod A 0) khat
        (∫ t in (0 : ℝ)..Gamma.T, A.m t)) khat
      (GaugeFlowDerivCost.costG1 (rearPeriod A 0) khat (rearKappa2 kh)
        (∫ t in (0 : ℝ)..Gamma.T, A.m t))
      (khat * GaugeFlowDerivCost.costG1 (rearPeriod A 0) khat (rearKappa2 kh)
          (∫ t in (0 : ℝ)..Gamma.T, A.m t) +
        rearKappa2 kh * GaugeFlowDerivCost.costP1 (rearPeriod A 0) khat
          (∫ t in (0 : ℝ)..Gamma.T, A.m t) ^ 2) :=
    { increment := W.Delta
      increment_geometry := W.geometry
      increment_cost := W.cost_eq.le.trans B.cost_le
      rear_curve_deriv := residual.rear_curve_deriv
      rear_vel_deriv := residual.rear_vel_deriv
      rear_periodic := residual.rear_periodic
      rear_curvature_nonnegative := residual.rear_curvature_nonnegative
      range_edge := residual.range_edge
      rear_harnack := residual.rear_harnack }
  have hendpoint : dist J.rear base ≤
      MarkingDeviationC2.markingC2Bound
        (2 * B.Lmax * rearKappa1 kh * W.Delta.cost)
        (MarkingFlowDefectC2.flowDefectC1Int (rearPeriod A 0)
          (rearKappa1 kh * W.Delta.cost))
        (MarkingFlowDefectC2.flowDefectC2Int (rearPeriod A 0)
          (rearKappa1 kh * W.Delta.cost)
        (rearKappa2 kh * W.Delta.cost))
        B.physical.L B.physical.kb B.physical.kL := by
    apply ConfiguredGaugeEndpointDefect.dist_le_of_retainedGaugeFrame
      (Gamma := W.Delta)
      (Phi := E.Phi)
      (Q := rearPeriod A)
      (Q' := fun t =>
        (∫ u in (0 : ℝ)..A.P t,
          SelectedChangeOfVariable.cosTimeDeriv A.delta
            (RearOwnHigherRegularity.partialTime A.delta) t u) +
        A.P' t * Real.cos (A.delta t (A.P t)))
      (m := A.m)
      (xi := frameTangential A.Ydot
        (rearOwnAngle A.Theta A.delta A.sf))
      (kappa := rearKappa1 kh)
      (kappa2 := rearKappa2 kh)
      (Lmax := B.Lmax)
      (L := B.physical.L)
      (kb := B.physical.kb)
      (kL := B.physical.kL)
      (cq := B.physical.cq)
      (kminq := B.physical.kmin)
      (dltq := B.physical.dlt)
      (Θ := B.physical.Theta)
      (k := B.physical.curvature)
      (q' := J.rear)
      E.frame A.density_continuous W.density_eq
      (A.rear_period_pos 0) B.rearPeriod_le
    · calc
        rearPeriod A W.Delta.T = rearPeriod A Gamma.T :=
          congrArg (rearPeriod A) W.time_eq
        _ = perim base := B.rearPeriod_terminal
        _ = B.physical.L := B.physical.perim_eq
    · exact B.physical.cq_pos
    · exact B.physical.tube
    · exact B.physical.perim_eq
    · exact B.physical.curve_frenet
    · exact B.physical.angle_deriv
    · exact B.physical.curvature_bound
    · exact B.physical.curvature_lipschitz
    · intro u
      rw [W.time_eq, J.position]
      simp [ev]
    · exact J.curve_deriv
    · exact J.vel_deriv
  refine ⟨{
    jets := J
    chosen := W
    stage := stage
    stage_eq := rfl
    c2 := W.c2
    marking := orient
    ddpsi := ddpsi
    psi_eq := fun _ => rfl
    dpsi_eq := fun _ => rfl
    ddpsi_eq := fun _ => rfl
    psi_deriv := hpsi
    dpsi_deriv := hdpsi
    ddpsi_cont := J.flow2_cont.div_const (perim base)
    psi_zero := hzero
    oriented_curvature := hcurv
    endpoint_dist := hendpoint
    frontKinematics := B.frontKinematics
    physicalFront := B.physicalFront
  }⟩

/-- Compatibility wrapper for the historical coincident-front boundary. -/
theorem exists_output
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A)
    (B : TerminalInput (p := p) (base := base) (bound := bound) E) :
    Nonempty (Output E B) := by
  obtain ⟨O⟩ := exists_presentedOutputCore E B.toPresentedCore
  exact ⟨{
    jets := O.jets
    chosen := O.chosen
    stage := O.stage
    stage_eq := O.stage_eq
    c2 := O.c2
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
    endpoint_dist := O.endpoint_dist
    physicalFront := B.physicalFront
    physicalFront_eq := B.physicalFront_eq }⟩

/-- The exact marked endpoint defect for the same selected path.  The cost is
the cost of `O.chosen.Delta`, whose retained density is definitionally the
frame density `A.m`; no comparison with an independently selected path is
used. -/
theorem Output.endpoint_dist_le
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := p) (base := base) (bound := bound) E}
    (O : Output E B) :
    dist O.jets.rear base ≤
      MarkingDeviationC2.markingC2Bound
        (2 * B.Lmax * rearKappa1 kh * O.chosen.Delta.cost)
        (MarkingFlowDefectC2.flowDefectC1Int (rearPeriod A 0)
          (rearKappa1 kh * O.chosen.Delta.cost))
        (MarkingFlowDefectC2.flowDefectC2Int (rearPeriod A 0)
          (rearKappa1 kh * O.chosen.Delta.cost)
          (rearKappa2 kh * O.chosen.Delta.cost))
        B.physical.L B.physical.kb B.physical.kL := by
  exact O.endpoint_dist

/-- Terminal curvature sign in the unmarked numerator convention consumed by
the marking-aware cap family. -/
theorem Output.terminal_curvature_nonnegative
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := p) (base := base) (bound := bound) E}
    (O : Output E B) (u : ℝ) :
    0 ≤ ((starRingEnd ℂ) (O.jets.rear.2.1 u) * O.jets.rear.2.2 u).im :=
  O.oriented_curvature u

end FiniteSmoothRearFamilyMarkingAwareChosenTerminal
