import UnitTangentIterates.FiniteSmoothRearFamilyAppliedSource
import UnitTangentIterates.GaugeRearFamilyEnrichedRichTerminalStage
import UnitTangentIterates.SelectedInverseApproximateMapPathRearFamilyAdapter

/-!
# A chosen terminal output from an applied rear-family source

This is the sound replacement for the historical universal endpoint producer.
An ordinary physical terminal representative is fixed first.  The gauge flow
then constructs its actual marked endpoint and all correlated path, marking,
separated-component, and physical data.
-/

noncomputable section

open Set Function MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
  RearTrack RearOwnArclength RearFamilyFrame
  NormalPathC2IncrementVariableSpeed GaugeFlowDerivCost

namespace FiniteSmoothRearFamilyChosenTerminal

open FiniteSmoothRearFamilyAnalyticSource
  FiniteSmoothRearFamilyAppliedSource
  GaugeMarkedDataOfRearFamily
  GaugeFlowMarkedTerminalJets
  GaugeRearFamilyVariableTerminal
  GaugeRearFamilySeparatedContinuation
  SelectedInverseApproximateMapPath

/-- Genuine endpoint/physical input not supplied by the long gauge theorem. -/
structure TerminalInput
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax P1 bound : ℝ}
    {A : Source Gamma P0 kh khat Qmax}
    (E : Applied Gamma A P1) where
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
  density_eq : A.m = fun t => mapK kh * Gamma.m t
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
  physicalKinematics : PhysicalRearLimitKinematics kh base b

/-- The retained unit-speed frame has zero first and second spatial speed
derivatives. -/
private theorem frame_speed_jets_zero
    {a b : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax P1 : ℝ}
    {A : Source Gamma P0 kh khat Qmax}
    (E : Applied Gamma A P1) :
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

/-- Construct the actual terminal spatial flow jets from the retained frame. -/
theorem Applied.exists_terminalJets
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax P1 bound : ℝ}
    {A : Source Gamma P0 kh khat Qmax}
    (E : Applied Gamma A P1)
    (B : TerminalInput (p := p) (base := base)
      (bound := bound) E) :
    Nonempty (TerminalJets E.frame.frame.xi E.frame.frame.xi1
      E.frame.frame.xi2 E.Phi (rearPeriod A 0) (perim base) Gamma.T base) := by
  have hxiC : ContDiff ℝ 1 (uncurry E.frame.frame.xi) := by
    have heq : E.frame.frame.xi =
        frameTangential A.Ydot (rearOwnAngle A.Theta A.delta A.sf) :=
      funext fun t => funext fun x => E.frame.xi_eq t x
    rw [heq]
    exact RearOwnTangential.contDiff_frameTangential
      (A.rear_velocity_contDiff.of_le (by norm_num))
      (A.rear_angle_contDiff.of_le (by norm_num))
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
    (A.rear_period_pos 0) hL hxiC.continuous E.frame.frame.hxi
    E.frame.frame.hxi1c E.frame.frame.hxi1 E.frame.frame.hxi2c
    hC hC2 (rearKappa1_nonneg A.kh_nonnegative A.kh_lt_one)
    (rearKappa2_nonneg A.kh_nonnegative A.kh_lt_one)
    A.density_continuous A.density_nonnegative A.density_support
    E.initial hflow B.zero_floor_tube.hasDerivAt_curve
    B.zero_floor_tube.hasDerivAt_vel

/-- Construct one exact chosen enriched rear-family output. -/
theorem exists_enrichedOutput
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax P1 bound : ℝ}
    {A : Source Gamma P0 kh khat Qmax}
    (E : Applied Gamma A P1)
    (B : TerminalInput (p := p) (base := base)
      (bound := bound) E) :
    ∃ rear : Data,
      Nonempty (FiniteSmoothRearFamilyEnrichedOutput Gamma
        A.F A.Theta A.delta A.sf A.Ydot E.Phi
        (rearPeriod A 0) (∫ t in (0 : ℝ)..Gamma.T, A.m t)
        P0 kh khat p rear) := by
  obtain ⟨J⟩ :=
    FiniteSmoothRearFamilyChosenTerminal.Applied.exists_terminalJets E B
  have hterminal : ∀ u, J.rear.1 u =
      rearOwn A.F A.Theta A.delta A.sf Gamma.T (E.Phi Gamma.T u) := by
    intro u
    exact (J.position u).trans (B.terminal_carrier (E.Phi Gamma.T u))
  obtain ⟨R⟩ := E.chosen p J.rear B.initial
    (fun u => (hterminal u).symm) B.normal_sup
  have hflowedR : GaugeNormalPathSeparated.FlowedBounds Gamma.eta R.Delta.eta
      E.CW E.C0 E.C10 E.C11 E.C20 E.C21 E.C22 := by
    have heta : R.Delta.eta = fun t u => rearNormal A t (E.Phi t u) :=
      funext fun t => funext fun u => R.eta_eq t u
    simpa [heta] using E.flowed
  let result : GaugeRearFamilySeparatedContinuation.Result Gamma p J.rear
      (∫ t in (0 : ℝ)..Gamma.T, A.m t) P0 (rearPeriod A 0) kh khat
      E.CW E.C0 E.C10 E.C11 E.C20 E.C21 E.C22 :=
    Result.ofLongOutput R.Delta R.time_eq R.cost_eq R.geometry R.c2 hflowedR
  have hL : 0 < perim base := perim_pos B.physical.cq_pos B.zero_floor_tube
  have hlower : ∀ u, B.lambda ≤ J.flow1 u / perim base := by
    intro u
    rw [J.flow1_eq]
    exact B.flow_lower u
  have hupper : ∀ u, J.flow1 u / perim base ≤ B.Lambda := by
    intro u
    rw [J.flow1_eq]
    exact B.flow_upper u
  let psi : ℝ → ℝ := fun u => E.Phi Gamma.T u / perim base
  let dpsi : ℝ → ℝ := fun u => J.flow1 u / perim base
  have hpsi : ∀ u, HasDerivAt psi (dpsi u) u :=
    fun u => (J.flow_deriv u).div_const (perim base)
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
    rw [R.shift Gamma.T u, B.rearPeriod_terminal]
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
  have hcurv := GaugeFlowMarkedTerminalJets.rear_orientedCurvature_nonnegative J
    A.kh_nonnegative A.kh_lt_one (A.strip_nonnegative Gamma.T)
    (A.strip_le Gamma.T) A.front_frenet A.angle_frenet A.steering
    A.sf_deriv A.cos_ne_zero rfl hterminal
  let residual : RawTerminalResidual b J.rear :=
    rawTerminalResidual_of_orientedReparametrization B.physical.cq_pos
      B.dlt_pos B.lambda_pos B.zero_floor_tube orient J.curve_deriv
      J.vel_deriv hcurv hsurj B.canonical_range B.strict
  let raw : GaugeRearFamilySeparatedContinuation.RawStageOutput Gamma
      p b J.rear bound (∫ t in (0 : ℝ)..Gamma.T, A.m t)
      P0 (rearPeriod A 0) kh khat
      E.CW E.C0 E.C10 E.C11 E.C20 E.C21 E.C22 :=
    RawStageOutput.ofResult result B.cost_le residual
  have hshiftTerminal : ∀ u, E.Phi Gamma.T (u + 1) =
      E.Phi Gamma.T u + perim base := by
    intro u
    rw [R.shift Gamma.T u, B.rearPeriod_terminal]
  obtain ⟨O⟩ := GaugeRearFamilyEnrichedRichTerminalStage.exists_output_of_raw
    (dlt := B.physical.dlt) J raw
    hL B.lambda_pos hshiftTerminal (E.base Gamma.T) hlower hupper
    B.zero_floor_tube B.physical.cq_pos B.dlt_pos A.kh_nonnegative
    A.kh_lt_one (A.strip_nonnegative Gamma.T) (A.strip_le Gamma.T)
    A.front_frenet A.angle_frenet A.steering A.sf_deriv A.cos_ne_zero
    hterminal
  have hxi : E.frame.frame.xi =
      frameTangential A.Ydot (rearOwnAngle A.Theta A.delta A.sf) :=
    funext fun t => funext fun x => E.frame.xi_eq t x
  refine ⟨J.rear, ⟨{
    Delta := R.Delta
    time_eq := R.time_eq
    density_eq := R.density_eq.trans B.density_eq
    cost_eq := R.cost_eq
    geometry := R.geometry
    c2 := R.c2
    Q := rearPeriod A
    Q' := rearPeriodDeriv A
    m := A.m
    xi := E.frame.frame.xi
    xiX := E.frame.frame.xi1
    xiXX := E.frame.frame.xi2
    kappa := rearKappa1 kh
    kappa2 := rearKappa2 kh
    retainedFrame := by simpa only [hxi] using E.frame
    frame_m_eq := R.density_eq
    m_continuous := A.density_continuous
    Q_zero_pos := A.rear_period_pos 0
    Lmax := B.Lmax
    Q_le := B.rearPeriod_le
    terminalBase := base
    terminalJets := J
    terminal_eq := rfl
    Q_terminal := by rw [R.time_eq]; exact B.rearPeriod_terminal
    physicalKinematics := B.physicalKinematics
    terminalPhysical := B.physical
    lambda := O.rich.lambda
    Lambda := O.rich.Lambda
    marking := NormalizedTerminalMarkingComposition.NormalizedC2Marking.ofRichStage
      O.rich
    terminal := residual
    CW := E.CW
    C0 := E.C0
    C10 := E.C10
    C11 := E.C11
    C20 := E.C20
    C21 := E.C21
    C22 := E.C22
    flowed := hflowedR }⟩⟩

end FiniteSmoothRearFamilyChosenTerminal
