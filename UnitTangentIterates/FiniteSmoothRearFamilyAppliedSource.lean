import UnitTangentIterates.FiniteSmoothRearFamilyAnalyticSource
import UnitTangentIterates.GaugeGeometryVariableSeparatedFlowed
import UnitTangentIterates.GaugeRearFamilySeparatedContinuation

/-!
# Applying a correlated rear-family analytic source

This module takes the non-erased analytic input of
`FiniteSmoothRearFamilyAnalyticSource.Source`, applies the long rear-family
theorem once, and derives the component-separated continuation using the
moving-period gauge estimate.  The resulting `Applied` object is the last
stage before terminal marking jets and physical endpoint data are attached.
-/

noncomputable section

open Set Function MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
  RearTrack RearOwnArclength RearFamilyFrame
  NormalPathC2IncrementVariableSpeed GaugeFlowDerivCost

namespace FiniteSmoothRearFamilyAppliedSource

open FiniteSmoothRearFamilyAnalyticSource
  GaugeMarkedDataOfRearFamily
  GaugeNormalPathSeparated
  GaugeRearFamilySeparatedContinuation

/-- Additional slice facts needed only for the sharp separated component
estimate.  They are not outputs of the long theorem. -/
structure SeparatedFacts
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} (A : Source Gamma P0 kh khat Qmax)
    (P1 : ℝ) where
  P0_pos : 0 < P0
  period_lower : ∀ t, P0 ≤ A.P t
  period_upper : ∀ t, A.P t ≤ P1
  etaFs : ℝ → ℝ → ℝ
  etaF_deriv : ∀ t s, HasDerivAt (A.etaF t) (etaFs t s) s
  etaFs_continuous : ∀ t, Continuous (etaFs t)
  etaF_periodic : ∀ t, Periodic (A.etaF t) (A.P t)
  normal_stopped : ∀ t ∉ Ioo (0 : ℝ) Gamma.T,
    frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t = fun _ => 0

/-- The moving rear arclength period retained by the long theorem. -/
def rearPeriod
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} (A : Source Gamma P0 kh khat Qmax) (t : ℝ) : ℝ :=
  rearArclength (A.delta t) (A.P t)

/-- The derivative used for the moving rear period. -/
def rearPeriodDeriv
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} (A : Source Gamma P0 kh khat Qmax) (t : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..A.P t,
      SelectedChangeOfVariable.cosTimeDeriv A.delta
        (RearOwnHigherRegularity.partialTime A.delta) t u) +
    A.P' t * Real.cos (A.delta t (A.P t))

/-- The unmarked selected-rear normal velocity in its own arclength. -/
def rearNormal
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} (A : Source Gamma P0 kh khat Qmax) :
    ℝ → ℝ → ℝ :=
  frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf)

/-- One endpoint-specialized path selected by the long theorem, retaining the
equalities needed by the chosen-terminal output. -/
structure ChosenPath
    {p q : Data} (Gamma : NormalPath p q)
    {P0 kh khat Qmax : ℝ} (A : Source Gamma P0 kh khat Qmax)
    (Phi : ℝ → ℝ → ℝ) (a b : Data) where
  Delta : NormalPath a b
  time_eq : Delta.T = Gamma.T
  eta_eq : ∀ t u, Delta.eta t u = rearNormal A t (Phi t u)
  shift : ∀ t u, Phi t (u + 1) = Phi t u + rearPeriod A t
  phi1 : ℝ → ℝ → ℝ
  phi2 : ℝ → ℝ → ℝ
  phi1_deriv : ∀ t u, HasDerivAt (Phi t) (phi1 t u) u
  phi2_deriv : ∀ t u, HasDerivAt (phi1 t) (phi2 t u) u
  phi1_continuous : ∀ t, Continuous (phi1 t)
  phi2_continuous : ∀ t, Continuous (phi2 t)
  density_eq : Delta.m = A.m
  cost_eq : Delta.cost = ∫ t in (0 : ℝ)..Gamma.T, A.m t
  geometry : IsVariableSpeedNormalPath P0
    (costP1 (rearPeriod A 0) khat
      (∫ t in (0 : ℝ)..Gamma.T, A.m t)) khat
    (costG1 (rearPeriod A 0) khat (rearKappa2 kh)
      (∫ t in (0 : ℝ)..Gamma.T, A.m t))
    (khat * costG1 (rearPeriod A 0) khat (rearKappa2 kh)
        (∫ t in (0 : ℝ)..Gamma.T, A.m t) +
      rearKappa2 kh * costP1 (rearPeriod A 0) khat
        (∫ t in (0 : ℝ)..Gamma.T, A.m t) ^ 2) Delta
  c2 : C2NormalPathData Delta

/-- A concrete application of the long theorem together with the sharp
moving-period separated continuation.  Every field except the selected
existential witnesses is proved by `exists_applied`; there is no producer
callback in this structure. -/
structure Applied
    {p q : Data} (Gamma : NormalPath p q)
    {P0 kh khat Qmax : ℝ}
    (A : Source Gamma P0 kh khat Qmax) (P1 : ℝ) where
  Phi : ℝ → ℝ → ℝ
  initial : ∀ u, Phi 0 u = rearPeriod A 0 * u
  base : ∀ t, Phi t 0 = 0
  flow : ∀ u t, HasDerivAt (fun s => Phi s u)
    (-frameTangential A.Ydot (rearOwnAngle A.Theta A.delta A.sf)
      t (Phi t u)) t
  frame : GaugeRearFamilyFundamental.RetainedGaugeFrame Phi
    (rearPeriod A) (rearPeriodDeriv A) A.m
    (frameTangential A.Ydot (rearOwnAngle A.Theta A.delta A.sf))
    (rearKappa1 kh) (rearKappa2 kh)
  CW : ℝ
  C0 : ℝ
  C10 : ℝ
  C11 : ℝ
  C20 : ℝ
  C21 : ℝ
  C22 : ℝ
  flowed : FlowedBounds Gamma.eta
    (fun t u => rearNormal A t (Phi t u)) CW C0 C10 C11 C20 C21 C22
  chosen : ∀ (a b : Data),
    (∀ u, rearOwn A.F A.Theta A.delta A.sf 0 (Phi 0 u) = a.1 u) →
    (∀ u, rearOwn A.F A.Theta A.delta A.sf Gamma.T (Phi Gamma.T u) = b.1 u) →
    (∀ t, ∀ j ≤ 2, supNorm
      (iteratedDeriv j (fun u => rearNormal A t (Phi t u))) ≤ A.m t) →
    Nonempty (ChosenPath Gamma A Phi a b)
  continuation : GaugeRearFamilySeparatedContinuation.Continuation Gamma
    A.F A.Theta A.delta A.sf A.Ydot Phi
    (∫ t in (0 : ℝ)..Gamma.T, A.m t) A.m
    P0 (rearPeriod A 0) kh khat CW C0 C10 C11 C20 C21 C22

/-- Apply the long theorem and the existing variable-period separated gauge
estimate. -/
theorem exists_applied
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    (A : Source Gamma P0 kh khat Qmax) (S : SeparatedFacts A P1) :
    Nonempty (Applied Gamma A P1) := by
  obtain ⟨Phi, hPhi0, hbase, hflow, hpair, ⟨hframe⟩⟩ := A.applyLong
  let etaR : ℝ → ℝ → ℝ := rearNormal A
  have hetaC2 : ∀ t, ContDiff ℝ (2 : ℕ) (etaR t) := by
    intro t
    have H : ContDiff ℝ (2 : ℕ)
        (uncurry (frameNormal A.Ydot
          (rearOwnAngle A.Theta A.delta A.sf))) :=
      RearOwnTangential.contDiff_frameNormal
        (A.rear_velocity_contDiff.of_le (by norm_num))
        (A.rear_angle_contDiff.of_le (by norm_num))
    simpa [etaR, rearNormal, Function.uncurry] using
      H.comp (contDiff_const.prodMk contDiff_id)
  have hetaPer : ∀ t, Periodic (etaR t) (rearPeriod A t) := by
    intro t
    simpa [etaR, rearNormal, rearPeriod] using
      RearOwnDriftFundamental.periodic_frameNormal_rearOwn
        A.kh_nonnegative A.kh_lt_one
        A.strip_nonnegative A.strip_le A.cos_ne_zero A.front_frenet
        A.angle_frenet A.steering A.sf_deriv A.sf_rightInverse
        A.steering_periodic A.front_periodic A.angle_periodic
        A.front_contDiff A.angle_contDiff A.steering_contDiff A.sf_contDiff
        A.period_contDiff A.rear_time_deriv t
  have hflowed := GaugeGeometryVariableSeparatedFlowed.flowedBounds Gamma
    hframe.frame S.P0_pos A.kh_nonnegative A.kh_lt_one
    S.period_lower S.period_upper A.steering A.strip_nonnegative A.strip_le
    A.steering_periodic A.curvature_le S.etaF_deriv S.etaFs_continuous
    S.etaF_periodic A.sf_rightInverse A.jacobi (fun _ => rfl)
    hframe.period_deriv hetaPer hetaC2 A.eta_link hframe.v_periodic
    hframe.xi_quasiPeriodic hframe.flow hframe.initial S.normal_stopped
  let CW := GaugeNormalPath.gaugeCW P1 hframe.frame.rateLip Gamma.T
    (rearPeriod A 0)
  let C0 := P1 /
    (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0)))
  let C10 := flowFirst C0 hframe.frame.rateLip Gamma.T (rearPeriod A 0)
  let C11 := flowFirst (1 / Real.sqrt (1 - kh ^ 2))
    hframe.frame.rateLip Gamma.T (rearPeriod A 0)
  let C20 := flowSecond C0 hframe.frame.rateLip Gamma.T (rearPeriod A 0) +
    flowDrift C0 hframe.frame.rateLip hframe.frame.rateBound2
      Gamma.T (rearPeriod A 0)
  let C21 := flowSecond
      (2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
        1 / Real.sqrt (1 - kh ^ 2))
      hframe.frame.rateLip Gamma.T (rearPeriod A 0) +
    flowDrift (1 / Real.sqrt (1 - kh ^ 2))
      hframe.frame.rateLip hframe.frame.rateBound2 Gamma.T (rearPeriod A 0)
  let C22 := flowSecond
    (1 / (P0 * Real.sqrt (1 - kh ^ 2) ^ 2))
    hframe.frame.rateLip Gamma.T (rearPeriod A 0)
  have hflowed' : FlowedBounds Gamma.eta
      (fun t u => rearNormal A t (Phi t u))
      CW C0 C10 C11 C20 C21 C22 := by
    simpa [CW, C0, C10, C11, C20, C21, C22, etaR] using hflowed
  have hchosen : ∀ (a b : Data),
      (∀ u, rearOwn A.F A.Theta A.delta A.sf 0 (Phi 0 u) = a.1 u) →
      (∀ u, rearOwn A.F A.Theta A.delta A.sf Gamma.T (Phi Gamma.T u) = b.1 u) →
      (∀ t, ∀ j ≤ 2, supNorm
        (iteratedDeriv j (fun u => rearNormal A t (Phi t u))) ≤ A.m t) →
      Nonempty (ChosenPath Gamma A Phi a b) := by
    intro a b hinitial hterminal hsup
    obtain ⟨Delta, htime, _hX, heta, hshift, hphi, hm, hcost,
        hgeometry, ⟨hc2⟩⟩ := hpair a b hinitial hterminal hsup
    obtain ⟨phi1, phi2, hphi1, hphi2, hphi1c, hphi2c,
      _hphi1bd, _hphi2bd⟩ := hphi
    exact ⟨{
      Delta := Delta
      time_eq := htime
      eta_eq := heta
      shift := hshift
      phi1 := phi1
      phi2 := phi2
      phi1_deriv := hphi1
      phi2_deriv := hphi2
      phi1_continuous := hphi1c
      phi2_continuous := hphi2c
      density_eq := hm
      cost_eq := hcost
      geometry := hgeometry
      c2 := hc2 }⟩
  refine ⟨{
    Phi := Phi
    initial := hPhi0
    base := hbase
    flow := hflow
    frame := hframe
    CW := CW
    C0 := C0
    C10 := C10
    C11 := C11
    C20 := C20
    C21 := C21
    C22 := C22
    flowed := hflowed'
    chosen := hchosen
    continuation := ?_ }⟩
  intro a b hinitial hterminal hsup
  obtain ⟨R⟩ := hchosen a b hinitial hterminal hsup
  have hflowedDelta : FlowedBounds Gamma.eta R.Delta.eta
      CW C0 C10 C11 C20 C21 C22 := by
    have hetaEq : R.Delta.eta = fun t u => rearNormal A t (Phi t u) :=
      funext fun t => funext fun u => R.eta_eq t u
    simpa [hetaEq] using hflowed'
  exact ⟨GaugeRearFamilySeparatedContinuation.Result.ofLongOutput R.Delta
    R.time_eq R.cost_eq R.geometry R.c2 hflowedDelta⟩

/-- Attach genuinely terminal geometric facts to the exact separated path
selected by an applied source. -/
theorem Applied.exists_rawStageOutput
    {a b p front rear : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax P1 bound : ℝ}
    {A : Source Gamma P0 kh khat Qmax}
    (E : Applied Gamma A P1)
    (hinitial : ∀ u,
      rearOwn A.F A.Theta A.delta A.sf 0 (E.Phi 0 u) = p.1 u)
    (hterminal : ∀ u,
      rearOwn A.F A.Theta A.delta A.sf Gamma.T (E.Phi Gamma.T u) = rear.1 u)
    (hsup : ∀ t, ∀ j ≤ 2, supNorm
      (iteratedDeriv j
        (fun u => frameNormal A.Ydot
          (rearOwnAngle A.Theta A.delta A.sf) t (E.Phi t u))) ≤ A.m t)
    (hcost : (∫ t in (0 : ℝ)..Gamma.T, A.m t) ≤ bound)
    (T : GaugeRearFamilyVariableTerminal.RawTerminalResidual front rear) :
    Nonempty (GaugeRearFamilySeparatedContinuation.RawStageOutput Gamma
      p front rear bound (∫ t in (0 : ℝ)..Gamma.T, A.m t)
      P0 (rearPeriod A 0) kh khat
      E.CW E.C0 E.C10 E.C11 E.C20 E.C21 E.C22) :=
  GaugeRearFamilySeparatedContinuation.rawStageOutput_of_continuation
    E.continuation hinitial hterminal hsup hcost T

end FiniteSmoothRearFamilyAppliedSource
