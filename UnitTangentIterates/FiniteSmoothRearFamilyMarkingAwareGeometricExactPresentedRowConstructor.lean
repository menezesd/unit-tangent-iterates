import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedTerminalInputAdapter
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGridDischarge

/-!
# Generic presented row constructor for an exact nonaffine state

All choices in the row are theorem-produced.  The input record contains only
the geometric and density facts not carried by the lightweight
`MarkingAwareSource` structure.
-/

noncomputable section

open Function Set MarkedSpace MarkedTopology PathMetric RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwareGeometricExactPresentedRowConstructor

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower
  FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGridDischarge
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalInputAdapter
  FiniteSmoothRearFamilyMarkingAwareRegularitySum
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily

/-- Exact obligations needed to construct the next presented row from a
heterogeneous analytic state. -/
structure Ready (X : State) where
  initial : Data
  spatial : SpatialFrameRegularity X.path X.source.Ydot X.source.Theta
    X.source.delta X.source.sf X.source.P X.source.m X.kh X.Qmax
  terminalCurvature_nonnegative : ∀ s, 0 ≤ X.source.K X.path.T s
  terminalRange : range (X.source.F X.path.T) = range X.finish.1
  initial_eq : X.source.selectedRearData 0 = initial
  density_d1 : ∀ t,
    2 * (X.path.m t / Real.sqrt (1 - X.kh ^ 2)) *
      GaugeFlowDerivCost.costP1 (rearPeriod X.source 0)
        (rearKappa1 X.kh) (∫ s in (0 : ℝ)..X.path.T, X.source.m s) ≤
          X.source.m t
  density_d2 : ∀ t,
    (X.source.Dd t + 2 * (X.path.m t / Real.sqrt (1 - X.kh ^ 2))) *
        GaugeFlowDerivCost.costP1 (rearPeriod X.source 0)
          (rearKappa1 X.kh) (∫ s in (0 : ℝ)..X.path.T, X.source.m s) ^ 2 +
      2 * (X.path.m t / Real.sqrt (1 - X.kh ^ 2)) *
        GaugeFlowDerivCost.costG1 (rearPeriod X.source 0)
          (rearKappa1 X.kh) (rearKappa2 X.kh)
          (∫ s in (0 : ℝ)..X.path.T, X.source.m s) ≤ X.source.m t
  front_injective : InjOn
    (FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.normalizedFront
      X.source) (Ico 0 1)

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
  simpa [GaugeRate.gaugeRate1, E.frame.v_eq_one,
    frame_speed_one_zero E] using hr

/-- The source-selected rear at time zero gives the exact initial boundary for
every theorem-produced application. -/
theorem Ready.initial_alignment
    {X : State} (H : Ready X) (E : Applied X.path X.source) (u : ℝ) :
    rearOwn X.source.F X.source.Theta X.source.delta X.source.sf 0
      (E.Phi 0 u) = H.initial.1 u := by
  rw [E.initial]
  have h := congrArg (fun D : Data ↦ D.1 u) H.initial_eq
  simpa [MarkingAwareSource.selectedRearData_curve,
    MarkingAwareSource.selectedRearCurve] using h

/-- Every ready state has a canonical theorem-produced presented row. -/
theorem Ready.exists_alignedPresentedRow {X : State} (H : Ready X) :
    ∃ R : PresentedRow X.source, R.p = H.initial ∧ R.kFront = 0 := by
  obtain ⟨E⟩ := exists_applied X.source
  obtain ⟨G⟩ := exists_presentedTerminalGeometry_of_spatial
    X.source E (ExactSidecars.ofSource X.source) H.spatial
    H.terminalCurvature_nonnegative H.density_d1 H.density_d2 X.Qmax
    X.source.rear_period_le
  obtain ⟨dFront, hdFront, hfrontTube⟩ :=
    FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGridDischarge.PresentedTerminalGeometry.exists_frontData_tube
      G H.terminalCurvature_nonnegative H.front_injective
  let ell := rearPeriod X.source 0
  let L := perim G.presented
  let r := E.frame.frame.rateLip
  have hL : 0 < L := perim_pos G.physical.cq_pos G.zero_floor_tube
  have hell : 0 < ell := X.source.rear_period_pos 0
  have hr0 : 0 ≤ r := E.frame.frame.rateLip_nonneg
  let lambda := ell * Real.exp (-(r * |X.path.T|)) / L
  let Lambda := ell * Real.exp (r * |X.path.T|) / L
  have hlambda : 0 < lambda :=
    div_pos (mul_pos hell (Real.exp_pos _)) hL
  have hlower : ∀ u, lambda ≤
      FlowDerivative.flowDeriv (fun t x ↦ -E.frame.frame.xi1 t x)
        E.Phi ell X.path.T u / L := by
    intro u
    apply (div_le_div_iff_of_pos_right hL).2
    have hb := (FlowDerivative.flowDeriv_bounds
      (K := Real.toNNReal r) (hx := fun t x ↦ -E.frame.frame.xi1 t x)
      (Phi := E.Phi) hell
      (fun t x ↦ by
        rw [Real.coe_toNNReal _ hr0]
        exact neg_xi1_le_rateLip E t x)
      X.path.T u).1
    simpa [lambda, ell, r, Real.coe_toNNReal _ hr0] using hb
  have hupper : ∀ u,
      FlowDerivative.flowDeriv (fun t x ↦ -E.frame.frame.xi1 t x)
        E.Phi ell X.path.T u / L ≤ Lambda := by
    intro u
    apply (div_le_div_iff_of_pos_right hL).2
    have hb := (FlowDerivative.flowDeriv_bounds
      (K := Real.toNNReal r) (hx := fun t x ↦ -E.frame.frame.xi1 t x)
      (Phi := E.Phi) hell
      (fun t x ↦ by
        rw [Real.coe_toNNReal _ hr0]
        exact neg_xi1_le_rateLip E t x)
      X.path.T u).2
    simpa [Lambda, ell, r, Real.coe_toNNReal _ hr0] using hb
  let B := ofPresentedTerminalGeometry E G (H.initial_alignment E)
    H.terminalRange.symm le_rfl hlambda hlower hupper
  obtain ⟨O⟩ := exists_presentedOutputCore E B
  exact ⟨{
    applied := E
    p := H.initial
    base := G.presented
    frontEndpoint := X.finish
    bound := ∫ t in (0 : ℝ)..X.path.T, X.source.m t
    terminalInput := B
    output := O
    cFront := X.source.P X.path.T
    kFront := 0
    dFront := dFront
    cFront_pos := X.source.period_pos X.path.T
    front_tube := hfrontTube
    frontData_eq := G.frontData_eq }, rfl, rfl⟩

theorem Ready.exists_presentedRow {X : State} (H : Ready X) :
    Nonempty (PresentedRow X.source) := by
  obtain ⟨R, _, _⟩ := H.exists_alignedPresentedRow
  exact ⟨R⟩

end FiniteSmoothRearFamilyMarkingAwareGeometricExactPresentedRowConstructor
