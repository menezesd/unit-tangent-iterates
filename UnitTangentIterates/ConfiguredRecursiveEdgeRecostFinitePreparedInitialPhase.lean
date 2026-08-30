import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedAnalytic
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierCrossRowPhaseCompatibility
import UnitTangentIterates.MarkingAwareSourceSelectedInverseCertificate
import UnitTangentIterates.SelectedInverseShiftEquivariance

/-! # Unconditional initial-front identities for a prepared analytic source

`BridgeData` determines the zero-time front of the prepared analytic source:
it is the inverse terminal-front shift of the preceding prepared row.  It
also retains the preceding source's terminal selected rear exactly as the
geometric base.

The intrinsic selected-inverse certificate of a marking-aware source makes
the corresponding rear identity unconditional.  The predecessor certificate
is transported through the retained terminal-front shift and uniqueness then
identifies the prepared source's selected rear with the shifted geometric
base.
-/

noncomputable section

open Function Set MarkedSpace PathMetric RearTrack

namespace ConfiguredRecursiveEdgeRecostFinitePreparedInitialPhase

open ConfiguredRecursiveEdgeRecostFinitePreparedAnalytic
  ConfiguredRecursiveEdgeRecostFinitePreparedGeometrySchema
  ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  (H : Output R)

/-- A marked selected-inverse certificate transports through a shift of its
front marking.  The induced rear shift is obtained from the same steering
arclength witness, so no global injectivity callback is needed. -/
theorem transport_isMarkedSelectedInverse_shiftData
    {c kmin dlt cR kminR dltR kap : ℝ} {p q : Data}
    (hc : 0 < c) (hp : IsTubeMember c kmin dlt p)
    (hcR : 0 < cR) (hq : IsTubeMember cR kminR dltR q)
    (Hq : SelectedInverseMap.IsMarkedSelectedInverse kap p q) (b : ℝ) :
    ∃ a : ℝ, SelectedInverseMap.IsMarkedSelectedInverse kap
      (MarkedShift.shiftData b p) (MarkedShift.shiftData a q) := by
  obtain ⟨_, Theta, K, dl, sf, hX, hTheta, hdper, hdmem, hode,
    hsfinv, hperim, hev⟩ := Hq
  let L : ℝ := perim p
  have hLpos : 0 < L := by
    simpa [L] using perim_pos hc hp
  have hQpos : 0 < perim q := perim_pos hcR hq
  have hdc : Continuous dl :=
    Differentiable.continuous fun s => (hode s).differentiableAt
  let t : ℝ := b * L
  let a : ℝ := rearArclength dl t
  let rearPhase : ℝ := a / perim q
  refine ⟨rearPhase, ?_⟩
  have hperimb : perim (MarkedShift.shiftData b p) = L := by
    simpa [L] using SelectedInverseShiftEquivariance.perim_shiftData hp b
  have hevb : ∀ s, ev (MarkedShift.shiftData b p) s = ev p (s + t) := by
    intro s
    simpa [t, L] using
      (SelectedInverseShiftEquivariance.ev_shiftData hp
        (perim_pos hc hp).ne' b s)
  have hinner : ∀ s : ℝ, HasDerivAt (fun y : ℝ => y + t) 1 s := fun s => by
    simpa using (hasDerivAt_id s).add_const t
  have hXb : ∀ s, HasDerivAt (ev (MarkedShift.shiftData b p))
      (Complex.exp (Complex.I * ((Theta (s + t) : ℝ) : ℂ))) s := by
    intro s
    have h : HasDerivAt (fun y => ev p (y + t))
        (Complex.exp (Complex.I * ((Theta (s + t) : ℝ) : ℂ))) s := by
      simpa using (hX (s + t)).scomp s (hinner s)
    exact h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => hevb y)
  have hThetab : ∀ s, HasDerivAt (fun y => Theta (y + t))
      (K (s + t)) s := fun s => by
    simpa using (hTheta (s + t)).scomp s (hinner s)
  have hdperb : Function.Periodic (fun y => dl (y + t))
      (perim (MarkedShift.shiftData b p)) := by
    rw [hperimb]
    intro s
    have hs : s + L + t = s + t + L := by ring
    simp only [hs]
    exact hdper (s + t)
  have hdmem_b : ∀ s, dl (s + t) ∈ Icc 0 (Real.arcsin kap) :=
    fun s => hdmem (s + t)
  have hode_b : ∀ s, HasDerivAt (fun y => dl (y + t))
      (K (s + t) - Real.sin (dl (s + t))) s := fun s => by
    simpa using (hode (s + t)).scomp s (hinner s)
  have hrs : ∀ y, rearArclength (fun s => dl (s + t)) y =
      rearArclength dl (y + t) - a := fun y =>
    SelectedInverseShiftEquivariance.rearArclength_shift hdc t y
  have hsfinv_b : ∀ x,
      rearArclength (fun s => dl (s + t)) (sf (x + a) - t) = x := by
    intro x
    rw [hrs]
    have hs : sf (x + a) - t + t = sf (x + a) := by ring
    rw [hs, hsfinv (x + a)]
    ring
  have hperim_b : perim (MarkedShift.shiftData rearPhase q) =
      rearArclength (fun s => dl (s + t))
        (perim (MarkedShift.shiftData b p)) := by
    rw [SelectedInverseShiftEquivariance.perim_shiftData hq rearPhase,
      hperimb, hrs L, hperim]
    change rearArclength dl L = rearArclength dl (L + t) - a
    have hadd : rearArclength dl (L + t) =
        rearArclength dl t + rearArclength dl L := by
      rw [add_comm L t]
      simpa [L] using
        (SelectedInverseShiftEquivariance.rearArclength_add_period
          hdc hdper t)
    rw [hadd]
    dsimp [a]
    ring
  have hev_b : ∀ x, ev (MarkedShift.shiftData rearPhase q) x =
      rearTrack (ev (MarkedShift.shiftData b p))
        (fun y => Theta (y + t)) (fun y => dl (y + t))
        (sf (x + a) - t) := by
    intro x
    have hshift : ev (MarkedShift.shiftData rearPhase q) x =
        ev q (x + a) := by
      rw [SelectedInverseShiftEquivariance.ev_shiftData hq hQpos.ne'
        rearPhase x]
      congr 1
      dsimp [rearPhase]
      field_simp [hQpos.ne'] <;> ring
    have hs : sf (x + a) - t + t = sf (x + a) := by ring
    rw [hshift, hev (x + a)]
    simp only [rearTrack, rearAngle, hevb (sf (x + a) - t), hs]
  exact ⟨⟨cR, kminR, dltR,
      MarkedShift.isTubeMember_shiftData hq rearPhase⟩,
    (fun y => Theta (y + t)), (fun y => K (y + t)),
    (fun y => dl (y + t)), (fun x => sf (x + a) - t),
    hXb, hThetab, hdperb, hdmem_b, hode_b, hsfinv_b, hperim_b, hev_b⟩

/-- The arbitrary-time source front datum specializes at the source terminal
time to the canonical presented `unitTangentData`, including all three `Data`
components. -/
theorem frontData_terminal_eq_unitTangentData
    {a b : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    MarkingAwareSource.frontData A Gamma.T = unitTangentData A := by
  apply Prod.ext
  · exact BoundedContinuousFunction.ext fun u => by
      simp [MarkingAwareSource.frontCurve, normalizedFront]
  · apply Prod.ext
    · exact BoundedContinuousFunction.ext fun u => by
        simp [MarkingAwareSource.frontVelocity, normalizedFrontVelocity]
    · exact BoundedContinuousFunction.ext fun u => by
        change MarkingAwareSource.frontAcceleration A Gamma.T u =
          normalizedFrontAcceleration A u
        rfl

/-- The geometric terminal time retained by the predecessor core is exactly
the terminal time used by its canonical unit-tangent datum. -/
theorem predecessor_frontData_terminal_eq_unitTangentData
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    MarkingAwareSource.frontData (Z.nodes n).stage.source
        (Z.pre H n).geometric.output.chosen.Delta.T =
      unitTangentData (Z.nodes n).stage.source := by
  rw [(Z.pre H n).geometric.output.chosen.time_eq]
  exact frontData_terminal_eq_unitTangentData (Z.nodes n).stage.source

/-- The front phase visible unconditionally at the start of the prepared
analytic source.  It cancels the retained terminal-front phase. -/
noncomputable def preparedAnalyticInitialFrontPhase
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) : ℝ :=
  -D.geometry.terminalFrontPhase n

@[simp] theorem preparedAnalyticInitialFrontPhase_add_terminalFrontPhase
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    preparedAnalyticInitialFrontPhase H D n +
        D.geometry.terminalFrontPhase n = 0 := by
  simp [preparedAnalyticInitialFrontPhase]

/-- Inverting the retained terminal phase recovers the following displayed
datum as complete marked data. -/
theorem preparedAnalytic_displayed_eq_shift_terminalFront
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (Z.nodes (n + 1)).stage.displayed =
      MarkedShift.shiftData (preparedAnalyticInitialFrontPhase H D n)
        (Z.presented n).terminal.frontData := by
  rw [D.geometry.terminalFront_eq_phase n]
  simp [preparedAnalyticInitialFrontPhase, MarkedShift.shiftData_add]

/-- The same inverse phase, after replacing the retained terminal front by
the preceding source's canonical terminal unit-tangent datum. -/
theorem preparedAnalytic_displayed_eq_shift_predecessorTerminal
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (Z.nodes (n + 1)).stage.displayed =
      MarkedShift.shiftData (preparedAnalyticInitialFrontPhase H D n)
        (unitTangentData (Z.nodes n).stage.source) := by
  calc
    (Z.nodes (n + 1)).stage.displayed =
        MarkedShift.shiftData (preparedAnalyticInitialFrontPhase H D n)
          (Z.presented n).terminal.frontData :=
      preparedAnalytic_displayed_eq_shift_terminalFront H D n
    _ = MarkedShift.shiftData (preparedAnalyticInitialFrontPhase H D n)
          (unitTangentData (Z.nodes n).stage.source) :=
      congrArg (MarkedShift.shiftData
        (preparedAnalyticInitialFrontPhase H D n))
        (D.geometry.frontData_eq_source n)

/-- The preceding geometric input retains its terminal selected rear exactly,
not merely up to range or phase. -/
theorem predecessor_selectedRearData_terminal_eq_base
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (Z.nodes n).stage.source.selectedRearData
        (Z.pre H n).geometric.output.chosen.Delta.T =
      (Z.pre H n).geometric.base := by
  simpa using
    (ConfiguredRecursiveEdgeRecostMultiplierCrossRowPhaseCompatibility.GeometricInput.selectedRearData_terminal_eq_base
        (Z.pre H n).geometric)

/-- Direct recosting and multiplier scaling preserve the constructed
successor front at time zero; the prepared provenance identifies it with the
following displayed datum. -/
theorem preparedAnalytic_source_front_zero_eq_displayed
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (preparedAnalytic H D n).source.F 0 =
      ev (Z.nodes (n + 1)).stage.displayed := by
  let I := preparedAnalytic H D n
  calc
    I.source.F 0 = front (sourceNode H Z n).stage.source 0 :=
      ConfiguredRecursiveEdgeRecostMultiplierPhaseNormalization.source_front_zero I
    _ = ev ((sourceNode H Z n).stage.source.selectedRearData 0) := by
      funext x
      exact ((sourceNode H Z n).stage.source.ev_selectedRearData 0 x).symm
    _ = ev (Z.nodes (n + 1)).stage.displayed :=
      (congrArg ev (D.geometry.displayed_eq_selected (n + 1))).symm

/-- The zero-time period is likewise the marked perimeter of the displayed
datum selected by the predecessor source. -/
theorem preparedAnalytic_source_period_zero_eq_displayed_perim
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (preparedAnalytic H D n).source.P 0 =
      perim (Z.nodes (n + 1)).stage.displayed := by
  let I := preparedAnalytic H D n
  calc
    I.source.P 0 = rearPeriod (sourceNode H Z n).stage.source 0 :=
      congrFun
        (ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input.source_period_eq I)
        0
    _ = perim ((sourceNode H Z n).stage.source.selectedRearData 0) :=
      ((sourceNode H Z n).stage.source.selectedRearData_perim 0).symm
    _ = perim (Z.nodes (n + 1)).stage.displayed :=
      (congrArg perim (D.geometry.displayed_eq_selected (n + 1))).symm

/-- Strongest unconditional source-start identity in terms of the retained
terminal front. -/
theorem preparedAnalytic_source_front_zero_eq_shift_terminalFront
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (preparedAnalytic H D n).source.F 0 =
      ev (MarkedShift.shiftData (preparedAnalyticInitialFrontPhase H D n)
        (Z.presented n).terminal.frontData) := by
  calc
    (preparedAnalytic H D n).source.F 0 =
        ev (Z.nodes (n + 1)).stage.displayed :=
      preparedAnalytic_source_front_zero_eq_displayed H D n
    _ = ev (MarkedShift.shiftData (preparedAnalyticInitialFrontPhase H D n)
          (Z.presented n).terminal.frontData) :=
      congrArg ev (preparedAnalytic_displayed_eq_shift_terminalFront H D n)

/-- Phase-composed source-start identity using only the preceding source's
canonical terminal unit-tangent datum. -/
theorem preparedAnalytic_source_front_zero_eq_shift_predecessorTerminal
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (preparedAnalytic H D n).source.F 0 =
      ev (MarkedShift.shiftData (preparedAnalyticInitialFrontPhase H D n)
        (unitTangentData (Z.nodes n).stage.source)) := by
  calc
    (preparedAnalytic H D n).source.F 0 =
        ev (Z.nodes (n + 1)).stage.displayed :=
      preparedAnalytic_source_front_zero_eq_displayed H D n
    _ = ev (MarkedShift.shiftData (preparedAnalyticInitialFrontPhase H D n)
          (unitTangentData (Z.nodes n).stage.source)) :=
      congrArg ev
        (preparedAnalytic_displayed_eq_shift_predecessorTerminal H D n)

/-- The following displayed datum has the intrinsic zero-floor tube witness
of the source that selected it. -/
theorem prepared_displayed_tube
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    IsTubeMember (rearPeriod (Z.nodes (n + 1)).stage.source 0) 0 0
      (Z.nodes (n + 1)).stage.displayed := by
  rw [D.geometry.displayed_eq_selected (n + 1)]
  exact MarkingAwareSource.selectedRearData_tube
    (Z.nodes (n + 1)).stage.source 0

/-- Complete marked front data of the prepared source at time zero are the
following displayed datum, not merely a curve with the same range. -/
theorem preparedAnalytic_frontData_zero_eq_displayed
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    MarkingAwareSource.frontData (preparedAnalytic H D n).source 0 =
      (Z.nodes (n + 1)).stage.displayed := by
  have hp := prepared_displayed_tube H D n
  have hpper : 0 < perim (Z.nodes (n + 1)).stage.displayed :=
    perim_pos ((Z.nodes (n + 1)).stage.source.rear_period_pos 0) hp
  have hcurve : ∀ u,
      (MarkingAwareSource.frontData
          (preparedAnalytic H D n).source 0).1 u =
        (Z.nodes (n + 1)).stage.displayed.1 u := by
    intro u
    change (preparedAnalytic H D n).source.F 0
      ((preparedAnalytic H D n).source.P 0 * u) =
        (Z.nodes (n + 1)).stage.displayed.1 u
    rw [preparedAnalytic_source_front_zero_eq_displayed H D n,
      preparedAnalytic_source_period_zero_eq_displayed_perim H D n, ev]
    rw [mul_div_cancel_left₀ u hpper.ne']
  have hcurveFun :
      (⇑(MarkingAwareSource.frontData
          (preparedAnalytic H D n).source 0).1) =
        (Z.nodes (n + 1)).stage.displayed.1 := funext hcurve
  have hvel : ∀ u,
      (MarkingAwareSource.frontData
          (preparedAnalytic H D n).source 0).2.1 u =
        (Z.nodes (n + 1)).stage.displayed.2.1 u := by
    intro u
    have hder : HasDerivAt
        (⇑(MarkingAwareSource.frontData
          (preparedAnalytic H D n).source 0).1)
        ((MarkingAwareSource.frontData
          (preparedAnalytic H D n).source 0).2.1 u) u := by
      change HasDerivAt
        (MarkingAwareSource.frontCurve
          (preparedAnalytic H D n).source 0)
        (MarkingAwareSource.frontVelocity
          (preparedAnalytic H D n).source 0 u) u
      exact MarkingAwareSource.frontCurve_deriv
        (preparedAnalytic H D n).source 0 u
    rw [hcurveFun] at hder
    exact hder.unique (hp.hasDerivAt_curve u)
  have hvelFun :
      (⇑(MarkingAwareSource.frontData
          (preparedAnalytic H D n).source 0).2.1) =
        (Z.nodes (n + 1)).stage.displayed.2.1 := funext hvel
  have hacc : ∀ u,
      (MarkingAwareSource.frontData
          (preparedAnalytic H D n).source 0).2.2 u =
        (Z.nodes (n + 1)).stage.displayed.2.2 u := by
    intro u
    have hder : HasDerivAt
        (⇑(MarkingAwareSource.frontData
          (preparedAnalytic H D n).source 0).2.1)
        ((MarkingAwareSource.frontData
          (preparedAnalytic H D n).source 0).2.2 u) u := by
      change HasDerivAt
        (MarkingAwareSource.frontVelocity
          (preparedAnalytic H D n).source 0)
        (MarkingAwareSource.frontAcceleration
          (preparedAnalytic H D n).source 0 u) u
      exact MarkingAwareSource.frontVelocity_deriv
        (preparedAnalytic H D n).source 0 u
    rw [hvelFun] at hder
    exact hder.unique (hp.hasDerivAt_vel u)
  apply Prod.ext
  · exact BoundedContinuousFunction.ext hcurve
  · apply Prod.ext
    · exact BoundedContinuousFunction.ext hvel
    · exact BoundedContinuousFunction.ext hacc

/-- The two intrinsic selected-inverse fronts agree after the retained inverse
terminal phase, as complete marked `Data`. -/
theorem preparedAnalytic_frontData_zero_eq_shift_predecessorTerminal
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    MarkingAwareSource.frontData (preparedAnalytic H D n).source 0 =
      MarkedShift.shiftData (preparedAnalyticInitialFrontPhase H D n)
        (MarkingAwareSource.frontData (Z.nodes n).stage.source
          (Z.pre H n).geometric.output.chosen.Delta.T) := by
  calc
    MarkingAwareSource.frontData (preparedAnalytic H D n).source 0 =
        (Z.nodes (n + 1)).stage.displayed :=
      preparedAnalytic_frontData_zero_eq_displayed H D n
    _ = MarkedShift.shiftData (preparedAnalyticInitialFrontPhase H D n)
          (Z.presented n).terminal.frontData :=
      preparedAnalytic_displayed_eq_shift_terminalFront H D n
    _ = MarkedShift.shiftData (preparedAnalyticInitialFrontPhase H D n)
          (unitTangentData (Z.nodes n).stage.source) :=
      congrArg (MarkedShift.shiftData
        (preparedAnalyticInitialFrontPhase H D n))
        (D.geometry.frontData_eq_source n)
    _ = MarkedShift.shiftData (preparedAnalyticInitialFrontPhase H D n)
          (MarkingAwareSource.frontData (Z.nodes n).stage.source
            (Z.pre H n).geometric.output.chosen.Delta.T) :=
      congrArg (MarkedShift.shiftData
        (preparedAnalyticInitialFrontPhase H D n))
        (predecessor_frontData_terminal_eq_unitTangentData H D n).symm

/-- The predecessor's associated terminal front inherits the following
displayed datum's positive-speed tube certificate. -/
theorem predecessor_frontData_terminal_tube
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    IsTubeMember (rearPeriod (Z.nodes (n + 1)).stage.source 0) 0 0
      (MarkingAwareSource.frontData (Z.nodes n).stage.source
        (Z.pre H n).geometric.output.chosen.Delta.T) := by
  rw [predecessor_frontData_terminal_eq_unitTangentData H D n,
    ← D.geometry.frontData_eq_source n,
    D.geometry.terminalFront_eq_phase n]
  exact MarkedShift.isTubeMember_shiftData
    (prepared_displayed_tube H D n) (D.geometry.terminalFrontPhase n)

/-- The common front used for uniqueness has a positive-speed tube witness. -/
theorem preparedAnalytic_frontData_zero_tube
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    IsTubeMember (rearPeriod (Z.nodes (n + 1)).stage.source 0) 0 0
      (MarkingAwareSource.frontData (preparedAnalytic H D n).source 0) := by
  rw [preparedAnalytic_frontData_zero_eq_displayed H D n]
  exact prepared_displayed_tube H D n

/-- A callback-free transported predecessor certificate over the prepared
source's exact time-zero front. -/
theorem preparedAnalytic_exists_initialPhase_certificate
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    ∃ phase : ℝ,
      SelectedInverseMap.IsMarkedSelectedInverse
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
        (MarkingAwareSource.frontData (preparedAnalytic H D n).source 0)
        (MarkedShift.shiftData phase (Z.pre H n).geometric.base) := by
  obtain ⟨phase, hphase⟩ :=
    transport_isMarkedSelectedInverse_shiftData
      ((Z.nodes (n + 1)).stage.source.rear_period_pos 0)
      (predecessor_frontData_terminal_tube H D n)
      ((Z.nodes n).stage.source.rear_period_pos
        (Z.pre H n).geometric.output.chosen.Delta.T)
      (MarkingAwareSource.selectedRearData_tube
        (Z.nodes n).stage.source
        (Z.pre H n).geometric.output.chosen.Delta.T)
      (MarkingAwareSource.isMarkedSelectedInverse_selectedRearData
        (Z.nodes n).stage.source
        (Z.pre H n).geometric.output.chosen.Delta.T)
      (preparedAnalyticInitialFrontPhase H D n)
  refine ⟨phase, ?_⟩
  simpa only [
    ← preparedAnalytic_frontData_zero_eq_shift_predecessorTerminal H D n,
    predecessor_selectedRearData_terminal_eq_base H D n] using hphase

/-- The rear phase selected by the transported predecessor certificate. -/
noncomputable def preparedAnalyticInitialPhase
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) : ℝ :=
  Classical.choose (preparedAnalytic_exists_initialPhase_certificate H D n)

theorem preparedAnalyticInitialPhase_certificate
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    SelectedInverseMap.IsMarkedSelectedInverse
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
      (MarkingAwareSource.frontData (preparedAnalytic H D n).source 0)
      (MarkedShift.shiftData (preparedAnalyticInitialPhase H D n)
        (Z.pre H n).geometric.base) :=
  Classical.choose_spec (preparedAnalytic_exists_initialPhase_certificate H D n)

/-- The prepared source's time-zero selected rear is a marked shift of the
retained predecessor base, with no hypotheses or callbacks. -/
theorem preparedAnalytic_selectedRearData_zero_eq_shift_base
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (preparedAnalytic H D n).source.selectedRearData 0 =
      MarkedShift.shiftData (preparedAnalyticInitialPhase H D n)
        (Z.pre H n).geometric.base := by
  exact SelectedInverseMap.IsMarkedSelectedInverse.unique
    ((Z.nodes (n + 1)).stage.source.rear_period_pos 0)
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one
    (preparedAnalytic_frontData_zero_tube H D n)
    (MarkingAwareSource.isMarkedSelectedInverse_selectedRearData
      (preparedAnalytic H D n).source 0)
    (preparedAnalyticInitialPhase_certificate H D n)

end ConfiguredRecursiveEdgeRecostFinitePreparedInitialPhase
