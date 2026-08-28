import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometryCore

/-! # Marked terminal selected from the terminal rear curve -/

noncomputable section

set_option maxHeartbeats 1000000

open Function Set MarkedSpace PathMetric RearTrack RearOwnArclength ArclengthInverse

namespace FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront GaugeMarkedDataOfRearFamily

variable {a b : Data} {Gamma : NormalPath a b}
  {P0 kh khat Qmax : ℝ}

structure MarkedTerminal
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) where
  presented : Data
  dlt : ℝ
  dlt_pos : 0 < dlt
  period_eq : perim presented = terminalPeriod A
  carrier : ∀ x, presented.1 (x / perim presented) = terminalCurve A x
  tube : IsTubeMember (terminalPeriod A) 0 dlt presented
  oval : MainTheoremConditional.IsOval (ev presented)
  embedded : InjOn (ev presented) (Ico 0 (terminalPeriod A))

theorem MarkedTerminal.ev_eq
    {A : MarkingAwareSource Gamma P0 kh khat Qmax} (M : MarkedTerminal A) :
    ev M.presented = terminalCurve A :=
  funext M.carrier

structure OvalTubeRaw (Y : ℝ → ℂ) (kmin : ℝ) where
  q : Data
  L : ℝ
  dlt : ℝ
  L_pos : 0 < L
  dlt_pos : 0 < dlt
  tube : IsTubeMember L kmin dlt q
  perim_eq : perim q = L
  ev_eq : ev q = Y
  minimal : ∀ T, 0 < T → Periodic Y T → L ≤ T

theorem exists_ovalTubeRaw
    {Y : ℝ → ℂ} {th k : ℝ → ℝ} {kmin kmax : ℝ}
    (hoval : MainTheoremConditional.IsOval Y)
    (hY : ∀ s, HasDerivAt Y (Complex.exp (Complex.I * (th s : ℂ))) s)
    (hth : ∀ s, HasDerivAt th (k s) s) (hkc : Continuous k)
    (hkmin : ∀ s, kmin ≤ k s) (hkmax : ∀ s, k s ≤ kmax) :
    Nonempty (OvalTubeRaw Y kmin) := by
  obtain ⟨q, L, dlt, hLpos, hdltpos, htube, hqper, hevq, hminimal, -⟩ :=
    SelectedInverseTube.exists_tube_member_of_oval_data
      (Y := Y) (th := th) (k := k) (kmin := kmin) (kmax := kmax)
      hoval hY hth hkc hkmin hkmax
  exact ⟨{
    q := q
    L := L
    dlt := dlt
    L_pos := hLpos
    dlt_pos := hdltpos
    tube := htube
    perim_eq := hqper
    ev_eq := hevq
    minimal := hminimal
  }⟩

abbrev TerminalTubeRaw
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :=
  OvalTubeRaw (terminalCurve A) 0

theorem terminalCurvature_continuous
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    Continuous (terminalCurvature A) := by
  have hd : Continuous (A.delta Gamma.T) :=
    A.steering_contDiff.continuous.comp
      (continuous_const.prodMk continuous_id)
  have hsf : Continuous (A.sf Gamma.T) :=
    A.sf_contDiff.continuous.comp
      (continuous_const.prodMk continuous_id)
  rw [continuous_iff_continuousAt]
  intro x
  exact ((Real.continuousAt_tan.2
    (A.cos_ne_zero Gamma.T (A.sf Gamma.T x))).comp
      hd.continuousAt).comp hsf.continuousAt

theorem terminalCurvature_upper
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (x : ℝ) :
    terminalCurvature A x ≤ rearKappa1 kh :=
  (le_abs_self _).trans (terminalCurvature_bound A x)

theorem exists_terminalTubeRaw
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (hK0 : ∀ s, 0 ≤ A.K Gamma.T s) : Nonempty (TerminalTubeRaw A) := by
  exact exists_ovalTubeRaw
    (Y := terminalCurve A) (th := terminalAngle A) (k := terminalCurvature A)
    (kmin := 0) (kmax := rearKappa1 kh)
    (terminalCurve_oval A hK0)
    ((MarkingAwareSource.successorFrontCore A).front_frenet Gamma.T)
    ((MarkingAwareSource.successorFrontCore A).angle_frenet Gamma.T)
    (terminalCurvature_continuous A) (terminalCurvature_nonnegative A)
    (terminalCurvature_upper A)

noncomputable def TerminalTubeRaw.toMarked
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (R : TerminalTubeRaw A) (hK0 : ∀ s, 0 ≤ A.K Gamma.T s) :
    MarkedTerminal A := by
  have hYper : Periodic (terminalCurve A) (terminalPeriod A) :=
    (MarkingAwareSource.successorFrontCore A).front_periodic Gamma.T
  have hLle : R.L ≤ terminalPeriod A :=
    R.minimal (terminalPeriod A) (A.rear_period_pos Gamma.T) hYper
  have hQle : terminalPeriod A ≤ R.L := by
    by_contra hnot
    have hlt : R.L < terminalPeriod A := lt_of_not_ge hnot
    have h0 : (0 : ℝ) ∈ Ico 0 (terminalPeriod A) :=
      ⟨le_rfl, A.rear_period_pos Gamma.T⟩
    have hLm : R.L ∈ Ico 0 (terminalPeriod A) := ⟨R.L_pos.le, hlt⟩
    have hqL : ev R.q R.L = ev R.q 0 := by
      simpa [R.perim_eq] using (periodic_ev R.L_pos R.tube 0)
    have hYL : terminalCurve A R.L = terminalCurve A 0 := by
      calc
        terminalCurve A R.L = ev R.q R.L := (congrFun R.ev_eq R.L).symm
        _ = ev R.q 0 := hqL
        _ = terminalCurve A 0 := congrFun R.ev_eq 0
    exact R.L_pos.ne' (terminalCurve_embedded A hK0 hLm h0 hYL)
  have hLQ : R.L = terminalPeriod A := le_antisymm hLle hQle
  have hper : perim R.q = terminalPeriod A := R.perim_eq.trans hLQ
  have htubeQ : IsTubeMember (terminalPeriod A) 0 R.dlt R.q := by
    simpa [hLQ] using R.tube
  exact {
    presented := R.q
    dlt := R.dlt
    dlt_pos := R.dlt_pos
    period_eq := hper
    carrier := fun x ↦ congrFun R.ev_eq x
    tube := htubeQ
    oval := by rw [R.ev_eq]; exact terminalCurve_oval A hK0
    embedded := by rw [R.ev_eq]; exact terminalCurve_embedded A hK0
  }

theorem exists_markedTerminal
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (hK0 : ∀ s, 0 ≤ A.K Gamma.T s) : Nonempty (MarkedTerminal A) := by
  obtain ⟨R⟩ := exists_terminalTubeRaw A hK0
  exact ⟨R.toMarked hK0⟩

end FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
