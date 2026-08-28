import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear

/-!
# Chosen-flow jet bounds from an intrinsic period floor

The all-time gauge-flow estimate does not use affine source alignment.  Its
only use of `SeparatedFacts` was to obtain a positive uniform lower bound for
the rear period.  This module states that estimate with the lower bound as an
explicit hypothesis, so it applies to reachable nonaffine recost sources.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric FlowDerivative
  GaugeFlowTimeDerivative RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction
  GaugeMarkedDataOfRearFamily
  GaugeTerminalNearIdentityJets
  MarkingFlowDefectC2

variable {p q a b : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}

/-- Exact nonlinear jet error with an arbitrary genuine rear-period floor. -/
def floorJetError (A : MarkingAwareSource Gamma P0 kh khat Qmax) (L : ℝ) : ℝ :=
  jetError (rearPeriod A 0) L
    (rearKappa1 kh * sourceMass A) (rearKappa2 kh * sourceMass A)

/-- Linear coefficient corresponding to the same explicit period floor. -/
def floorJetLinearConst
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (L M : ℝ) : ℝ :=
  jetLinearConst (rearPeriod A 0) L (rearKappa1 kh) (rearKappa2 kh) M

/-- Uniform chosen-flow jets from a positive intrinsic period floor.  No
affine identity between `Gamma.eta` and `A.etaF` occurs in the proof. -/
def normalizedJetBounds_of_flow_floor
    (W : ChosenPath Gamma A E.Phi a b) {L : ℝ}
    (hL : 0 < L) (hfloor : ∀ t, L ≤ rearPeriod A t)
    (hunit : Gamma.T = 1) : NormalizedJetBounds W (floorJetError A L) := by
  let D := E.frame.frame
  let hx := GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1
  let hxx := GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2
  let ell := rearPeriod A 0
  let M := sourceMass A
  let c0 := rearKappa1 kh * M
  let c2 := rearKappa2 kh * M
  have hell : 0 < ell := A.rear_period_pos 0
  have hM : 0 ≤ M := sourceMass_nonnegative A
  have hk1 : 0 ≤ rearKappa1 kh := rearKappa1_nonneg A.kh_nonnegative A.kh_lt_one
  have hk2 : 0 ≤ rearKappa2 kh := rearKappa2_nonneg A.kh_nonnegative A.kh_lt_one
  have hc0 : 0 ≤ c0 := mul_nonneg hk1 hM
  have hc2 : 0 ≤ c2 := mul_nonneg hk2 hM
  have hC0 : Continuous (fun t ↦ rearKappa1 kh * A.m t) :=
    continuous_const.mul A.density_continuous
  have hC2 : Continuous (fun t ↦ rearKappa2 kh * A.m t) :=
    continuous_const.mul A.density_continuous
  have hrate1 : ∀ t x, |hx t x| ≤ rearKappa1 kh * A.m t := by
    intro t x
    exact E.frame.rate1_bound t x
  have hrate2 : ∀ t x, |hxx t x| ≤ rearKappa2 kh * A.m t := by
    intro t x
    exact E.frame.rate2_bound t x
  have hLglobal : 0 ≤ D.rateLip :=
    (abs_nonneg (hx 0 0)).trans (D.hrate1 0 0)
  obtain ⟨hlip, hcont, hxd, hxcont, hxxd, hxxcont, hxxbd⟩ :=
    GaugeRate.gaugeRate_flow_hypotheses_of_bounds hLglobal D.hxi D.hxi1
      D.hv D.hv1 D.hvne D.hxic D.hxi1c D.hxi2c D.hvc D.hv1c
      D.hv2c D.hrate1 D.hrate2
  have hphi1 (t u : ℝ) :
      W.phi1 t u = flowDeriv hx E.Phi ell t u := by
    exact (W.phi1_deriv t u).unique
      (hasDerivAt_flow_initial hlip hcont E.frame.flow hell
        E.frame.initial hxd u t)
  have hphi1fun (t : ℝ) : W.phi1 t = flowDeriv hx E.Phi ell t :=
    funext (hphi1 t)
  have hphi2 (t u : ℝ) :
      W.phi2 t u = flowDeriv2 hx hxx E.Phi ell t u := by
    have hw := W.phi2_deriv t u
    rw [hphi1fun t] at hw
    exact hw.unique
      (hasDerivAt_flowDeriv hlip hcont E.frame.flow hell E.frame.initial
        hxd hxcont hxxd hxxcont hxxbd u t)
  have hprefix (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ∫ s in (0 : ℝ)..t, A.m s ≤ M := by
    have htT : t ≤ Gamma.T := by simpa [hunit] using ht.2
    exact intervalIntegral.integral_mono_interval le_rfl ht.1 htT
      (Filter.Eventually.of_forall fun s ↦ A.density_nonnegative s)
      (A.density_continuous.intervalIntegrable 0 Gamma.T)
  have hprefix0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫ s in (0 : ℝ)..t, rearKappa1 kh * A.m s) ≤ c0 := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hprefix t ht) hk1
  have hprefix2 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫ s in (0 : ℝ)..t, rearKappa2 kh * A.m s) ≤ c2 := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hprefix t ht) hk2
  have hprefix2_nonnegative (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      0 ≤ ∫ s in (0 : ℝ)..t, rearKappa2 kh * A.m s :=
    intervalIntegral.integral_nonneg ht.1 fun s _ ↦
      mul_nonneg hk2 (A.density_nonnegative s)
  have hperiod (t : ℝ) : E.Phi t 1 - E.Phi t 0 = rearPeriod A t := by
    have hs := W.shift t 0
    rw [E.base t] at hs
    rw [E.base t]
    simpa using hs
  refine
    { eps_nonnegative := jetError_nonnegative hell.le hL hc0 hc2
      dpsi := ?_
      ddpsi := ?_ }
  · intro t ht u
    have hspace : ∀ v, HasDerivAt (fun v' ↦ E.Phi t v')
        (flowDeriv hx E.Phi ell t v) v := fun v ↦
      hasDerivAt_flow_initial hlip hcont E.frame.flow hell E.frame.initial
        hxd v t
    have hraw := abs_flowDeriv_sub_period_le_int
      (hx := hx) (Phi := E.Phi) hell hrate1 hC0 ht.1 hspace u
    rw [hperiod t, ← hphi1 t u] at hraw
    have hdefect : |W.phi1 t u - rearPeriod A t| ≤
        flowDefectC1Int ell c0 :=
      hraw.trans (flowDefectC1Int_mono hell.le (hprefix0 t ht))
    have hdefect0 : 0 ≤ flowDefectC1Int ell c0 :=
      flowDefectC1Int_nonneg hell.le hc0
    have hRt : 0 < rearPeriod A t := A.rear_period_pos t
    have hdiv : W.phi1 t u / rearPeriod A t - 1 =
        (W.phi1 t u - rearPeriod A t) / rearPeriod A t := by
      field_simp
    calc
      |normalizedPsi1 W t u - 1| =
          |W.phi1 t u - rearPeriod A t| / rearPeriod A t := by
        rw [normalizedPsi1, hdiv, abs_div, abs_of_pos hRt]
      _ ≤ flowDefectC1Int ell c0 / rearPeriod A t :=
        div_le_div_of_nonneg_right hdefect hRt.le
      _ ≤ flowDefectC1Int ell c0 / L :=
        div_le_div_of_nonneg_left hdefect0 hL (hfloor t)
      _ ≤ floorJetError A L := le_max_left _ _
  · intro t ht u
    have hraw := abs_flowDeriv_deriv_le_int
      (hx := hx) (hxx := hxx) (Phi := E.Phi) hell
      hrate1 hC0 hrate2 hC2 ht.1 u
    have hraw' : |W.phi2 t u| ≤ flowDefectC2Int ell
        (∫ s in (0 : ℝ)..t, rearKappa1 kh * A.m s)
        (∫ s in (0 : ℝ)..t, rearKappa2 kh * A.m s) := by
      simpa [hphi2, flowDeriv2] using hraw
    have hdefect := hraw'.trans
      (flowDefectC2Int_mono (ell := ell) (hprefix2_nonnegative t ht)
        (hprefix0 t ht) (hprefix2 t ht))
    have hdefect0 : 0 ≤ flowDefectC2Int ell c0 c2 := by
      dsimp [flowDefectC2Int]
      positivity
    have hRt : 0 < rearPeriod A t := A.rear_period_pos t
    calc
      |normalizedPsi2 W t u| = |W.phi2 t u| / rearPeriod A t := by
        rw [normalizedPsi2, abs_div, abs_of_pos hRt]
      _ ≤ flowDefectC2Int ell c0 c2 / rearPeriod A t :=
        div_le_div_of_nonneg_right hdefect hRt.le
      _ ≤ flowDefectC2Int ell c0 c2 / L :=
        div_le_div_of_nonneg_left hdefect0 hL (hfloor t)
      _ ≤ floorJetError A L := le_max_right _ _

theorem floorJetError_le_linear
    {L M : ℝ} (hL : 0 < L) (hM : sourceMass A ≤ M) :
    floorJetError A L ≤ floorJetLinearConst A L M * sourceMass A := by
  exact jetError_le_linear (A.rear_period_pos 0).le hL
    (rearKappa1_nonneg A.kh_nonnegative A.kh_lt_one)
    (rearKappa2_nonneg A.kh_nonnegative A.kh_lt_one)
    (sourceMass_nonnegative A) hM

/-- Linear all-time chosen jets for a reachable nonaffine source. -/
def normalizedJetBounds_linear_floor
    (W : ChosenPath Gamma A E.Phi a b) {L M : ℝ}
    (hL : 0 < L) (hfloor : ∀ t, L ≤ rearPeriod A t)
    (hunit : Gamma.T = 1) (hM : sourceMass A ≤ M) :
    NormalizedJetBounds W (floorJetLinearConst A L M * sourceMass A) :=
  normalizedJetBounds_mono
    (normalizedJetBounds_of_flow_floor W hL hfloor hunit)
    (floorJetError_le_linear hL hM)

/-- Configured period-one specialization. -/
def normalizedJetBounds_linear_one
    (W : ChosenPath Gamma A E.Phi a b) {M : ℝ}
    (hfloor : ∀ t, 1 ≤ rearPeriod A t)
    (hunit : Gamma.T = 1) (hM : sourceMass A ≤ M) :
    NormalizedJetBounds W (floorJetLinearConst A 1 M * sourceMass A) :=
  normalizedJetBounds_linear_floor W (by norm_num) hfloor hunit hM

end FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds
