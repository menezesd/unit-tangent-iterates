import UnitTangentIterates.GaugeRearFamilyFromFront

/-!
# Intrinsic-bound selected-rear gauge construction

This sibling exposes the full from-front comparison theorem without assuming an
affine relation between the input path marking and the physical front
arclength.  The long proof only uses that relation to bound the intrinsic front
normal velocity, so the mathematically relevant hypothesis is stated directly.
The legacy affine theorem remains available in `GaugeRearFamilyFromFront`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeRearFamilyFromFrontIntrinsic

open GaugeRearFamilyFromFront
open GaugeFlowDerivCost GaugeFlowVariableSpeedPath NormalPathC2IncrementVariableSpeed
  RearFamilyFrame RearOwnArclength RearOwnTangential RearOwnTangentialCost
  UniformFrameBounds GaugeMarkedDataOfRearFamily GaugeRearFamilyFundamental
  RearOwnDriftFundamental RearTrack

variable {F Ydot : ℝ → ℝ → ℂ} {Θ δ K sf etaF alphaT kT gS : ℝ → ℝ → ℝ}
  {m P P' Kx Dd : ℝ → ℝ} {P0 khat d kx kh Qmax : ℝ}

theorem exists_variableSpeed_normalPath_of_rearFamily_from_front_with_eta_spatialC2_of_intrinsic_bound
    {p q : Data} (Γ : NormalPath p q)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hK : ∀ t s, |K t s| ≤ kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hFC : ContDiff ℝ 1 (uncurry F)) (hΘC : ContDiff ℝ 1 (uncurry Θ))
    (hδC : ContDiff ℝ 1 (uncurry δ)) (hsfC : ContDiff ℝ 1 (uncurry sf))
    (hPC : ContDiff ℝ 1 P) (hPd : ∀ t, HasDerivAt P (P' t) t)
    (Sxi : RearOwnFrameDrift.SpatialC2
      (frameTangential Ydot (rearOwnAngle Θ δ sf)))
    (Sen : RearOwnFrameDrift.SpatialC2
      (frameNormal Ydot (rearOwnAngle Θ δ sf)))
    (hCbd : ∀ t x, |Sxi.xi1 t x| ≤ rearKappa1 kh * m t)
    (hC2bd : ∀ t x, |Sxi.xi2 t x| ≤ rearKappa2 kh * m t)
    (hkC1 : ContDiff ℝ 1 (uncurry fun t x => Real.tan (δ t (sf t x))))
    -- the closing of the front, and the rear period
    (hδper : ∀ t, Function.Periodic (δ t) (P t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hQpos : ∀ t, 0 < rearArclength (δ t) (P t))
    (hQmax : ∀ t, rearArclength (δ t) (P t) ≤ Qmax)
    (hxi0 : ∀ t, frameTangential Ydot (rearOwnAngle Θ δ sf) t 0 = 0)
    -- the inverse Jacobi ODE of the rear normal rate
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hetaFbd : ∀ t s, |etaF t s| ≤ Γ.m t)
    (hkappa1 : rearKappa1 kh ≤ khat)
    (halphaT : ∀ t x, HasDerivAt (fun r => rearOwnAngle Θ δ sf r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => Real.tan (δ r (sf r x))) (kT t x) t)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (rearOwnAngle Θ δ sf r s : ℂ))) W t ∧
      HasDerivAt (fun x => (frameTangential Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ))
        + (frameNormal Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * (Complex.I * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ)))) W s)
    (hKxbd : ∀ t x, |(K t (sf t x) - Real.sin (δ t (sf t x)))
      / Real.cos (δ t (sf t x)) ^ 3| ≤ Kx t)
    (hKxnn : ∀ t, 0 ≤ Kx t) (hKxm : ∀ t, Kx t ≤ kx)
    (hkXc : Continuous (uncurry fun t x => (K t (sf t x) - Real.sin (δ t (sf t x)))
      / Real.cos (δ t (sf t x)) ^ 3))
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (rearArclength (δ t) (P t)),
      |frameTangential Ydot (rearOwnAngle Θ δ sf) t x|
        ≤ rearDriftConst Qmax kh * Γ.m t)
    (hgSd : ∀ t x, HasDerivAt (fun x' => etaF t (sf t x') / Real.cos (δ t (sf t x')))
      (gS t x) x)
    (hgSbd : ∀ t x, |gS t x| ≤ Dd t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hmc : Continuous m) (hm0 : ∀ t, 0 ≤ m t)
    (hmstop : ∀ t ∉ Ioo (0 : ℝ) Γ.T, m t = 0)
    (hmge : ∀ t, Γ.m t / Real.sqrt (1 - kh ^ 2) ≤ m t)
    (hnumA : 2 + 2 * khat * rearDriftConst Qmax kh ≤ 1 / P0)
    (hnumK : (d + 2) + khat ^ 2 + 2 * rearDriftConst Qmax kh * kx
      ≤ 1 / P0 ^ 2 + khat ^ 2) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      (∀ t, Phi t 0 = 0) ∧
      (∀ u t, HasDerivAt (fun s => Phi s u)
        (-frameTangential Ydot (rearOwnAngle Θ δ sf) t (Phi t u)) t) ∧
      (∀ a b : Data, (∀ u, rearOwn F Θ δ sf 0 (Phi 0 u) = a.1 u) →
        (∀ u, rearOwn F Θ δ sf Γ.T (Phi Γ.T u) = b.1 u) →
        (∀ t, ∀ j ≤ 2, MarkedTopology.supNorm
          (iteratedDeriv j (fun u => frameNormal Ydot (rearOwnAngle Θ δ sf) t (Phi t u)))
            ≤ m t) →
        ∃ Γ' : NormalPath a b, Γ'.T = Γ.T ∧
          (∀ t u, Γ'.X t u = rearOwn F Θ δ sf t (Phi t u)) ∧
          (∀ t u, Γ'.eta t u = frameNormal Ydot (rearOwnAngle Θ δ sf) t (Phi t u)) ∧
          (∀ t u, Phi t (u + 1) = Phi t u + rearArclength (δ t) (P t)) ∧
          (∃ phi1 phi2 : ℝ → ℝ → ℝ,
            (∀ t u, HasDerivAt (Phi t) (phi1 t u) u) ∧
            (∀ t u, HasDerivAt (phi1 t) (phi2 t u) u) ∧
            (∀ t, Continuous (phi1 t)) ∧ (∀ t, Continuous (phi2 t)) ∧
            (∀ t u, phi1 t u ≤ costP1 (rearArclength (δ 0) (P 0)) khat
              (∫ t in (0 : ℝ)..Γ.T, m t)) ∧
            (∀ t u, |phi2 t u| ≤ costG1 (rearArclength (δ 0) (P 0)) khat
              (rearKappa2 kh) (∫ t in (0 : ℝ)..Γ.T, m t))) ∧
          Γ'.m = m ∧
          cost Γ' = (∫ t in (0 : ℝ)..Γ.T, m t) ∧
          IsVariableSpeedNormalPath P0
            (costP1 (rearArclength (δ 0) (P 0)) khat (∫ t in (0 : ℝ)..Γ.T, m t)) khat
            (costG1 (rearArclength (δ 0) (P 0)) khat (rearKappa2 kh)
              (∫ t in (0 : ℝ)..Γ.T, m t))
            (khat * costG1 (rearArclength (δ 0) (P 0)) khat (rearKappa2 kh)
                (∫ t in (0 : ℝ)..Γ.T, m t)
              + rearKappa2 kh
                * costP1 (rearArclength (δ 0) (P 0)) khat
                  (∫ t in (0 : ℝ)..Γ.T, m t) ^ 2) Γ' ∧
          Nonempty (PathMetric.C2NormalPathData Γ')) ∧
      Nonempty (RetainedGaugeFrame Phi
        (fun t => rearArclength (δ t) (P t))
        (fun t => (∫ u in (0 : ℝ)..P t,
          SelectedChangeOfVariable.cosTimeDeriv δ
            (RearOwnHigherRegularity.partialTime δ) t u)
          + P' t * Real.cos (δ t (P t)))
        m (frameTangential Ydot (rearOwnAngle Θ δ sf))
        (rearKappa1 kh) (rearKappa2 kh)) := by
  have hδslice : ∀ t, Continuous (δ t) := fun t =>
    hδC.continuous.comp (continuous_const.prodMk continuous_id)
  have hQmax0 : 0 ≤ Qmax := le_trans (hQpos 0).le (hQmax 0)
  have hrnn : 0 ≤ rearDriftConst Qmax kh := rearDriftConst_nonneg hQmax0 hkh0 hkh1
  -- the closing of the slices and the turning of their tangent angle
  have hclose : ∀ t x, rearOwn F Θ δ sf t (x + rearArclength (δ t) (P t))
      = rearOwn F Θ δ sf t x := fun t x =>
    rearOwn_closing hkh0 hkh1 hδslice hstrip0 hstrip1 hδper hsfinv hFper hΘper t x
  have hangper : ∀ t x, rearOwnAngle Θ δ sf t (x + rearArclength (δ t) (P t))
      = rearOwnAngle Θ δ sf t x + 2 * Real.pi := fun t x =>
    RearOwnPathDistFrame.rearOwnAngle_shift hkh0 hkh1 hδslice hstrip0 hstrip1 hδper
      hsfinv hΘper t x
  -- the rear period moves differentiably, with no constraint on its derivative
  have hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r))
      ((∫ u in (0 : ℝ)..P t,
          SelectedChangeOfVariable.cosTimeDeriv δ (RearOwnHigherRegularity.partialTime δ) t u)
        + P' t * Real.cos (δ t (P t))) t := fun t =>
    SelInvDriftRigidity.hasDerivAt_rearPeriod hδC hPd t
  have hroot : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hroot1 : Real.sqrt (1 - kh ^ 2) ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
  have hcostle : ∀ t, Γ.m t ≤ m t := by
    intro t
    refine le_trans ?_ (hmge t)
    rw [le_div_iff₀ hroot]
    nlinarith [Γ.m_nonneg t]
  obtain ⟨Phi, hPhi0, hbase, hflow, hpair⟩ :=
    exists_variableSpeed_normalPath_of_rearFamily_fundamental_with_eta_spatialC2_of_intrinsic_bound
    (Q := fun t => rearArclength (δ t) (P t))
    (Q' := fun t => (∫ u in (0 : ℝ)..P t,
        SelectedChangeOfVariable.cosTimeDeriv δ (RearOwnHigherRegularity.partialTime δ) t u)
      + P' t * Real.cos (δ t (P t)))
    (Rb := fun t => rearDriftConst Qmax kh * Γ.m t) (r := rearDriftConst Qmax kh)
    (K := K) (etaF := etaF) (Kx := Kx) (Dd := Dd) (gS := gS)
    (alphaT := alphaT) (kT := kT) (m := m) (khat := khat) (d := d) (kx := kx)
    (P0 := P0) (kh := kh)
    Γ hkh0 hkh1 hstrip0 hstrip1 hK hF hΘ hsteer hsf hcos hYt hFC hΘC hδC hsfC
    Sxi Sen.continuous0 hCbd hC2bd hkC1 hQpos hQd hclose hangper hxi0 hjac
    hetaFbd
    hkappa1 halphaT hkT
    halphaTc hkTc halphaTS hmixed hKxbd hKxnn hKxm hkXc hRbd
    (fun t => mul_le_mul_of_nonneg_left (hcostle t) hrnn) hrnn
    hgSd hgSbd hDm hmc hm0 hmstop hmge hnumA hnumK
  refine ⟨Phi, hPhi0, hbase, hflow, ?_, hpair.2⟩
  intro a b hstart hfinish hsup
  obtain ⟨GammaR, hGammaT, hGammaX, hGammaEta, htrans,
    ⟨phi1, phi2, hphi1, hphi2, hphi1c, hphi2c, hphi1bd, hphi2bd⟩,
    hGammam, hGammacost, hGammavar⟩ := hpair.1 a b hstart hfinish hsup
  have hnormalPer : ∀ t, Function.Periodic
      (frameNormal Ydot (rearOwnAngle Θ δ sf) t) (rearArclength (δ t) (P t)) :=
    fun t => periodic_frameNormal_rearOwn hkh0 hkh1 hstrip0 hstrip1 hcos hF hΘ hsteer
      hsf hsfinv hδper hFper hΘper hFC hΘC hδC hsfC hPC hYt t
  let hframe : FrameNormalSpatialC2Certificate.Data
      (frameNormal Ydot (rearOwnAngle Θ δ sf)) Sen.xi1 Sen.xi2
      (fun t => rearArclength (δ t) (P t)) :=
    { normal_deriv := Sen.deriv1
      normal1_deriv := Sen.deriv2
      normal1_cont := fun t => Sen.continuous1.comp
        (continuous_const.prodMk continuous_id)
      normal2_cont := fun t => Sen.continuous2.comp
        (continuous_const.prodMk continuous_id)
      normal_periodic := hnormalPer }
  have hGammaC2 :=
    FrameNormalSpatialC2Certificate.c2NormalPathData_of_marked_frameNormal GammaR
      hframe hGammaEta hphi1 hphi2 hphi1c hphi2c htrans
  exact ⟨GammaR, hGammaT, hGammaX, hGammaEta, htrans,
    ⟨phi1, phi2, hphi1, hphi2, hphi1c, hphi2c, hphi1bd, hphi2bd⟩,
    hGammam, hGammacost, hGammavar, ⟨hGammaC2⟩⟩

end GaugeRearFamilyFromFrontIntrinsic
