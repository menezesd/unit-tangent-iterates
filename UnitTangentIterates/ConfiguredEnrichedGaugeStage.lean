import UnitTangentIterates.ConfiguredGenericErrorJetScaledTransition
import UnitTangentIterates.GaugeNormalPath

/-!
# Enriched configured gauge stages

This is the pre-erasure interface for the stable recursive construction.  It
retains the concrete terminal gauge jets, converts the long gauge theorem's
four density estimates to physical arclength scale, and packages the exact
near-identity component transition together with all recosting data.
-/

noncomputable section

open Function Set MeasureTheory MarkedTopology MarkedSpace PathMetric PathMetric.NormalPath

namespace ConfiguredEnrichedGaugeStage

open ConfiguredApproximateDefectPathRowwise
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  NormalizedMarkingControlledJunction
  ArclengthScaledJacobiTransition
  AnchoredJacobiStableTransition
  ConfiguredGenericErrorScaledTransition
  ConfiguredGenericErrorJetScaledTransition
  GaugeFlowMarkedTerminalJets GaugeRearFamilyRichTerminalStage
  GaugeTerminalNearIdentityJets ConfiguredGaugeJetDistortion

/-- Scalar inequalities which convert the normalized estimates exported by
`GaugeNormalPath` to one fixed physical set of Jacobi coefficients. -/
structure FixedDensityDomination
    (PF PR CW c0 c1 c2 C0 C1 C2 : ℝ) : Prop where
  PR_nonnegative : 0 ≤ PR
  C0_nonnegative : 0 ≤ C0
  C1_nonnegative : 0 ≤ C1
  C2_nonnegative : 0 ≤ C2
  w : PR * CW ≤ PF
  s0 : c0 ≤ C0 * PF
  s1w : c1 ≤ C1 * PF
  s1s : c1 ≤ C1
  s2w : c2 ≤ C2 * PF
  s2s : c2 ≤ C2

/-- The exact elementary conversion from the long gauge output to the
arclength-scaled density interface. -/
def physicalDensityBounds_of_flowed
    {front rear : ℝ → ℝ → ℝ}
    {PF PR CW c0 c1 c2 C0 C1 C2 : ℝ}
    (F : GaugeNormalPath.FlowedDensityBounds front rear CW c0 c1 c2)
    (H : FixedDensityDomination PF PR CW c0 c1 c2 C0 C1 C2) :
    DensityBounds PF PR front rear C0 C1 C2 where
  w t := by
    have hw0 : 0 ≤ ∫ u in (0 : ℝ)..1, |front t u| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)
    calc
      PR * (∫ u in (0 : ℝ)..1, |rear t u|) ≤
          PR * (CW * ∫ u in (0 : ℝ)..1, |front t u|) :=
        mul_le_mul_of_nonneg_left (F.w t) H.PR_nonnegative
      _ = (PR * CW) * ∫ u in (0 : ℝ)..1, |front t u| := by ring
      _ ≤ PF * ∫ u in (0 : ℝ)..1, |front t u| :=
        mul_le_mul_of_nonneg_right H.w hw0
  s0 t := by
    have hw0 : 0 ≤ ∫ u in (0 : ℝ)..1, |front t u| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)
    calc
      supNorm (rear t) ≤ c0 * ∫ u in (0 : ℝ)..1, |front t u| := F.s0 t
      _ ≤ (C0 * PF) * ∫ u in (0 : ℝ)..1, |front t u| :=
        mul_le_mul_of_nonneg_right H.s0 hw0
      _ = C0 * (PF * ∫ u in (0 : ℝ)..1, |front t u|) := by ring
  s1 t := by
    let w := ∫ u in (0 : ℝ)..1, |front t u|
    let s := supNorm (front t)
    have hw : 0 ≤ w := intervalIntegral.integral_nonneg zero_le_one
      (fun _ _ => abs_nonneg _)
    have hs : 0 ≤ s := supNorm_nonneg _
    calc
      supNorm (iteratedDeriv 1 (rear t)) ≤ c1 * (w + s) := F.s1 t
      _ = c1 * w + c1 * s := by ring
      _ ≤ (C1 * PF) * w + C1 * s := add_le_add
        (mul_le_mul_of_nonneg_right H.s1w hw)
        (mul_le_mul_of_nonneg_right H.s1s hs)
      _ = C1 * s + (C1 * PF) * w := by ring
  s2 t := by
    let w := ∫ u in (0 : ℝ)..1, |front t u|
    let s0 := supNorm (front t)
    let s1 := supNorm (iteratedDeriv 1 (front t))
    have hw : 0 ≤ w := intervalIntegral.integral_nonneg zero_le_one
      (fun _ _ => abs_nonneg _)
    have hs0 : 0 ≤ s0 := supNorm_nonneg _
    have hs1 : 0 ≤ s1 := supNorm_nonneg _
    calc
      supNorm (iteratedDeriv 2 (rear t)) ≤ c2 * (w + s0 + s1) := F.s2 t
      _ = c2 * w + c2 * s0 + c2 * s1 := by ring
      _ ≤ (C2 * PF) * w + C2 * s0 + C2 * s1 :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right H.s2w hw)
          (mul_le_mul_of_nonneg_right H.s2s hs0))
          (mul_le_mul_of_nonneg_right H.s2s hs1)
      _ = C2 * s0 + C2 * s1 + (C2 * PF) * w := by ring

/-- Every controlled fixed spatial junction canonically carries its `C²`
certificate; no additional analytic hypothesis is needed. -/
def reparamC2Certificate_of_junction
    {p q p' q' : Data} {Gamma : NormalPath p q}
    (hC2 : C2NormalPathData Gamma)
    (J : ReparamJunctionCertificate (p' := p') (q' := q') Gamma) :
    ReparamC2Certificate Gamma hC2 J where
  eta1 := fun t u => hC2.eta1 t (J.phi u) * J.phi1 u
  eta2 := fun t u => hC2.eta2 t (J.phi u) * J.phi1 u ^ 2 +
    hC2.eta1 t (J.phi u) * J.phi2 u
  eta_deriv := fun t u => (hC2.eta_deriv t (J.phi u)).comp u (J.phi_deriv u)
  eta1_deriv := by
    intro t u
    convert ((hC2.eta1_deriv t (J.phi u)).comp u (J.phi_deriv u)).mul
      (J.phi1_deriv u) using 1
    simp only [Function.comp_apply]
    ring
  eta1_cont := fun t => by
    have hphic : Continuous J.phi :=
      Differentiable.continuous fun u => (J.phi_deriv u).differentiableAt
    exact ((hC2.eta1_cont t).comp hphic).mul J.phi1_cont
  eta2_cont := fun t => by
    have hphic : Continuous J.phi :=
      Differentiable.continuous fun u => (J.phi_deriv u).differentiableAt
    exact (((hC2.eta2_cont t).comp hphic).mul (J.phi1_cont.pow 2)).add
      (((hC2.eta1_cont t).comp hphic).mul J.phi2_cont)
  eta1_bdd := fun t => ArclengthInverse.bddAbove_abs_of_periodic one_pos
    (by
      have hphic : Continuous J.phi :=
        Differentiable.continuous fun u => (J.phi_deriv u).differentiableAt
      exact ((hC2.eta1_cont t).comp hphic).mul J.phi1_cont)
    (by
      intro u
      change hC2.eta1 t (J.phi (u + 1)) * J.phi1 (u + 1) =
        hC2.eta1 t (J.phi u) * J.phi1 u
      rw [J.phi_add_one, hC2.eta1_periodic t, J.phi1_periodic])
  eta2_bdd := fun t => ArclengthInverse.bddAbove_abs_of_periodic one_pos
    (by
      have hphic : Continuous J.phi :=
        Differentiable.continuous fun u => (J.phi_deriv u).differentiableAt
      exact (((hC2.eta2_cont t).comp hphic).mul (J.phi1_cont.pow 2)).add
        (((hC2.eta1_cont t).comp hphic).mul J.phi2_cont))
    (by
      intro u
      change hC2.eta2 t (J.phi (u + 1)) * J.phi1 (u + 1) ^ 2 +
          hC2.eta1 t (J.phi (u + 1)) * J.phi2 (u + 1) =
        hC2.eta2 t (J.phi u) * J.phi1 u ^ 2 +
          hC2.eta1 t (J.phi u) * J.phi2 u
      rw [J.phi_add_one, hC2.eta2_periodic t, J.phi1_periodic,
        hC2.eta1_periodic t, J.phi2_periodic])
  eta_periodic := fun t u => by
    change Gamma.eta t (J.phi (u + 1)) = Gamma.eta t (J.phi u)
    rw [J.phi_add_one, hC2.eta_periodic t]
  eta1_periodic := fun t u => by
    change hC2.eta1 t (J.phi (u + 1)) * J.phi1 (u + 1) =
      hC2.eta1 t (J.phi u) * J.phi1 u
    rw [J.phi_add_one, hC2.eta1_periodic t, J.phi1_periodic]
  eta2_periodic := fun t u => by
    change hC2.eta2 t (J.phi (u + 1)) * J.phi1 (u + 1) ^ 2 +
        hC2.eta1 t (J.phi (u + 1)) * J.phi2 (u + 1) =
      hC2.eta2 t (J.phi u) * J.phi1 u ^ 2 +
        hC2.eta1 t (J.phi u) * J.phi2 u
    rw [J.phi_add_one, hC2.eta2_periodic t, J.phi1_periodic,
      hC2.eta1_periodic t, J.phi2_periodic]
  eta1_formula := fun _ _ => rfl
  eta2_formula := fun _ _ => rfl

/-- A mapped path before it is recosted and forgotten into the generic rich
column.  These are exactly the fields needed by canonical recosting and the
depth-uniform component induction. -/
structure Output
    {pf qf pr qr : Data} (front : NormalPath pf qf) (rear : NormalPath pr qr)
    (frontL rearL e C0 C1 C2 : ℝ) where
  rear_time_one : rear.T = 1
  rearC2 : C2NormalPathData rear
  rear_eta_continuous : Continuous (uncurry rear.eta)
  rear_eta1_continuous : Continuous (uncurry rearC2.eta1)
  rear_eta2_continuous : Continuous (uncurry rearC2.eta2)
  rear_perim_one : 1 ≤ rearL
  transition : Transition (physicalComponents frontL front.eta)
    (physicalComponents rearL rear.eta)
    (1 / (1 - e)) (1 + e) e C0 C1 C2

/-- Construct the complete pre-erasure stage package from the actual long
gauge output and actual terminal flow jets. -/
def output_of_flowed_terminalJets
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {err : ℕ → ℕ → ℝ} {c dlt : ℝ}
    {P1 G1 Cg C : ℕ → ℝ}
    {Q current : ℕ → Data} {k n : ℕ}
    (S : ColumnStep Q current err k (rowP0 D) P1 (fun _ => D.kstar)
      G1 Cg C c dlt)
    (I : AffineInput D S n)
    (frontC2 : C2NormalPathData (S.richStage (n + 1)).stage.increment)
    (hfront0 : Continuous (uncurry (S.richStage (n + 1)).stage.increment.eta))
    (hfront1 : Continuous (uncurry frontC2.eta1))
    (hfront2 : Continuous (uncurry frontC2.eta2))
    (hrear0 : Continuous (uncurry I.affinePath.eta))
    (hrear1 : Continuous (uncurry I.affineC2.eta1))
    (hrear2 : Continuous (uncurry I.affineC2.eta2))
    (hrearT : I.affinePath.T = 1)
    {C0 C1 C2 CW c0 c1 c2 : ℝ}
    (hPF : 0 ≤ perim (S.richStage (n + 1)).terminalBase)
    (hPR1 : 1 ≤ perim I.terminalBase)
    (F : GaugeNormalPath.FlowedDensityBounds
      (S.richStage (n + 1)).stage.increment.eta I.affinePath.eta
      CW c0 c1 c2)
    (HD : FixedDensityDomination
      (perim (S.richStage (n + 1)).terminalBase) (perim I.terminalBase)
      CW c0 c1 c2 C0 C1 C2)
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {ell L T : ℝ} {base : Data}
    (TJ : TerminalJets xi xiX xiXX Phi ell L T base)
    {p frontData : Data} {bound P0 kh khat M c' C' dlt' : ℝ}
    (R : RichStageOutput TJ p frontData bound P0 kh khat M c' C' dlt')
    (hdpsi : ∀ u, (S.richStage n).marking.marking.dpsi u =
      R.marking.dpsi u)
    (hddpsi : ∀ u, (S.richStage n).marking.ddpsi u = R.ddpsi u)
    {m : ℝ → ℝ} {kappa kappa2 Mcap Cjet : ℝ}
    (hell : 0 < ell) (hL : 0 < L) (hT : 0 ≤ T)
    (hm : Continuous m) (hm0 : ∀ t, 0 ≤ m t)
    (hxiX : ∀ t x, |-(xiX t x)| ≤ kappa * m t)
    (hxiXX : ∀ t x, |-(xiXX t x)| ≤ kappa2 * m t)
    (hkappa : 0 ≤ kappa) (hkappa2 : 0 ≤ kappa2)
    (hcost : (∫ t in (0 : ℝ)..T, m t) ≤ rowDefect D (n + k))
    (hcap : rowDefect D (n + k) ≤ Mcap)
    (hCjet : jetLinearConst ell L kappa kappa2 Mcap ≤ Cjet)
    (he : eps D Cjet n k ≤ 1 / 2) :
    PSigma fun A : ControlledAnchoringBounds (S.richStage n).marking
        (1 - eps D Cjet n k) (1 + eps D Cjet n k) (eps D Cjet n k) =>
      let hstart : ∀ u,
          I.affinePath.X 0 ((S.richStage n).marking.marking.psi u) =
            (S.next n).1 u := fun u => by
              rw [I.affinePath.start]
              exact ((S.richStage n).marking.marking.position u).symm
      let J := controlledJunction I.affinePath (S.richStage n).marking A
        hstart I.finish
      Output (S.richStage (n + 1)).stage.increment
        (reparamAtJunction I.affinePath I.affineC2 J)
        (perim (S.richStage (n + 1)).terminalBase) (perim I.terminalBase)
        (eps D Cjet n k) C0 C1 C2 := by
  let DB := physicalDensityBounds_of_flowed F HD
  let JB : JetBounds TJ R (eps D Cjet n k) :=
    configured_stage_jetBounds D TJ R hell hL hT hm hm0 hxiX hxiXX
      hkappa hkappa2 hcost hcap hCjet
  let ee := eps D Cjet n k
  let A : ControlledAnchoringBounds (S.richStage n).marking
      (1 - ee) (1 + ee) ee :=
    { m_pos := by linarith [JB.eps_nonnegative]
      M_nonneg := by linarith [JB.eps_nonnegative]
      N_nonneg := JB.eps_nonnegative
      lower := fun u => by
        have hneg := neg_le_of_abs_le (JB.dpsi u)
        rw [hdpsi u]
        linarith
      upper := fun u => by
        rw [hdpsi u]
        calc
          |R.marking.dpsi u| = |(R.marking.dpsi u - 1) + 1| := by ring_nf
          _ ≤ |R.marking.dpsi u - 1| + |(1 : ℝ)| := abs_add_le _ _
          _ ≤ ee + 1 := by simpa [ee] using add_le_add_right (JB.dpsi u) 1
          _ = 1 + ee := by ring
      second := fun u => by
        rw [hddpsi u]
        exact JB.ddpsi u }
  refine ⟨A, ?_⟩
  dsimp only
  let hstart : ∀ u,
      I.affinePath.X 0 ((S.richStage n).marking.marking.psi u) =
        (S.next n).1 u := fun u => by
    rw [I.affinePath.start]
    exact ((S.richStage n).marking.marking.position u).symm
  let J := controlledJunction I.affinePath (S.richStage n).marking A
    hstart I.finish
  let RC := reparamC2Certificate_of_junction I.affineC2 J
  let rearC2 := c2NormalPathData_reparamAtJunction I.affineC2 J RC
  have hphic : Continuous J.phi :=
    Differentiable.continuous fun u => (J.phi_deriv u).differentiableAt
  have hpair : Continuous (fun z : ℝ × ℝ => (z.1, J.phi z.2)) :=
    continuous_fst.prodMk (hphic.comp continuous_snd)
  have hc0 : Continuous
      (uncurry (reparamAtJunction I.affinePath I.affineC2 J).eta) := by
    simpa [reparamAtJunction, NormalPath.reparamSpace] using hrear0.comp hpair
  have hc1 : Continuous (uncurry rearC2.eta1) := by
    exact (hrear1.comp hpair).mul (J.phi1_cont.comp continuous_snd)
  have hc2 : Continuous (uncurry rearC2.eta2) := by
    exact ((hrear2.comp hpair).mul ((J.phi1_cont.comp continuous_snd).pow 2)).add
      ((hrear1.comp hpair).mul (J.phi2_cont.comp continuous_snd))
  have htransition := ConfiguredGenericErrorScaledTransition.transition D S I
    frontC2 hfront0 hfront1 hfront2 hrear0 hrear1 hrear2
    HD.C0_nonnegative hPF (le_trans zero_le_one hPR1) DB A
  refine
    { rear_time_one := by
        exact hrearT
      rearC2 := rearC2
      rear_eta_continuous := hc0
      rear_eta1_continuous := hc1
      rear_eta2_continuous := hc2
      rear_perim_one := hPR1
      transition := by simpa only [ee, controlledJunction] using htransition }

end ConfiguredEnrichedGaugeStage
