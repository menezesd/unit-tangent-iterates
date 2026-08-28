import UnitTangentIterates.ArclengthScaledJacobiTransition
import UnitTangentIterates.ConfiguredRichMapStageProvider
import UnitTangentIterates.ConfiguredGaugeJetDistortion

/-!
# Physical-component transition for an actual configured affine gauge stage

This adapter applies the arclength-scaled Jacobi theorem to the precise
controlled junction used by `ConfiguredRichMapStageProvider.provider`.
-/

noncomputable section

open Function Set MarkedSpace PathMetric PathMetric.NormalPath

namespace ConfiguredAffineGaugeScaledTransition

open ConfiguredRichMapStageProvider
  ConfiguredApproximateDefectPathRowwise
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  NormalizedMarkingControlledJunction
  ArclengthScaledJacobiTransition
  AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds
  GaugeFlowMarkedTerminalJets GaugeRearFamilyRichTerminalStage
  GaugeTerminalNearIdentityJets ConfiguredGaugeJetDistortion

/-- The actual affine gauge image gives a paper-faithful physical-component
transition after its initial marking is anchored to the preceding rich stage.
All functional integrability is derived from joint `C²` continuity. -/
theorem transition
    (D : ConstructedConfiguredSequenceWeighted.Data) {kh mA MA NA c dlt : ℝ}
    {rawP1 rawG1 rawCg C : ℕ → ℝ}
    {Q current : ℕ → Data} {k n : ℕ}
    (S : ColumnStep Q current
      (ConfiguredRowDefectProvider.error D (K kh mA MA NA)) k
      (rowP0 D) (mapP1 D rawP1 MA) (fun _ ↦ D.kstar)
      (mapG1 D rawP1 rawG1 MA NA) (mapCg D rawP1 rawCg MA NA) C c dlt)
    (I : AffineGaugeImage D rawP1 rawG1 rawCg C S n)
    (frontC2 : C2NormalPathData (S.richStage (n + 1)).stage.increment)
    (hfront0 : Continuous
      (uncurry (S.richStage (n + 1)).stage.increment.eta))
    (hfront1 : Continuous (uncurry frontC2.eta1))
    (hfront2 : Continuous (uncurry frontC2.eta2))
    (hrear0 : Continuous (uncurry I.affinePath.eta))
    (hrear1 : Continuous (uncurry I.affineC2.eta1))
    (hrear2 : Continuous (uncurry I.affineC2.eta2))
    {C0 C1 C2 : ℝ} (hC0 : 0 ≤ C0)
    (hPF : 0 ≤ perim (S.richStage (n + 1)).terminalBase)
    (hPR : 0 ≤ perim I.terminalBase)
    (B : DensityBounds
      (perim (S.richStage (n + 1)).terminalBase) (perim I.terminalBase)
      (S.richStage (n + 1)).stage.increment.eta I.affinePath.eta C0 C1 C2)
    {jm jM jN : ℝ}
    (A : ControlledAnchoringBounds (S.richStage n).marking jm jM jN) :
    let hstart : ∀ u,
        I.affinePath.X 0 ((S.richStage n).marking.marking.psi u) =
          (S.next n).1 u := fun u => by
          rw [I.affinePath.start]
          exact ((S.richStage n).marking.marking.position u).symm
    let J := controlledJunction I.affinePath (S.richStage n).marking A
      hstart I.finish
    Transition
      (physicalComponents (perim (S.richStage (n + 1)).terminalBase)
        (S.richStage (n + 1)).stage.increment.eta)
      (physicalComponents (perim I.terminalBase)
        (reparamAtJunction I.affinePath I.affineC2 J).eta)
      (1 / J.m) J.M J.N C0 C1 C2 := by
  dsimp only
  let hstart : ∀ u,
      I.affinePath.X 0 ((S.richStage n).marking.marking.psi u) =
        (S.next n).1 u := fun u => by
    rw [I.affinePath.start]
    exact ((S.richStage n).marking.marking.position u).symm
  let J := controlledJunction I.affinePath (S.richStage n).marking A
    hstart I.finish
  let hraw : AnalyticInput
      (perim (S.richStage (n + 1)).terminalBase) (perim I.terminalBase)
      (S.richStage (n + 1)).stage.increment.eta I.affinePath.eta C0 C1 C2 :=
    AnalyticInput.of_jointC2_densityBounds frontC2 I.affineC2
      hfront0 hfront1 hfront2 hrear0 hrear1 hrear2 hPF hC0 B
  let hsource : FunctionalIntegrable I.affinePath.eta :=
    PeriodicSupNormFunctionalIntegrable.functionalIntegrable_of_jointC2
      I.affineC2 hrear0 hrear1 hrear2
  let htarget : FunctionalIntegrable
      (reparamAtJunction I.affinePath I.affineC2 J).eta := by
    exact PeriodicSupNormFunctionalIntegrable.functionalIntegrable_comp_of_jointC2
      I.affineC2 hrear0 hrear1 hrear2 J.phi_deriv J.phi1_deriv
      J.phi1_cont J.phi2_cont J.phi_add_one J.phi1_periodic J.phi2_periodic
  exact transition_of_raw_and_junction I.affinePath I.affineC2 J hPR
    hraw hsource htarget

/-- The configured terminal flow supplies the junction coefficients used by
the physical-component transition.  The only alignment data are the two
definitional jet identities lost when a rich gauge stage is stored in the
generic `ColumnStep`; no jet or anchoring estimate is assumed. -/
theorem transition_of_configured_terminalJets
    (D : ConstructedConfiguredSequenceWeighted.Data) {kh mA MA NA c dlt : ℝ}
    {rawP1 rawG1 rawCg C : ℕ → ℝ}
    {Q current : ℕ → Data} {k n : ℕ}
    (S : ColumnStep Q current
      (ConfiguredRowDefectProvider.error D (K kh mA MA NA)) k
      (rowP0 D) (mapP1 D rawP1 MA) (fun _ ↦ D.kstar)
      (mapG1 D rawP1 rawG1 MA NA) (mapCg D rawP1 rawCg MA NA) C c dlt)
    (I : AffineGaugeImage D rawP1 rawG1 rawCg C S n)
    (frontC2 : C2NormalPathData (S.richStage (n + 1)).stage.increment)
    (hfront0 : Continuous
      (uncurry (S.richStage (n + 1)).stage.increment.eta))
    (hfront1 : Continuous (uncurry frontC2.eta1))
    (hfront2 : Continuous (uncurry frontC2.eta2))
    (hrear0 : Continuous (uncurry I.affinePath.eta))
    (hrear1 : Continuous (uncurry I.affineC2.eta1))
    (hrear2 : Continuous (uncurry I.affineC2.eta2))
    {C0 C1 C2 : ℝ} (hC0 : 0 ≤ C0)
    (hPF : 0 ≤ perim (S.richStage (n + 1)).terminalBase)
    (hPR : 0 ≤ perim I.terminalBase)
    (DB : DensityBounds
      (perim (S.richStage (n + 1)).terminalBase) (perim I.terminalBase)
      (S.richStage (n + 1)).stage.increment.eta I.affinePath.eta C0 C1 C2)
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {ell L T : ℝ} {base : Data}
    (TJ : TerminalJets xi xiX xiXX Phi ell L T base)
    {p front : Data} {bound P0 kh' khat M c' C' dlt' : ℝ}
    (R : RichStageOutput TJ p front bound P0 kh' khat M c' C' dlt')
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
    ∃ A : ControlledAnchoringBounds (S.richStage n).marking
        (1 - eps D Cjet n k) (1 + eps D Cjet n k) (eps D Cjet n k),
      let hstart : ∀ u,
          I.affinePath.X 0 ((S.richStage n).marking.marking.psi u) =
            (S.next n).1 u := fun u => by
              rw [I.affinePath.start]
              exact ((S.richStage n).marking.marking.position u).symm
      let J := controlledJunction I.affinePath (S.richStage n).marking A
        hstart I.finish
      Transition
        (physicalComponents (perim (S.richStage (n + 1)).terminalBase)
          (S.richStage (n + 1)).stage.increment.eta)
        (physicalComponents (perim I.terminalBase)
          (reparamAtJunction I.affinePath I.affineC2 J).eta)
        (1 / (1 - eps D Cjet n k)) (1 + eps D Cjet n k)
        (eps D Cjet n k) C0 C1 C2 := by
  let JB : JetBounds TJ R (eps D Cjet n k) :=
    configured_stage_jetBounds D TJ R hell hL hT hm hm0 hxiX hxiXX
      hkappa hkappa2 hcost hcap hCjet
  let e := eps D Cjet n k
  let A : ControlledAnchoringBounds (S.richStage n).marking
      (1 - e) (1 + e) e :=
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
          _ ≤ e + 1 := by simpa [e] using add_le_add_right (JB.dpsi u) 1
          _ = 1 + e := by ring
      second := fun u => by
        rw [hddpsi u]
        exact JB.ddpsi u }
  refine ⟨A, ?_⟩
  have htransition := transition D S I frontC2 hfront0 hfront1 hfront2
    hrear0 hrear1 hrear2 hC0 hPF hPR DB A
  simpa only [e, controlledJunction] using htransition

end ConfiguredAffineGaugeScaledTransition
