import UnitTangentIterates.ConfiguredGenericErrorScaledTransition
import UnitTangentIterates.ConfiguredGaugeJetDistortion

/-!
# Concrete gauge-jet specialization of the generic stable transition

The recursive stable scheme uses an arbitrary scalar error provider.  This
adapter keeps the concrete rich gauge output until after its terminal marking
jets have supplied the exact fixed-junction coefficients.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath

namespace ConfiguredGenericErrorJetScaledTransition

open ConfiguredApproximateDefectPathRowwise
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  NormalizedMarkingControlledJunction
  ArclengthScaledJacobiTransition
  AnchoredJacobiStableTransition
  ConfiguredGenericErrorScaledTransition
  GaugeFlowMarkedTerminalJets GaugeRearFamilyRichTerminalStage
  GaugeTerminalNearIdentityJets ConfiguredGaugeJetDistortion

/-- A concrete configured terminal flow, rather than an opaque jet callback,
supplies the exact near-identity coefficients of a generic-error affine
stage.  The two alignment equations are definitional for a rich stage before
it is forgotten into `RichStageData`. -/
theorem transition_of_terminalJets
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {e : ℕ → ℕ → ℝ} {c dlt : ℝ}
    {P1 G1 Cg C : ℕ → ℝ}
    {Q current : ℕ → Data} {k n : ℕ}
    (S : ColumnStep Q current e k (rowP0 D) P1 (fun _ => D.kstar)
      G1 Cg C c dlt)
    (I : AffineInput D S n)
    (frontC2 : C2NormalPathData (S.richStage (n + 1)).stage.increment)
    (hfront0 : Continuous (uncurry (S.richStage (n + 1)).stage.increment.eta))
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
    {p front : Data} {bound P0 kh khat M c' C' dlt' : ℝ}
    (R : RichStageOutput TJ p front bound P0 kh khat M c' C' dlt')
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
  have H := ConfiguredGenericErrorScaledTransition.transition D S I frontC2
    hfront0 hfront1 hfront2 hrear0 hrear1 hrear2 hC0 hPF hPR DB A
  simpa only [ee, controlledJunction] using H

end ConfiguredGenericErrorJetScaledTransition
