import UnitTangentIterates.GaugeRearFamilyRichTerminalStage
import UnitTangentIterates.GaugeRearFamilySeparatedContinuation

/-! Rich terminal stages retaining the correlated separated path certificate. -/

noncomputable section

open Set Function MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
  RearOwnArclength RearFamilyFrame NormalPathC2IncrementVariableSpeed GaugeFlowDerivCost

namespace GaugeRearFamilyEnrichedRichTerminalStage

open GaugeFlowMarkedTerminalJets GaugeRearFamilyVariableTerminal
  GaugeRearFamilyRichTerminalStage GaugeRearFamilySeparatedContinuation
  GaugeMarkedDataOfRearFamily VariableMarkedTube GaugeNormalPathSeparated

structure Output
    {a b : Data} (frontPath : NormalPath a b)
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {ell L T : ℝ} {base : Data}
    (J : TerminalJets xi xiX xiXX Phi ell L T base)
    (p front : Data) (bound P0 kh khat M c C dlt : ℝ)
    (CW C0 C10 C11 C20 C21 C22 : ℝ) where
  rich : GaugeRearFamilyRichTerminalStage.RichStageOutput J p front
    bound P0 kh khat M c C dlt
  c2 : C2NormalPathData rich.stage.increment
  flowed : FlowedBounds frontPath.eta rich.stage.increment.eta
    CW C0 C10 C11 C20 C21 C22

theorem exists_output_of_raw
    {a b : Data} {frontPath : NormalPath a b}
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {ell L T : ℝ} {base : Data}
    (J : TerminalJets xi xiX xiXX Phi ell L T base)
    {p front : Data}
    {M bound P0 kh khat cb db lambda Lambda dlt : ℝ}
    {CW C0 C10 C11 C20 C21 C22 : ℝ}
    (E : GaugeRearFamilySeparatedContinuation.RawStageOutput frontPath p front J.rear
      bound M P0 ell kh khat CW C0 C10 C11 C20 C21 C22)
    (hL : 0 < L) (hlambda : 0 < lambda)
    (hshift : ∀ u, Phi T (u + 1) = Phi T u + L)
    (hzero : Phi T 0 = 0)
    (hlower : ∀ u, lambda ≤ J.flow1 u / L)
    (hupper : ∀ u, J.flow1 u / L ≤ Lambda)
    (hbase : IsTubeMember cb 0 db base) (hcb : 0 < cb) (hdb : 0 < db)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    {F : ℝ → ℝ → ℂ} {Θ delta K sf : ℝ → ℝ → ℝ}
    (hstrip0 : ∀ s, 0 ≤ delta T s)
    (hstrip1 : ∀ s, delta T s ≤ Real.arcsin kh)
    (hF : ∀ t s, HasDerivAt (F t)
      (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (delta t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (delta t s) ≠ 0)
    (hterminal : ∀ u, J.rear.1 u = rearOwn F Θ delta sf T (Phi T u)) :
    Nonempty (Output frontPath J p front bound P0 kh khat M
      (lambda * cb) (Lambda * perim base) dlt
      CW C0 C10 C11 C20 C21 C22) := by
  let psi : ℝ → ℝ := fun u => Phi T u / L
  let dpsi : ℝ → ℝ := fun u => J.flow1 u / L
  let ddpsi : ℝ → ℝ := fun u => J.flow2 u / L
  have hpsi : ∀ u, HasDerivAt psi (dpsi u) u :=
    fun u => (J.flow_deriv u).div_const L
  have hdpsi : ∀ u, HasDerivAt dpsi (ddpsi u) u :=
    fun u => (J.flow1_deriv u).div_const L
  have hddpsi : Continuous ddpsi := J.flow2_cont.div_const L
  have hvelocity : ∀ u, J.rear.2.1 u =
      (dpsi u : ℂ) * base.2.1 (psi u) := by
    intro u
    have hchain := (hbase.hasDerivAt_curve (psi u)).scomp u (hpsi u)
    have heq : (⇑base.1 ∘ psi) = ⇑J.rear.1 :=
      funext fun x => (J.position x).symm
    rw [heq] at hchain
    have hu := (J.curve_deriv u).unique hchain
    simpa [Complex.real_smul] using hu
  have htranslate : ∀ u, psi (u + 1) = psi u + 1 := by
    intro u
    dsimp [psi]
    rw [hshift u]
    field_simp [hL.ne']
  let R : OrientedReparametrization base J.rear lambda Lambda :=
    { psi := psi
      dpsi := dpsi
      position := J.position
      velocity := hvelocity
      translate := htranslate
      lower := hlower
      upper := hupper }
  have hcurv := GaugeFlowMarkedTerminalJets.rear_orientedCurvature_nonnegative J
    hkh0 hkh1 hstrip0 hstrip1 hF hΘ hsteer hsf hcos rfl hterminal
  have hpsiZero : R.psi 0 = 0 := by
    dsimp [R, psi]
    rw [hzero, zero_div]
  let rich : GaugeRearFamilyRichTerminalStage.RichStageOutput J p front
      bound P0 kh khat M (lambda * cb) (Lambda * perim base) dlt :=
    { stage := E.stage
      lambda := lambda
      Lambda := Lambda
      lambda_pos := hlambda
      marking := R
      ddpsi := ddpsi
      psi_eq := fun _ => rfl
      dpsi_eq := fun _ => rfl
      ddpsi_eq := fun _ => rfl
      psi_deriv := hpsi
      dpsi_deriv := hdpsi
      ddpsi_cont := hddpsi
      psi_zero := hpsiZero
      oriented_curvature := hcurv }
  exact ⟨{ rich := rich, c2 := E.c2, flowed := E.flowed }⟩

end GaugeRearFamilyEnrichedRichTerminalStage
