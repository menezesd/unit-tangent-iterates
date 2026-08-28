import UnitTangentIterates.GaugeFlowMarkedTerminalJets
import UnitTangentIterates.GaugeRearFamilyVariableTerminal

/-!
# Rich gauge stages with their actual terminal marking

This adapter chooses the endpoint carried by `TerminalJets`, retains the
normalized `C2` marking data used by terminal compactness, and simultaneously
constructs the existing variable-terminal stage output.
-/

noncomputable section

open Set Function MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearOwnArclength RearFamilyFrame
  NormalPathC2IncrementVariableSpeed GaugeFlowDerivCost

namespace GaugeRearFamilyRichTerminalStage

open GaugeFlowMarkedTerminalJets GaugeRearFamilyVariableTerminal
  GaugeMarkedDataOfRearFamily VariableMarkedTube

/-- A variable-terminal stage retaining the normalized terminal marking and
its second spatial jet. -/
structure RichStageOutput
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {ell L T : ℝ} {base : Data}
    (J : TerminalJets xi xiX xiXX Phi ell L T base)
    (p front : Data) (bound P0 kh khat M c C dlt : ℝ) where
  stage : GaugeRearFamilyVariableTerminal.RawStageOutput p front J.rear bound
    P0 (costP1 ell khat M) khat
    (costG1 ell khat (rearKappa2 kh) M)
    (khat * costG1 ell khat (rearKappa2 kh) M +
      rearKappa2 kh * costP1 ell khat M ^ 2)
  lambda : ℝ
  Lambda : ℝ
  lambda_pos : 0 < lambda
  marking : OrientedReparametrization base J.rear lambda Lambda
  ddpsi : ℝ → ℝ
  psi_eq : ∀ u, marking.psi u = Phi T u / L
  dpsi_eq : ∀ u, marking.dpsi u = J.flow1 u / L
  ddpsi_eq : ∀ u, ddpsi u = J.flow2 u / L
  psi_deriv : ∀ u, HasDerivAt marking.psi (marking.dpsi u) u
  dpsi_deriv : ∀ u, HasDerivAt marking.dpsi (ddpsi u) u
  ddpsi_cont : Continuous ddpsi
  psi_zero : marking.psi 0 = 0
  oriented_curvature : ∀ u, 0 ≤
    ((starRingEnd ℂ) (J.rear.2.1 u) * J.rear.2.2 u).im

/-- Construct a rich stage at the exact endpoint selected by `TerminalJets`.
The shift/basepoint and two-sided derivative bounds are the finite flow facts
which feed `TerminalMarkingCompactness`; all curvature sign information is
derived from the selected strip. -/
theorem exists_richStageOutput
    {xi xiX xiXX Phi : ℝ → ℝ → ℝ} {ell L T : ℝ} {base : Data}
    (J : TerminalJets xi xiX xiXX Phi ell L T base)
    {p front : Data}
    {F : ℝ → ℝ → ℂ} {Θ delta K sf : ℝ → ℝ → ℝ}
    {Ydot : ℝ → ℝ → ℂ} {m : ℝ → ℝ}
    {M bound P0 kh khat cb db lambda Lambda dlt : ℝ}
    (hL : 0 < L) (hlambda : 0 < lambda)
    (hshift : ∀ u, Phi T (u + 1) = Phi T u + L)
    (hzero : Phi T 0 = 0)
    (hlower : ∀ u, lambda ≤ J.flow1 u / L)
    (hupper : ∀ u, J.flow1 u / L ≤ Lambda)
    (hbase : IsTubeMember cb 0 db base) (hcb : 0 < cb) (hdb : 0 < db)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
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
    (hterminal : ∀ u, J.rear.1 u = rearOwn F Θ delta sf T (Phi T u))
    (hcanonical : range (⇑front.1) =
      range (UnitTangent.unitTangentMap (ev base)))
    (hstrict : UnconditionalAssembly.LimitStrictnessDataH base)
    (hcontinue :
      GaugeRearFamilyTriangularStageAdapter.RearFamilyContinuation
        F Θ delta sf Ydot Phi T M m P0 ell kh khat)
    (hinitial : ∀ u, rearOwn F Θ delta sf 0 (Phi 0 u) = p.1 u)
    (hsup : ∀ t, ∀ j ≤ 2, supNorm
      (iteratedDeriv j
        (fun u => frameNormal Ydot (rearOwnAngle Θ delta sf) t (Phi t u))) ≤ m t)
    (hcost : M ≤ bound) :
    Nonempty (RichStageOutput J p front bound P0 kh khat M
      (lambda * cb) (Lambda * perim base) dlt) := by
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
  have hcurv :=
    GaugeFlowMarkedTerminalJets.rear_orientedCurvature_nonnegative J
      hkh0 hkh1 hstrip0 hstrip1 hF hΘ hsteer hsf hcos rfl hterminal
  have hcont : Continuous R.psi :=
    continuous_iff_continuousAt.2 fun u => (hpsi u).continuousAt
  have hmono : StrictMono R.psi := by
    refine strictMono_of_deriv_pos fun u => ?_
    rw [(hpsi u).deriv]
    exact lt_of_lt_of_le hlambda (hlower u)
  have hpsiZero : R.psi 0 = 0 := by
    dsimp [R, psi]
    rw [hzero, zero_div]
  have hsurj : Surjective R.psi :=
    GaugeMarkedSelectedInverseEndpoint.surjective_of_continuous_strictMono_quasiPeriodic
      one_pos hcont hmono R.translate hpsiZero
  let residual := rawTerminalResidual_of_orientedReparametrization hcb hdb
    hlambda hbase R J.curve_deriv J.vel_deriv hcurv hsurj hcanonical
    hstrict
  obtain ⟨stage⟩ := rawStageOutput_of_rearFamilyContinuation hcontinue
    hinitial (fun u => (hterminal u).symm) hsup hcost residual
  exact ⟨{
    stage := stage
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
    oriented_curvature := hcurv }⟩

end GaugeRearFamilyRichTerminalStage
