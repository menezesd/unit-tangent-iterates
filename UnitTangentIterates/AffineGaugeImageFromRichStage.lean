import UnitTangentIterates.ConfiguredRichMapStageProvider
import UnitTangentIterates.MarkedDataOfMarking

/-! Re-mark an affine gauge-rich stage at the preceding actual endpoint. -/

noncomputable section

open Function Set MarkedSpace PathMetric PathMetric.NormalPath

namespace AffineGaugeImageFromRichStage

open GaugeRearFamilyVariableTerminal
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  NormalizedTerminalMarkingComposition
  NormalizedMarkingControlledJunction
  ConfiguredApproximateDefectPathRowwise
  ConfiguredRichMapStageProvider

theorem normalized_surjective
    {base rear : Data} {lambda Lambda : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda) :
    Surjective M.marking.psi := by
  have hc : Continuous M.marking.psi :=
    continuous_iff_continuousAt.2 fun u => (M.psi_deriv u).continuousAt
  have hm : StrictMono M.marking.psi := by
    refine strictMono_of_deriv_pos fun u => ?_
    rw [(M.psi_deriv u).deriv]
    exact M.lambda_pos.trans_le (M.marking.lower u)
  exact GaugeMarkedSelectedInverseEndpoint.surjective_of_continuous_strictMono_quasiPeriodic
    one_pos hc hm M.marking.translate M.psi_zero

/-- Reparameterize the terminal datum of an affine rich gauge stage by the
preceding stage marking.  The only retained physical inputs are those erased
by `RichStageData`: tube membership of its terminal physical base and the
canonical range/strictness identities. -/
theorem affineGaugeImage_of_richStage
    (D : ConstructedConfiguredSequenceWeighted.Data) {kh mA MA NA c dlt : ℝ}
    {rawP1 rawG1 rawCg C : ℕ → ℝ}
    {Q current : ℕ → Data} {k n : ℕ}
    (S : ColumnStep Q current
      (ConfiguredRowDefectProvider.error D (K kh mA MA NA)) k
      (rowP0 D) (mapP1 D rawP1 MA) (fun _ ↦ D.kstar)
      (mapG1 D rawP1 rawG1 MA NA) (mapCg D rawP1 rawCg MA NA) C c dlt)
    {b : Data} {bound cb db : ℝ}
    (W : RichStageData (S.richStage n).terminalBase (S.next (n + 1)) b
      bound (rowP0 D n) (rawP1 n) D.kstar (rawG1 n) (rawCg n)
      c (C n) dlt)
    (hC2 : C2NormalPathData W.stage.increment)
    (hcost : cost W.stage.increment ≤
      SelectedInverseApproximateMapPath.mapK kh *
        cost (S.richStage (n + 1)).stage.increment)
    (A : ControlledAnchoringBounds (S.richStage n).marking mA MA NA)
    (hcb : 0 < cb) (hdb : 0 < db)
    (hbase : IsTubeMember cb 0 db W.terminalBase)
    (hphysical : PhysicalRearLimitKinematics kh W.terminalBase
      (S.richStage (n + 1)).terminalBase)
    (hcanonical : range (⇑(S.next (n + 1)).1) =
      range (UnitTangent.unitTangentMap (ev W.terminalBase)))
    (hstrict : UnconditionalAssembly.LimitStrictnessDataH W.terminalBase) :
    Nonempty (AffineGaugeImage D rawP1 rawG1 rawCg C S n) := by
  let A0 := (S.richStage n).marking
  have hA1c : Continuous A0.marking.dpsi :=
    continuous_iff_continuousAt.2 fun u => (A0.dpsi_deriv u).continuousAt
  obtain ⟨rear, hpos, hvel, hacc, hcurve, hvelderiv⟩ :=
    MarkedDataOfMarking.exists_data_of_marking
      W.stage.rear_curve_deriv W.stage.rear_vel_deriv
      A0.psi_deriv A0.dpsi_deriv hA1c A0.ddpsi_cont
      A.upper
      A.second
  let psi : ℝ → ℝ := fun u => W.marking.marking.psi (A0.marking.psi u)
  let dpsi : ℝ → ℝ := fun u =>
    A0.marking.dpsi u * W.marking.marking.dpsi (A0.marking.psi u)
  let ddpsi : ℝ → ℝ := fun u =>
    W.marking.ddpsi (A0.marking.psi u) * A0.marking.dpsi u ^ 2 +
      W.marking.marking.dpsi (A0.marking.psi u) * A0.ddpsi u
  have hpsi : ∀ u, HasDerivAt psi (dpsi u) u := by
    intro u
    simpa [psi, dpsi, mul_comm, smul_eq_mul] using
      (W.marking.psi_deriv (A0.marking.psi u)).scomp u (A0.psi_deriv u)
  have hdpsi : ∀ u, HasDerivAt dpsi (ddpsi u) u := by
    intro u
    have hright :=
      (W.marking.dpsi_deriv (A0.marking.psi u)).scomp u (A0.psi_deriv u)
    have h := (A0.dpsi_deriv u).mul hright
    convert h using 1 <;> simp [dpsi, ddpsi, smul_eq_mul] <;> ring
  have hddc : Continuous ddpsi := by
    have hApsi : Continuous A0.marking.psi :=
      continuous_iff_continuousAt.2 fun u => (A0.psi_deriv u).continuousAt
    have hWd : Continuous W.marking.marking.dpsi :=
      continuous_iff_continuousAt.2 fun u => (W.marking.dpsi_deriv u).continuousAt
    dsimp [ddpsi]
    exact ((W.marking.ddpsi_cont.comp hApsi).mul (hA1c.pow 2)).add
      ((hWd.comp hApsi).mul A0.ddpsi_cont)
  have hposition : ∀ u, rear.1 u = W.terminalBase.1 (psi u) := by
    intro u
    rw [hpos u, W.marking.marking.position]
  have hvelocity : ∀ u, rear.2.1 u =
      (dpsi u : ℂ) * W.terminalBase.2.1 (psi u) := by
    intro u
    rw [hvel u, W.marking.marking.velocity]
    simp [dpsi, psi, Complex.ofReal_mul]
    ring
  have htranslate : ∀ u, psi (u + 1) = psi u + 1 := by
    intro u
    simp only [psi, A0.marking.translate, W.marking.marking.translate]
  let R : OrientedReparametrization W.terminalBase rear
      (W.lambda * mA) (W.Lambda * MA) :=
    { psi := psi
      dpsi := dpsi
      position := hposition
      velocity := hvelocity
      translate := htranslate
      lower := by
        intro u
        dsimp [dpsi]
        have h := mul_le_mul
          (W.marking.marking.lower (A0.marking.psi u)) (A.lower u)
          A.m_pos.le
          (W.marking.lambda_pos.le.trans
            (W.marking.marking.lower (A0.marking.psi u)))
        simpa [mul_comm] using h
      upper := by
        intro u
        dsimp [dpsi]
        have hAu : A0.marking.dpsi u ≤ MA :=
          (le_abs_self _).trans (A.upper u)
        have h := mul_le_mul hAu
          (W.marking.marking.upper (A0.marking.psi u))
          (W.marking.lambda_pos.le.trans
            (W.marking.marking.lower (A0.marking.psi u)))
          A.M_nonneg
        simpa [mul_comm] using h }
  let NM : NormalizedC2Marking W.terminalBase rear
      (W.lambda * mA) (W.Lambda * MA) :=
    { lambda_pos := mul_pos W.marking.lambda_pos A.m_pos
      marking := R
      ddpsi := ddpsi
      psi_deriv := hpsi
      dpsi_deriv := hdpsi
      ddpsi_cont := hddc
      psi_zero := by simp [R, psi, A0.psi_zero, W.marking.psi_zero] }
  have hcurv : ∀ u, 0 ≤
      ((starRingEnd ℂ) (rear.2.1 u) * rear.2.2 u).im := by
    intro u
    rw [hvel u, hacc u]
    have hpow : (A0.marking.dpsi u : ℂ) ^ 2 =
        (A0.marking.dpsi u ^ 2 : ℝ) := by norm_cast
    rw [hpow]
    have ha : 0 ≤ A0.marking.dpsi u :=
      A.m_pos.le.trans (A.lower u)
    have hb := W.stage.rear_curvature_nonnegative (A0.marking.psi u)
    simp only [map_mul, Complex.mul_im, Complex.add_im, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.conj_re, Complex.conj_im] at hb ⊢
    ring_nf at hb ⊢
    nlinarith [sq_nonneg (b.2.1 (A0.marking.psi u)).re,
      sq_nonneg (b.2.1 (A0.marking.psi u)).im,
      mul_nonneg (pow_nonneg ha 3) hb]
  have hterminal : RawTerminalResidual (S.next (n + 1)) rear :=
    rawTerminalResidual_of_orientedReparametrization hcb hdb
      (mul_pos W.marking.lambda_pos A.m_pos) hbase R hcurve hvelderiv
      hcurv (normalized_surjective NM) hcanonical hstrict
  refine ⟨{
    affineRear := b
    rear := rear
    terminalBase := W.terminalBase
    physicalKinematics := hphysical
    affinePath := W.stage.increment
    affineC2 := hC2
    affineGeometry := W.stage.increment_geometry
    affineCost := hcost
    finish := ?_
    lambda := W.lambda * mA
    Lambda := W.Lambda * MA
    marking := NM
    terminal := hterminal }⟩
  intro u
  rw [W.stage.increment.finish, hpos u]

end AffineGaugeImageFromRichStage
