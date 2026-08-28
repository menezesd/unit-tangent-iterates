import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostBounds

/-! # Composition-scaled direct exact successor on the canonical recost

The multiplier and its mass estimate are stated on the actual canonical
recost density, not on the raw chosen-path density.
-/

noncomputable section

open Function Set RearTrack RearOwnArclength RearFamilyFrame MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource

variable {p q a b : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax kap P0Next khatNext QmaxNext : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}
  (W : ChosenPath Gamma A E.Phi a b)
  (S : ExactSelected A (kap := kap))
  (R : PreTransport S)
  (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
  (T : ShiftedTransport R G)
  (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
  (C : Scalar (A := A) (kap := kap) (P0Next := P0Next)
    (khatNext := khatNext) (QmaxNext := QmaxNext))
  (hP0 : 0 < P0Next)
  (hC2 : C2NormalPathData W.Delta)
  (heta : Continuous (uncurry W.Delta.eta))
  (heta1 : Continuous (uncurry hC2.eta1))
  (heta2 : Continuous (uncurry hC2.eta2))

/-- Scalar multiplier data whose mass premise is about the canonical recost. -/
structure RecostScalar where
  coeff : ℝ
  coeff_ge_two : 2 ≤ coeff
  scaled_mass_le_one :
    (∫ t in (0 : ℝ)..W.Delta.T,
      coeff * density (kap := kap) W hC2 heta heta1 heta2 t) ≤ 1
  coeff_first :
    2 * GaugeFlowDerivCost.costP1 QmaxNext
      (GaugeMarkedDataOfRearFamily.rearKappa1 kap) 1 ≤ coeff
  coeff_second :
    (2 * sourceConst (kh := kh) (kap := kap) + 2) *
          GaugeFlowDerivCost.costP1 QmaxNext
            (GaugeMarkedDataOfRearFamily.rearKappa1 kap) 1 ^ 2 +
        2 * GaugeFlowDerivCost.costG1 QmaxNext
          (GaugeMarkedDataOfRearFamily.rearKappa1 kap)
          (GaugeMarkedDataOfRearFamily.rearKappa2 kap) 1 ≤ coeff

def scaledDensity (K : RecostScalar W (kap := kap) (QmaxNext := QmaxNext)
    hC2 heta heta1 heta2) (t : ℝ) : ℝ :=
  K.coeff * density (kap := kap) W hC2 heta heta1 heta2 t

private theorem sourceConst_nonnegative :
    0 ≤ sourceConst (kh := kh) (kap := kap) := by
  apply RearJacobiSourceCost.jacobiSourceConst_nonneg
  exact one_div_pos.mpr (by
    dsimp [derivativeConst,
      FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst]
    positivity)

/-- Multiplier-aware direct source with undoubled Jacobi constant. -/
def scaledDirectSource
    (B : DirectBounds W S R G T hkap0 hkap1 C hP0
      hC2 heta heta1 heta2)
    (K : RecostScalar W (kap := kap) (QmaxNext := QmaxNext)
      hC2 heta heta1 heta2) :
    MarkingAwareSource (carrier W hC2 heta heta1 heta2)
      P0Next kap khatNext QmaxNext := by
  let U := rawSource W S R G T hkap0 hkap1 C hP0
  let Delta' := carrier W hC2 heta heta1 heta2
  let rho := density (kap := kap) W hC2 heta heta1 heta2
  let dens := scaledDensity W hC2 heta heta1 heta2 K
  have hsqrt : 0 < Real.sqrt (1 - kap ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith)
  have hd0 : 0 ≤ U.d := sourceConst_nonnegative (kh := kh) (kap := kap)
  have hpsi : rearOwnAngle U.Theta U.delta U.sf = shiftedPsi R G := by
    funext t x
    exact psi_eq_shift S G.q t x
  refine
    { U with
      m := dens
      Dd := fun t ↦ (2 * U.d) * rho t
      frame_regularity := FrameRegularity.spatial
        { tangential := (geometricSpatialFrames S R G T hkap0 hkap1).1
          normal := (geometricSpatialFrames S R G T hkap0 hkap1).2
          tangential1_bound := by
            intro t x
            have hr : 0 ≤ rho t := by
              dsimp [rho,
                FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.density]
              exact div_nonneg (Delta'.m_nonneg t) hsqrt.le
            have hone : 1 ≤ K.coeff := K.coeff_ge_two.trans' (by norm_num)
            exact (B.tangential1_bound t x).trans
              (mul_le_mul_of_nonneg_left
                (show rho t ≤ dens t by
                  dsimp [dens, scaledDensity]
                  exact le_mul_of_one_le_left hr hone)
                (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hkap0 hkap1))
          tangential2_bound := by
            intro t x
            have hr : 0 ≤ rho t := by
              dsimp [rho,
                FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.density]
              exact div_nonneg (Delta'.m_nonneg t) hsqrt.le
            have hone : 1 ≤ K.coeff := K.coeff_ge_two.trans' (by norm_num)
            exact (B.tangential2_bound t x).trans
              (mul_le_mul_of_nonneg_left
                (show rho t ≤ dens t by
                  dsimp [dens, scaledDensity]
                  exact le_mul_of_one_le_left hr hone)
                (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg hkap0 hkap1))
          tangential_period_bound := by simpa [hpsi] using
            B.tangential_period_bound }
      eta_link := ?_
      etaF_bound := ?_
      Dd_le := fun t ↦ by
        have hr : 0 ≤ rho t := by
          dsimp [rho,
            FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.density]
          exact div_nonneg (Delta'.m_nonneg t) hsqrt.le
        have hscale : 2 * rho t ≤ K.coeff * rho t :=
          mul_le_mul_of_nonneg_right K.coeff_ge_two hr
        change (2 * U.d) * rho t ≤ U.d * (K.coeff * rho t)
        calc
          (2 * U.d) * rho t = U.d * (2 * rho t) := by ring
          _ ≤ U.d * (K.coeff * rho t) :=
            mul_le_mul_of_nonneg_left hscale hd0
      density_continuous := continuous_const.mul (Delta'.cont_m.div_const _)
      density_nonnegative := fun t ↦ by
        exact mul_nonneg (by linarith [K.coeff_ge_two])
          (div_nonneg (Delta'.m_nonneg t) hsqrt.le)
      density_support := ?_
      density_domination := fun t ↦ by
        have hr : 0 ≤ rho t := by
          dsimp [rho,
            FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.density]
          exact div_nonneg (Delta'.m_nonneg t) hsqrt.le
        have hone : 1 ≤ K.coeff := K.coeff_ge_two.trans' (by norm_num)
        dsimp [dens, scaledDensity]
        exact le_mul_of_one_le_left hr hone
      gS_bound := by
        intro t x
        simpa [rho] using B.gS_bound t x
      numerical_K := ?_ }
  · intro t u
    simpa [Delta', carrier] using U.eta_link t u
  · let M : MarkingCertificate Delta' U.etaF U.P :=
      { phi := U.phi
        phi1 := U.phi1
        phi2 := U.phi2
        eta_link := by
          intro t u
          simpa [Delta', carrier] using U.eta_link t u
        shift := U.phi_shift
        deriv := U.phi_deriv
        deriv2 := U.phi1_deriv
        phi1_continuous := U.phi1_continuous
        phi2_continuous := U.phi2_continuous }
    exact M.etaF_bound U.period_pos
  · intro t ht
    change K.coeff * (Delta'.m t / Real.sqrt (1 - kap ^ 2)) = 0
    rw [Delta'.m_stop t ht]
    simp
  · have H := B.numerical_K
    nlinarith

@[simp] theorem scaledDirectSource_m
    (B : DirectBounds W S R G T hkap0 hkap1 C hP0
      hC2 heta heta1 heta2)
    (K : RecostScalar W (kap := kap) (QmaxNext := QmaxNext)
      hC2 heta heta1 heta2) (t : ℝ) :
    (scaledDirectSource W S R G T hkap0 hkap1 C hP0
      hC2 heta heta1 heta2 B K).m t =
      K.coeff * density (kap := kap) W hC2 heta heta1 heta2 t := rfl

/-- The actual multiplier source has mass at most one. -/
theorem scaledDirectSource_mass_le_one
    (B : DirectBounds W S R G T hkap0 hkap1 C hP0
      hC2 heta heta1 heta2)
    (K : RecostScalar W (kap := kap) (QmaxNext := QmaxNext)
      hC2 heta heta1 heta2) :
    (∫ t in (0 : ℝ)..W.Delta.T,
      (scaledDirectSource W S R G T hkap0 hkap1 C hP0
        hC2 heta heta1 heta2 B K).m t) ≤ 1 := by
  simpa only [scaledDirectSource_m] using K.scaled_mass_le_one

/-- The exact two composition budgets required by presented terminal
geometry, now proved for the actual canonical multiplier source. -/
theorem scaledDirectSource_composition_budgets
    (B : DirectBounds W S R G T hkap0 hkap1 C hP0
      hC2 heta heta1 heta2)
    (K : RecostScalar W (kap := kap) (QmaxNext := QmaxNext)
      hC2 heta heta1 heta2) :
    let D := scaledDirectSource W S R G T hkap0 hkap1 C hP0
      hC2 heta heta1 heta2 B K
    let M := ∫ s in (0 : ℝ)..W.Delta.T, D.m s
    (∀ t, 2 * ((carrier W hC2 heta heta1 heta2).m t /
          Real.sqrt (1 - kap ^ 2)) *
          GaugeFlowDerivCost.costP1
            (rearArclength (delta S G.q 0) (period A 0))
            (GaugeMarkedDataOfRearFamily.rearKappa1 kap) M ≤ D.m t) ∧
      (∀ t,
        (D.Dd t + 2 * ((carrier W hC2 heta heta1 heta2).m t /
            Real.sqrt (1 - kap ^ 2))) *
              GaugeFlowDerivCost.costP1
                (rearArclength (delta S G.q 0) (period A 0))
                (GaugeMarkedDataOfRearFamily.rearKappa1 kap) M ^ 2 +
            2 * ((carrier W hC2 heta heta1 heta2).m t /
              Real.sqrt (1 - kap ^ 2)) *
              GaugeFlowDerivCost.costG1
                (rearArclength (delta S G.q 0) (period A 0))
                (GaugeMarkedDataOfRearFamily.rearKappa1 kap)
                (GaugeMarkedDataOfRearFamily.rearKappa2 kap) M ≤ D.m t) := by
  dsimp only
  let D := scaledDirectSource W S R G T hkap0 hkap1 C hP0
    hC2 heta heta1 heta2 B K
  let rho := density (kap := kap) W hC2 heta heta1 heta2
  let M := ∫ s in (0 : ℝ)..W.Delta.T, D.m s
  let ell := rearArclength (delta S G.q 0) (period A 0)
  let k1 := GaugeMarkedDataOfRearFamily.rearKappa1 kap
  let k2 := GaugeMarkedDataOfRearFamily.rearKappa2 kap
  let p := GaugeFlowDerivCost.costP1 ell k1 M
  let p1 := GaugeFlowDerivCost.costP1 QmaxNext k1 1
  let g := GaugeFlowDerivCost.costG1 ell k1 k2 M
  let g1 := GaugeFlowDerivCost.costG1 QmaxNext k1 k2 1
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg W.Delta.T_pos.le
    (fun t _ ↦ D.density_nonnegative t)
  have hM1 : M ≤ 1 := by
    simpa [M, D] using
      (scaledDirectSource_mass_le_one W S R G T hkap0 hkap1 C hP0
        hC2 heta heta1 heta2 B K)
  have hell0 : 0 ≤ ell :=
    ((rawBounds W S R G T hkap0 hkap1 C hP0).rear_period_pos 0).le
  have hell : ell ≤ QmaxNext :=
    (rawBounds W S R G T hkap0 hkap1 C hP0).rear_period_le 0
  have hk10 : 0 ≤ k1 :=
    GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hkap0 hkap1
  have hk20 : 0 ≤ k2 :=
    GaugeMarkedDataOfRearFamily.rearKappa2_nonneg hkap0 hkap1
  have hp : p ≤ p1 := by
    simpa [p, p1, ell, k1] using
      GaugeFlowDerivCost.costP1_le hell0 hell hk10 hM0 hM1
  have hg : g ≤ g1 := by
    simpa [g, g1, ell, k1, k2] using
      GaugeFlowDerivCost.costG1_le hell0 hell hk10 hk20 hM0 hM1
  have hp0 : 0 ≤ p := by
    unfold p GaugeFlowDerivCost.costP1
    exact mul_nonneg hell0 (Real.exp_pos _).le
  have hp10 : 0 ≤ p1 := hp0.trans hp
  have hpsq : p ^ 2 ≤ p1 ^ 2 := (sq_le_sq₀ hp0 hp10).2 hp
  have hg0 : 0 ≤ g := by
    unfold g GaugeFlowDerivCost.costG1
    exact mul_nonneg (sq_nonneg _) (mul_nonneg hk20 hM0)
  have hg10 : 0 ≤ g1 := hg0.trans hg
  have hd0 := sourceConst_nonnegative (kh := kh) (kap := kap)
  constructor
  · intro t
    have hr : 0 ≤ rho t := by
      dsimp [rho,
        FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.density]
      exact div_nonneg ((carrier W hC2 heta heta1 heta2).m_nonneg t)
        (Real.sqrt_nonneg _)
    have hterm : 2 * rho t * p ≤ K.coeff * rho t := by
      calc
        2 * rho t * p ≤ 2 * rho t * p1 :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num) hr)
        _ ≤ K.coeff * rho t := by
          have H := mul_le_mul_of_nonneg_right K.coeff_first hr
          nlinarith
    change 2 * rho t * p ≤ D.m t
    rw [scaledDirectSource_m]
    exact hterm
  · intro t
    have hr : 0 ≤ rho t :=
      div_nonneg ((carrier W hC2 heta heta1 heta2).m_nonneg t)
        (Real.sqrt_nonneg _)
    let s := sourceConst (kh := kh) (kap := kap)
    have hfac : D.Dd t + 2 * rho t = (2 * s + 2) * rho t := by
      change (2 * (rawSource W S R G T hkap0 hkap1 C hP0).d) * rho t +
        2 * rho t = (2 * s + 2) * rho t
      rw [show (rawSource W S R G T hkap0 hkap1 C hP0).d = s from rfl]
      ring
    have hfac0 : 0 ≤ (2 * s + 2) * rho t :=
      mul_nonneg (add_nonneg (mul_nonneg (by norm_num) hd0) (by norm_num)) hr
    have hterm1 : (D.Dd t + 2 * rho t) * p ^ 2 ≤
        ((2 * s + 2) * p1 ^ 2) * rho t := by
      rw [hfac]
      calc
        ((2 * s + 2) * rho t) * p ^ 2 ≤
            ((2 * s + 2) * rho t) * p1 ^ 2 :=
          mul_le_mul_of_nonneg_left hpsq hfac0
        _ = ((2 * s + 2) * p1 ^ 2) * rho t := by ring
    have hterm2 : 2 * rho t * g ≤ (2 * g1) * rho t := by
      calc
        2 * rho t * g ≤ 2 * rho t * g1 :=
          mul_le_mul_of_nonneg_left hg (mul_nonneg (by norm_num) hr)
        _ = (2 * g1) * rho t := by ring
    have hcoeff := mul_le_mul_of_nonneg_right K.coeff_second hr
    have htotal :
        (D.Dd t + 2 * rho t) * p ^ 2 + 2 * rho t * g ≤
          K.coeff * rho t := by
      dsimp [p1, g1, s] at hcoeff ⊢
      nlinarith [hterm1, hterm2]
    change (D.Dd t + 2 * rho t) * p ^ 2 + 2 * rho t * g ≤ D.m t
    rw [scaledDirectSource_m]
    exact htotal

end FiniteSmoothRearFamilyMarkingAwareExactSuccessorScaledDirectRecostSource
