import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorRecostDerivativeBound

/-! # Analytic bounds for the direct canonical-recost successor source -/

noncomputable section

open Function Set RearTrack RearOwnArclength RearFamilyFrame MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostBounds

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorRecostTransportInput
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorRecostDerivativeBound
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam

variable {p q a b : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax kap P0Next khatNext QmaxNext eps : ℝ}
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
  (heta0 : Continuous (uncurry W.Delta.eta))
  (heta1 : Continuous (uncurry W.c2.eta1))
  (heta2 : Continuous (uncurry W.c2.eta2))

private theorem carrier_le_density
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (t : ℝ) :
    (carrier W W.c2 heta0 heta1 heta2).m t ≤
      density (kap := kap) W W.c2 heta0 heta1 heta2 t := by
  have hsqrt : 0 < Real.sqrt (1 - kap ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [hkap0, hkap1])
  have hsqrt_le : Real.sqrt (1 - kap ^ 2) ≤ 1 := by
    have h := Real.sqrt_le_sqrt
      (show 1 - kap ^ 2 ≤ (1 : ℝ) by nlinarith [sq_nonneg kap])
    simpa using h
  exact (le_div_iff₀ hsqrt).2
    (mul_le_of_le_one_right
      ((carrier W W.c2 heta0 heta1 heta2).m_nonneg t) hsqrt_le)

/-- All analytic fields of `DirectBounds`; only the strengthened scalar
`numerical_K` inequality is retained as an explicit input. -/
def directBounds
    (J : NormalizedJetBounds W eps)
    (heps : eps ≤ 1 / 4)
    (hperiod : ∀ t, 1 ≤ rearPeriod A t)
    (hT : W.Delta.T = 1)
    (hnum :
      ((2 * (rawSource W S R G T hkap0 hkap1 C hP0).d) + 2) +
          khatNext ^ 2 + 2 *
            GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap *
              (rawSource W S R G T hkap0 hkap1 C hP0).kx ≤
        1 / P0Next ^ 2 + khatNext ^ 2) :
    DirectBounds W S R G T hkap0 hkap1 C hP0 W.c2
      heta0 heta1 heta2 := by
  let D := carrier W W.c2 heta0 heta1 heta2
  let dens := density (kap := kap) W W.c2 heta0 heta1 heta2
  let RB := rawBounds W S R G T hkap0 hkap1 C hP0
  have hk1nonneg := GaugeMarkedDataOfRearFamily.rearKappa1_nonneg
    hkap0 hkap1
  have hk2nonneg := GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
    hkap0 hkap1
  have hdom : ∀ t, D.m t ≤ dens t := by
    intro t
    exact carrier_le_density W heta0 heta1 heta2 hkap0 hkap1 t
  refine
    { tangential1_bound := ?_
      tangential2_bound := ?_
      tangential_period_bound := ?_
      gS_bound := ?_
      numerical_K := hnum }
  · intro t x
    rw [geometric_xi1_eq_raw S R G T hkap0 hkap1]
    exact (raw_xi1_bound_of_eta_le W S R hkap0 hkap1
      D.m D.m_nonneg D.abs_eta_le t (x + G.q t)).trans
        (mul_le_mul_of_nonneg_left (hdom t) hk1nonneg)
  · intro t x
    rw [geometric_xi2_eq_raw S R G T hkap0 hkap1]
    exact (raw_xi2_bound_of_eta_le W S R hkap0 hkap1 C.curvature_le
      D.m D.m_nonneg D.abs_eta_le t (x + G.q t)).trans
        (mul_le_mul_of_nonneg_left (hdom t) hk2nonneg)
  · intro t x hx
    let f : ℝ → ℝ := frameTangential (Ydot R G) (shiftedPsi R G) t
    let fp : ℝ → ℝ := fun y =>
      (spatialFrames S R G T hkap0 hkap1).1.xi1 t y
    have hd := RearOwnDriftFundamental.abs_le_of_deriv_le_on_Icc
      (f := f) (f' := fp) (RB.rear_period_pos t).le
      (fun y => (spatialFrames S R G T hkap0 hkap1).1.deriv1 t y)
      (by
        dsimp [f]
        simpa [Ydot, shiftedPsi, xi] using
          RearOwnFrameGaugeFlowReanchoring.frameTangential_shiftedYdot_zero
            R.Ydot S.psi G.q t)
      (fun y => by
        change |(geometricSpatialFrames S R G T hkap0 hkap1).1.xi1 t y| ≤
          GaugeMarkedDataOfRearFamily.rearKappa1 kap * D.m t
        rw [geometric_xi1_eq_raw S R G T hkap0 hkap1]
        exact raw_xi1_bound_of_eta_le W S R hkap0 hkap1
          D.m D.m_nonneg D.abs_eta_le t (y + G.q t)) hx
    exact hd.trans (calc
      rearArclength (delta S G.q t) (period A t) *
            (GaugeMarkedDataOfRearFamily.rearKappa1 kap * D.m t) ≤
          QmaxNext *
            (GaugeMarkedDataOfRearFamily.rearKappa1 kap * D.m t) :=
        mul_le_mul_of_nonneg_right (RB.rear_period_le t)
          (mul_nonneg hk1nonneg (D.m_nonneg t))
      _ = GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap * D.m t := by
        simp [GaugeRearFamilyFromFront.rearDriftConst,
          GaugeMarkedDataOfRearFamily.rearKappa1]
        ring)
  · intro t x
    have hg := raw_gS_bound_recost W S R hkap0 hkap1 C.curvature_le
      heta0 heta1 heta2 J heps hperiod hT t (x + G.q t)
    have hdd : 0 ≤ sourceConst (kh := kh) (kap := kap) :=
      RearJacobiSourceCost.jacobiSourceConst_nonneg
        (one_div_pos.mpr (by
          dsimp [derivativeConst,
            FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst]
          positivity))
    have hg' : |R.gS t (x + G.q t)| ≤
        (2 * sourceConst (kh := kh) (kap := kap)) * dens t :=
      hg.trans (by
        calc
          sourceConst (kh := kh) (kap := kap) * (2 * D.m t) =
              (2 * sourceConst (kh := kh) (kap := kap)) * D.m t := by ring
          _ ≤ (2 * sourceConst (kh := kh) (kap := kap)) * dens t :=
            mul_le_mul_of_nonneg_left (hdom t) (mul_nonneg (by norm_num) hdd))
    have hdraw : (rawSource W S R G T hkap0 hkap1 C hP0).d =
        sourceConst (kh := kh) (kap := kap) := rfl
    simpa [gS, TimeDependentSpatialReanchoring.shift, hdraw] using hg'

end FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostBounds
