import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFiniteSource

/-! # Canonical quantitative bounds for the exact C1 successor -/

noncomputable section

open Function Set RearTrack RearOwnArclength RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence

variable {p q a b : MarkedSpace.Data} {Gamma : PathMetric.NormalPath p q}
  {P0 kh khat Qmax kap P0Next khatNext QmaxNext : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}
  (W : ChosenPath Gamma A E.Phi a b)
  (S : ExactSelected A (kap := kap))
  (R : PreTransport S)
  (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
  (T : ShiftedTransport R G)

def density (t : ℝ) : ℝ := W.Delta.m t / Real.sqrt (1 - kap ^ 2)

def derivativeConst : ℝ :=
  FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst kh
def sourceConst : ℝ :=
  FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst kap
    (derivativeConst (kh := kh))
def curvatureConst : ℝ :=
  FiniteSmoothRearFamilyMarkingAwareSmoothSource.successorKx kap

structure Scalar where
  curvature_le : ∀ t s, |curvature A t s| ≤ kap
  period_le : ∀ t, period A t ≤ QmaxNext
  rearKappa1_le : GaugeMarkedDataOfRearFamily.rearKappa1 kap ≤ khatNext
  numerical_A : 2 + 2 * khatNext *
    GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap ≤ 1 / P0Next
  numerical_K : (sourceConst (kh := kh) (kap := kap) + 2) + khatNext ^ 2 +
    2 * GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap *
      curvatureConst (kap := kap) ≤ 1 / P0Next ^ 2 + khatNext ^ 2

private theorem sqrt_pos (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) :
    0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)

private theorem density_nonnegative (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (t : ℝ) :
    0 ≤ density W (kap := kap) t :=
  div_nonneg (W.Delta.m_nonneg t) (sqrt_pos hkap0 hkap1).le

private theorem density_dominates (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (t : ℝ) :
    W.Delta.m t ≤ density W (kap := kap) t := by
  have hsle : Real.sqrt (1 - kap ^ 2) ≤ 1 := by
    have := Real.sqrt_le_sqrt (show 1 - kap ^ 2 ≤ (1 : ℝ) by nlinarith [sq_nonneg kap])
    simpa using this
  exact (le_div_iff₀ (sqrt_pos hkap0 hkap1)).2
    (mul_le_of_le_one_right (W.Delta.m_nonneg t) hsle)

private theorem etaDerivative_bound (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (t s : ℝ) :
    |A.etaF t (A.sf t s) / Real.cos (A.delta t (A.sf t s)) -
      rearNormal A t s| ≤ derivativeConst (kh := kh) * W.Delta.m t := by
  have hgamma : 0 < Real.sqrt (1 - kh ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [A.kh_nonnegative, A.kh_lt_one])
  have hcos : Real.sqrt (1 - kh ^ 2) ≤ Real.cos (A.delta t (A.sf t s)) :=
    Shadowing.cos_ge_of_mem_strip (A.strip_nonnegative t _) (A.strip_le t _)
  have hGle : Gamma.m t ≤ A.m t := by
    have hsle : Real.sqrt (1 - kh ^ 2) ≤ 1 := by
      have := Real.sqrt_le_sqrt (show 1 - kh ^ 2 ≤ (1 : ℝ) by nlinarith [sq_nonneg kh])
      simpa using this
    exact ((le_div_iff₀ hgamma).2
      (mul_le_of_le_one_right (Gamma.m_nonneg t) hsle)).trans
        (A.density_domination t)
  have heta : |A.etaF t (A.sf t s)| ≤ W.Delta.m t :=
    (A.etaF_bound t _).trans (hGle.trans_eq (congrFun W.density_eq.symm t))
  have hfrac : |A.etaF t (A.sf t s) / Real.cos (A.delta t (A.sf t s))| ≤
      W.Delta.m t / Real.sqrt (1 - kh ^ 2) := by
    rw [abs_div, abs_of_pos (hgamma.trans_le hcos)]
    exact div_le_div₀ (W.Delta.m_nonneg t) heta hgamma hcos
  calc
    _ ≤ |A.etaF t (A.sf t s) / Real.cos (A.delta t (A.sf t s))| +
        |rearNormal A t s| := abs_sub _ _
    _ ≤ W.Delta.m t / Real.sqrt (1 - kh ^ 2) + W.Delta.m t :=
      add_le_add hfrac (rearNormal_bound W t s)
    _ = derivativeConst (kh := kh) * W.Delta.m t := by
      simp [derivativeConst,
        FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst]
      ring

def bounds (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (C : Scalar (A := A) (kap := kap) (P0Next := P0Next)
      (khatNext := khatNext) (QmaxNext := QmaxNext))
    (hP0 : 0 < P0Next) :
    Bounds (P0Next := P0Next) (khatNext := khatNext) (QmaxNext := QmaxNext)
      W S R G T hkap0 hkap1 := by
  let dens := density W (kap := kap)
  let dd := sourceConst (kh := kh) (kap := kap)
  let kx0 := curvatureConst (kap := kap)
  have hperiodPos : ∀ t, 0 < period A t :=
    (MarkingAwareSource.successorFrontCore A).period_pos
  have hrearPos : ∀ t, 0 < rearArclength (delta S G.q t) (period A t) := by
    intro t
    exact SelectedInverseUnique.rearArclength_pos (hperiodPos t) hkap0 hkap1
      ((delta_contDiff S G.contDiff).continuous.comp
        (continuous_const.prodMk continuous_id))
      (fun s => ⟨delta_strip_nonnegative S G.q t s, delta_strip_le S G.q t s⟩)
  have hrearLe : ∀ t, rearArclength (delta S G.q t) (period A t) ≤ QmaxNext := by
    intro t
    exact (ArclengthInverse.rearArclength_le_of_period
      ((delta_contDiff S G.contDiff).continuous.comp
        (continuous_const.prodMk continuous_id)) (hperiodPos t).le).trans
      (C.period_le t)
  have hkx0 : 0 ≤ kx0 := by
    dsimp [kx0, curvatureConst,
      FiniteSmoothRearFamilyMarkingAwareSmoothSource.successorKx]
    exact div_nonneg (mul_nonneg (by norm_num) hkap0)
      (pow_nonneg (Real.sqrt_nonneg _) 3)
  have hdd0 : 0 ≤ dd :=
    RearJacobiSourceCost.jacobiSourceConst_nonneg
      (one_div_pos.mpr (by
        dsimp [derivativeConst,
          FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst]
        positivity))
  have hgSraw : ∀ t x, |R.gS t x| ≤ dd * W.Delta.m t := by
    intro t x
    apply RearJacobiSourceCost.abs_source_deriv_le hkap0 hkap1
      (one_div_pos.mpr (by
        dsimp [derivativeConst,
          FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst]
        positivity))
      (fun s => by simpa [rearNormal] using A.jacobi t s)
      (rearNormal_bound W t)
      (fun s => by
        have h := etaDerivative_bound W hkap0 hkap1 t s
        simpa [div_eq_mul_inv, mul_comm, derivativeConst] using h)
      (S.strip_nonnegative t) (S.strip_le t) (S.steering t)
      (C.curvature_le t) (S.sf_deriv t) (R.gS_deriv t) x
  exact
    { Kx := fun _ => kx0
      Dd := fun t => dd * dens t
      m := dens
      kx := kx0
      d := dd
      curvature_le := fun t s => C.curvature_le t (s + sigma S G.q t)
      rear_period_pos := hrearPos
      rear_period_le := hrearLe
      tangential1_bound := fun t x => by
        rw [geometric_xi1_eq_raw S R G T hkap0 hkap1]
        exact (raw_xi1_bound W S R hkap0 hkap1 t (x + G.q t)).trans
          (mul_le_mul_of_nonneg_left (density_dominates W hkap0 hkap1 t)
            (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hkap0 hkap1))
      tangential2_bound := fun t x => by
        rw [geometric_xi2_eq_raw S R G T hkap0 hkap1]
        exact (raw_xi2_bound W S R hkap0 hkap1 C.curvature_le t (x + G.q t)).trans
          (mul_le_mul_of_nonneg_left (density_dominates W hkap0 hkap1 t)
            (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg hkap0 hkap1))
      tangential_period_bound := by
        intro t x hx
        let f : ℝ → ℝ := frameTangential (Ydot R G) (shiftedPsi R G) t
        let fp : ℝ → ℝ := fun y =>
          (spatialFrames S R G T hkap0 hkap1).1.xi1 t y
        have hd := RearOwnDriftFundamental.abs_le_of_deriv_le_on_Icc
          (f := f) (f' := fp)
          (le_of_lt (hrearPos t))
          (fun y => (spatialFrames S R G T hkap0 hkap1).1.deriv1 t y)
          (by
            dsimp [f]
            simpa [Ydot, shiftedPsi, xi] using
              RearOwnFrameGaugeFlowReanchoring.frameTangential_shiftedYdot_zero
                R.Ydot S.psi G.q t)
          (fun y => by
            change |(geometricSpatialFrames S R G T hkap0 hkap1).1.xi1 t y| ≤
              GaugeMarkedDataOfRearFamily.rearKappa1 kap * W.Delta.m t
            rw [geometric_xi1_eq_raw S R G T hkap0 hkap1]
            exact raw_xi1_bound W S R hkap0 hkap1 t (y + G.q t)) hx
        exact hd.trans (calc
          rearArclength (delta S G.q t) (period A t) *
                (GaugeMarkedDataOfRearFamily.rearKappa1 kap * W.Delta.m t) ≤
              QmaxNext *
                (GaugeMarkedDataOfRearFamily.rearKappa1 kap * W.Delta.m t) :=
            mul_le_mul_of_nonneg_right (hrearLe t)
              (mul_nonneg
                (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hkap0 hkap1)
                (W.Delta.m_nonneg t))
          _ = GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap *
              W.Delta.m t := by
            simp [GaugeRearFamilyFromFront.rearDriftConst,
              GaugeMarkedDataOfRearFamily.rearKappa1]
            ring)
      rearKappa1_le := C.rearKappa1_le
      Kx_bound := fun t x => by
        simpa [kx0, curvatureConst,
          FiniteSmoothRearFamilyMarkingAwareSmoothSource.successorKx] using
          RearOwnTangential.abs_curvDeriv_le_strip hkap0 hkap1
            (S.strip_nonnegative t (S.sf t (x + G.q t)))
            (S.strip_le t (S.sf t (x + G.q t)))
            (C.curvature_le t (S.sf t (x + G.q t)))
      Kx_nonnegative := fun _ => hkx0
      Kx_le := fun _ => le_rfl
      gS_bound := fun t x => by
        have h := (hgSraw t (x + G.q t)).trans
          (mul_le_mul_of_nonneg_left (density_dominates W hkap0 hkap1 t) hdd0)
        simpa [gS, TimeDependentSpatialReanchoring.shift] using h
      Dd_le := fun _ => le_rfl
      density_continuous := W.Delta.cont_m.div_const _
      density_nonnegative := density_nonnegative W hkap0 hkap1
      density_support := fun t ht => by simp [dens, density, W.Delta.m_stop t ht]
      density_domination := fun _ => le_rfl
      numerical_A := C.numerical_A
      numerical_K := C.numerical_K }

end FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
