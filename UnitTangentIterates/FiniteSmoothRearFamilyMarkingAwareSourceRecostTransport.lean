import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSource
import UnitTangentIterates.CanonicalNormalPathRecost
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion

/-!
# Transporting marking-aware sources to a canonical recost

Canonical recosting preserves the path geometry and normal velocity but
replaces the path density.  Most source fields therefore transport directly.
For a source carrying only spatial frame regularity, one genuinely new fact
is required: its tangential drift must be bounded by the new path density.
The structure below isolates exactly that condition.
-/

noncomputable section

open Function Set MarkedSpace PathMetric PathMetric.NormalPath
  RearOwnArclength RearFamilyFrame RearTrack

namespace FiniteSmoothRearFamilyMarkingAwareSourceRecostTransport

open FiniteSmoothRearFamilyMarkingAwareSource
  GaugeMarkedDataOfRearFamily

variable {p q : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax : ℝ}

/-- Enlarge the source envelope just enough to dominate the canonical recost
density after the pinching loss. -/
def transportDensity
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (R : NormalPath p q) (t : ℝ) : ℝ :=
  A.m t + R.m t / Real.sqrt (1 - kh ^ 2)

/-- The only path-density-sensitive fact not recoverable from `recost_eta`.
It is unused when the source has joint frame regularity. -/
structure TransportInput
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (R : NormalPath p q) : Prop where
  d_nonnegative : 0 ≤ A.d
  tangential_period_bound : ∀ t, ∀ x ∈ Icc (0 : ℝ)
      (rearArclength (A.delta t) (A.P t)),
    |frameTangential A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t x| ≤
      GaugeRearFamilyFromFront.rearDriftConst Qmax kh * R.m t

private theorem sourceDensity_le_transportDensity
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (R : NormalPath p q) (t : ℝ) :
    A.m t ≤ transportDensity A R t := by
  unfold transportDensity
  exact le_add_of_nonneg_right
    (div_nonneg (R.m_nonneg t) (Real.sqrt_nonneg _))

/-- The first spatial derivative of the tangential drift is the selected-rear
normal velocity times the rear curvature.  Unlike the older joint-smooth
lemma, this proof uses the mixed-derivative witness retained by every
marking-aware source and the two `SpatialC2` derivative certificates. -/
theorem spatial_tangential1_eq
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (S : SpatialFrameRegularity Gamma A.Ydot A.Theta A.delta A.sf
      A.P A.m kh Qmax) (t x : ℝ) :
    S.tangential.xi1 t x =
      frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t x *
        Real.tan (A.delta t (A.sf t x)) := by
  let psi := rearOwnAngle A.Theta A.delta A.sf
  let tau : ℝ → ℝ → ℂ := fun r y =>
    Complex.exp (Complex.I * (psi r y : ℂ))
  obtain ⟨Z, hZt, hZx⟩ := A.mixed_derivative t x
  have htauT : HasDerivAt (fun r => tau r x)
      (Complex.I * (A.alphaT t x : ℂ) * tau t x) t := by
    simpa [tau, psi] using
      (MarkingDeviationC2.hasDerivAt_exp_angle
        (fun r => A.rear_angle_time_deriv r x) t)
  have hpsiX : ∀ y, HasDerivAt (psi t)
      (Real.tan (A.delta t (A.sf t y))) y := fun y =>
    RearOwnTangential.hasDerivAt_rearOwnAngle_space
      A.angle_frenet A.steering A.sf_deriv t y
  have htauX : HasDerivAt (tau t)
      (Complex.I * (Real.tan (A.delta t (A.sf t x)) : ℂ) * tau t x) x := by
    simpa [tau, psi] using
      (MarkingDeviationC2.hasDerivAt_exp_angle hpsiX x)
  have hxi : HasDerivAt
      (fun y => (frameTangential A.Ydot psi t y : ℂ))
      (S.tangential.xi1 t x : ℂ) x :=
    (Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt x
      (S.tangential.deriv1 t x)
  have heta : HasDerivAt
      (fun y => (frameNormal A.Ydot psi t y : ℂ))
      (S.normal.xi1 t x : ℂ) x :=
    (Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt x
      (S.normal.deriv1 t x)
  have hcoeff : HasDerivAt
      (fun y => (frameTangential A.Ydot psi t y : ℂ) +
        Complex.I * (frameNormal A.Ydot psi t y : ℂ))
      ((S.tangential.xi1 t x : ℂ) +
        Complex.I * (S.normal.xi1 t x : ℂ)) x := by
    exact hxi.add (heta.const_mul Complex.I)
  have hvelocity : HasDerivAt
      (fun y =>
        (frameTangential A.Ydot psi t y : ℂ) * tau t y +
          (frameNormal A.Ydot psi t y : ℂ) *
            (Complex.I * tau t y))
      (((S.tangential.xi1 t x : ℂ) +
          Complex.I * (S.normal.xi1 t x : ℂ)) * tau t x +
        ((frameTangential A.Ydot psi t x : ℂ) +
          Complex.I * (frameNormal A.Ydot psi t x : ℂ)) *
            (Complex.I * (Real.tan (A.delta t (A.sf t x)) : ℂ)) *
              tau t x) x := by
    have hprod := hcoeff.mul htauX
    convert hprod using 1
    · funext y
      simp only [Pi.add_apply, Pi.mul_apply]
      ring
    · ring
  have heqT : Z = Complex.I * (A.alphaT t x : ℂ) * tau t x :=
    hZt.unique htauT
  have heqX : Z =
      (((S.tangential.xi1 t x : ℂ) +
          Complex.I * (S.normal.xi1 t x : ℂ)) * tau t x +
        ((frameTangential A.Ydot psi t x : ℂ) +
          Complex.I * (frameNormal A.Ydot psi t x : ℂ)) *
            (Complex.I * (Real.tan (A.delta t (A.sf t x)) : ℂ)) *
              tau t x) := by
    exact hZx.unique (by simpa [psi, tau] using hvelocity)
  have hmix :
      ((0 : ℝ) : ℂ) * tau t x +
          Complex.I * (((1 : ℝ) * A.alphaT t x : ℝ) : ℂ) * tau t x =
        (((S.tangential.xi1 t x : ℝ) : ℂ) +
            Complex.I * ((S.normal.xi1 t x : ℝ) : ℂ)) * tau t x +
          (((frameTangential A.Ydot psi t x : ℝ) : ℂ) +
            Complex.I * ((frameNormal A.Ydot psi t x : ℝ) : ℂ)) *
              (Complex.I * ((Real.tan (A.delta t (A.sf t x)) : ℝ) : ℂ)) *
                tau t x := by
    simpa using heqT.symm.trans heqX
  have hfirst := (GeneralVariation.mixed_partial_general_variation
    (psi := psi t x) (vdot := 0) (v := 1)
    (psidot := A.alphaT t x) (xix := S.tangential.xi1 t x)
    (etax := S.normal.xi1 t x)
    (xi := frameTangential A.Ydot psi t x)
    (eta := frameNormal A.Ydot psi t x)
    (psix := Real.tan (A.delta t (A.sf t x))) (by
      simpa [tau] using hmix)).1
  linarith

set_option maxHeartbeats 800000 in
/-- A spatial source can be transported to any normal path whose density
pointwise dominates the source normal velocity.  The proof is the spatial
Jacobi argument: the mixed-partial identity identifies the derivative of the
rear tangential drift, and the zero at the selected base point is integrated
over one rear period. -/
def transportInput_of_spatial
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (R : NormalPath p q)
    (S : SpatialFrameRegularity Gamma A.Ydot A.Theta A.delta A.sf
      A.P A.m kh Qmax)
    (hd : 0 ≤ A.d)
    (heta : ∀ t u, |Gamma.eta t u| ≤ R.m t) :
    TransportInput A R := by
  refine
    { d_nonnegative := hd
      tangential_period_bound := ?_ }
  intro t x hx
  have hetaF : ∀ r s, |A.etaF r s| ≤ R.m r := by
    intro r s
    have hc : Continuous (A.phi r) := continuous_iff_continuousAt.2 fun u =>
      (A.phi_deriv r u).continuousAt
    have hs : Surjective (A.phi r) :=
      surjective_of_continuous_quasiPeriodic (A.period_pos r) hc
        (A.phi_shift r)
    obtain ⟨u, hu⟩ := hs s
    rw [← hu, ← A.eta_link r u]
    exact heta r u
  have hnormalPeriod : ∀ r, Periodic
      (frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) r)
      (rearArclength (A.delta r) (A.P r)) := by
    intro r
    exact RearOwnDriftFundamental.periodic_frameNormal_rearOwn
      A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le
      A.cos_ne_zero A.front_frenet A.angle_frenet A.steering A.sf_deriv
      A.sf_rightInverse A.steering_periodic A.front_periodic
      A.angle_periodic A.front_contDiff A.angle_contDiff
      A.steering_contDiff A.sf_contDiff A.period_contDiff
      A.rear_time_deriv r
  have hnormal : ∀ y,
      |frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t y| ≤
        R.m t / Real.sqrt (1 - kh ^ 2) := by
    intro y
    exact RearOwnTangentialCost.abs_frameNormal_le_slice
      A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le
      A.rear_period_pos hnormalPeriod A.jacobi
      hetaF t y
  have hsqrt : 0 < Real.sqrt (1 - kh ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [A.kh_nonnegative, A.kh_lt_one])
  have hsqrtSq : Real.sqrt (1 - kh ^ 2) ^ 2 = 1 - kh ^ 2 :=
    Real.sq_sqrt (by nlinarith [A.kh_nonnegative, A.kh_lt_one])
  have hxi : ∀ y, |S.tangential.xi1 t y| ≤
      GaugeMarkedDataOfRearFamily.rearKappa1 kh * R.m t := by
    intro y
    rw [spatial_tangential1_eq A S t y, abs_mul]
    have htan := RearOwnTangential.abs_tan_le_strip
      A.kh_nonnegative A.kh_lt_one
      (A.strip_nonnegative t (A.sf t y)) (A.strip_le t (A.sf t y))
    have hmul :
        |frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t y| *
            |Real.tan (A.delta t (A.sf t y))| ≤
          (R.m t / Real.sqrt (1 - kh ^ 2)) *
            (kh / Real.sqrt (1 - kh ^ 2)) :=
      mul_le_mul (hnormal y) htan (abs_nonneg _)
        (div_nonneg (R.m_nonneg t) (Real.sqrt_nonneg _))
    exact hmul.trans_eq (by
      rw [GaugeMarkedDataOfRearFamily.rearKappa1]
      calc
        (R.m t / Real.sqrt (1 - kh ^ 2)) *
              (kh / Real.sqrt (1 - kh ^ 2)) =
            (kh / Real.sqrt (1 - kh ^ 2) ^ 2) * R.m t := by
              field_simp [hsqrt.ne']
              <;> ring
        _ = (kh / (1 - kh ^ 2)) * R.m t := by rw [hsqrtSq])
  have hperiodBound := RearOwnDriftFundamental.abs_le_of_deriv_le_on_Icc
    (f := frameTangential A.Ydot
      (rearOwnAngle A.Theta A.delta A.sf) t)
    (f' := S.tangential.xi1 t)
    (B := GaugeMarkedDataOfRearFamily.rearKappa1 kh * R.m t)
    (A.rear_period_pos t).le (fun y => S.tangential.deriv1 t y)
    (A.tangential_zero t) hxi hx
  exact hperiodBound.trans (calc
    rearArclength (A.delta t) (A.P t) *
          (GaugeMarkedDataOfRearFamily.rearKappa1 kh * R.m t) ≤
        Qmax * (GaugeMarkedDataOfRearFamily.rearKappa1 kh * R.m t) := by
      simpa using mul_le_mul_of_nonneg_right (A.rear_period_le t)
        (mul_nonneg
          (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg
            A.kh_nonnegative A.kh_lt_one)
          (R.m_nonneg t))
    _ = GaugeRearFamilyFromFront.rearDriftConst Qmax kh * R.m t := by
      simp [GaugeRearFamilyFromFront.rearDriftConst,
        GaugeMarkedDataOfRearFamily.rearKappa1]
      ring)

private def recostFrameRegularity
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (R : NormalPath p q) (H : TransportInput A R) :
    FrameRegularity R A.Ydot A.Theta A.delta A.sf A.P
      (transportDensity A R) kh Qmax := by
  cases A.frame_regularity with
  | joint hYdot hangle => exact FrameRegularity.joint hYdot hangle
  | spatial S =>
      apply FrameRegularity.spatial
      exact
        { tangential := S.tangential
          normal := S.normal
          tangential1_bound := fun t x =>
            (S.tangential1_bound t x).trans
              (mul_le_mul_of_nonneg_left
                (sourceDensity_le_transportDensity A R t)
                (rearKappa1_nonneg A.kh_nonnegative A.kh_lt_one))
          tangential2_bound := fun t x =>
            (S.tangential2_bound t x).trans
              (mul_le_mul_of_nonneg_left
                (sourceDensity_le_transportDensity A R t)
                (rearKappa2_nonneg A.kh_nonnegative A.kh_lt_one))
          tangential_period_bound := H.tangential_period_bound }

/-- A marking-aware source transported to the canonical recost of its path.
All geometric fields are unchanged.  The source density is enlarged, while
the path-density bounds are rebuilt using `recost_eta` and `TransportInput`. -/
def transport
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (hC2 : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2.eta1))
    (heta2 : Continuous (Function.uncurry hC2.eta2))
    (H : TransportInput A
      (CanonicalNormalPathRecost.recost Gamma hC2 heta heta1 heta2)) :
    MarkingAwareSource
      (CanonicalNormalPathRecost.recost Gamma hC2 heta heta1 heta2)
      P0 kh khat Qmax := by
  let R := CanonicalNormalPathRecost.recost Gamma hC2 heta heta1 heta2
  have hroot : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by
    nlinarith [A.kh_nonnegative, A.kh_lt_one])
  refine
    { A with
      m := transportDensity A R
      frame_regularity := recostFrameRegularity A R H
      eta_link := ?_
      etaF_bound := ?_
      Dd_le := ?_
      density_continuous := ?_
      density_nonnegative := ?_
      density_support := ?_
      density_domination := ?_ }
  · intro t u
    simpa [R] using A.eta_link t u
  · intro t s
    have hphi : Surjective (A.phi t) :=
      surjective_of_continuous_quasiPeriodic (A.period_pos t)
        (Differentiable.continuous fun u =>
          (A.phi_deriv t u).differentiableAt)
        (A.phi_shift t)
    obtain ⟨u, hu⟩ := hphi s
    calc
      |A.etaF t s| = |Gamma.eta t u| := by
        rw [← hu, ← A.eta_link t u]
      _ = |R.eta t u| := by simp [R]
      _ ≤ R.m t := R.abs_eta_le t u
  · intro t
    exact (A.Dd_le t).trans
      (mul_le_mul_of_nonneg_left
        (sourceDensity_le_transportDensity A R t) H.d_nonnegative)
  · exact A.density_continuous.add
      (R.cont_m.div_const (Real.sqrt (1 - kh ^ 2)))
  · intro t
    exact add_nonneg (A.density_nonnegative t)
      (div_nonneg (R.m_nonneg t) hroot.le)
  · intro t ht
    have htGamma : t ∉ Ioo (0 : ℝ) Gamma.T := by
      simpa [R, CanonicalNormalPathRecost.recost] using ht
    rw [transportDensity, A.density_support t htGamma, R.m_stop t ht]
    simp
  · intro t
    unfold transportDensity
    exact le_add_of_nonneg_left (A.density_nonnegative t)

/-- The exact analytic slice certificate transports with the source.  Its
spatial functions are unchanged, while the two marked boundedness fields use
the definitional `recost_eta` identity. -/
def transportSlice
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (S : FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.AnalyticSuccessorSliceFacts A)
    (hC2 : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2.eta1))
    (heta2 : Continuous (Function.uncurry hC2.eta2))
    (H : TransportInput A
      (CanonicalNormalPathRecost.recost Gamma hC2 heta heta1 heta2)) :
    FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion.AnalyticSuccessorSliceFacts
      (transport A hC2 heta heta1 heta2 H) := by
  let R := CanonicalNormalPathRecost.recost Gamma hC2 heta heta1 heta2
  let B := transport A hC2 heta heta1 heta2 H
  refine
    { periodUpper := S.periodUpper
      periodLower_pos := S.periodLower_pos
      period_lower := ?_
      period_upper := ?_
      etaFs := S.etaFs
      etaF_deriv := ?_
      etaFs_continuous := S.etaFs_continuous
      etaF_periodic := ?_
      rearNormal_c2 := ?_
      normal_stopped := ?_
      markingLower := S.markingLower
      markingUpper := S.markingUpper
      marking_increment := ?_
      markingLower_pos := S.markingLower_pos
      marking_lower := ?_
      markingUpper_nonnegative := S.markingUpper_nonnegative
      marking_upper := ?_
      marked_bdd0 := ?_
      marked_bdd1 := ?_ }
  · simpa [B, transport] using S.period_lower
  · simpa [B, transport] using S.period_upper
  · simpa [B, transport] using S.etaF_deriv
  · simpa [B, transport] using S.etaF_periodic
  · simpa [B, transport] using S.rearNormal_c2
  · intro t ht
    have htGamma : t ∉ Ioo (0 : ℝ) Gamma.T := by
      simpa [R, CanonicalNormalPathRecost.recost] using ht
    simpa [B, transport] using S.normal_stopped t htGamma
  · simpa [B, transport] using S.marking_increment
  · intro t ht u
    have htGamma : t ∈ Ioo (0 : ℝ) Gamma.T := by
      simpa [R, CanonicalNormalPathRecost.recost] using ht
    simpa [B, transport] using S.marking_lower t htGamma u
  · intro t ht u
    have htGamma : t ∈ Ioo (0 : ℝ) Gamma.T := by
      simpa [R, CanonicalNormalPathRecost.recost] using ht
    simpa [B, transport] using S.marking_upper t htGamma u
  · intro t
    simpa [R] using S.marked_bdd0 t
  · intro t
    simpa [R] using S.marked_bdd1 t

end FiniteSmoothRearFamilyMarkingAwareSourceRecostTransport
