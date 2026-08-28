import UnitTangentIterates.FiniteSmoothRearFamilyAnalyticSource
import UnitTangentIterates.FiniteSmoothRearFamilyAppliedSource
import UnitTangentIterates.GaugeRearFamilyFromFrontIntrinsic

/-!
# Marking-aware analytic sources for rear-family transport

The legacy analytic source identifies the input normal velocity through the
affine physical marking `P t * u`.  Recursive gauge endpoints carry a
nonaffine marking.  This sibling retains that marking and its first two spatial
jets, while the rear-family theorem consumes the intrinsic bound on `etaF`
directly.
-/

noncomputable section

open Function Set MarkedSpace PathMetric PathMetric.NormalPath
  RearOwnArclength RearFamilyFrame RearTrack

namespace FiniteSmoothRearFamilyMarkingAwareSource

open EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyEnrichedMapProvider
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- Continuity and a positive quasi-periodic drift already force surjectivity;
monotonicity of the marking is not needed for this zeroth-order argument. -/
theorem surjective_of_continuous_quasiPeriodic
    {phi : ℝ → ℝ} {Q : ℝ} (hQ : 0 < Q) (hcont : Continuous phi)
    (hshift : ∀ u, phi (u + 1) = phi u + Q) : Surjective phi := by
  have hnat : ∀ n : ℕ, phi (n : ℝ) = phi 0 + (n : ℝ) * Q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.cast_succ, hshift, ih]
        ring
  have hneg : ∀ n : ℕ, phi (-(n : ℝ)) = phi 0 - (n : ℝ) * Q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hshift (-((n + 1 : ℕ) : ℝ))
        have heq : -((n + 1 : ℕ) : ℝ) + 1 = -(n : ℝ) := by
          push_cast
          ring
        rw [heq, ih] at hs
        push_cast at hs ⊢
        linarith
  intro x
  obtain ⟨n, hn⟩ := exists_nat_ge (|x - phi 0| / Q)
  have hnQ : |x - phi 0| ≤ (n : ℝ) * Q := by
    rw [div_le_iff₀ hQ] at hn
    exact hn
  have hxmem : x ∈ Icc (phi (-(n : ℝ))) (phi (n : ℝ)) := by
    rw [hneg, hnat]
    constructor <;> linarith [neg_abs_le (x - phi 0), le_abs_self (x - phi 0)]
  have hle : (-(n : ℝ)) ≤ (n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  obtain ⟨u, -, hu⟩ :=
    intermediate_value_Icc hle hcont.continuousOn hxmem
  exact ⟨u, hu⟩

/-- The exact spatial regularity needed by the gauge construction. -/
structure SpatialFrameRegularity
    {p q : Data} (Gamma : NormalPath p q)
    (Ydot : ℝ → ℝ → ℂ) (Theta delta sf : ℝ → ℝ → ℝ)
    (P m : ℝ → ℝ) (kh Qmax : ℝ) where
  tangential : RearOwnFrameDrift.SpatialC2
    (frameTangential Ydot (rearOwnAngle Theta delta sf))
  normal : RearOwnFrameDrift.SpatialC2
    (frameNormal Ydot (rearOwnAngle Theta delta sf))
  tangential1_bound : ∀ t x,
    |tangential.xi1 t x| ≤ GaugeMarkedDataOfRearFamily.rearKappa1 kh * m t
  tangential2_bound : ∀ t x,
    |tangential.xi2 t x| ≤ GaugeMarkedDataOfRearFamily.rearKappa2 kh * m t
  tangential_period_bound : ∀ t, ∀ x ∈ Icc (0 : ℝ) (rearArclength (delta t) (P t)),
    |frameTangential Ydot (rearOwnAngle Theta delta sf) t x| ≤
      GaugeRearFamilyFromFront.rearDriftConst Qmax kh * Gamma.m t

/-- Smooth sources retain their former joint certificate; stopped sources may
supply only the spatial certificate actually consumed downstream. -/
inductive FrameRegularity
    {p q : Data} (Gamma : NormalPath p q)
    (Ydot : ℝ → ℝ → ℂ) (Theta delta sf : ℝ → ℝ → ℝ)
    (P m : ℝ → ℝ) (kh Qmax : ℝ) : Prop
  | joint
      (velocity : ContDiff ℝ (2 : ℕ) (uncurry Ydot))
      (angle : ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Theta delta sf)))
  | spatial (certificate : SpatialFrameRegularity Gamma Ydot Theta delta sf P m kh Qmax)

structure MarkingAwareSource
    {p q : Data} (Gamma : NormalPath p q)
    (P0 kh khat Qmax : ℝ) where
  F : ℝ → ℝ → ℂ
  Theta : ℝ → ℝ → ℝ
  delta : ℝ → ℝ → ℝ
  K : ℝ → ℝ → ℝ
  sf : ℝ → ℝ → ℝ
  P : ℝ → ℝ
  P' : ℝ → ℝ
  Ydot : ℝ → ℝ → ℂ
  etaF : ℝ → ℝ → ℝ
  alphaT : ℝ → ℝ → ℝ
  kT : ℝ → ℝ → ℝ
  Kx : ℝ → ℝ
  Dd : ℝ → ℝ
  gS : ℝ → ℝ → ℝ
  m : ℝ → ℝ
  kx : ℝ
  d : ℝ
  kh_nonnegative : 0 ≤ kh
  kh_lt_one : kh < 1
  strip_nonnegative : ∀ t s, 0 ≤ delta t s
  strip_le : ∀ t s, delta t s ≤ Real.arcsin kh
  curvature_le : ∀ t s, |K t s| ≤ kh
  front_frenet : ∀ t s,
    HasDerivAt (F t) (Complex.exp (Complex.I * (Theta t s : ℂ))) s
  angle_frenet : ∀ t s, HasDerivAt (Theta t) (K t s) s
  steering : ∀ t s,
    HasDerivAt (delta t) (K t s - Real.sin (delta t s)) s
  sf_deriv : ∀ t x,
    HasDerivAt (sf t) (1 / Real.cos (delta t (sf t x))) x
  sf_rightInverse : ∀ t x, rearArclength (delta t) (sf t x) = x
  cos_ne_zero : ∀ t s, Real.cos (delta t s) ≠ 0
  rear_time_deriv : ∀ t x,
    HasDerivAt (fun r => rearOwn F Theta delta sf r x) (Ydot t x) t
  front_contDiff : ContDiff ℝ 1 (uncurry F)
  angle_contDiff : ContDiff ℝ 1 (uncurry Theta)
  steering_contDiff : ContDiff ℝ 1 (uncurry delta)
  sf_contDiff : ContDiff ℝ 1 (uncurry sf)
  period_contDiff : ContDiff ℝ 1 P
  period_deriv : ∀ t, HasDerivAt P (P' t) t
  frame_regularity : FrameRegularity Gamma Ydot Theta delta sf P m kh Qmax
  rear_curvature_contDiff :
    ContDiff ℝ 1 (uncurry fun t x => Real.tan (delta t (sf t x)))
  steering_periodic : ∀ t, Function.Periodic (delta t) (P t)
  front_periodic : ∀ t s, F t (s + P t) = F t s
  angle_periodic : ∀ t s, Theta t (s + P t) = Theta t s + 2 * Real.pi
  rear_period_pos : ∀ t, 0 < rearArclength (delta t) (P t)
  rear_period_le : ∀ t, rearArclength (delta t) (P t) ≤ Qmax
  tangential_zero : ∀ t,
    frameTangential Ydot (rearOwnAngle Theta delta sf) t 0 = 0
  jacobi : ∀ t x,
    HasDerivAt
      (fun x' => frameNormal Ydot (rearOwnAngle Theta delta sf) t x')
      (etaF t (sf t x) / Real.cos (delta t (sf t x)) -
        frameNormal Ydot (rearOwnAngle Theta delta sf) t x) x
  period_pos : ∀ t, 0 < P t
  phi : ℝ → ℝ → ℝ
  phi1 : ℝ → ℝ → ℝ
  phi2 : ℝ → ℝ → ℝ
  eta_link : ∀ t u, Gamma.eta t u = etaF t (phi t u)
  phi_shift : ∀ t u, phi t (u + 1) = phi t u + P t
  phi_deriv : ∀ t u, HasDerivAt (phi t) (phi1 t u) u
  phi1_deriv : ∀ t u, HasDerivAt (phi1 t) (phi2 t u) u
  phi1_continuous : ∀ t, Continuous (phi1 t)
  phi2_continuous : ∀ t, Continuous (phi2 t)
  etaF_bound : ∀ t s, |etaF t s| ≤ Gamma.m t
  rearKappa1_le : GaugeMarkedDataOfRearFamily.rearKappa1 kh ≤ khat
  rear_angle_time_deriv : ∀ t x,
    HasDerivAt (fun r => rearOwnAngle Theta delta sf r x) (alphaT t x) t
  rear_curvature_time_deriv : ∀ t x,
    HasDerivAt (fun r => Real.tan (delta r (sf r x))) (kT t x) t
  rear_angle_time_continuous : Continuous (uncurry alphaT)
  rear_curvature_time_continuous : Continuous (uncurry kT)
  rear_angle_time_spatial : ∀ t s, HasDerivAt (alphaT t) (kT t s) s
  mixed_derivative : ∀ t s, ∃ W : ℂ,
    HasDerivAt
      (fun r => Complex.exp
        (Complex.I * (rearOwnAngle Theta delta sf r s : ℂ))) W t ∧
    HasDerivAt
      (fun x =>
        (frameTangential Ydot (rearOwnAngle Theta delta sf) t x : ℂ) *
            Complex.exp
              (Complex.I * (rearOwnAngle Theta delta sf t x : ℂ)) +
          (frameNormal Ydot (rearOwnAngle Theta delta sf) t x : ℂ) *
            (Complex.I * Complex.exp
              (Complex.I * (rearOwnAngle Theta delta sf t x : ℂ)))) W s
  Kx_bound : ∀ t x,
    |(K t (sf t x) - Real.sin (delta t (sf t x))) /
      Real.cos (delta t (sf t x)) ^ 3| ≤ Kx t
  Kx_nonnegative : ∀ t, 0 ≤ Kx t
  Kx_le : ∀ t, Kx t ≤ kx
  Kx_continuous : Continuous (uncurry fun t x =>
    (K t (sf t x) - Real.sin (delta t (sf t x))) /
      Real.cos (delta t (sf t x)) ^ 3)
  gS_deriv : ∀ t x,
    HasDerivAt
      (fun x' => etaF t (sf t x') / Real.cos (delta t (sf t x')))
      (gS t x) x
  gS_bound : ∀ t x, |gS t x| ≤ Dd t
  Dd_le : ∀ t, Dd t ≤ d * m t
  density_continuous : Continuous m
  density_nonnegative : ∀ t, 0 ≤ m t
  density_support : ∀ t ∉ Ioo (0 : ℝ) Gamma.T, m t = 0
  density_domination : ∀ t,
    Gamma.m t / Real.sqrt (1 - kh ^ 2) ≤ m t
  numerical_A :
    2 + 2 * khat * GaugeRearFamilyFromFront.rearDriftConst Qmax kh ≤
      1 / P0
  numerical_K :
    (d + 2) + khat ^ 2 +
        2 * GaugeRearFamilyFromFront.rearDriftConst Qmax kh * kx ≤
      1 / P0 ^ 2 + khat ^ 2


/-- Apply the long rear-family theorem using the intrinsic front normal bound.
The retained marking witnesses that this source is aligned with the actual
nonaffinely marked input path, but no affine identity is assumed. -/
def MarkingAwareSource.applyLong
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) := by
  let applySpatial (R : SpatialFrameRegularity Gamma A.Ydot A.Theta A.delta A.sf
      A.P A.m kh Qmax) :=
    GaugeRearFamilyFromFrontIntrinsic.exists_variableSpeed_normalPath_of_rearFamily_from_front_with_eta_spatialC2_of_intrinsic_bound
    (P := A.P) (P' := A.P') (F := A.F) (Θ := A.Theta)
    (δ := A.delta) (K := A.K) (sf := A.sf) (Ydot := A.Ydot)
    (etaF := A.etaF) (alphaT := A.alphaT) (kT := A.kT)
    (Kx := A.Kx) (Dd := A.Dd) (gS := A.gS) (m := A.m)
    (kx := A.kx) (d := A.d) (P0 := P0) (kh := kh)
    (khat := khat) (Qmax := Qmax) Gamma
    A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le
    A.curvature_le A.front_frenet A.angle_frenet A.steering A.sf_deriv
    A.sf_rightInverse A.cos_ne_zero A.rear_time_deriv A.front_contDiff
    A.angle_contDiff A.steering_contDiff A.sf_contDiff A.period_contDiff
    A.period_deriv R.tangential R.normal R.tangential1_bound R.tangential2_bound
    A.rear_curvature_contDiff A.steering_periodic A.front_periodic
    A.angle_periodic A.rear_period_pos A.rear_period_le A.tangential_zero
    A.jacobi A.etaF_bound A.rearKappa1_le
    A.rear_angle_time_deriv A.rear_curvature_time_deriv
    A.rear_angle_time_continuous A.rear_curvature_time_continuous
    A.rear_angle_time_spatial A.mixed_derivative A.Kx_bound
    A.Kx_nonnegative A.Kx_le A.Kx_continuous R.tangential_period_bound
    A.gS_deriv A.gS_bound
    A.Dd_le A.density_continuous A.density_nonnegative A.density_support
    A.density_domination A.numerical_A A.numerical_K
  cases A.frame_regularity with
  | spatial R => exact applySpatial R
  | joint hYdotC hangC =>
      have hYdotC1 : ContDiff ℝ (1 : ℕ) (uncurry A.Ydot) :=
        hYdotC.of_le (by norm_num)
      have hangC1 : ContDiff ℝ (1 : ℕ)
          (uncurry (rearOwnAngle A.Theta A.delta A.sf)) :=
        hangC.of_le (by norm_num)
      have hnormalPer : ∀ t, Function.Periodic
          (frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t)
          (rearArclength (A.delta t) (A.P t)) :=
        fun t => RearOwnDriftFundamental.periodic_frameNormal_rearOwn
          A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le A.cos_ne_zero
          A.front_frenet A.angle_frenet A.steering A.sf_deriv A.sf_rightInverse
          A.steering_periodic A.front_periodic A.angle_periodic A.front_contDiff
          A.angle_contDiff A.steering_contDiff A.sf_contDiff A.period_contDiff
          A.rear_time_deriv t
      have hroot : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by
        nlinarith [A.kh_nonnegative, A.kh_lt_one])
      have hroot1 : Real.sqrt (1 - kh ^ 2) ≤ 1 := Real.sqrt_le_one.2 (by
        nlinarith [A.kh_nonnegative, A.kh_lt_one])
      have hcostle : ∀ t, Gamma.m t ≤ A.m t := by
        intro t
        refine le_trans ?_ (A.density_domination t)
        rw [le_div_iff₀ hroot]
        nlinarith [Gamma.m_nonneg t]
      let Sxi := RearOwnFrameDrift.SpatialC2.ofContDiff
        (RearOwnTangential.contDiff_frameTangential hYdotC hangC)
      let Sen := RearOwnFrameDrift.SpatialC2.ofContDiff
        (RearOwnTangential.contDiff_frameNormal hYdotC hangC)
      have hCbd : ∀ t x, |Sxi.xi1 t x| ≤
          GaugeMarkedDataOfRearFamily.rearKappa1 kh * A.m t := by
        intro t x
        refine le_trans (RearOwnTangentialCost.abs_partialX_frameTangential_le_front
          (K := A.K) (Q := fun t => rearArclength (A.delta t) (A.P t))
          (etaF := A.etaF) (EF := Gamma.m) A.kh_nonnegative A.kh_lt_one
          A.strip_nonnegative A.strip_le A.front_frenet A.angle_frenet A.steering
          A.sf_deriv A.cos_ne_zero A.rear_time_deriv hYdotC1 hangC1
          A.rear_period_pos hnormalPer A.jacobi A.etaF_bound t x) ?_
        rw [GaugeMarkedDataOfRearFamily.rearKappa1, mul_comm]
        exact mul_le_mul_of_nonneg_left (hcostle t)
          (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg
            A.kh_nonnegative A.kh_lt_one)
      have hC2bd : ∀ t x, |Sxi.xi2 t x| ≤
          GaugeMarkedDataOfRearFamily.rearKappa2 kh * A.m t := by
        intro t x
        refine le_trans (RearOwnTangentialCostC2.abs_partialX_partialX_frameTangential_le_front
          (K := A.K) (Q := fun t => rearArclength (A.delta t) (A.P t))
          (etaF := A.etaF) (EF := Gamma.m) A.kh_nonnegative A.kh_lt_one
          A.strip_nonnegative A.strip_le A.curvature_le A.front_frenet A.angle_frenet
          A.steering A.sf_deriv A.cos_ne_zero A.rear_time_deriv hYdotC hangC
          A.rear_period_pos hnormalPer A.jacobi A.etaF_bound t x) ?_
        rw [GaugeMarkedDataOfRearFamily.rearKappa2]
        exact mul_le_mul_of_nonneg_left (hcostle t)
          (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
            A.kh_nonnegative A.kh_lt_one)
      have hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (rearArclength (A.delta t) (A.P t)),
          |frameTangential A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t x| ≤
            GaugeRearFamilyFromFront.rearDriftConst Qmax kh * Gamma.m t :=
        fun t x hx => RearOwnDriftFundamental.abs_frameTangential_le_cost_on_period
          (K := A.K) (etaF := A.etaF) (m := Gamma.m)
          A.kh_nonnegative A.kh_lt_one A.rear_period_pos A.rear_period_le
          A.strip_nonnegative A.strip_le A.cos_ne_zero A.front_frenet A.angle_frenet
          A.steering A.sf_deriv A.sf_rightInverse A.steering_periodic A.front_periodic
          A.angle_periodic A.front_contDiff A.angle_contDiff A.steering_contDiff
          A.sf_contDiff A.period_contDiff A.rear_time_deriv hYdotC1 hangC1 A.jacobi
          A.etaF_bound (fun t => Gamma.m_nonneg t) A.tangential_zero t hx
      exact applySpatial
        { tangential := Sxi
          normal := Sen
          tangential1_bound := hCbd
          tangential2_bound := hC2bd
          tangential_period_bound := hRbd }

/-- The nonaffine marking retained by a chosen long-theorem output gives the
marking side of a successor source without any identification with `P t * u`. -/
structure MarkingCertificate
    {p q : Data} (Gamma : NormalPath p q)
    (etaF : ℝ → ℝ → ℝ) (P : ℝ → ℝ) where
  phi : ℝ → ℝ → ℝ
  phi1 : ℝ → ℝ → ℝ
  phi2 : ℝ → ℝ → ℝ
  eta_link : ∀ t u, Gamma.eta t u = etaF t (phi t u)
  shift : ∀ t u, phi t (u + 1) = phi t u + P t
  deriv : ∀ t u, HasDerivAt (phi t) (phi1 t u) u
  deriv2 : ∀ t u, HasDerivAt (phi1 t) (phi2 t u) u
  phi1_continuous : ∀ t, Continuous (phi1 t)
  phi2_continuous : ∀ t, Continuous (phi2 t)

/-- A positive quasi-periodic marking transfers the path density bound from
the marked composite to the intrinsic normal velocity. -/
theorem MarkingCertificate.etaF_bound
    {a b : Data} {Delta : NormalPath a b} {etaF : ℝ → ℝ → ℝ}
    {P : ℝ → ℝ} (B : MarkingCertificate Delta etaF P)
    (hP : ∀ t, 0 < P t) : ∀ t s, |etaF t s| ≤ Delta.m t := by
  intro t s
  have hcont : Continuous (B.phi t) :=
    continuous_iff_continuousAt.2 fun u => (B.deriv t u).continuousAt
  have hsurj : Surjective (B.phi t) :=
    surjective_of_continuous_quasiPeriodic (hP t) hcont (B.shift t)
  obtain ⟨u, hu⟩ := hsurj s
  rw [← hu, ← B.eta_link t u]
  exact Delta.abs_eta_le t u

/-- The actual gauge marking and jets retained by a chosen long-theorem path
form the marking certificate for the next recursive level. -/
def MarkingCertificate.ofChosenPath
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : FiniteSmoothRearFamilyAnalyticSource.Source Gamma P0 kh khat Qmax}
    (E : FiniteSmoothRearFamilyAppliedSource.Applied Gamma A P1)
    (R : FiniteSmoothRearFamilyAppliedSource.ChosenPath
      Gamma A E.Phi a b) :
    MarkingCertificate R.Delta
      (FiniteSmoothRearFamilyAppliedSource.rearNormal A)
      (FiniteSmoothRearFamilyAppliedSource.rearPeriod A) :=
  { phi := E.Phi
    phi1 := R.phi1
    phi2 := R.phi2
    eta_link := R.eta_eq
    shift := R.shift
    deriv := R.phi1_deriv
    deriv2 := R.phi2_deriv
    phi1_continuous := R.phi1_continuous
    phi2_continuous := R.phi2_continuous }

/-- The actual chosen gauge endpoint supplies the intrinsic normal-velocity
bound required by the marking-aware long theorem. -/
theorem chosenPath_etaF_bound
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : FiniteSmoothRearFamilyAnalyticSource.Source Gamma P0 kh khat Qmax}
    (E : FiniteSmoothRearFamilyAppliedSource.Applied Gamma A P1)
    (R : FiniteSmoothRearFamilyAppliedSource.ChosenPath
      Gamma A E.Phi a b) :
    ∀ t s, |FiniteSmoothRearFamilyAppliedSource.rearNormal A t s| ≤
      R.Delta.m t := by
  intro t s
  have hcont : Continuous (E.Phi t) :=
    continuous_iff_continuousAt.2 fun u =>
      (R.phi1_deriv t u).continuousAt
  have hsurj : Surjective (E.Phi t) :=
    surjective_of_continuous_quasiPeriodic
      (A.rear_period_pos t) hcont (R.shift t)
  obtain ⟨u, hu⟩ := hsurj s
  rw [← hu, ← R.eta_eq t u]
  exact R.Delta.abs_eta_le t u

end FiniteSmoothRearFamilyMarkingAwareSource
