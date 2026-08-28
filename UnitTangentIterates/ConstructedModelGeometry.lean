import UnitTangentIterates.ConstructedConfiguredSequence
import UnitTangentIterates.TwoCapPairsAssembly
import UnitTangentIterates.TwoCapMarked
import UnitTangentIterates.SelectedInverseEmbedded

/-!
# Geometry produced by the constructed configured sequence

This file is a paper-facing facade for the geometric information which survives
in `ConfiguredModelSequence`.  In particular, every level has an explicit
steering function, exact front/rear closure, and the exact unit-tangent
identity.  The curvature is nonnegative, but the configured-sequence interface
does not retain a positive curvature floor.  Consequently strict convexity and
embeddedness cannot honestly be recovered here from that interface alone.

Likewise, the hypotheses of `WidthUniformProduced` concern a single continuous
family in the separation parameter, with a centered-angle positivity statement.
Those data are not fields of `ConfiguredModelSequence`, so no uniform-width
claim is included below.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral
open ModelOrbitDefect UnconditionalAssembly TwoCapPairsAssembly

namespace ConstructedModelGeometry

/-- The exact two-cap geometry available at one level of a configured model
sequence.  `curvature_nonneg` is the precise convexity conclusion retained by
the construction; no uniform or pointwise positive lower bound is asserted. -/
structure ExactPairCertificate
    (kappa delta : ℝ → ℝ) (H theta0 steeringCap : ℝ) : Prop where
  separation_pos : 0 < H
  curvature_continuous : Continuous kappa
  curvature_periodic : Function.Periodic kappa H
  curvature_nonneg : ∀ s, 0 ≤ kappa s
  total_turning : ∫ r in (0 : ℝ)..H, kappa r = π
  steering_cap_nonneg : 0 ≤ steeringCap
  steering_cap_lt_one : steeringCap < 1
  steering_continuous : Continuous delta
  steering_periodic : Function.Periodic delta H
  steering_mem : ∀ s, delta s ∈ Icc 0 (arcsin steeringCap)
  steering_ode : ∀ s, HasDerivAt delta (kappa s - sin (delta s)) s
  rear_speed_pos : ∀ s, 0 < cos (delta s)
  front_unit_speed : ∀ s,
    ‖deriv (front kappa theta0 H) s‖ = 1
  front_halfPeriod : ∀ s,
    front kappa theta0 H (s + H) = -front kappa theta0 H s
  front_periodic : Function.Periodic (front kappa theta0 H) (2 * H)
  front_perimeter :
    ∫ s in (0 : ℝ)..(2 * H), ‖deriv (front kappa theta0 H) s‖ = 2 * H
  rear_velocity : ∀ s,
    HasDerivAt (rear kappa delta theta0 H)
      ((cos (delta s) : ℂ) *
        Complex.exp (Complex.I *
          (RearTrack.rearAngle (frontAngle kappa theta0) delta s : ℂ))) s
  unitTangent_exact : ∀ s,
    rear kappa delta theta0 H s +
        deriv (rear kappa delta theta0 H) s /
          ‖deriv (rear kappa delta theta0 H) s‖ =
      front kappa theta0 H s
  rear_halfPeriod : ∀ s,
    rear kappa delta theta0 H (s + H) = -rear kappa delta theta0 H s
  rear_periodic : Function.Periodic (rear kappa delta theta0 H) (2 * H)
  rear_perimeter :
    ∫ s in (0 : ℝ)..(2 * H), ‖deriv (rear kappa delta theta0 H) s‖ =
      2 * ∫ s in (0 : ℝ)..H, cos (delta s)

/-- Every level of a configured model sequence produces an exact two-cap pair.
The steering is the arcsine of the periodized pulse stored in that level's
configuration. -/
theorem exactPairCertificate_of_configuredModelSequence
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (m : ConfiguredModelSequence kappas Hs eps) (n : ℕ) :
    ∃ delta : ℝ → ℝ,
      ExactPairCertificate (kappas n) delta (Hs n) m.thetaBase m.au := by
  let c := m.configs n
  let Y : ℝ → ℝ := periodizedPulse c.yu (Hs n)
  let Yd : ℝ → ℝ := fun s => ∑' j : ℤ, c.yu' (s - j * Hs n)
  let delta : ℝ → ℝ := modelSteering Y
  have hYdef : ∀ s, Y s = ∑' j : ℤ, c.yu (s - j * Hs n) := by
    intro s
    rfl
  have hYc : Continuous Y := by
    dsimp [Y]
    exact PeriodizedTurning.continuous_periodization
      c.ha c.Ppos c.continuous_yu c.abs_yu_le
  have hYd : ∀ s, HasDerivAt Y (Yd s) s := by
    intro s
    exact ModelOrbitDefect.hasDerivAt_periodized
      c.ha c.Ppos c.hyuderiv c.abs_yu_le c.abs_yu'_le hYdef s
  have hYnonneg : ∀ s, 0 ≤ Y s := by
    intro s
    dsimp [Y, periodizedPulse]
    exact tsum_nonneg fun _ => c.hyu0 _
  have hYupper : ∀ s, Y s ≤ m.au := by
    intro s
    simpa [Y, periodizedPulse] using c.hYau s
  have hYabs : ∀ s, |Y s| ≤ m.au := by
    intro s
    rw [abs_of_nonneg (hYnonneg s)]
    exact hYupper s
  have hYper : Function.Periodic Y (Hs n) := by
    dsimp [Y]
    exact PeriodizedTurning.periodic_periodization c.yu (Hs n)
  have hdc : Continuous delta :=
    ModelOrbitDefect.continuous_modelSteering hYc
  have hdper : Function.Periodic delta (Hs n) := by
    intro s
    simp only [delta, modelSteering, hYper s]
  have hdmem : ∀ s, delta s ∈ Icc 0 (arcsin m.au) := by
    intro s
    constructor
    · simpa [delta, modelSteering] using Real.arcsin_nonneg.mpr (hYnonneg s)
    · simpa [delta, modelSteering] using Real.arcsin_le_arcsin (hYupper s)
  have hode : ∀ s, HasDerivAt delta (kappas n s - sin (delta s)) s := by
    intro s
    have h := ModelOrbitDefect.hasDerivAt_modelSteering
      (hYd s) c.hau1 (hYabs s)
    simpa [delta, Y, Yd, modelCurvature, periodizedPulse, m.curvature_eq n] using h
  have hcosge : ∀ s, sqrt (1 - m.au ^ 2) ≤ cos (delta s) := by
    intro s
    exact ModelOrbitDefect.cos_modelSteering_ge (hYabs s)
  have hsqrtpos : 0 < sqrt (1 - m.au ^ 2) :=
    ModelOrbitDefect.sqrt_one_sub_sq_pos c.hau0 c.hau1
  have hcospos : ∀ s, 0 < cos (delta s) := by
    intro s
    exact lt_of_lt_of_le hsqrtpos (hcosge s)
  have hk : Continuous (kappas n) := m.curvature_continuous n
  have hknonneg : ∀ s, 0 ≤ kappas n s := by
    intro s
    rw [m.curvature_eq n]
    exact c.KP_nonneg s
  refine ⟨delta, ?_⟩
  refine
    { separation_pos := m.separation_pos n
      curvature_continuous := m.curvature_continuous n
      curvature_periodic := m.curvature_periodic n
      curvature_nonneg := hknonneg
      total_turning := m.total_turning n
      steering_cap_nonneg := c.hau0
      steering_cap_lt_one := c.hau1
      steering_continuous := hdc
      steering_periodic := hdper
      steering_mem := hdmem
      steering_ode := hode
      rear_speed_pos := hcospos
      front_unit_speed := ?_
      front_halfPeriod := ?_
      front_periodic := ?_
      front_perimeter := ?_
      rear_velocity := ?_
      unitTangent_exact := ?_
      rear_halfPeriod := ?_
      rear_periodic := ?_
      rear_perimeter := ?_ }
  · intro s
    exact TwoCapPairsAssembly.front_unit_speed hk s
  · intro s
    exact TwoCapPairsAssembly.front_add_halfPeriod
      hk (m.curvature_periodic n) (m.total_turning n) s
  · exact TwoCapPairsAssembly.front_periodic
      hk (m.curvature_periodic n) (m.total_turning n)
  · exact TwoCapPairsAssembly.front_perimeter
      hk
  · intro s
    exact TwoCapPairsAssembly.rear_hasDerivAt hk (hode s)
  · intro s
    exact TwoCapPairsAssembly.unitTangentMap_rear_eq_front
      hk (hode s) (hcospos s)
  · intro s
    exact TwoCapPairsAssembly.rear_add_halfPeriod
      hk (m.curvature_periodic n) (m.total_turning n) hdper s
  · exact TwoCapPairsAssembly.rear_periodic
      hk (m.curvature_periodic n) (m.total_turning n) hdper
  · exact TwoCapPairsAssembly.rear_perimeter
      hk hdc hdper hode (fun s => (hcospos s).le)

/-- The precise extra datum needed to upgrade the constructed model curves from
nonnegative curvature to strict convexity.  The floor is allowed to depend on
the level; no uniform positive lower bound is required. -/
structure LevelwiseCurvatureFloor
    (kappas : ℕ → ℝ → ℝ) (kmin : ℕ → ℝ) : Prop where
  kmin_pos : ∀ n, 0 < kmin n
  lower : ∀ n s, kmin n ≤ kappas n s

/-- Strict convexity and embeddedness of both members of an exact pair. -/
structure StrictExactPairCertificate
    (kappa delta : ℝ → ℝ) (H theta0 steeringCap : ℝ) : Prop
    extends ExactPairCertificate kappa delta H theta0 steeringCap where
  front_angle_strict : StrictMono (frontAngle kappa theta0)
  front_embedded : InjOn (front kappa theta0 H) (Ico 0 (2 * H))
  rear_angle_strict : StrictMono (RearTrack.rearAngle (frontAngle kappa theta0) delta)
  rear_embedded : InjOn (rear kappa delta theta0 H) (Ico 0 (2 * H))

/-- An n-dependent positive curvature floor upgrades the exact identities to
strict convexity and embeddedness. -/
theorem StrictExactPairCertificate.of_floor
    {kappa delta : ℝ → ℝ} {H theta0 steeringCap kmin : ℝ}
    (base : ExactPairCertificate kappa delta H theta0 steeringCap)
    (hkminpos : 0 < kmin) (hkmin : ∀ s, kmin ≤ kappa s) :
    StrictExactPairCertificate kappa delta H theta0 steeringCap := by
  have hsinlower : ∀ s, kmin ≤ sin (delta s) := fun s =>
    SelectedInverseEmbedded.sin_steering_ge base.separation_pos
      base.steering_periodic base.steering_ode hkmin base.steering_mem s
  have hrearder : ∀ s,
      HasDerivAt (RearTrack.rearAngle (frontAngle kappa theta0) delta)
        (sin (delta s)) s := fun s =>
    RearTrack.hasDerivAt_rearAngle
      (CurvatureInterpolation.hasDerivAt_tangentAngle
        (θ₀ := theta0) base.curvature_continuous s)
      (base.steering_ode s)
  have hrearStrict :
      StrictMono (RearTrack.rearAngle (frontAngle kappa theta0) delta) := by
    refine strictMono_of_deriv_pos fun s => ?_
    rw [(hrearder s).deriv]
    exact lt_of_lt_of_le hkminpos (hsinlower s)
  have hdper2 : Function.Periodic delta (2 * H) := by
    intro s
    rw [show s + 2 * H = (s + H) + H by ring,
      base.steering_periodic (s + H), base.steering_periodic s]
  have hrearEmbedded :
      InjOn (rear kappa delta theta0 H) (Ico 0 (2 * H)) := by
    have h := SelectedInverseEmbedded.injOn_rearTrack_front
      base.separation_pos base.curvature_continuous base.curvature_periodic
      hkminpos base.steering_cap_nonneg base.steering_cap_lt_one hkmin
      base.total_turning (frontAngle kappa theta0) kappa delta
      (fun s => TwoCapPairsAssembly.front_hasDerivAt
        (theta0 := theta0) (H := H) base.curvature_continuous s)
      (fun s => CurvatureInterpolation.hasDerivAt_tangentAngle
        (θ₀ := theta0) base.curvature_continuous s)
      hdper2 base.steering_mem base.steering_ode
    simpa [rear] using h
  exact
    { base with
      front_angle_strict :=
        TwoCapMarked.strictMono_frontAngle
          base.curvature_continuous hkminpos hkmin
      front_embedded :=
        TwoCapMarked.injOn_front base.curvature_continuous
          base.curvature_periodic hkminpos hkmin base.total_turning
      rear_angle_strict := hrearStrict
      rear_embedded := hrearEmbedded }

/-- Paper-facing strict-geometry facade under exactly the missing analytic
certificate.  Each level may use its own positive floor. -/
theorem strictExactPairCertificates_of_levelwiseFloor
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ} {kmin : ℕ → ℝ}
    (m : ConfiguredModelSequence kappas Hs eps)
    (floor : LevelwiseCurvatureFloor kappas kmin) :
    ∀ n, ∃ delta : ℝ → ℝ,
      StrictExactPairCertificate (kappas n) delta (Hs n) m.thetaBase m.au := by
  intro n
  obtain ⟨delta, base⟩ := exactPairCertificate_of_configuredModelSequence m n
  exact ⟨delta, StrictExactPairCertificate.of_floor base
    (floor.kmin_pos n) (floor.lower n)⟩

/-- The fully constructed sequence, together with exact two-cap geometry at
every level.  This is the strongest geometric statement obtainable solely from
`exists_configuredModelSequence_of_eps`: its result type contains nonnegative
curvature but no positive curvature floor, and it does not retain the
continuous-family data required by the uniform-width theorem. -/
theorem exists_constructedModelGeometry_of_eps
    {eps : ℝ} (heps : 0 < eps) (heps10 : eps ≤ (1 : ℝ) / 10) :
    ∃ (kappas : ℕ → ℝ → ℝ) (Hs : ℕ → ℝ)
        (deltaStep kd kstar cst beta : ℝ),
      0 < deltaStep ∧
      (∀ n, Hs n + deltaStep ≤ Hs (n + 1)) ∧
      ∃ m : ConfiguredModelSequence
          kappas Hs (fun _ => (1 : ℝ)),
        (∀ n, ∃ delta : ℝ → ℝ,
          ExactPairCertificate
            (kappas n) delta (Hs n) m.thetaBase m.au) ∧
        Summable (fun n =>
          CurvatureStabilityL1.l1Modulus (2 * kd)
            (cst * Real.exp (-(beta * Hs (n + 1)))) (Hs n)
            * (1 : ℝ) ^ 2 * (1 + kstar * (1 : ℝ))) := by
  obtain ⟨kappas, Hs, deltaStep, kd, kstar, cst, beta,
      hstep, hgrowth, hm, hsum⟩ :=
    exists_configuredModelSequence_of_eps heps heps10
  obtain ⟨hm⟩ := hm
  refine ⟨kappas, Hs, deltaStep, kd, kstar, cst, beta,
    hstep, hgrowth, hm, ?_, hsum⟩
  intro n
  exact exactPairCertificate_of_configuredModelSequence hm n

end ConstructedModelGeometry
