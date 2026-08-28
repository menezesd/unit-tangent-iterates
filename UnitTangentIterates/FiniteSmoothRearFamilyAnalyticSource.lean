import UnitTangentIterates.FiniteSmoothRearFamilyEnrichedMapProvider
import UnitTangentIterates.GaugeRearFamilyFromFront

/-!
# Correlated analytic sources for finite rear-family columns

`FiniteSmoothRearFamilyEnrichedMapProvider.Provider` consumes a selected
`CertifiedColumn`, but that erased column does not retain the front/rear
analytic data needed to run the long gauge theorem at the next depth.  This
module records those hypotheses before erasure.

The record below is deliberately theorem-shaped: its fields are precisely the
hypotheses of
`GaugeRearFamilyFromFront.exists_variableSpeed_normalPath_of_rearFamily_from_front_with_eta_c2flow_and_c2`.
The `applyLong` definition invokes that theorem directly; it is not a new
existence callback.  `CorrelatedColumn` then pairs the ordinary selected
column with one such source for every row and projects definitionally to the
existing API.
-/

noncomputable section

open Function Set MarkedSpace PathMetric PathMetric.NormalPath
  RearOwnArclength RearFamilyFrame RearTrack

namespace FiniteSmoothRearFamilyAnalyticSource

open EnrichedPhysicalChosenRichFamily
  FiniteSmoothRearFamilyEnrichedMapProvider
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- All analytic data required for one application of the long rear-family
gauge theorem.  No output or existence assertion is stored in this record. -/
structure Source
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
  rear_velocity_contDiff : ContDiff ℝ (2 : ℕ) (uncurry Ydot)
  rear_angle_contDiff :
    ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Theta delta sf))
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
  eta_link : ∀ t u, Gamma.eta t u = etaF t (P t * u)
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

/-- Apply the long theorem to a retained analytic source.  The result type is
inferred from the existing theorem, so this definition remains definitionally
aligned if the theorem's output is strengthened. -/
def Source.applyLong
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} (A : Source Gamma P0 kh khat Qmax) :=
  GaugeRearFamilyFromFront.exists_variableSpeed_normalPath_of_rearFamily_from_front_with_eta_c2flow_and_c2
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
    A.period_deriv A.rear_velocity_contDiff A.rear_angle_contDiff
    A.rear_curvature_contDiff A.steering_periodic A.front_periodic
    A.angle_periodic A.rear_period_pos A.rear_period_le A.tangential_zero
    A.jacobi A.period_pos A.eta_link A.rearKappa1_le
    A.rear_angle_time_deriv A.rear_curvature_time_deriv
    A.rear_angle_time_continuous A.rear_curvature_time_continuous
    A.rear_angle_time_spatial A.mixed_derivative A.Kx_bound
    A.Kx_nonnegative A.Kx_le A.Kx_continuous A.gS_deriv A.gS_bound
    A.Dd_le A.density_continuous A.density_nonnegative A.density_support
    A.density_domination A.numerical_A A.numerical_K

/-- A selected column together with the non-erased analytic input for each
rear-family step sourced from its next row. -/
structure CorrelatedColumn
    (Q current : ℕ → Data) (e : ℕ → ℕ → ℝ) (k : ℕ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal : ℕ → ℝ)
    (kh Qmax : ℕ → ℝ) (K0 K1 K2 : ℝ) where
  column : CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
    period diagonal (GaugeFamily period K0 K1 K2)
  source : ∀ n, Source
    (column.step.richStage (n + 1)).stage.increment
    (P0 n) (kh n) (khat n) (Qmax n)

/-- Forget the analytic source only at an existing erased API boundary. -/
def CorrelatedColumn.toCertifiedColumn
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax : ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) :=
  S.column

/-- Apply the long theorem rowwise before projecting the selected column. -/
def CorrelatedColumn.applyLong
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {kh Qmax : ℕ → ℝ} {K0 K1 K2 : ℝ}
    (S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2) (n : ℕ) :=
  (S.source n).applyLong

end FiniteSmoothRearFamilyAnalyticSource
