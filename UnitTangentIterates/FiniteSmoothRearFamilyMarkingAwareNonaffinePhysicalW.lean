import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedArclengthTransition
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
import UnitTangentIterates.AnchoredJacobiStableTransitionMonotone
import UnitTangentIterates.NearIdentityDistortionBudget
import UnitTangentIterates.VariableArclengthScaledJacobiTransition

/-!
# The marking-invariant physical `W` component for a nonaffine source

The scalar-period expression `P(t) * integral |eta(t,u)| du` is physical
arclength only in an affine marking.  For an arbitrary marking `phi`, the
correct density is its spatial Jacobian `phi1`.  This file proves that the
resulting component is exactly the intrinsic arclength integral and applies
the existing Jacobi estimate to an arbitrary theorem-produced chosen path.

No affine identity for the source density is used.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric
open PathMetric.NormalPath RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds

open FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
  VariableArclengthScaledJacobiTransition

/-- The physical `L1` component in an arbitrary spatial marking. -/
def jacobianPhysicalW (J eta : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, J t u * |eta t u|

/-- Change of variables through one possibly shifted period.  Periodicity
removes the irrelevant value of `phi 0`. -/
theorem integral_jacobian_abs_comp_eq_period
    {eta phi phi1 : ℝ → ℝ} {P : ℝ}
    (heta : Continuous eta) (hetaPer : Periodic eta P)
    (hphi : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi1c : Continuous phi1) (hshift : phi 1 = phi 0 + P) :
    (∫ u in (0 : ℝ)..1, phi1 u * |eta (phi u)|) =
      ∫ x in (0 : ℝ)..P, |eta x| := by
  have hchange := intervalIntegral.integral_comp_smul_deriv
    (a := (0 : ℝ)) (b := 1) (f := phi) (f' := phi1)
    (g := fun x ↦ |eta x|) (fun u _ ↦ hphi u) hphi1c.continuousOn heta.abs
  have hperabs : Periodic (fun x ↦ |eta x|) P := fun x ↦ by
    change |eta (x + P)| = |eta x|
    rw [hetaPer x]
  calc
    (∫ u in (0 : ℝ)..1, phi1 u * |eta (phi u)|) =
        ∫ x in phi 0..phi 1, |eta x| := by
      simpa [smul_eq_mul] using hchange
    _ = ∫ x in phi 0..phi 0 + P, |eta x| := by rw [hshift]
    _ = ∫ x in (0 : ℝ)..P, |eta x| := by
      simpa using (hperabs.intervalIntegral_add_eq (phi 0) 0)

/-- The source Jacobian-weighted slice is its intrinsic front-density
integral, even when the source marking is nonaffine. -/
theorem source_jacobian_slice_eq_intrinsic
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 m M : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (S : Nonaffine.Facts A P1 m M) (t : ℝ) :
    (∫ u in (0 : ℝ)..1, A.phi1 t u * |Gamma.eta t u|) =
      ∫ x in (0 : ℝ)..A.P t, |A.etaF t x| := by
  have hshift : A.phi t 1 = A.phi t 0 + A.P t := by
    simpa using A.phi_shift t 0
  calc
    (∫ u in (0 : ℝ)..1, A.phi1 t u * |Gamma.eta t u|) =
        ∫ u in (0 : ℝ)..1, A.phi1 t u * |A.etaF t (A.phi t u)| := by
      congr 1
      funext u
      rw [A.eta_link t u]
    _ = ∫ x in (0 : ℝ)..A.P t, |A.etaF t x| :=
      integral_jacobian_abs_comp_eq_period
        (Differentiable.continuous fun x ↦ (S.etaF_deriv t x).differentiableAt)
        (S.etaF_periodic t) (A.phi_deriv t) (A.phi1_continuous t) hshift

/-- The chosen Jacobian-weighted slice is the intrinsic selected-rear
density integral. -/
theorem chosen_jacobian_slice_eq_intrinsic
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 m M : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b)
    (S : Nonaffine.Facts A P1 m M) (t : ℝ) :
    (∫ u in (0 : ℝ)..1, W.phi1 t u * |W.Delta.eta t u|) =
      ∫ x in (0 : ℝ)..rearPeriod A t, |rearNormal A t x| := by
  have hrearPer : Periodic (rearNormal A t) (rearPeriod A t) := by
    simpa [rearNormal, rearPeriod] using
      RearOwnDriftFundamental.periodic_frameNormal_rearOwn
        A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le
        A.cos_ne_zero A.front_frenet A.angle_frenet A.steering A.sf_deriv
        A.sf_rightInverse A.steering_periodic A.front_periodic
        A.angle_periodic A.front_contDiff A.angle_contDiff
        A.steering_contDiff A.sf_contDiff A.period_contDiff A.rear_time_deriv t
  have hshift : E.Phi t 1 = E.Phi t 0 + rearPeriod A t := by
    simpa using W.shift t 0
  calc
    (∫ u in (0 : ℝ)..1, W.phi1 t u * |W.Delta.eta t u|) =
        ∫ u in (0 : ℝ)..1, W.phi1 t u * |rearNormal A t (E.Phi t u)| := by
      congr 1
      funext u
      rw [W.eta_eq t u]
    _ = ∫ x in (0 : ℝ)..rearPeriod A t, |rearNormal A t x| :=
      integral_jacobian_abs_comp_eq_period
        (S.rearNormal_c2 t).continuous hrearPer (W.phi1_deriv t)
        (W.phi1_continuous t) hshift

/-- Exact slicewise nonexpansiveness of physical `W` for a genuinely
nonaffine source and the actual chosen successor marking. -/
theorem chosen_jacobianPhysicalW_slice_le
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 m M : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b)
    (S : Nonaffine.Facts A P1 m M) (t : ℝ) :
    (∫ u in (0 : ℝ)..1, W.phi1 t u * |W.Delta.eta t u|) ≤
      ∫ u in (0 : ℝ)..1, A.phi1 t u * |Gamma.eta t u| := by
  have hrearPer : Periodic (rearNormal A t) (rearPeriod A t) := by
    simpa [rearNormal, rearPeriod] using
      RearOwnDriftFundamental.periodic_frameNormal_rearOwn
        A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le
        A.cos_ne_zero A.front_frenet A.angle_frenet A.steering A.sf_deriv
        A.sf_rightInverse A.steering_periodic A.front_periodic
        A.angle_periodic A.front_contDiff A.angle_contDiff
        A.steering_contDiff A.sf_contDiff A.period_contDiff A.rear_time_deriv t
  let C := GaugeGeometrySeparatedSliceCertificate.certificate
    (P0 := A.P t) (P1 := A.P t) (kh := kh)
    (P := fun _ ↦ A.P t)
    (delta := fun _ ↦ A.delta t) (K := fun _ ↦ A.K t)
    (etaF := fun _ ↦ A.etaF t) (etaFs := fun _ ↦ S.etaFs t)
    (etaR := fun _ ↦ rearNormal A t) (sf := fun _ ↦ A.sf t)
    (A.period_pos t) A.kh_nonnegative A.kh_lt_one
    (fun _ ↦ le_rfl) (fun _ ↦ le_rfl)
    (fun _ ↦ A.steering t) (fun _ ↦ A.strip_nonnegative t)
    (fun _ ↦ A.strip_le t) (fun _ ↦ A.steering_periodic t)
    (fun _ ↦ A.curvature_le t) (fun _ ↦ S.etaF_deriv t)
    (fun _ ↦ S.etaFs_continuous t) (fun _ ↦ S.etaF_periodic t)
    (fun _ ↦ A.sf_rightInverse t) (fun _ ↦ A.jacobi t)
    (fun _ ↦ hrearPer)
  have hraw := C.w 0
  have hfront :
      A.P t * (∫ u in (0 : ℝ)..1, |A.etaF t (A.P t * u)|) =
        ∫ x in (0 : ℝ)..A.P t, |A.etaF t x| := by
    rw [JacobiNormalized.integral_abs_comp_mul (A.period_pos t).ne' (A.etaF t)]
    field_simp [(A.period_pos t).ne']
  rw [chosen_jacobian_slice_eq_intrinsic W S t,
    source_jacobian_slice_eq_intrinsic S t, ← hfront]
  exact hraw

/-- Integrated exact nonexpansiveness.  Integrability is kept explicit because
the lightweight nonaffine source API only retains slicewise continuity. -/
theorem chosen_jacobianPhysicalW_le
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 m M : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b)
    (S : Nonaffine.Facts A P1 m M)
    (hsource : IntervalIntegrable
      (fun t ↦ ∫ u in (0 : ℝ)..1, A.phi1 t u * |Gamma.eta t u|) volume 0 1)
    (htarget : IntervalIntegrable
      (fun t ↦ ∫ u in (0 : ℝ)..1, W.phi1 t u * |W.Delta.eta t u|) volume 0 1) :
    jacobianPhysicalW W.phi1 W.Delta.eta ≤
      jacobianPhysicalW A.phi1 Gamma.eta := by
  exact intervalIntegral.integral_mono_on zero_le_one htarget hsource
    (fun t _ ↦ chosen_jacobianPhysicalW_slice_le W S t)

/-- Existing intrinsic-front physical integrability transports exactly to the
Jacobian-weighted nonaffine source component. -/
theorem source_jacobianPhysicalW_integrable
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 m M : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (S : Nonaffine.Facts A P1 m M)
    (H : IntervalIntegrable
      (fun t ↦ A.P t * ∫ u in (0 : ℝ)..1,
        |A.etaF t (A.P t * u)|) volume 0 1) :
    IntervalIntegrable
      (fun t ↦ ∫ u in (0 : ℝ)..1, A.phi1 t u * |Gamma.eta t u|)
      volume 0 1 := by
  have heq : (fun t ↦ ∫ u in (0 : ℝ)..1,
      A.phi1 t u * |Gamma.eta t u|) =
      fun t ↦ A.P t * ∫ u in (0 : ℝ)..1,
        |A.etaF t (A.P t * u)| := by
    funext t
    rw [source_jacobian_slice_eq_intrinsic S t,
      JacobiNormalized.integral_abs_comp_mul (A.period_pos t).ne' (A.etaF t)]
    field_simp [(A.period_pos t).ne']
  rw [heq]
  exact H

/-- Existing intrinsic-rear physical integrability transports exactly to the
Jacobian-weighted chosen component. -/
theorem chosen_jacobianPhysicalW_integrable
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 m M : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b)
    (S : Nonaffine.Facts A P1 m M)
    (H : IntervalIntegrable
      (fun t ↦ rearPeriod A t * ∫ u in (0 : ℝ)..1,
        |rearNormal A t (rearPeriod A t * u)|) volume 0 1) :
    IntervalIntegrable
      (fun t ↦ ∫ u in (0 : ℝ)..1,
        W.phi1 t u * |W.Delta.eta t u|) volume 0 1 := by
  have heq : (fun t ↦ ∫ u in (0 : ℝ)..1,
      W.phi1 t u * |W.Delta.eta t u|) =
      fun t ↦ rearPeriod A t * ∫ u in (0 : ℝ)..1,
        |rearNormal A t (rearPeriod A t * u)| := by
    funext t
    rw [chosen_jacobian_slice_eq_intrinsic W S t,
      ← intervalIntegral.integral_const_mul]
    have hrearPer : Periodic (rearNormal A t) (rearPeriod A t) := by
      simpa [rearNormal, rearPeriod] using
        RearOwnDriftFundamental.periodic_frameNormal_rearOwn
          A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le
          A.cos_ne_zero A.front_frenet A.angle_frenet A.steering A.sf_deriv
          A.sf_rightInverse A.steering_periodic A.front_periodic
          A.angle_periodic A.front_contDiff A.angle_contDiff
          A.steering_contDiff A.sf_contDiff A.period_contDiff A.rear_time_deriv t
    exact (integral_jacobian_abs_comp_eq_period
      (S.rearNormal_c2 t).continuous hrearPer
      (fun u ↦ by simpa using
        (hasDerivAt_const u (rearPeriod A t)).mul (hasDerivAt_id u))
      continuous_const (by ring)).symm
  rw [heq]
  exact H

/-! ## The tower-ready component adapter -/

/-- Components whose `W` entry uses the actual marking Jacobian.  The three
supremum channels remain in the marked coordinate, as required by the compact
marked-path topology. -/
def jacobianComponents (J eta : ℝ → ℝ → ℝ) : Components where
  w := jacobianPhysicalW J eta
  s0 := S 0 eta
  s1 := S 1 eta
  s2 := S 2 eta

/-- Comparison from a marked source to its intrinsic arclength components.
The `W` channel is nonexpansive (in applications, equal), `S0` is invariant,
and only `S1` uses the predecessor inverse first-jet bound. -/
structure SourceIntrinsicComparison
    (marked intrinsic : Components) (invLower : ℝ) : Prop where
  w : intrinsic.w ≤ marked.w
  s0 : intrinsic.s0 ≤ marked.s0
  s1 : intrinsic.s1 ≤ invLower * marked.s1

/-- Comparison from an intrinsic selected rear to its current chosen marking.
These are exactly the first and second spatial chain-rule bounds. -/
structure TargetMarkingComparison
    (intrinsic marked : Components) (upper second : ℝ) : Prop where
  w : marked.w ≤ intrinsic.w
  s0 : marked.s0 ≤ intrinsic.s0
  s1 : marked.s1 ≤ upper * intrinsic.s1
  s2 : marked.s2 ≤ upper ^ 2 * intrinsic.s2 + second * intrinsic.s1

/-- Normalized first-jet control retained by a nonaffine successor source. -/
structure SourceNormalizedJetBounds
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (eps : ℝ) : Prop where
  eps_nonnegative : 0 ≤ eps
  dphi : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u,
    |A.phi1 t u / A.P t - 1| ≤ eps

/-- Exact successor identities transport the predecessor chosen jet bound to
the next source without any affine-source assertion. -/
def SourceNormalizedJetBounds.ofPredecessor
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P0' kh' khat' Qmax' eps : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A} (W : ChosenPath Gamma A E.Phi a b)
    (A' : MarkingAwareSource W.Delta P0' kh' khat' Qmax')
    (J : NormalizedJetBounds W eps)
    (hperiod : A'.P = rearPeriod A) (hphi1 : A'.phi1 = W.phi1) :
    SourceNormalizedJetBounds A' eps where
  eps_nonnegative := J.eps_nonnegative
  dphi := by
    intro t ht u
    rw [hphi1, hperiod]
    exact J.dpsi t ht u

theorem SourceNormalizedJetBounds.lower
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax eps : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (J : SourceNormalizedJetBounds A eps) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (u : ℝ) :
    (1 - eps) * A.P t ≤ A.phi1 t u := by
  have h := (abs_le.mp (J.dphi t ht u)).1
  have hP := A.period_pos t
  apply (le_div_iff₀ hP).1
  simpa [sub_mul] using h

theorem SourceNormalizedJetBounds.upper
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax eps : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (J : SourceNormalizedJetBounds A eps) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (u : ℝ) :
    A.phi1 t u ≤ (1 + eps) * A.P t := by
  have h := (abs_le.mp (J.dphi t ht u)).2
  have hP := A.period_pos t
  apply (div_le_iff₀ hP).1
  simpa [add_mul, add_comm] using h

/-- Integrate the three source comparison inequalities.  In the concrete
nonaffine row, `H.w` is supplied by the exact Jacobian change of variables and
`H.s0/H.s1` by `frontComparison_of_reparam` using the predecessor jet lower
bound. -/
def sourceIntrinsicComparison_of_slices
    {J marked intrinsic : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {invLower : ℝ}
    (Fmarked : FunctionalIntegrable marked)
    (Fintrinsic : FunctionalIntegrable intrinsic)
    (hw : physicalW P intrinsic ≤ jacobianPhysicalW J marked)
    (H : ∀ t ∈ Icc (0 : ℝ) 1,
      GaugeNormalPathVariableSeparatedNonaffine.FrontComparison
        (intrinsic t) (marked t) 1 1 invLower) :
    SourceIntrinsicComparison (jacobianComponents J marked)
      (physicalComponents P intrinsic) invLower where
  w := hw
  s0 := by
    exact intervalIntegral.integral_mono_on zero_le_one Fintrinsic.s0 Fmarked.s0
      (fun t ht ↦ by simpa using (H t ht).s0)
  s1 := by
    calc
      S 1 intrinsic ≤ ∫ t in (0 : ℝ)..1,
          invLower * supNorm (iteratedDeriv 1 (marked t)) :=
        intervalIntegral.integral_mono_on zero_le_one Fintrinsic.s1
          (Fmarked.s1.const_mul invLower) (fun t ht ↦ (H t ht).s1)
      _ = invLower * S 1 marked := by
        unfold S
        rw [intervalIntegral.integral_const_mul]

/-- Existing time-dependent reparametrization bounds become the target half
of the nonaffine component adapter once the exact Jacobian `W` comparison is
substituted for their coarse unweighted `W` estimate. -/
def targetMarkingComparison_of_timeReparamBounds
    {J intrinsic target : ℝ → ℝ → ℝ} {P : ℝ → ℝ}
    {m upper second : ℝ}
    (hw : jacobianPhysicalW J target ≤ physicalW P intrinsic)
    (B : VariableFixedReparamBounds P intrinsic target m upper second) :
    TargetMarkingComparison (physicalComponents P intrinsic)
      (jacobianComponents J target) upper second where
  w := hw
  s0 := B.s0
  s1 := B.s1
  s2 := B.s2

/-- Full nonaffine transition adapter.

An intrinsic Jacobi row is nonexpansive in `W`.  The predecessor normalized
first jet is used only through `invLower`; the current chosen first and second
jets are used through `upper` and `second`.  Consequently the tower distortion
is `a = 1`, `MA = upper * invLower`, `NA = second`.
-/
theorem transition_of_intrinsic_and_markingComparisons
    {source intrinsicFront intrinsicRear target : Components}
    {invLower upper second C0 C1 C2 : ℝ}
    (hsource : source.Nonnegative)
    (hinv : 1 ≤ invLower) (hupper : 0 ≤ upper) (hsecond : 0 ≤ second)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (HS : SourceIntrinsicComparison source intrinsicFront invLower)
    (Hraw : Transition intrinsicFront intrinsicRear 1 1 0 C0 C1 C2)
    (HT : TargetMarkingComparison intrinsicRear target upper second) :
    Transition source target 1 (upper * invLower) second C0 C1 C2 := by
  have hInv0 : 0 ≤ invLower := zero_le_one.trans hinv
  have hsum0 : 0 ≤ source.w + source.s0 := add_nonneg hsource.w hsource.s0
  have hsum1 : 0 ≤ source.w + source.s0 + source.s1 :=
    add_nonneg hsum0 hsource.s1
  have hfront01 : intrinsicFront.w + intrinsicFront.s0 ≤
      source.w + source.s0 := add_le_add HS.w HS.s0
  have hfront012 : intrinsicFront.w + intrinsicFront.s0 + intrinsicFront.s1 ≤
      invLower * (source.w + source.s0 + source.s1) := by
    calc
      intrinsicFront.w + intrinsicFront.s0 + intrinsicFront.s1 ≤
          source.w + source.s0 + invLower * source.s1 :=
        add_le_add hfront01 HS.s1
      _ ≤ invLower * (source.w + source.s0 + source.s1) := by
        have h01 : source.w + source.s0 ≤
            invLower * (source.w + source.s0) := by nlinarith
        nlinarith
  have hrear1 : intrinsicRear.s1 ≤
      C1 * (source.w + source.s0) := by
    calc
      intrinsicRear.s1 ≤ 1 * C1 *
          (intrinsicFront.w + intrinsicFront.s0) := Hraw.s1
      _ ≤ C1 * (source.w + source.s0) := by
        simpa using mul_le_mul_of_nonneg_left hfront01 hC1
  have hrear2 : intrinsicRear.s2 ≤
      C2 * (invLower * (source.w + source.s0 + source.s1)) := by
    calc
      intrinsicRear.s2 ≤ 1 ^ 2 * C2 *
          (intrinsicFront.w + intrinsicFront.s0 + intrinsicFront.s1) +
          0 * C1 * (intrinsicFront.w + intrinsicFront.s0) := Hraw.s2
      _ = C2 * (intrinsicFront.w + intrinsicFront.s0 + intrinsicFront.s1) := by ring
      _ ≤ C2 * (invLower * (source.w + source.s0 + source.s1)) :=
        mul_le_mul_of_nonneg_left hfront012 hC2
  refine
    { w := HT.w.trans (Hraw.w.trans ?_)
      s0 := HT.s0.trans (Hraw.s0.trans ?_)
      s1 := ?_
      s2 := ?_ }
  · simpa using HS.w
  · exact mul_le_mul_of_nonneg_left HS.w hC0
  · calc
      target.s1 ≤ upper * intrinsicRear.s1 := HT.s1
      _ ≤ upper * (C1 * (source.w + source.s0)) :=
        mul_le_mul_of_nonneg_left hrear1 hupper
      _ ≤ (upper * invLower) * C1 * (source.w + source.s0) := by
        have hnonneg : 0 ≤ upper * C1 * (source.w + source.s0) :=
          mul_nonneg (mul_nonneg hupper hC1) hsum0
        calc
          upper * (C1 * (source.w + source.s0)) =
              upper * C1 * (source.w + source.s0) := by ring
          _ ≤ invLower * (upper * C1 * (source.w + source.s0)) := by
            nlinarith
          _ = (upper * invLower) * C1 * (source.w + source.s0) := by ring
  · calc
      target.s2 ≤ upper ^ 2 * intrinsicRear.s2 +
          second * intrinsicRear.s1 := HT.s2
      _ ≤ upper ^ 2 *
            (C2 * (invLower * (source.w + source.s0 + source.s1))) +
          second * (C1 * (source.w + source.s0)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hrear2 (sq_nonneg upper))
          (mul_le_mul_of_nonneg_left hrear1 hsecond)
      _ ≤ (upper * invLower) ^ 2 * C2 *
            (source.w + source.s0 + source.s1) +
          second * C1 * (source.w + source.s0) := by
        have hinvSq : invLower ≤ invLower ^ 2 := by nlinarith
        have hfac : upper ^ 2 * invLower ≤ (upper * invLower) ^ 2 := by
          nlinarith [sq_nonneg upper]
        have hrest : 0 ≤ C2 * (source.w + source.s0 + source.s1) :=
          mul_nonneg hC2 hsum1
        have hfirst := mul_le_mul_of_nonneg_right hfac hrest
        nlinarith

/-- Two adjacent normalized jet errors are absorbed by one summable tower
majorant.  The intended specialization is
`mu j = 2 * (major j + major (j-1))` (with the missing predecessor set to
zero at the base row). -/
theorem adjacentJetInflation
    {epsPrev epsCur majorPrev majorCur : ℝ}
    (hepsPrev0 : 0 ≤ epsPrev) (hepsCur0 : 0 ≤ epsCur)
    (hmajorPrev0 : 0 ≤ majorPrev) (hmajorCur0 : 0 ≤ majorCur)
    (hprev : epsPrev ≤ majorPrev) (hcur : epsCur ≤ majorCur)
    (hsum : majorPrev + majorCur ≤ 1 / 4) :
    let mu := 2 * (majorCur + majorPrev)
    0 ≤ mu ∧ mu ≤ 1 / 2 ∧ epsCur ≤ mu ∧
      (1 + epsCur) / (1 - epsPrev) ≤ 1 + mu := by
  dsimp
  have hsum0 : 0 ≤ majorPrev + majorCur := add_nonneg hmajorPrev0 hmajorCur0
  have hmu0 : 0 ≤ 2 * (majorCur + majorPrev) := by nlinarith
  have hmuHalf : 2 * (majorCur + majorPrev) ≤ 1 / 2 := by nlinarith
  have hcurMu : epsCur ≤ 2 * (majorCur + majorPrev) := by nlinarith
  have hepsPrevQuarter : epsPrev ≤ 1 / 4 := by nlinarith
  have hden : 0 < 1 - epsPrev := by nlinarith
  refine ⟨hmu0, hmuHalf, hcurMu, (div_le_iff₀ hden).2 ?_⟩
  nlinarith [mul_nonneg
    (sub_nonneg.mpr (show epsPrev ≤ 1 / 2 by nlinarith)) hsum0]

/-! ## Paired tower majorants -/

/-- The predecessor major, with zero inserted at the base row. -/
def previousMajor (major : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => major j

/-- One majorant controlling the predecessor inverse jet and the current
upper/second jets simultaneously. -/
def pairedMajor (major : ℕ → ℝ) (j : ℕ) : ℝ :=
  2 * (major j + major (j + 1))

theorem previousMajor_nonnegative
    {major : ℕ → ℝ} (hmajor0 : ∀ j, 0 ≤ major j) :
    ∀ j, 0 ≤ previousMajor major j
  | 0 => le_rfl
  | j + 1 => hmajor0 j

theorem previousMajor_summable
    {major : ℕ → ℝ} (hmajor : Summable major) :
    Summable (previousMajor major) := by
  apply (summable_nat_add_iff (f := previousMajor major) 1).1
  simpa [previousMajor, Nat.add_comm] using hmajor

theorem tsum_previousMajor
    {major : ℕ → ℝ} (hmajor : Summable major) :
    (∑' j, previousMajor major j) = ∑' j, major j := by
  have hprev := previousMajor_summable hmajor
  have H := hprev.sum_add_tsum_nat_add 1
  have H' : (∑' j, major j) = ∑' j, previousMajor major j := by
    simpa [previousMajor, Nat.add_comm] using H
  exact H'.symm

theorem pairedMajor_nonnegative
    {major : ℕ → ℝ} (hmajor0 : ∀ j, 0 ≤ major j) (j : ℕ) :
    0 ≤ pairedMajor major j := by
  exact mul_nonneg (by norm_num)
    (add_nonneg (hmajor0 j) (hmajor0 (j + 1)))

theorem pairedMajor_summable
    {major : ℕ → ℝ} (hmajor : Summable major) :
    Summable (pairedMajor major) := by
  exact (hmajor.add ((summable_nat_add_iff (f := major) 1).2 hmajor)).mul_left 2

theorem tsum_pairedMajor_le
    {major : ℕ → ℝ} (hmajor0 : ∀ j, 0 ≤ major j)
    (hmajor : Summable major) :
    (∑' j, pairedMajor major j) ≤ 4 * ∑' j, major j := by
  have hshift : Summable (fun j => major (j + 1)) :=
    (summable_nat_add_iff (f := major) 1).2 hmajor
  have H := hmajor.sum_add_tsum_nat_add 1
  have H' : major 0 + (∑' j, major (j + 1)) = ∑' j, major j := by
    simpa using H
  rw [show pairedMajor major = fun j ↦
    2 * (major j + major (j + 1)) by rfl, tsum_mul_left,
    hmajor.tsum_add hshift]
  nlinarith [hmajor0 0]

/-- Complete sequence data for the paired nonaffine distortion majorant. -/
structure PairedMajorData (major : ℕ → ℝ) (E : ℝ) : Prop where
  nonnegative : ∀ j, 0 ≤ pairedMajor major j
  half : ∀ j, pairedMajor major j ≤ 1 / 2
  summable : Summable (pairedMajor major)
  tsum_le : (∑' j, pairedMajor major j) ≤ 4 * E

theorem pairedMajorData
    {major : ℕ → ℝ} {E : ℝ}
    (hmajor0 : ∀ j, 0 ≤ major j) (hmajor : Summable major)
    (htsum : (∑' j, major j) ≤ E) (hE : E ≤ 1 / 8) :
    PairedMajorData major E := by
  have hterm (j : ℕ) : major j ≤ ∑' i, major i :=
    hmajor.le_tsum j (fun i _ ↦ hmajor0 i)
  refine
    { nonnegative := pairedMajor_nonnegative hmajor0
      half := ?_
      summable := pairedMajor_summable hmajor
      tsum_le := ?_ }
  · intro j
    unfold pairedMajor
    nlinarith [hterm j, hterm (j + 1)]
  · exact (tsum_pairedMajor_le hmajor0 hmajor).trans (by nlinarith)

/-- The paired major directly supplies the existing near-identity distortion
budget, with total parameters `(8E,4E,4E)`. -/
def pairedNearIdentityBudget
    {major : ℕ → ℝ} {E : ℝ}
    (hmajor0 : ∀ j, 0 ≤ major j) (hmajor : Summable major)
    (htsum : (∑' j, major j) ≤ E) (hE : E ≤ 1 / 8) :
    DistortionBudget
      (NearIdentityDistortionBudget.invLower (pairedMajor major))
      (NearIdentityDistortionBudget.upper (pairedMajor major))
      (pairedMajor major) (8 * E) (4 * E) (4 * E) := by
  let D := pairedMajorData hmajor0 hmajor htsum hE
  simpa only [show 2 * (4 * E) = 8 * E by ring] using
    NearIdentityDistortionBudget.budget D.nonnegative D.half D.summable D.tsum_le

/-- Mono-enlarge one concrete adjacent-jet transition to the paired tower
majorant. -/
def transition_to_pairedMajor
    {x y : Components} {major : ℕ → ℝ} {j : ℕ}
    {epsPrev epsCur C0 C1 C2 : ℝ}
    (hx : x.Nonnegative) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hepsPrev0 : 0 ≤ epsPrev) (hepsCur0 : 0 ≤ epsCur)
    (hmajor0 : ∀ i, 0 ≤ major i)
    (hprev : epsPrev ≤ major j) (hcur : epsCur ≤ major (j + 1))
    (hadjacent : major j + major (j + 1) ≤ 1 / 4)
    (H : Transition x y 1 ((1 + epsCur) / (1 - epsPrev)) epsCur C0 C1 C2) :
    Transition x y
      (NearIdentityDistortionBudget.invLower (pairedMajor major) j)
      (NearIdentityDistortionBudget.upper (pairedMajor major) j)
      (pairedMajor major j) C0 C1 C2 := by
  let Q := adjacentJetInflation hepsPrev0 hepsCur0
    (hmajor0 j) (hmajor0 (j + 1)) hprev hcur hadjacent
  have hden : 0 < 1 - epsPrev := by
    have hp : epsPrev ≤ 1 / 4 := hprev.trans (le_trans
      (le_add_of_nonneg_right (hmajor0 (j + 1))) hadjacent)
    linarith
  have hMA0 : 0 ≤ (1 + epsCur) / (1 - epsPrev) :=
    div_nonneg (by linarith) hden.le
  have hmu0 : 0 ≤ pairedMajor major j := by
    simpa [pairedMajor, add_comm] using Q.1
  have hmuHalf : pairedMajor major j ≤ 1 / 2 := by
    simpa [pairedMajor, add_comm] using Q.2.1
  have hmuDen : 0 < 1 - pairedMajor major j := by linarith
  have ha : 1 ≤ NearIdentityDistortionBudget.invLower (pairedMajor major) j := by
    dsimp [NearIdentityDistortionBudget.invLower]
    apply (le_div_iff₀ hmuDen).2
    linarith
  apply H.monoDistortion hx hC1 hC2 ha hMA0
  · simpa [NearIdentityDistortionBudget.upper, pairedMajor, add_comm] using
      Q.2.2.2
  · simpa [pairedMajor, add_comm] using Q.2.2.1

end FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
