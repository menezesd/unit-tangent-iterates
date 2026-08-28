import UnitTangentIterates.FiniteSmoothRearFamilySmoothSource
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSuccessorFront
/-!
# All-order analytic data for recursive rear families

The finite `MarkingAwareSource` used by one gauge construction intentionally records only
the differentiability needed by that one application.  Infinite recursion must
not attempt to reconstruct higher jets from its `C2NormalPathData`.  The
sidecar below retains the intrinsic selected rear as a smooth next front,
together with the normalized curvature and period derivatives needed by the
variable-period steering bootstrap.
-/

noncomputable section

open scoped ContDiff

open Function Set MarkedSpace PathMetric RearTrack RearOwnArclength RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareSmoothSource

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront

/-- Curvature of the intrinsic successor front in its normalized spatial
parameter. -/
def normalizedCurvature
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : ℝ → ℝ → ℝ :=
  fun t sigma => curvature A t (period A t * sigma)

/-- A `C∞` sidecar for one source, retaining exactly the all-order data which
the next normalized-period steering problem consumes.  The exact time
derivatives of the intrinsic front, angle, and curvature are already the
`Ydot`, `alphaT`, and `kT` fields of `A`; their all-order regularity is retained
here. -/
structure SmoothSource
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (periodLower kap : ℝ) where
  periodDerivative : ℝ → ℝ
  normalizedCurvatureDerivative : ℝ → ℝ → ℝ
  periodUpper : ℝ
  curvatureDerivativeBound : ℝ
  periodDerivativeBound : ℝ
  curvatureLipschitz : ℝ
  periodLipschitz : ℝ
  curvatureTaylor : ℝ
  periodTaylor : ℝ
  front_smooth : ContDiff ℝ ∞ (uncurry (front A))
  angle_smooth : ContDiff ℝ ∞ (uncurry (angle A))
  curvature_smooth : ContDiff ℝ ∞ (uncurry (curvature A))
  period_smooth : ContDiff ℝ ∞ (period A)
  frontTime_smooth : ContDiff ℝ ∞ (uncurry A.Ydot)
  angleTime_smooth : ContDiff ℝ ∞ (uncurry A.alphaT)
  curvatureTime_smooth : ContDiff ℝ ∞ (uncurry A.kT)
  periodDerivative_smooth : ContDiff ℝ ∞ periodDerivative
  normalizedCurvature_smooth :
    ContDiff ℝ ∞ (uncurry (normalizedCurvature A))
  normalizedCurvatureDerivative_smooth :
    ContDiff ℝ ∞ (uncurry normalizedCurvatureDerivative)
  period_deriv : ∀ t, HasDerivAt (period A) (periodDerivative t) t
  normalizedCurvature_deriv : ∀ t sigma,
    HasDerivAt (fun r => normalizedCurvature A r sigma)
      (normalizedCurvatureDerivative t sigma) t
  kap_nonnegative : 0 ≤ kap
  kap_lt_one : kap < 1
  periodLower_pos : 0 < periodLower
  period_lower : ∀ t, periodLower ≤ period A t
  period_upper : ∀ t, period A t ≤ periodUpper
  curvature_periodic : ∀ t,
    Function.Periodic (normalizedCurvature A t) 1
  curvatureDerivative_periodic : ∀ t,
    Function.Periodic (normalizedCurvatureDerivative t) 1
  curvature_bound : ∀ t sigma, |normalizedCurvature A t sigma| ≤ kap
  curvatureDerivative_bound : ∀ t sigma,
    |normalizedCurvatureDerivative t sigma| ≤ curvatureDerivativeBound
  periodDerivative_bound : ∀ t,
    |periodDerivative t| ≤ periodDerivativeBound
  curvature_lipschitz : ∀ a b sigma,
    |normalizedCurvature A a sigma - normalizedCurvature A b sigma| ≤
      curvatureLipschitz * |a - b|
  period_lipschitz : ∀ a b,
    |period A a - period A b| ≤ periodLipschitz * |a - b|
  curvature_taylor : ∀ a b sigma,
    |normalizedCurvature A a sigma - normalizedCurvature A b sigma -
        (a - b) * normalizedCurvatureDerivative b sigma| ≤
      curvatureTaylor * (a - b) ^ 2
  period_taylor : ∀ a b,
    |period A a - period A b - (a - b) * periodDerivative b| ≤
      periodTaylor * (a - b) ^ 2
  curvatureTaylor_nonnegative : 0 ≤ curvatureTaylor
  periodTaylor_nonnegative : 0 ≤ periodTaylor

/-- A selected steering family for the successor front, written in normalized
spatial parameter.  Existence is slice-wise; this record retains only the
defining equation and selected branch needed by the smooth bootstrap. -/
structure NormalizedSteering
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (S : SmoothSource A periodLower kap) where
  delta : ℝ → ℝ → ℝ
  equation : ∀ t sigma, HasDerivAt (delta t)
    (period A t *
      (normalizedCurvature A t sigma - Real.sin (delta t sigma))) sigma
  strip : ∀ t sigma, delta t sigma ∈ Icc (0 : ℝ) (Real.arcsin kap)
  periodic : ∀ t, Function.Periodic (delta t) 1

/-- The normalized selected steering is `C∞`.  This is the all-orders form of
one recursive derivative-gain step. -/
theorem NormalizedSteering.contDiff_infty
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {S : SmoothSource A periodLower kap}
    (D : NormalizedSteering S) : ContDiff ℝ ∞ (uncurry D.delta) := by
  rw [_root_.contDiff_infty]
  intro n
  have hperiodC : ContDiff ℝ (n : ℕ) (period A) :=
    (_root_.contDiff_infty.mp S.period_smooth n)
  have hperiodDerivativeC : ContDiff ℝ (n : ℕ) S.periodDerivative :=
    _root_.contDiff_infty.mp S.periodDerivative_smooth n
  have hcurvatureC : ContDiff ℝ (n : ℕ)
      (uncurry (normalizedCurvature A)) :=
    _root_.contDiff_infty.mp S.normalizedCurvature_smooth n
  have hcurvatureDerivativeC : ContDiff ℝ (n : ℕ)
      (uncurry S.normalizedCurvatureDerivative) :=
    _root_.contDiff_infty.mp S.normalizedCurvatureDerivative_smooth n
  have h := SteeringNormalizedPeriod.contDiff_succ_uncurry_delta
    (n := n) S.periodLower_pos S.kap_nonnegative S.kap_lt_one S.period_lower
    S.period_upper D.equation D.strip D.periodic S.curvature_periodic
    S.curvatureDerivative_periodic S.curvature_bound
    S.curvatureDerivative_bound S.periodDerivative_bound
    S.curvature_lipschitz S.period_lipschitz S.curvature_taylor
    S.period_taylor S.curvatureTaylor_nonnegative
    S.periodTaylor_nonnegative hperiodC hperiodDerivativeC hcurvatureC
    hcurvatureDerivativeC
  exact h.of_le (by exact_mod_cast (Nat.le_add_right n 1))

/-- Read the normalized successor steering back in the intrinsic arclength of
each slice. -/
def NormalizedSteering.arclength
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {S : SmoothSource A periodLower kap}
    (D : NormalizedSteering S) : ℝ → ℝ → ℝ :=
  fun t s => D.delta t (s / period A t)

theorem NormalizedSteering.contDiff_infty_arclength
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {S : SmoothSource A periodLower kap}
    (D : NormalizedSteering S) : ContDiff ℝ ∞ (uncurry D.arclength) := by
  rw [_root_.contDiff_infty]
  intro n
  exact SteeringNormalizedPeriod.contDiff_arclength_of_normalized
    (_root_.contDiff_infty.mp D.contDiff_infty n)
    (_root_.contDiff_infty.mp S.period_smooth n)
    (fun t => lt_of_lt_of_le S.periodLower_pos (S.period_lower t))

/-! ## The intrinsic front after one more selected-rear step -/

def nextFront
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {S : SmoothSource A periodLower kap}
    (D : NormalizedSteering S) (sf : ℝ → ℝ → ℝ) : ℝ → ℝ → ℂ :=
  rearOwn (front A) (angle A) D.arclength sf

def nextAngle
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {S : SmoothSource A periodLower kap}
    (D : NormalizedSteering S) (sf : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  rearOwnAngle (angle A) D.arclength sf

/-- Defining the next curvature as the spatial derivative of its smooth angle
avoids asking for global smoothness of `tan` across its poles.  The selected
strip later identifies this derivative with the usual `tan delta` formula. -/
def nextCurvature
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {S : SmoothSource A periodLower kap}
    (D : NormalizedSteering S) (sf : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  RearOwnHigherRegularity.partialArc (nextAngle D sf)

def nextPeriod
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {S : SmoothSource A periodLower kap}
    (D : NormalizedSteering S) : ℝ → ℝ :=
  fun t => rearArclength (D.arclength t) (period A t)

/-- All-order intrinsic data obtained after one further selected-rear step. -/
structure SuccessorRegularity
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {S : SmoothSource A periodLower kap}
    (D : NormalizedSteering S) where
  sf : ℝ → ℝ → ℝ
  sf_rightInverse : ∀ t x, rearArclength (D.arclength t) (sf t x) = x
  steering_deriv : ∀ t s, HasDerivAt (D.arclength t)
    (curvature A t s - Real.sin (D.arclength t s)) s
  sf_deriv : ∀ t x, HasDerivAt (sf t)
    (1 / Real.cos (D.arclength t (sf t x))) x
  sf_smooth : ContDiff ℝ ∞ (uncurry sf)
  front_smooth : ContDiff ℝ ∞ (uncurry (nextFront D sf))
  angle_smooth : ContDiff ℝ ∞ (uncurry (nextAngle D sf))
  curvature_smooth : ContDiff ℝ ∞ (uncurry (nextCurvature D sf))
  period_smooth : ContDiff ℝ ∞ (nextPeriod D)
  angle_deriv : ∀ t x, HasDerivAt (nextAngle D sf t)
    (nextCurvature D sf t x) x
  curvature_eq_tan : ∀ t x, nextCurvature D sf t x =
    Real.tan (D.arclength t (sf t x))
  front_time_deriv : ∀ t x, HasDerivAt
    (fun r => nextFront D sf r x)
    (RearOwnHigherRegularity.partialTime (nextFront D sf) t x) t
  angle_time_deriv : ∀ t x, HasDerivAt
    (fun r => nextAngle D sf r x)
    (RearOwnHigherRegularity.partialTime (nextAngle D sf) t x) t
  curvature_time_deriv : ∀ t x, HasDerivAt
    (fun r => nextCurvature D sf r x)
    (RearOwnHigherRegularity.partialTime (nextCurvature D sf) t x) t
  period_time_deriv : ∀ t, HasDerivAt (nextPeriod D)
    (deriv (nextPeriod D) t) t

/-- One complete all-orders successor regularity step. -/
theorem NormalizedSteering.exists_successorRegularity
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {S : SmoothSource A periodLower kap}
    (D : NormalizedSteering S) : Nonempty (SuccessorRegularity D) := by
  have hdeltaC : ∀ t, Continuous (D.arclength t) := fun t =>
    D.contDiff_infty_arclength.continuous.comp
      (continuous_const.prodMk continuous_id)
  have hstrip0 : ∀ t s, 0 ≤ D.arclength t s := fun t s =>
    (D.strip t (s / period A t)).1
  have hstrip1 : ∀ t s, D.arclength t s ≤ Real.arcsin kap := fun t s =>
    (D.strip t (s / period A t)).2
  have hinv : ∀ t, ∃ g : ℝ → ℝ,
      ∀ x, rearArclength (D.arclength t) (g x) = x := fun t =>
    ArclengthInverse.exists_inverse_rearArclength S.kap_nonnegative
      S.kap_lt_one (hdeltaC t) (hstrip0 t) (hstrip1 t)
  choose sf hsf using hinv
  have hsfSmooth : ContDiff ℝ ∞ (uncurry sf) := by
    rw [_root_.contDiff_infty]
    intro n
    exact (RearOwnHigherRegularity.contDiff_sf S.kap_nonnegative S.kap_lt_one
      (_root_.contDiff_infty.mp D.contDiff_infty_arclength (n + 1))
      hstrip0 hstrip1 hsf).of_le (by exact_mod_cast Nat.le_add_right n 1)
  have hangleSmooth : ContDiff ℝ ∞ (uncurry (nextAngle D sf)) := by
    rw [_root_.contDiff_infty]
    intro n
    exact RearOwnHigherRegularity.contDiff_rearOwnAngle
      (_root_.contDiff_infty.mp S.angle_smooth n)
      (_root_.contDiff_infty.mp D.contDiff_infty_arclength n)
      (_root_.contDiff_infty.mp hsfSmooth n)
  have hfrontSmooth : ContDiff ℝ ∞ (uncurry (nextFront D sf)) := by
    rw [_root_.contDiff_infty]
    intro n
    have hcomp : ContDiff ℝ (n : ℕ)
        (fun z : ℝ × ℝ => (z.1, uncurry sf z)) :=
      contDiff_fst.prodMk (_root_.contDiff_infty.mp hsfSmooth n)
    have hfrontComp : ContDiff ℝ (n : ℕ)
        (fun z : ℝ × ℝ => uncurry (front A) (z.1, uncurry sf z)) :=
      (_root_.contDiff_infty.mp S.front_smooth n).comp hcomp
    have hangle : ContDiff ℝ (n : ℕ) (uncurry (nextAngle D sf)) :=
      _root_.contDiff_infty.mp hangleSmooth n
    have hcast : ContDiff ℝ (n : ℕ)
        (fun z => ((uncurry (nextAngle D sf) z : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hangle
    have hexp : ContDiff ℝ (n : ℕ)
        (fun z => Complex.exp (Complex.I *
          ((uncurry (nextAngle D sf) z : ℝ) : ℂ))) :=
      Complex.contDiff_exp.comp (contDiff_const.mul hcast)
    change ContDiff ℝ (n : ℕ) (fun z : ℝ × ℝ =>
      front A z.1 (sf z.1 z.2) - Complex.exp (Complex.I *
        ((angle A z.1 (sf z.1 z.2) - D.arclength z.1 (sf z.1 z.2) : ℝ) : ℂ)))
    simpa [nextAngle, rearOwnAngle, RearTrack.rearAngle, uncurry] using
      hfrontComp.sub hexp
  have hcurvatureSmooth : ContDiff ℝ ∞
      (uncurry (nextCurvature D sf)) := by
    rw [_root_.contDiff_infty]
    intro n
    exact RearOwnHigherRegularity.contDiff_partialArc_self
      (_root_.contDiff_infty.mp hangleSmooth (n + 1))
  have hperiodSmooth : ContDiff ℝ ∞ (nextPeriod D) := by
    rw [_root_.contDiff_infty]
    intro n
    have hRA := RearOwnHigherRegularity.contDiff_rearArclengthFamily
      (_root_.contDiff_infty.mp D.contDiff_infty_arclength n)
    have hmap : ContDiff ℝ (n : ℕ) (fun t => (t, period A t)) :=
      contDiff_id.prodMk (_root_.contDiff_infty.mp S.period_smooth n)
    simpa [nextPeriod, uncurry] using hRA.comp hmap
  have hangleDeriv : ∀ t x, HasDerivAt (nextAngle D sf t)
      (nextCurvature D sf t x) x := by
    intro t x
    exact RearOwnHigherRegularity.hasDerivAt_partialArc
      ((_root_.contDiff_infty.mp hangleSmooth 1).differentiable (by norm_num)) t x
  have hsteerArc : ∀ t s, HasDerivAt (D.arclength t)
      (curvature A t s - Real.sin (D.arclength t s)) s := by
    intro t s
    have hPpos : 0 < period A t :=
      lt_of_lt_of_le S.periodLower_pos (S.period_lower t)
    have hinner : HasDerivAt (fun y => y / period A t)
        (1 / period A t) s := (hasDerivAt_id s).div_const (period A t)
    have hnorm := (D.equation t (s / period A t)).comp s hinner
    convert hnorm using 1
    simp only [normalizedCurvature, NormalizedSteering.arclength]
    rw [mul_div_cancel₀ s hPpos.ne']
    field_simp
  have hsfDeriv : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (D.arclength t (sf t x))) x := by
    intro t x
    have hcpos : 0 < Real.sqrt (1 - kap ^ 2) :=
      Real.sqrt_pos.mpr (by nlinarith [S.kap_nonnegative, S.kap_lt_one])
    exact ArclengthInverse.hasDerivAt_of_rightInverse hcpos
      (fun s => hasDerivAt_rearArclength (hdeltaC t) s)
      (fun s => Shadowing.cos_ge_of_mem_strip (hstrip0 t s) (hstrip1 t s))
      (hsf t) x
  have hcurvatureEq : ∀ t x, nextCurvature D sf t x =
      Real.tan (D.arclength t (sf t x)) := by
    intro t x
    exact (hangleDeriv t x).unique
      (RearOwnIsFront.hasDerivAt_rearOwnAngle
        (FiniteSmoothRearFamilyMarkingAwareSuccessorFront.MarkingAwareSource.successorFrontCore A).angle_frenet
        hsteerArc hsfDeriv t x)
  have hfrontDiff : Differentiable ℝ (uncurry (nextFront D sf)) :=
    (_root_.contDiff_infty.mp hfrontSmooth 1).differentiable (by norm_num)
  have hangleDiff : Differentiable ℝ (uncurry (nextAngle D sf)) :=
    (_root_.contDiff_infty.mp hangleSmooth 1).differentiable (by norm_num)
  have hcurvatureDiff : Differentiable ℝ (uncurry (nextCurvature D sf)) :=
    (_root_.contDiff_infty.mp hcurvatureSmooth 1).differentiable (by norm_num)
  have hperiodDiff : Differentiable ℝ (nextPeriod D) :=
    (_root_.contDiff_infty.mp hperiodSmooth 1).differentiable (by norm_num)
  exact ⟨{
    sf := sf
    sf_rightInverse := hsf
    steering_deriv := hsteerArc
    sf_deriv := hsfDeriv
    sf_smooth := hsfSmooth
    front_smooth := hfrontSmooth
    angle_smooth := hangleSmooth
    curvature_smooth := hcurvatureSmooth
    period_smooth := hperiodSmooth
    angle_deriv := hangleDeriv
    curvature_eq_tan := hcurvatureEq
    front_time_deriv := RearOwnHigherRegularity.hasDerivAt_partialTime hfrontDiff
    angle_time_deriv := RearOwnHigherRegularity.hasDerivAt_partialTime hangleDiff
    curvature_time_deriv := RearOwnHigherRegularity.hasDerivAt_partialTime hcurvatureDiff
    period_time_deriv := fun t => (hperiodDiff t).hasDerivAt
  }⟩

theorem contDiff_infty_partialTime
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ → E} (hf : ContDiff ℝ ∞ (uncurry f)) :
    ContDiff ℝ ∞ (uncurry (RearOwnHigherRegularity.partialTime f)) := by
  rw [_root_.contDiff_infty]
  intro n
  exact RearOwnHigherRegularity.contDiff_partialTime_self
    (_root_.contDiff_infty.mp hf (n + 1))

end FiniteSmoothRearFamilyMarkingAwareSmoothSource
