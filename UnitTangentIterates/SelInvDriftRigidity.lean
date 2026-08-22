import Mathlib
import UnitTangentIterates.GaugePeriodRigidity
import UnitTangentIterates.RearOwnMotion
import UnitTangentIterates.PathMetricSlowTest
import UnitTangentIterates.RearOwnHigherRegularity
import UnitTangentIterates.SelectedChangeOfVariable

/-!
# The drift block of the `C²` estimate forces the rear period to stand still

The `C²` comparison of the two marked selected inverses
(`SelInvPathTubeC2.dist_selInv_le_modulus_of_path_tube_C2` and the statements
below it) is stated for any caller who can supply a bound

`|ξ(t,x)| ≤ Rb t`, `Rb t ≤ rr · m t`

for the tangential drift

`ξ(t,x) = ⟨∂_t Y(t,x), e^{iΨ(t,x)}⟩`

of the family `Y` of selected rear tracks written in its own arclength — a
bound *uniform in the arclength `x`*.  This file records exactly which paths
can satisfy it.

Differentiating the closing relation `Y(t, x + Q t) = Y(t, x)` of a family of
closed curves written in its own arclength gives

`ξ(t, x + Q t) = ξ(t, x) − Q'(t)` ,

so `ξ` drifts by `−Q'(t)` over each period; iterating, a bound uniform in `x`
forces `Q'(t) = 0`.  Since the cost density of a normal path is bounded
(`PathMetric.NormalPath.exists_bound_m`), the block above always yields such a
uniform bound.  Hence:

**the drift block of the `C²` estimate can be satisfied only along paths of
fronts whose rear arclength period `Q t = ∫₀^{P t} cos δ(t,·)` is the same at
every time.**

Main results:

* `period_deriv_eq_zero_of_bounded_tangential` — the abstract statement, for a
  jointly `C¹` family of closed curves written in its own arclength;
* `rearOwn_period_deriv_eq_zero`, `rearOwn_period_const` — the same for the
  family of selected rear tracks, whose closing relation comes from the closing
  of the fronts;
* `rearPeriod_const_of_cost_bound` — the corollary in the shape the estimate
  asks for: a drift dominated by the cost density of a normal path already
  forces the rear period to be constant;
* `hasDerivAt_rearPeriod` — the explicit derivative of the rear period,
  `Q'(t) = −∫₀^{P t} sin δ(t,u)·∂ₜδ(t,u) du + P'(t)·cos δ(t, P t)`;
* `front_period_closing_of_bounded_tangential` — the closing condition the
  drift block therefore imposes on the path,
  `P'(t)·cos δ(t, P t) = ∫₀^{P t} sin δ(t,u)·∂ₜδ(t,u) du`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
  RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength RearOwnMotion

namespace SelInvDriftRigidity

open RearOwnHigherRegularity

/-! ### The abstract rigidity -/

/-- **A family of closed curves written in its own arclength, whose tangential
drift is bounded uniformly in the arclength, has a stationary period.** -/
theorem period_deriv_eq_zero_of_bounded_tangential {Y tauY : ℝ → ℝ → ℂ}
    {xi eta : ℝ → ℝ → ℝ} {A0 : ℝ} {Q Q' : ℝ → ℝ}
    (hA0 : ∀ t x, |xi t x| ≤ A0)
    (hY : ContDiff ℝ (1 : ℕ) (uncurry Y))
    (hYx : ∀ t x, HasDerivAt (Y t) (tauY t x) x)
    (hYt : ∀ t x, HasDerivAt (fun r => Y r x)
      ((xi t x : ℂ) * tauY t x + (eta t x : ℂ) * (Complex.I * tauY t x)) t)
    (htaunorm : ∀ t x, ‖tauY t x‖ = 1)
    (hclose : ∀ t x, Y t (x + Q t) = Y t x)
    (hQd : ∀ t, HasDerivAt Q (Q' t) t) (t : ℝ) : Q' t = 0 := by
  have htau0 : ∀ t x, tauY t x ≠ 0 := by
    intro t x h
    have hn := htaunorm t x
    rw [h] at hn
    simp at hn
  have htauper : ∀ t, Function.Periodic (tauY t) (Q t) := by
    intro t x
    have hshift : HasDerivAt (fun y => Y t (y + Q t)) (tauY t (x + Q t)) x :=
      HasDerivAt.comp_add_const x (Q t) (hYx t (x + Q t))
    have hfun : (fun y => Y t (y + Q t)) = Y t := funext fun y => hclose t y
    rw [hfun] at hshift
    exact hshift.unique (hYx t x)
  have hqp : ∀ t x, xi t (x + Q t) = xi t x - Q' t * (1 : ℝ) := by
    intro t x
    have h := (GaugeClosingRelations.closing_relations hY hYx hYt htau0 htauper hclose
      hQd t x).1
    rw [h]
    ring
  exact GaugePeriodRigidity.constant_period_of_bounded_tangential (v := fun _ _ => (1 : ℝ))
    hA0 (fun _ _ => one_ne_zero) (fun _ _ => rfl) hqp t


/-- **Conversely, a stationary period makes the tangential drift periodic.**
The closing relation gives `ξ(t, x + Q t) = ξ(t, x) − Q'(t)`, so when the period
does not move the drift is periodic with it. -/
theorem periodic_tangential_of_period_deriv_zero {Y tauY : ℝ → ℝ → ℂ}
    {xi eta : ℝ → ℝ → ℝ} {Q Q' : ℝ → ℝ}
    (hY : ContDiff ℝ (1 : ℕ) (uncurry Y))
    (hYx : ∀ t x, HasDerivAt (Y t) (tauY t x) x)
    (hYt : ∀ t x, HasDerivAt (fun r => Y r x)
      ((xi t x : ℂ) * tauY t x + (eta t x : ℂ) * (Complex.I * tauY t x)) t)
    (htaunorm : ∀ t x, ‖tauY t x‖ = 1)
    (hclose : ∀ t x, Y t (x + Q t) = Y t x)
    (hQd : ∀ t, HasDerivAt Q (Q' t) t) (hQ0 : ∀ t, Q' t = 0) (t : ℝ) :
    Function.Periodic (xi t) (Q t) := by
  have htau0 : ∀ t x, tauY t x ≠ 0 := by
    intro t' x h
    have hn := htaunorm t' x
    rw [h] at hn
    simp at hn
  have htauper : ∀ t, Function.Periodic (tauY t) (Q t) := by
    intro t' x
    have hshift : HasDerivAt (fun y => Y t' (y + Q t')) (tauY t' (x + Q t')) x :=
      HasDerivAt.comp_add_const x (Q t') (hYx t' (x + Q t'))
    have hfun : (fun y => Y t' (y + Q t')) = Y t' := funext fun y => hclose t' y
    rw [hfun] at hshift
    exact hshift.unique (hYx t' x)
  intro x
  have h := (GaugeClosingRelations.closing_relations hY hYx hYt htau0 htauper hclose
    hQd t x).1
  rw [h, hQ0 t, sub_zero]

/-! ### The family of selected rear tracks -/

section Rear

variable {F Ydot : ℝ → ℝ → ℂ} {Θ δ K sf : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {kh : ℝ}

/-- The rear arclength period of the family: `Q t = ∫₀^{P t} cos δ(t,·)`. -/
def rearPeriod (δ : ℝ → ℝ → ℝ) (P : ℝ → ℝ) : ℝ → ℝ := fun t => rearArclength (δ t) (P t)

/-- The rear period of a `C¹` family of steering angles moving over a `C¹`
front period is `C¹`. -/
theorem contDiff_rearPeriod (hδC : ContDiff ℝ (1 : ℕ) (uncurry δ))
    (hPC : ContDiff ℝ (1 : ℕ) P) : ContDiff ℝ (1 : ℕ) (rearPeriod δ P) := by
  have hδdiff : Differentiable ℝ (uncurry δ) := hδC.differentiable (by norm_num)
  have hdt : ∀ t s, HasDerivAt (fun r => δ r s) (partialTime δ t s) t :=
    hasDerivAt_partialTime hδdiff
  have hdtc : Continuous (uncurry (partialTime δ)) :=
    (contDiff_partialTime_self (n := 0) (by exact_mod_cast hδC)).continuous
  have hfam : ContDiff ℝ (1 : ℕ) (uncurry fun t s => rearArclength (δ t) s) :=
    SelectedChangeOfVariable.contDiff_one_rearArclengthFamily hδC.continuous hdt hdtc
  have hcomp : ContDiff ℝ (1 : ℕ) fun t : ℝ => ((t, P t) : ℝ × ℝ) :=
    contDiff_id.prodMk hPC
  simpa [rearPeriod, Function.comp_def] using hfam.comp hcomp

/-! ### The derivative of the rear period -/

/-- **Chain rule for a jointly `C¹` function of time and arclength evaluated
along a moving arclength.** -/
theorem hasDerivAt_comp_moving {A At Ax : ℝ → ℝ → ℝ} {P P' : ℝ → ℝ}
    (hA : ContDiff ℝ (1 : ℕ) (uncurry A))
    (hAt : ∀ t s, HasDerivAt (fun r => A r s) (At t s) t)
    (hAx : ∀ t s, HasDerivAt (A t) (Ax t s) s)
    (hP : ∀ t, HasDerivAt P (P' t) t) (t : ℝ) :
    HasDerivAt (fun r => A r (P r)) (At t (P t) + P' t * Ax t (P t)) t := by
  have hdiff : Differentiable ℝ (uncurry A) := hA.differentiable (by norm_num)
  set s : ℝ := P t with hs
  set L := fderiv ℝ (uncurry A) (t, s) with hLdef
  have hL : HasFDerivAt (uncurry A) L (t, s) := (hdiff (t, s)).hasFDerivAt
  have hpt : HasDerivAt (fun r => A r s) (L (1, 0)) t := by
    have hg : HasDerivAt (fun r : ℝ => (r, s)) ((1 : ℝ), (0 : ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t s)
    simpa [Function.comp] using hL.comp_hasDerivAt t hg
  have hpx : HasDerivAt (A t) (L (0, 1)) s := by
    have hg : HasDerivAt (fun r : ℝ => (t, r)) ((0 : ℝ), (1 : ℝ)) s :=
      (hasDerivAt_const s t).prodMk (hasDerivAt_id s)
    simpa [Function.comp] using hL.comp_hasDerivAt s hg
  have hLt : L (1, 0) = At t s := hpt.unique (hAt t s)
  have hLx : L (0, 1) = Ax t s := hpx.unique (hAx t s)
  have hg : HasDerivAt (fun r : ℝ => (r, P r)) ((1 : ℝ), P' t) t :=
    (hasDerivAt_id t).prodMk (hP t)
  have hcomp : HasDerivAt (fun r => A r (P r)) (L (1, P' t)) t := by
    simpa [Function.comp] using hL.comp_hasDerivAt t hg
  have hsplit : ((1 : ℝ), P' t) = ((1 : ℝ), (0 : ℝ)) + P' t • ((0 : ℝ), (1 : ℝ)) := by
    simp
  rw [hsplit, map_add, map_smul, hLt, hLx, smul_eq_mul] at hcomp
  exact hcomp

/-- **The derivative of the rear arclength period.**  Writing
`Q t = ∫₀^{P t} cos δ(t,·)`, the period moves both because the front period `P`
moves and because the steering angle does:
`Q'(t) = −∫₀^{P t} sin δ(t,u)·∂ₜδ(t,u) du + P'(t)·cos δ(t, P t)`. -/
theorem hasDerivAt_rearPeriod {P' : ℝ → ℝ} (hδC : ContDiff ℝ (1 : ℕ) (uncurry δ))
    (hP : ∀ t, HasDerivAt P (P' t) t) (t : ℝ) :
    HasDerivAt (rearPeriod δ P)
      ((∫ u in (0 : ℝ)..P t,
          SelectedChangeOfVariable.cosTimeDeriv δ (partialTime δ) t u)
        + P' t * Real.cos (δ t (P t))) t := by
  have hδdiff : Differentiable ℝ (uncurry δ) := hδC.differentiable (by norm_num)
  have hdt : ∀ t s, HasDerivAt (fun r => δ r s) (partialTime δ t s) t :=
    hasDerivAt_partialTime hδdiff
  have hdtc : Continuous (uncurry (partialTime δ)) :=
    (contDiff_partialTime_self (n := 0) (by exact_mod_cast hδC)).continuous
  have hfam : ContDiff ℝ (1 : ℕ) (uncurry fun t s => rearArclength (δ t) s) :=
    SelectedChangeOfVariable.contDiff_one_rearArclengthFamily hδC.continuous hdt hdtc
  exact hasDerivAt_comp_moving (A := fun t s => rearArclength (δ t) s)
    (At := fun t s => ∫ u in (0 : ℝ)..s,
      SelectedChangeOfVariable.cosTimeDeriv δ (partialTime δ) t u)
    (Ax := fun t s => Real.cos (δ t s)) hfam
    (SelectedChangeOfVariable.hasDerivAt_rearArclength_time hδC.continuous hdt hdtc)
    (SelectedChangeOfVariable.hasDerivAt_rearArclength_space hδC.continuous) hP t

/-- **The rear period of the family of selected rears is stationary whenever the
tangential drift is bounded uniformly in the arclength.** -/
theorem rearOwn_period_deriv_eq_zero {A0 : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hδper : ∀ t, Function.Periodic (δ t) (P t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFC : ContDiff ℝ (1 : ℕ) (uncurry F)) (hΘC : ContDiff ℝ (1 : ℕ) (uncurry Θ))
    (hδC : ContDiff ℝ (1 : ℕ) (uncurry δ)) (hsfC : ContDiff ℝ (1 : ℕ) (uncurry sf))
    (hPC : ContDiff ℝ (1 : ℕ) P)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hA0 : ∀ t x, |frameTangential Ydot (rearOwnAngle Θ δ sf) t x| ≤ A0) (t : ℝ) :
    deriv (rearPeriod δ P) t = 0 := by
  have hδcont : ∀ t, Continuous (δ t) := fun t =>
    hδC.continuous.comp (continuous_const.prodMk continuous_id)
  have hQC : ContDiff ℝ (1 : ℕ) (rearPeriod δ P) := contDiff_rearPeriod hδC hPC
  have hQd : ∀ r, HasDerivAt (rearPeriod δ P) (deriv (rearPeriod δ P) r) r := fun r =>
    (hQC.differentiable (by norm_num) r).hasDerivAt
  refine period_deriv_eq_zero_of_bounded_tangential (Y := rearOwn F Θ δ sf)
    (tauY := rearOwnTangent Θ δ sf) (eta := frameNormal Ydot (rearOwnAngle Θ δ sf))
    hA0 (contDiff_one_rearOwn hFC hΘC hδC hsfC)
    (fun t' x => hasDerivAt_rearOwn_space hF hΘ hsteer hsf hcos t' x)
    (fun t' x => hasDerivAt_rearOwn_time_frame (hYt t' x))
    (fun t' x => norm_rearOwn_tangent t' x)
    (fun t' x => rearOwn_closing hkh0 hkh1 hδcont hstrip0 hstrip1 hδper hsfinv hFper
      hΘper t' x)
    hQd t

/-- **The rear arclength period is then the same at every time.** -/
theorem rearOwn_period_const {A0 : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hδper : ∀ t, Function.Periodic (δ t) (P t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFC : ContDiff ℝ (1 : ℕ) (uncurry F)) (hΘC : ContDiff ℝ (1 : ℕ) (uncurry Θ))
    (hδC : ContDiff ℝ (1 : ℕ) (uncurry δ)) (hsfC : ContDiff ℝ (1 : ℕ) (uncurry sf))
    (hPC : ContDiff ℝ (1 : ℕ) P)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hA0 : ∀ t x, |frameTangential Ydot (rearOwnAngle Θ δ sf) t x| ≤ A0) (a b : ℝ) :
    rearArclength (δ a) (P a) = rearArclength (δ b) (P b) := by
  have hQC : ContDiff ℝ (1 : ℕ) (rearPeriod δ P) := contDiff_rearPeriod hδC hPC
  exact is_const_of_deriv_eq_zero (hQC.differentiable (by norm_num))
    (fun r => rearOwn_period_deriv_eq_zero (A0 := A0) hkh0 hkh1 hstrip0 hstrip1 hcos hF
      hΘ hsteer hsf hsfinv hδper hFper hΘper hFC hΘC hδC hsfC hPC hYt hA0 r) a b


/-- **The tangential drift of the selected rears is periodic exactly when the
rear period stands still.**  Together with `rearOwn_period_deriv_eq_zero` this
identifies the three conditions: a drift bounded uniformly in the arclength, a
drift periodic in the rear arclength, and a rear arclength period constant in
time. -/
theorem periodic_frameTangential_of_period_const
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hδper : ∀ t, Function.Periodic (δ t) (P t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFC : ContDiff ℝ (1 : ℕ) (uncurry F)) (hΘC : ContDiff ℝ (1 : ℕ) (uncurry Θ))
    (hδC : ContDiff ℝ (1 : ℕ) (uncurry δ)) (hsfC : ContDiff ℝ (1 : ℕ) (uncurry sf))
    (hPC : ContDiff ℝ (1 : ℕ) P)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hQ0 : ∀ t, deriv (rearPeriod δ P) t = 0) (t : ℝ) :
    Function.Periodic (frameTangential Ydot (rearOwnAngle Θ δ sf) t)
      (rearArclength (δ t) (P t)) := by
  have hδcont : ∀ t, Continuous (δ t) := fun t =>
    hδC.continuous.comp (continuous_const.prodMk continuous_id)
  have hQC : ContDiff ℝ (1 : ℕ) (rearPeriod δ P) := contDiff_rearPeriod hδC hPC
  have hQd : ∀ r, HasDerivAt (rearPeriod δ P) (deriv (rearPeriod δ P) r) r := fun r =>
    (hQC.differentiable (by norm_num) r).hasDerivAt
  exact periodic_tangential_of_period_deriv_zero (Y := rearOwn F Θ δ sf)
    (tauY := rearOwnTangent Θ δ sf) (eta := frameNormal Ydot (rearOwnAngle Θ δ sf))
    (contDiff_one_rearOwn hFC hΘC hδC hsfC)
    (fun t' x => hasDerivAt_rearOwn_space hF hΘ hsteer hsf hcos t' x)
    (fun t' x => hasDerivAt_rearOwn_time_frame (hYt t' x))
    (fun t' x => norm_rearOwn_tangent t' x)
    (fun t' x => rearOwn_closing hkh0 hkh1 hδcont hstrip0 hstrip1 hδper hsfinv hFper
      hΘper t' x)
    hQd hQ0 t

/-- **The corollary in the shape of the estimate's drift block.**  The bound the
`C²` comparison asks for — a drift `Rb` dominated by the cost density of the
normal path — is a uniform bound, since the cost density of a normal path is
bounded; so it already forces the rear arclength period to be constant along
the path. -/
theorem rearPeriod_const_of_cost_bound {p q : Data} (Γ : NormalPath p q)
    {Rb : ℝ → ℝ} {rr : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hδper : ∀ t, Function.Periodic (δ t) (P t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFC : ContDiff ℝ (1 : ℕ) (uncurry F)) (hΘC : ContDiff ℝ (1 : ℕ) (uncurry Θ))
    (hδC : ContDiff ℝ (1 : ℕ) (uncurry δ)) (hsfC : ContDiff ℝ (1 : ℕ) (uncurry sf))
    (hPC : ContDiff ℝ (1 : ℕ) P)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hRbd : ∀ t x, |frameTangential Ydot (rearOwnAngle Θ δ sf) t x| ≤ Rb t)
    (hRbm : ∀ t, Rb t ≤ rr * Γ.m t) (hr : 0 ≤ rr) (a b : ℝ) :
    rearArclength (δ a) (P a) = rearArclength (δ b) (P b) := by
  obtain ⟨M, hM0, hM⟩ := Γ.exists_bound_m
  have hA0 : ∀ t x, |frameTangential Ydot (rearOwnAngle Θ δ sf) t x| ≤ rr * M := fun t x =>
    le_trans (le_trans (hRbd t x) (hRbm t)) (mul_le_mul_of_nonneg_left (hM t) hr)
  exact rearOwn_period_const (A0 := rr * M) hkh0 hkh1 hstrip0 hstrip1 hcos hF hΘ hsteer
    hsf hsfinv hδper hFper hΘper hFC hΘC hδC hsfC hPC hYt hA0 a b

/-- **The closing condition the drift block imposes on the path.**  Since a
drift bounded uniformly in the arclength forces `Q'(t) = 0`, the explicit
formula for `Q'` turns into a relation between the motion of the front period
and the motion of the steering angle:
`P'(t)·cos δ(t, P t) = ∫₀^{P t} sin δ(t,u)·∂ₜδ(t,u) du`. -/
theorem front_period_closing_of_bounded_tangential {A0 : ℝ} {P' : ℝ → ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hδper : ∀ t, Function.Periodic (δ t) (P t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFC : ContDiff ℝ (1 : ℕ) (uncurry F)) (hΘC : ContDiff ℝ (1 : ℕ) (uncurry Θ))
    (hδC : ContDiff ℝ (1 : ℕ) (uncurry δ)) (hsfC : ContDiff ℝ (1 : ℕ) (uncurry sf))
    (hPC : ContDiff ℝ (1 : ℕ) P) (hP : ∀ t, HasDerivAt P (P' t) t)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hA0 : ∀ t x, |frameTangential Ydot (rearOwnAngle Θ δ sf) t x| ≤ A0) (t : ℝ) :
    P' t * Real.cos (δ t (P t))
      = ∫ u in (0 : ℝ)..P t, Real.sin (δ t u) * partialTime δ t u := by
  have hzero : deriv (rearPeriod δ P) t = 0 :=
    rearOwn_period_deriv_eq_zero (A0 := A0) hkh0 hkh1 hstrip0 hstrip1 hcos hF hΘ hsteer
      hsf hsfinv hδper hFper hΘper hFC hΘC hδC hsfC hPC hYt hA0 t
  have hd := hasDerivAt_rearPeriod (P' := P') hδC hP t
  have hsum : (∫ u in (0 : ℝ)..P t,
      SelectedChangeOfVariable.cosTimeDeriv δ (partialTime δ) t u)
        + P' t * Real.cos (δ t (P t)) = 0 := by
    rw [← hd.deriv, hzero]
  have hfun : (fun u => SelectedChangeOfVariable.cosTimeDeriv δ (partialTime δ) t u)
      = fun u => -(Real.sin (δ t u) * partialTime δ t u) := by
    funext u
    simp [SelectedChangeOfVariable.cosTimeDeriv, neg_mul]
  rw [hfun, intervalIntegral.integral_neg] at hsum
  linarith

end Rear

end SelInvDriftRigidity
