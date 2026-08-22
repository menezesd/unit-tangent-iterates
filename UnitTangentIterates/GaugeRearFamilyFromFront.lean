import Mathlib
import UnitTangentIterates.GaugeRearFamilyFundamental
import UnitTangentIterates.RearOwnDriftFundamental
import UnitTangentIterates.RearOwnIsFront
import UnitTangentIterates.RearOwnPathDistFrame

/-!
# The comparison path of the selected rears, with the drift bound discharged

`GaugeRearFamilyFundamental.exists_variableSpeed_normalPath_of_rearFamily_fundamental`
asks for a bound `R_b` on the tangential component of the motion of the selected
rears on one period `[0, Q t]`, and for the closing of the slices.  Along a path
of fronts both are available from the front data alone:

* the slices close up with the rear arclength period `Q t = ∫₀^{P t} cos δ(t,·)`
  and their tangent angle turns by `2π` over it
  (`RearOwnArclength.rearOwn_closing`,
  `RearOwnPathDistFrame.rearOwnAngle_shift`);
* the rear period is differentiable in the time
  (`SelInvDriftRigidity.hasDerivAt_rearPeriod`), with no constraint on its
  derivative;
* the tangential component obeys the one-period drift estimate
  `|ξ(t,x)| ≤ (Q_max·κ̂/(1−κ̂²))·m_F(t)` for `x ∈ [0, Q t]`
  (`RearOwnDriftFundamental.abs_frameTangential_le_cost_on_period`), which needs
  no periodicity of `ξ` and therefore no rigidity of the period.

So the comparison path of the family of selected rears exists along **every**
path of fronts in the selected strip, whether or not its rear length moves.

Main result: `exists_variableSpeed_normalPath_of_rearFamily_from_front`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeRearFamilyFromFront

open GaugeFlowDerivCost GaugeFlowVariableSpeedPath NormalPathC2IncrementVariableSpeed
  RearFamilyFrame RearOwnArclength RearOwnTangential RearOwnTangentialCost
  UniformFrameBounds GaugeMarkedDataOfRearFamily GaugeRearFamilyFundamental
  RearOwnDriftFundamental RearTrack

variable {F Ydot : ℝ → ℝ → ℂ} {Θ δ K sf etaF alphaT kT gS : ℝ → ℝ → ℝ}
  {m P P' Kx Dd : ℝ → ℝ} {P0 khat d kx kh Qmax : ℝ}

/-- The coefficient of the one-period drift estimate of the selected rears:
`Q_max·κ̂/(1 − κ̂²)`. -/
def rearDriftConst (Qmax kh : ℝ) : ℝ := Qmax * (kh / (1 - kh ^ 2))

theorem rearDriftConst_nonneg (hQ : 0 ≤ Qmax) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    0 ≤ rearDriftConst Qmax kh := by
  have hsq : 0 < 1 - kh ^ 2 := by nlinarith
  exact mul_nonneg hQ (div_nonneg hkh0 hsq.le)

/-- **The comparison path of the family of selected rears of a path of fronts,
with no hypothesis on the motion of the rear length.**

Every structural input is read off the front data: the slices close up with the
rear arclength period, their tangent angle turns by `2π` over it, and the
tangential component of the motion obeys the one-period drift estimate.  The
marking is the flow of minus that tangential component; it fixes the base point
and carries the unit parameter interval onto one rear period. -/
theorem exists_variableSpeed_normalPath_of_rearFamily_from_front
    {p q : Data} (Γ : NormalPath p q)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hK : ∀ t s, |K t s| ≤ kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hFC : ContDiff ℝ 1 (uncurry F)) (hΘC : ContDiff ℝ 1 (uncurry Θ))
    (hδC : ContDiff ℝ 1 (uncurry δ)) (hsfC : ContDiff ℝ 1 (uncurry sf))
    (hPC : ContDiff ℝ 1 P) (hPd : ∀ t, HasDerivAt P (P' t) t)
    (hYdotC : ContDiff ℝ (3 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (3 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hkC1 : ContDiff ℝ 1 (uncurry fun t x => Real.tan (δ t (sf t x))))
    -- the closing of the front, and the rear period
    (hδper : ∀ t, Function.Periodic (δ t) (P t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hQpos : ∀ t, 0 < rearArclength (δ t) (P t))
    (hQmax : ∀ t, rearArclength (δ t) (P t) ≤ Qmax)
    (hxi0 : ∀ t, frameTangential Ydot (rearOwnAngle Θ δ sf) t 0 = 0)
    -- the inverse Jacobi ODE of the rear normal rate
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hPpos : ∀ t, 0 < P t) (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    (hkappa1 : rearKappa1 kh ≤ khat)
    (halphaT : ∀ t x, HasDerivAt (fun r => rearOwnAngle Θ δ sf r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => Real.tan (δ r (sf r x))) (kT t x) t)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (rearOwnAngle Θ δ sf r s : ℂ))) W t ∧
      HasDerivAt (fun x => (frameTangential Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ))
        + (frameNormal Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * (Complex.I * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ)))) W s)
    (hKxbd : ∀ t x, |(K t (sf t x) - Real.sin (δ t (sf t x)))
      / Real.cos (δ t (sf t x)) ^ 3| ≤ Kx t)
    (hKxnn : ∀ t, 0 ≤ Kx t) (hKxm : ∀ t, Kx t ≤ kx)
    (hkXc : Continuous (uncurry fun t x => (K t (sf t x) - Real.sin (δ t (sf t x)))
      / Real.cos (δ t (sf t x)) ^ 3))
    (hgSd : ∀ t x, HasDerivAt (fun x' => etaF t (sf t x') / Real.cos (δ t (sf t x')))
      (gS t x) x)
    (hgSbd : ∀ t x, |gS t x| ≤ Dd t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hmc : Continuous m) (hm0 : ∀ t, 0 ≤ m t)
    (hmstop : ∀ t ∉ Ioo (0 : ℝ) Γ.T, m t = 0)
    (hmge : ∀ t, Γ.m t / Real.sqrt (1 - kh ^ 2) ≤ m t)
    (hnumA : 2 + 2 * khat * rearDriftConst Qmax kh ≤ 1 / P0)
    (hnumK : (d + 2) + khat ^ 2 + 2 * rearDriftConst Qmax kh * kx
      ≤ 1 / P0 ^ 2 + khat ^ 2) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      (∀ t, Phi t 0 = 0) ∧
      (∀ u t, HasDerivAt (fun s => Phi s u)
        (-frameTangential Ydot (rearOwnAngle Θ δ sf) t (Phi t u)) t) ∧
      ∀ a b : Data, (∀ u, rearOwn F Θ δ sf 0 (Phi 0 u) = a.1 u) →
        (∀ u, rearOwn F Θ δ sf Γ.T (Phi Γ.T u) = b.1 u) →
        (∀ t, ∀ j ≤ 2, MarkedTopology.supNorm
          (iteratedDeriv j (fun u => frameNormal Ydot (rearOwnAngle Θ δ sf) t (Phi t u)))
            ≤ m t) →
        ∃ Γ' : NormalPath a b, Γ'.T = Γ.T ∧
          (∀ t u, Γ'.X t u = rearOwn F Θ δ sf t (Phi t u)) ∧ Γ'.m = m ∧
          cost Γ' = (∫ t in (0 : ℝ)..Γ.T, m t) ∧
          IsVariableSpeedNormalPath P0
            (costP1 (rearArclength (δ 0) (P 0)) khat (∫ t in (0 : ℝ)..Γ.T, m t)) khat
            (costG1 (rearArclength (δ 0) (P 0)) khat (rearKappa2 kh)
              (∫ t in (0 : ℝ)..Γ.T, m t))
            (khat * costG1 (rearArclength (δ 0) (P 0)) khat (rearKappa2 kh)
                (∫ t in (0 : ℝ)..Γ.T, m t)
              + rearKappa2 kh
                * costP1 (rearArclength (δ 0) (P 0)) khat
                  (∫ t in (0 : ℝ)..Γ.T, m t) ^ 2) Γ' := by
  have hYdotC1 : ContDiff ℝ (1 : ℕ) (uncurry Ydot) := hYdotC.of_le (by norm_num)
  have hangC1 : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf)) :=
    hangC.of_le (by norm_num)
  have hδslice : ∀ t, Continuous (δ t) := fun t =>
    hδC.continuous.comp (continuous_const.prodMk continuous_id)
  have hQmax0 : 0 ≤ Qmax := le_trans (hQpos 0).le (hQmax 0)
  have hrnn : 0 ≤ rearDriftConst Qmax kh := rearDriftConst_nonneg hQmax0 hkh0 hkh1
  -- the closing of the slices and the turning of their tangent angle
  have hclose : ∀ t x, rearOwn F Θ δ sf t (x + rearArclength (δ t) (P t))
      = rearOwn F Θ δ sf t x := fun t x =>
    rearOwn_closing hkh0 hkh1 hδslice hstrip0 hstrip1 hδper hsfinv hFper hΘper t x
  have hangper : ∀ t x, rearOwnAngle Θ δ sf t (x + rearArclength (δ t) (P t))
      = rearOwnAngle Θ δ sf t x + 2 * Real.pi := fun t x =>
    RearOwnPathDistFrame.rearOwnAngle_shift hkh0 hkh1 hδslice hstrip0 hstrip1 hδper
      hsfinv hΘper t x
  -- the rear period moves differentiably, with no constraint on its derivative
  have hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r))
      ((∫ u in (0 : ℝ)..P t,
          SelectedChangeOfVariable.cosTimeDeriv δ (RearOwnHigherRegularity.partialTime δ) t u)
        + P' t * Real.cos (δ t (P t))) t := fun t =>
    SelInvDriftRigidity.hasDerivAt_rearPeriod hδC hPd t
  -- the one-period drift estimate of the tangential component
  have hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (rearArclength (δ t) (P t)),
      |frameTangential Ydot (rearOwnAngle Θ δ sf) t x|
        ≤ rearDriftConst Qmax kh * Γ.m t := fun t x hx =>
    abs_frameTangential_le_cost_on_period (K := K) (etaF := etaF) (m := Γ.m) hkh0 hkh1
      hQpos hQmax hstrip0 hstrip1 hcos hF hΘ hsteer hsf hsfinv hδper hFper hΘper hFC
      hΘC hδC hsfC hPC hYt hYdotC1 hangC1 hjac
      (fun a y => abs_frontNormalVelocity_le_cost_density Γ hPpos hlink a y)
      (fun a => Γ.m_nonneg a) hxi0 t hx
  have hroot : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hroot1 : Real.sqrt (1 - kh ^ 2) ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
  have hcostle : ∀ t, Γ.m t ≤ m t := by
    intro t
    refine le_trans ?_ (hmge t)
    rw [le_div_iff₀ hroot]
    nlinarith [Γ.m_nonneg t]
  exact exists_variableSpeed_normalPath_of_rearFamily_fundamental
    (Q := fun t => rearArclength (δ t) (P t))
    (Q' := fun t => (∫ u in (0 : ℝ)..P t,
        SelectedChangeOfVariable.cosTimeDeriv δ (RearOwnHigherRegularity.partialTime δ) t u)
      + P' t * Real.cos (δ t (P t)))
    (Rb := fun t => rearDriftConst Qmax kh * Γ.m t) (r := rearDriftConst Qmax kh)
    (K := K) (etaF := etaF) (P := P) (Kx := Kx) (Dd := Dd) (gS := gS)
    (alphaT := alphaT) (kT := kT) (m := m) (khat := khat) (d := d) (kx := kx)
    (P0 := P0) (kh := kh)
    Γ hkh0 hkh1 hstrip0 hstrip1 hK hF hΘ hsteer hsf hcos hYt hFC hΘC hδC hsfC hYdotC
    hangC hkC1 hQpos hQd hclose hangper hxi0 hjac hPpos hlink hkappa1 halphaT hkT
    halphaTc hkTc halphaTS hmixed hKxbd hKxnn hKxm hkXc hRbd
    (fun t => mul_le_mul_of_nonneg_left (hcostle t) hrnn) hrnn
    hgSd hgSbd hDm hmc hm0 hmstop hmge hnumA hnumK

end GaugeRearFamilyFromFront
