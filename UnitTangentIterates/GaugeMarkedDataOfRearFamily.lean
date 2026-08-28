import Mathlib
import UnitTangentIterates.GaugeMarkedDataOfTangential
import UnitTangentIterates.RearOwnTangentialCost
import UnitTangentIterates.RearOwnTangentialCostC2

/-!
# The variable-speed normal path of the family of selected rears

`GaugeMarkedDataOfTangential.exists_variableSpeed_normalPath_of_tangential_const`
produces the comparison path `Γ'` — its marking, the two flow derivatives of
that marking, its Lipschitz constant and the whole variable-speed block — from
the tangential component `ξ` of the motion of a family carried in its own
arclength, given two estimates `|∂ₓξ| ≤ κ₁·m` and `|∂²ₓξ| ≤ κ₂·m` against the
cost density.

This file performs the last substitution: the family is the family of
**selected rears** `rearOwn F Θ δ sf` of a normal path of fronts `Γ`, and the
two estimates are exactly the ones proved for it,

* `RearOwnTangentialCost.abs_partialX_frameTangential_le_front` with
  `RearOwnTangentialCost.abs_frontNormalVelocity_le_cost_density`, giving
  `κ₁ = κ̂/(1 − κ̂²)`;
* `RearOwnTangentialCostC2.abs_partialX_partialX_frameTangential_le_cost_density`,
  giving `κ₂ = gaugeGrowth2 κ̂`.

Everything the tangential interface asks about the *geometry* of the family is
discharged here from the rear data alone: each slice is carried in its own
arclength (`RearOwnArclength.hasDerivAt_rearOwn_space`), its tangent angle is
the rear angle and its curvature is `tan δ`
(`RearOwnTangential.hasDerivAt_rearOwnAngle_space`,
`hasDerivAt_rearCurv_space`), the motion splits in the moving frame
(`RearFamilyFrame.frame_reconstruct`), the curvature bound `κ̂` of the slices
follows from the strip bounds, the normal rate solves the inverse Jacobi ODE
`∂ₓη = g − η` with `g = sec δ · η_F ∘ s_f`, and the sup bound the maximum
principle gives for `η` and for `g` is `m/√(1−κ̂²)`.

The cost density of the path of rears is *not* the cost density `m_F` of the
path of fronts: the maximum principle bounds the rear normal rate by
`m_F/√(1−κ̂²)`, so what the statement asks for is any density `m` above that
rescaled one.  With that choice the pointwise bound on the rear normal rate is
not a hypothesis but a conclusion, and the constant of the comparison against
the cost is `c = 1`.

What remains as hypotheses are the data the family does not determine: the time
derivatives of the tangent angle and of the curvature, the bound `R_b` on the
tangential component itself, the bound `D` on `∂ₓg`, and the two numerical
conditions of the block.

Main result: `exists_variableSpeed_normalPath_of_rearFamily`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeMarkedDataOfRearFamily

open GaugeFlowDerivCost GaugeFlowVariableSpeedPath GaugeMarkedDataOfTangential
  NormalPathC2IncrementVariableSpeed RearFamilyFrame RearOwnArclength RearOwnTangential
  RearOwnTangentialCost RearOwnTangentialCostC2 UniformFrameBounds

variable {F Ydot : ℝ → ℝ → ℂ} {Θ δ K sf etaF alphaT kT gS : ℝ → ℝ → ℝ}
  {m : ℝ → ℝ}
  {Q P Kx Rb Dd : ℝ → ℝ} {ell P0 khat d r kx kh : ℝ}

/-! ### The two constants of the rear family -/

/-- The first gauge constant of the family of selected rears, `κ̂/(1 − κ̂²)`. -/
def rearKappa1 (kh : ℝ) : ℝ := kh / (1 - kh ^ 2)

/-- The second gauge constant of the family of selected rears,
`gaugeGrowth2 κ̂ = 2κ̂/(1−κ̂²) + 2κ̂/(1−κ̂²)²`. -/
def rearKappa2 (kh : ℝ) : ℝ := gaugeGrowth2 kh

theorem rearKappa1_nonneg (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) : 0 ≤ rearKappa1 kh := by
  have hsq : 0 < 1 - kh ^ 2 := by nlinarith
  exact div_nonneg hkh0 hsq.le

theorem rearKappa2_nonneg (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) : 0 ≤ rearKappa2 kh :=
  gaugeGrowth2_nonneg hkh0 hkh1

/-- Uniformize the variable-speed constants produced for one selected-rear
path by replacing its initial rear period and accumulated cost with common
ceilings. -/
theorem uniformize_variableSpeed_certificate
    {p q : Data} (Γ : NormalPath p q)
    {P0 ell Qmax khat kh M Mtotal : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hkhat : 0 ≤ khat)
    (hell : 0 ≤ ell) (hellQ : ell ≤ Qmax)
    (hM : 0 ≤ M) (hMM : M ≤ Mtotal)
    (hΓ : IsVariableSpeedNormalPath P0 (costP1 ell khat M) khat
      (costG1 ell khat (rearKappa2 kh) M)
      (khat * costG1 ell khat (rearKappa2 kh) M +
        rearKappa2 kh * costP1 ell khat M ^ 2) Γ) :
    IsVariableSpeedNormalPath P0 (costP1 Qmax khat Mtotal) khat
      (costG1 Qmax khat (rearKappa2 kh) Mtotal)
      (khat * costG1 Qmax khat (rearKappa2 kh) Mtotal +
        rearKappa2 kh * costP1 Qmax khat Mtotal ^ 2) Γ := by
  apply NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath.mono Γ hΓ hkhat
  · exact costP1_le hell hellQ hkhat hM hMM
  · exact costG1_le hell hellQ hkhat (rearKappa2_nonneg hkh0 hkh1) hM hMM
  · exact mixedCost_le hell hellQ hkhat (rearKappa2_nonneg hkh0 hkh1) hM hMM

/-- Uniform transport conclusion obtained from the raw output of the rear
gauge construction.  This is the exact adapter from
`GaugeRearFamilyFromFront` to recursive pullback transport. -/
theorem uniform_transport_of_raw_gauge
    {p q : Data} (Γ : NormalPath p q)
    {B : Data → Data} {P0 ell Qmax khat kh M Mtotal Kfac : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hkhat : 0 ≤ khat)
    (hell : 0 ≤ ell) (hellQ : ell ≤ Qmax)
    (hM : 0 ≤ M) (hMM : M ≤ Mtotal)
    (hraw : ∃ Δ : NormalPath (B p) (B q),
      cost Δ ≤ Kfac * cost Γ ∧
      IsVariableSpeedNormalPath P0 (costP1 ell khat M) khat
        (costG1 ell khat (rearKappa2 kh) M)
        (khat * costG1 ell khat (rearKappa2 kh) M +
          rearKappa2 kh * costP1 ell khat M ^ 2) Δ) :
    ∃ Δ : NormalPath (B p) (B q),
      cost Δ ≤ Kfac * cost Γ ∧
      IsVariableSpeedNormalPath P0 (costP1 Qmax khat Mtotal) khat
        (costG1 Qmax khat (rearKappa2 kh) Mtotal)
        (khat * costG1 Qmax khat (rearKappa2 kh) Mtotal +
          rearKappa2 kh * costP1 Qmax khat Mtotal ^ 2) Δ := by
  obtain ⟨Δ, hcost, hgeom⟩ := hraw
  exact ⟨Δ, hcost, uniformize_variableSpeed_certificate Δ hkh0 hkh1 hkhat
    hell hellQ hM hMM hgeom⟩

/-- The curvature of a selected rear, `tan δ`, is at most `κ̂/(1 − κ̂²)`: the
strip bound gives `κ̂/√(1−κ̂²)`, and `√(1−κ̂²) ≥ 1−κ̂²`. -/
theorem abs_tan_le_rearKappa1 {dd : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hd0 : 0 ≤ dd)
    (hd1 : dd ≤ Real.arcsin kh) : |Real.tan dd| ≤ rearKappa1 kh := by
  have hsq : 0 < 1 - kh ^ 2 := by nlinarith
  have hroot : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 hsq
  have hle : 1 - kh ^ 2 ≤ Real.sqrt (1 - kh ^ 2) := by
    have hs2 : Real.sqrt (1 - kh ^ 2) ^ 2 = 1 - kh ^ 2 := Real.sq_sqrt hsq.le
    have hs1 : Real.sqrt (1 - kh ^ 2) ≤ 1 := by nlinarith
    nlinarith
  refine le_trans (abs_tan_le_strip hkh0 hkh1 hd0 hd1) ?_
  exact div_le_div_of_nonneg_left hkh0 hsq hle

/-! ### The sup bound on the rear normal rate and on the source of its ODE -/

/-- The maximum principle for the inverse Jacobi ODE, read against the cost
density: the normal rate of the selected rears is at most `m/√(1−κ̂²)`. -/
theorem abs_frameNormal_le_cost {p q : Data} (Γ : NormalPath p q)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hQpos : ∀ t, 0 < Q t)
    (hper : ∀ t, Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t) (Q t))
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hPpos : ∀ t, 0 < P t) (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u)) (t x : ℝ) :
    |frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ Γ.m t / Real.sqrt (1 - kh ^ 2) :=
  abs_frameNormal_le_slice (Q := Q) (EF := Γ.m) hkh0 hkh1 hstrip0 hstrip1 hQpos hper hjac
    (fun a y => abs_frontNormalVelocity_le_cost_density Γ hPpos hlink a y) t x

/-- The source `g = sec δ · η_F ∘ s_f` of the inverse Jacobi ODE is bounded by
the same quantity `m/√(1−κ̂²)`. -/
theorem abs_jacobiSource_le_cost {p q : Data} (Γ : NormalPath p q)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hPpos : ∀ t, 0 < P t) (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u)) (t x : ℝ) :
    |etaF t (sf t x) / Real.cos (δ t (sf t x))| ≤ Γ.m t / Real.sqrt (1 - kh ^ 2) :=
  abs_div_cos_le_strip hkh0 hkh1 (hstrip0 t (sf t x)) (hstrip1 t (sf t x))
    (abs_frontNormalVelocity_le_cost_density Γ hPpos hlink t (sf t x))

/-! ### The first estimate against the cost density -/

/-- The first arclength derivative of the tangential component of the motion of
the selected rears is at most `rearKappa1 κ̂` times the cost density. -/
theorem abs_partialX_frameTangential_le_rearKappa1 {p q : Data} (Γ : NormalPath p q)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hYdotC : ContDiff ℝ (1 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hQpos : ∀ t, 0 < Q t)
    (hper : ∀ t, Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t) (Q t))
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hPpos : ∀ t, 0 < P t) (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u)) (t x : ℝ) :
    |partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t x| ≤ rearKappa1 kh * Γ.m t := by
  have h := abs_partialX_frameTangential_le_front (K := K) (Q := Q) (EF := Γ.m)
    hkh0 hkh1 hstrip0 hstrip1 hF hΘ hsteer hsf hcos hYt hYdotC hangC hQpos hper hjac
    (fun a y => abs_frontNormalVelocity_le_cost_density Γ hPpos hlink a y) t x
  rw [rearKappa1, mul_comm]
  exact h

/-! ### The assembly -/

/-- **The comparison path of the family of selected rears.**  Along a normal
path `Γ` of fronts, the family of selected rears carried in its own arclength
admits a gauge marking `Φ` — the flow of minus its tangential component — under
which it is a normal path of the path metric whose slices form a variable-speed
family, with the explicit constants `costP1 ℓ κ̂ M`, `costG1 ℓ κ̂ (gaugeGrowth2 κ̂) M`
built from the cost `M = ∫₀^{T} m` of `Γ`.

Nothing about the marking is assumed: it is produced, together with its two flow
derivatives, its Lipschitz constant and the mixed second-derivative bound, from
the tangential estimates of the rear family.  The cost density `m` of the path
of rears is any density above `m_F/√(1−κ̂²)`, the bound the maximum principle
gives for the rear normal rate; the pointwise bound on that rate is therefore
discharged here rather than assumed. -/
theorem exists_variableSpeed_normalPath_of_rearFamily {p q : Data} (Γ : NormalPath p q)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hell : 0 < ell)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hK : ∀ t s, |K t s| ≤ kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hFC : ContDiff ℝ 1 (uncurry F)) (hΘC : ContDiff ℝ 1 (uncurry Θ))
    (hδC : ContDiff ℝ 1 (uncurry δ)) (hsfC : ContDiff ℝ 1 (uncurry sf))
    (hYdotC : ContDiff ℝ (3 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (3 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hkC1 : ContDiff ℝ 1 (uncurry fun t x => Real.tan (δ t (sf t x))))
    (hQpos : ∀ t, 0 < Q t)
    (hper : ∀ t, Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t) (Q t))
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
    (hRbd : ∀ t x, |frameTangential Ydot (rearOwnAngle Θ δ sf) t x| ≤ Rb t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hr : 0 ≤ r)
    (hgSd : ∀ t x, HasDerivAt (fun x' => etaF t (sf t x') / Real.cos (δ t (sf t x')))
      (gS t x) x)
    (hgSbd : ∀ t x, |gS t x| ≤ Dd t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hmc : Continuous m) (hm0 : ∀ t, 0 ≤ m t)
    (hmstop : ∀ t ∉ Ioo (0 : ℝ) Γ.T, m t = 0)
    (hmge : ∀ t, Γ.m t / Real.sqrt (1 - kh ^ 2) ≤ m t)
    (hnumA : 2 + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2) + khat ^ 2 + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = ell * u) ∧
      (∀ u t, HasDerivAt (fun s => Phi s u)
        (-frameTangential Ydot (rearOwnAngle Θ δ sf) t (Phi t u)) t) ∧
      ∀ a b : Data, (∀ u, rearOwn F Θ δ sf 0 (Phi 0 u) = a.1 u) →
        (∀ u, rearOwn F Θ δ sf Γ.T (Phi Γ.T u) = b.1 u) →
        (∀ t, ∀ j ≤ 2, MarkedTopology.supNorm
          (iteratedDeriv j (fun u => frameNormal Ydot (rearOwnAngle Θ δ sf) t (Phi t u)))
            ≤ m t) →
        ∃ Γ' : NormalPath a b, Γ'.T = Γ.T ∧ Γ'.m = m ∧
          cost Γ' = (∫ t in (0 : ℝ)..Γ.T, m t) ∧
          IsVariableSpeedNormalPath P0
            (costP1 ell khat (∫ t in (0 : ℝ)..Γ.T, m t)) khat
            (costG1 ell khat (rearKappa2 kh) (∫ t in (0 : ℝ)..Γ.T, m t))
            (khat * costG1 ell khat (rearKappa2 kh) (∫ t in (0 : ℝ)..Γ.T, m t)
              + rearKappa2 kh * costP1 ell khat (∫ t in (0 : ℝ)..Γ.T, m t) ^ 2) Γ' := by
  have hYdotC1 : ContDiff ℝ (1 : ℕ) (uncurry Ydot) := hYdotC.of_le (by norm_num)
  have hYdotC2 : ContDiff ℝ (2 : ℕ) (uncurry Ydot) := hYdotC.of_le (by norm_num)
  have hangC1 : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnAngle Θ δ sf)) :=
    hangC.of_le (by norm_num)
  have hangC2 : ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Θ δ sf)) :=
    hangC.of_le (by norm_num)
  have hroot : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hroot1 : Real.sqrt (1 - kh ^ 2) ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
  have hcostle : ∀ t, Γ.m t ≤ m t := by
    intro t
    refine le_trans ?_ (hmge t)
    rw [le_div_iff₀ hroot]
    nlinarith [Γ.m_nonneg t]
  have hen : ∀ t x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ m t := fun t x =>
    le_trans (abs_frameNormal_le_cost (Q := Q) (etaF := etaF) (P := P) Γ hkh0 hkh1
      hstrip0 hstrip1 hQpos hper hjac hPpos hlink t x) (hmge t)
  -- each slice is carried in its own arclength
  have hYspace : ∀ t s, HasDerivAt (rearOwn F Θ δ sf t)
      (Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t s : ℂ))) s := by
    intro t s
    simpa [rearOwnTangent] using
      hasDerivAt_rearOwn_space (K := K) hF hΘ hsteer hsf hcos t s
  -- the motion splits in the moving frame
  have hYtime : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x)
      ((frameTangential Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ))
        + (frameNormal Ydot (rearOwnAngle Θ δ sf) t x : ℂ)
          * (Complex.I * Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ)))) t := by
    intro t x
    have h := frame_reconstruct (Ydot t x) (rearOwnAngle Θ δ sf t x)
    refine (hYt t x).congr_deriv ?_
    simp only [frameTangential, frameNormal]
    conv_lhs => rw [← h]
    ring
  -- the curvature of the slices is dominated by `κ̂`
  have hkbd : ∀ t x, |Real.tan (δ t (sf t x))| ≤ khat := fun t x =>
    le_trans (abs_tan_le_rearKappa1 hkh0 hkh1 (hstrip0 t (sf t x)) (hstrip1 t (sf t x)))
      hkappa1
  -- the two tangential estimates
  have hCbd : ∀ t x, |partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t x|
      ≤ rearKappa1 kh * m t := by
    intro t x
    refine le_trans (abs_partialX_frameTangential_le_rearKappa1 (K := K) (Q := Q)
      (etaF := etaF) (P := P) Γ hkh0 hkh1 hstrip0 hstrip1 hF hΘ hsteer hsf hcos hYt
      hYdotC1 hangC1 hQpos hper hjac hPpos hlink t x) ?_
    exact mul_le_mul_of_nonneg_left (hcostle t) (rearKappa1_nonneg hkh0 hkh1)
  have hC2bd : ∀ t x,
      |partialX (partialX (frameTangential Ydot (rearOwnAngle Θ δ sf))) t x|
        ≤ rearKappa2 kh * m t := by
    intro t x
    refine le_trans (abs_partialX_partialX_frameTangential_le_cost_density (K := K)
      (Q := Q) (etaF := etaF) (P := P) Γ hkh0 hkh1 hstrip0 hstrip1 hK hF hΘ hsteer hsf
      hcos hYt hYdotC2 hangC2 hQpos hper hjac hPpos hlink t x) ?_
    exact mul_le_mul_of_nonneg_left (hcostle t) (rearKappa2_nonneg hkh0 hkh1)
  -- the second arclength derivative of the normal rate, read off the ODE
  have henSS : ∀ t x, HasDerivAt (fun x' => etaF t (sf t x') / Real.cos (δ t (sf t x'))
      - frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (gS t x - (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x)) x := fun t x =>
    (hgSd t x).sub (hjac t x)
  have hgbd : ∀ t x, |etaF t (sf t x) / Real.cos (δ t (sf t x))|
      ≤ Γ.m t / Real.sqrt (1 - kh ^ 2) := fun t x =>
    abs_jacobiSource_le_cost (etaF := etaF) (P := P) (sf := sf) Γ hkh0 hkh1 hstrip0
      hstrip1 hPpos hlink t x
  have henbd : ∀ t x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ Γ.m t / Real.sqrt (1 - kh ^ 2) := fun t x =>
    abs_frameNormal_le_cost (Q := Q) (etaF := etaF) (P := P) Γ hkh0 hkh1 hstrip0 hstrip1
      hQpos hper hjac hPpos hlink t x
  have hS0m : ∀ t, Γ.m t / Real.sqrt (1 - kh ^ 2) ≤ 1 * m t := by
    intro t
    rw [one_mul]
    exact hmge t
  obtain ⟨Phi, hPhi0, hflow, hmain⟩ := exists_variableSpeed_normalPath_of_tangential_const
    (Y := rearOwn F Θ δ sf) (alpha := rearOwnAngle Θ δ sf)
    (xi := frameTangential Ydot (rearOwnAngle Θ δ sf))
    (en := frameNormal Ydot (rearOwnAngle Θ δ sf))
    (k := fun t x => Real.tan (δ t (sf t x)))
    (kX := fun t x => (K t (sf t x) - Real.sin (δ t (sf t x)))
      / Real.cos (δ t (sf t x)) ^ 3)
    (enS := fun t x => etaF t (sf t x) / Real.cos (δ t (sf t x))
      - frameNormal Ydot (rearOwnAngle Θ δ sf) t x)
    (enSS := fun t x => gS t x - (etaF t (sf t x) / Real.cos (δ t (sf t x))
      - frameNormal Ydot (rearOwnAngle Θ δ sf) t x))
    (g := fun t x => etaF t (sf t x) / Real.cos (δ t (sf t x))) (gS := gS)
    (S0 := fun t => Γ.m t / Real.sqrt (1 - kh ^ 2)) (Dd := Dd) (Rb := Rb) (Kx := Kx)
    (m := m) (T := Γ.T) (kappa1 := rearKappa1 kh) (kappa2 := rearKappa2 kh)
    (alphaT := alphaT) (kT := kT) (c := 1) (d := d) (r := r) (kx := kx) (P0 := P0)
    (contDiff_frameTangential hYdotC hangC) hell
    (contDiff_one_rearOwn hFC hΘC hδC hsfC) hYspace hYtime
    (hasDerivAt_rearOwnAngle_space (K := K) hΘ hsteer hsf) hkbd
    (rearKappa2_nonneg hkh0 hkh1) hkappa1 hCbd hC2bd
    hangC1 hkC1 halphaT hkT
    (hasDerivAt_rearCurv_space (K := K) hsteer hsf hcos)
    halphaTc hkTc hkXc hkC1.continuous hKxbd hRbd hKxnn hjac henSS halphaTS hmixed hgSd
    hjac hgbd henbd hgSbd hS0m hDm hRbm hKxm hr hm0 (by simp only [mul_one]; linarith [hnumA])
    (by simp only [mul_one]; linarith [hnumK]) Γ.T_pos (contDiff_frameNormal hYdotC1 hangC1).continuous hmc
    hmstop
  exact ⟨Phi, hPhi0, hflow, fun a b ha hb hsup =>
    hmain a b ha hb (fun t u => hen t (Phi t u)) hsup⟩

end GaugeMarkedDataOfRearFamily
