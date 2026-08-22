import Mathlib
import UnitTangentIterates.RearOwnTangential
import UnitTangentIterates.MarkingDefectCost

/-!
# The growth coefficient of the gauge field, from the cost density

`MarkingDefectCost.lean` bounds the defect of a gauge marking whose field obeys
the linear growth condition `|R(t, x)| ≤ C t·|x|`, and bounds it by the cost of
the path once `C t ≤ κ · m t`.  This file produces both from the geometry of the
family of selected rears.

The mechanism is the one of `RearOwnTangential.lean`, read **at each time
separately** rather than uniformly in the time:

* the rear normal velocity solves the inverse Jacobi ODE
  `∂_xη = sec δ · η_F − η` and is periodic, so the maximum principle bounds it
  at time `t` by `‖η_F(t, ·)‖_∞ / √(1 − κ̂²)`;
* the family of rear tracks written in its own arclength has unit speed, so
  `∂_xξ = η tan δ`, and on the selected strip `0 ≤ δ ≤ arcsin κ̂` this gives
  `|∂_xξ(t, ·)| ≤ ‖η_F(t, ·)‖_∞ · κ̂/(1 − κ̂²)`;
* the tangential component vanishes at the base point of the gauge
  (`GaugeBaseFlow.lean`), so `|ξ(t, x)| ≤ |∂_xξ(t, ·)|_∞ |x|` and the tangential
  rate `−ξ/v` of the gauge flow grows linearly in `x`;
* along a normal path of fronts the front normal velocity at time `t` is the
  normal speed of the path, hence at most its cost density `m t`.

So the field of the gauge flow of the family of selected rears satisfies
`|R(t, x)| ≤ (κ̂/((1 − κ̂²) v₀) · m t)·|x|`, which is exactly the hypothesis
block that `MarkingDefectCost.abs_marking_defect_le_cost` consumes.

Main results:

* `abs_frameNormal_le_slice` — the maximum principle at a single time;
* `abs_partialX_frameTangential_le_slice` — the first gauge constant at a single
  time, from a bound for the rear normal velocity;
* `abs_partialX_frameTangential_le_front` — the same from a bound for the front
  normal velocity, with the constant `κ̂/(1 − κ̂²)`;
* `abs_gaugeRate_le_front` — the linear growth of the field of the gauge flow;
* `abs_frontNormalVelocity_le_cost_density` — the front normal velocity at time
  `t` is at most the cost density of the path;
* `abs_gaugeRate_le_cost_density` — hence the growth coefficient of the field is
  at most `κ̂/((1 − κ̂²)v₀)` times the cost density of the path.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearFamilyFrame RearOwnArclength

namespace RearOwnTangentialCost

open UniformFrameBounds RearOwnTangential

variable {F Ydot : ℝ → ℝ → ℂ} {Θ δ K sf : ℝ → ℝ → ℝ}

/-! ### The maximum principle at a single time -/

/-- **The normal velocity of the selected rears at time `t` is bounded by that
of the fronts at time `t`.**  The time-slice form of
`RearOwnTangential.abs_frameNormal_le_of_periodic`: the bound for the front
normal velocity may depend on the time, and the conclusion then does too. -/
theorem abs_frameNormal_le_slice {etaF : ℝ → ℝ → ℝ} {EF Q : ℝ → ℝ} {kh : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hQpos : ∀ t, 0 < Q t)
    (hper : ∀ t, Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t) (Q t))
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hEF : ∀ t s, |etaF t s| ≤ EF t) (t x : ℝ) :
    |frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ EF t / Real.sqrt (1 - kh ^ 2) :=
  abs_le_of_periodic_ode (hQpos t) (hper t) (hjac t)
    (fun y => abs_div_cos_le_strip hkh0 hkh1 (hstrip0 t (sf t y)) (hstrip1 t (sf t y))
      (hEF t (sf t y))) x

/-! ### The first gauge constant at a single time -/

/-- **The first gauge constant at time `t`.**  A bound `E₀ t` for the normal
velocity of the selected rears at time `t` bounds the arclength derivative of
the tangential component of their motion at that time by
`E₀ t · κ̂/√(1 − κ̂²)`. -/
theorem abs_partialX_frameTangential_le_slice {E0 : ℝ → ℝ} {kh : ℝ}
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
    (hE0 : ∀ t x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ E0 t) (t x : ℝ) :
    |partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t x|
      ≤ E0 t * (kh / Real.sqrt (1 - kh ^ 2)) := by
  rw [partialX_frameTangential_rearOwn (K := K) hF hΘ hsteer hsf hcos hYt hYdotC hangC t x,
    abs_mul]
  exact mul_le_mul (hE0 t x)
    (abs_tan_le_strip hkh0 hkh1 (hstrip0 t (sf t x)) (hstrip1 t (sf t x)))
    (abs_nonneg _) (le_trans (abs_nonneg _) (hE0 t x))

/-- **The first gauge constant at time `t`, from the front normal velocity.**
Composing the maximum principle with the previous bound: `√(1 − κ̂²)` appears
twice, so the coefficient is `κ̂/(1 − κ̂²)`. -/
theorem abs_partialX_frameTangential_le_front {etaF : ℝ → ℝ → ℝ} {EF Q : ℝ → ℝ} {kh : ℝ}
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
    (hEF : ∀ t s, |etaF t s| ≤ EF t) (t x : ℝ) :
    |partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t x|
      ≤ EF t * (kh / (1 - kh ^ 2)) := by
  have hsq : 0 < 1 - kh ^ 2 := by nlinarith
  have hroot : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 hsq
  have hrootsq : Real.sqrt (1 - kh ^ 2) * Real.sqrt (1 - kh ^ 2) = 1 - kh ^ 2 :=
    Real.mul_self_sqrt hsq.le
  have h := abs_partialX_frameTangential_le_slice (K := K)
    (E0 := fun r => EF r / Real.sqrt (1 - kh ^ 2)) hkh0 hkh1 hstrip0 hstrip1 hF hΘ hsteer
    hsf hcos hYt hYdotC hangC
    (fun r y => abs_frameNormal_le_slice (Q := Q) hkh0 hkh1 hstrip0 hstrip1 hQpos hper hjac
      hEF r y) t x
  refine le_trans h (le_of_eq ?_)
  rw [div_mul_div_comm, hrootsq]
  ring

/-! ### The linear growth of the field of the gauge flow -/

/-- **The field of the gauge flow of the family of selected rears grows at most
linearly.**  The tangential component vanishes at the base point of the gauge,
so it is bounded by its arclength derivative times `|x|`, and the tangential
rate `−ξ/v` of a slice of speed at least `v₀` therefore obeys
`|R(t, x)| ≤ (E_F t · κ̂/((1 − κ̂²)v₀))·|x|`. -/
theorem abs_gaugeRate_le_front {etaF : ℝ → ℝ → ℝ} {EF Q : ℝ → ℝ} {v : ℝ → ℝ → ℝ}
    {kh v0 : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
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
    (hEF : ∀ t s, |etaF t s| ≤ EF t)
    (hxi0 : ∀ t, frameTangential Ydot (rearOwnAngle Θ δ sf) t 0 = 0)
    (hv0 : 0 < v0) (hv : ∀ t x, v0 ≤ |v t x|) (t x : ℝ) :
    |GaugeRate.gaugeRate (frameTangential Ydot (rearOwnAngle Θ δ sf)) v t x|
      ≤ (EF t * (kh / (1 - kh ^ 2)) / v0) * |x| := by
  have hxiC : ContDiff ℝ (1 : ℕ)
      (uncurry (frameTangential Ydot (rearOwnAngle Θ δ sf))) :=
    RearOwnTangential.contDiff_frameTangential hYdotC hangC
  exact MarkingDefectCost.abs_gaugeRate_le_mul_abs
    (xi1 := partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)))
    (C := fun r => EF r * (kh / (1 - kh ^ 2)))
    (fun a y => hasDerivAt_partialX hxiC a y) hxi0
    (fun a y => abs_partialX_frameTangential_le_front (K := K) (Q := Q) hkh0 hkh1 hstrip0
      hstrip1 hF hΘ hsteer hsf hcos hYt hYdotC hangC hQpos hper hjac hEF a y)
    hv0 hv t x

/-! ### The front normal velocity and the cost density -/

/-- **The front normal velocity at time `t` is at most the cost density of the
path at time `t`.**  Every arclength `s` is the normalized parameter `s / P t`
read in the current period, at which the normal speed of the path is the front
normal velocity, and the cost density dominates the normal speed. -/
theorem abs_frontNormalVelocity_le_cost_density {p q : Data} (Γ : NormalPath p q)
    {etaF : ℝ → ℝ → ℝ} {P : ℝ → ℝ} (hPpos : ∀ t, 0 < P t)
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u)) (t s : ℝ) : |etaF t s| ≤ Γ.m t := by
  have hval : etaF t s = Γ.eta t (s / P t) := by
    rw [hlink t (s / P t), mul_div_cancel₀ _ (hPpos t).ne']
  rw [hval]
  exact Γ.abs_eta_le t (s / P t)

/-- **The growth coefficient of the field of the gauge flow is at most
`κ̂/((1 − κ̂²)v₀)` times the cost density of the path.**  This is the hypothesis
block consumed by `MarkingDefectCost.abs_marking_defect_le_cost`: the defect of
the gauge marking of the family of selected rears along a normal path of fronts
is therefore at most `2 L_max κ̂/((1 − κ̂²)v₀) · cost Γ`. -/
theorem abs_gaugeRate_le_cost_density {p q : Data} (Γ : NormalPath p q)
    {etaF v : ℝ → ℝ → ℝ} {Q P : ℝ → ℝ} {kh v0 : ℝ}
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
    (hxi0 : ∀ t, frameTangential Ydot (rearOwnAngle Θ δ sf) t 0 = 0)
    (hv0 : 0 < v0) (hv : ∀ t x, v0 ≤ |v t x|)
    (hPpos : ∀ t, 0 < P t) (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    (t x : ℝ) :
    |GaugeRate.gaugeRate (frameTangential Ydot (rearOwnAngle Θ δ sf)) v t x|
      ≤ (kh / ((1 - kh ^ 2) * v0) * Γ.m t) * |x| := by
  have hbase := abs_gaugeRate_le_front (K := K) (Q := Q) (EF := Γ.m) hkh0 hkh1 hstrip0
    hstrip1 hF hΘ hsteer hsf hcos hYt hYdotC hangC hQpos hper hjac
    (fun r y => abs_frontNormalVelocity_le_cost_density Γ hPpos hlink r y) hxi0 hv0 hv t x
  refine le_trans hbase (le_of_eq ?_)
  have hsq : (1 : ℝ) - kh ^ 2 ≠ 0 := by nlinarith [sq_nonneg kh]
  have hv0' : v0 ≠ 0 := hv0.ne'
  congr 1
  field_simp

end RearOwnTangentialCost
