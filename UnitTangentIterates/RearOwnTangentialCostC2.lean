import Mathlib
import UnitTangentIterates.RearOwnTangentialCost

/-!
# The second growth coefficient of the gauge field, from the cost density

`RearOwnTangentialCost.lean` produces the first coefficient of the gauge field
of the family of selected rears from the geometry: at each time the first
arclength derivative of the tangential component obeys
`|∂_xξ(t, ·)| ≤ κ̂/(1 − κ̂²) · m t`, `m` the cost density of the path of fronts.
That is what the `C⁰` defect of the gauge marking consumes.

The `C²` defect (`MarkingDefectCostC2.lean`, `GaugeMarkingDefectFrameC2.lean`)
consumes one more coefficient: a bound for the **second** arclength derivative
of the tangential component, again against the cost density.  This file produces
it, from the same mechanism read at each time separately.  By
`RearOwnTangential.partialX_partialX_frameTangential_rearOwn`,

```
  ∂_x²ξ = (sec δ · η_F − η) tan δ + η (K − sin δ) sec³δ ,
```

so on the selected strip a bound `E₀ t` for the rear normal velocity and a bound
`E_F t` for the front's give

```
  |∂_x²ξ(t, ·)| ≤ (E_F t/√(1−κ̂²) + E₀ t)·κ̂/√(1−κ̂²) + E₀ t·2κ̂/√(1−κ̂²)³ .
```

The maximum principle for the inverse Jacobi ODE replaces `E₀ t` by
`E_F t/√(1−κ̂²)`, and along a normal path of fronts `E_F t` is at most the cost
density, so

```
  |∂_x²ξ(t, ·)| ≤ (2κ̂/(1−κ̂²) + 2κ̂/(1−κ̂²)²) · m t = gaugeGrowth2 κ̂ · m t .
```

Main results:

* `abs_partialX_partialX_frameTangential_le_slice` — the bound at a single time;
* `abs_partialX_partialX_frameTangential_le_front` — the same with the rear
  normal velocity eliminated by the maximum principle;
* `abs_partialX_partialX_frameTangential_le_cost_density` — the bound against
  the cost density of the path, with the explicit constant `gaugeGrowth2 κ̂`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearFamilyFrame RearOwnArclength

namespace RearOwnTangentialCostC2

open UniformFrameBounds RearOwnTangential RearOwnTangentialCost

variable {F Ydot : ℝ → ℝ → ℂ} {Θ δ K sf : ℝ → ℝ → ℝ}

/-- The second growth coefficient of the gauge field on the selected strip. -/
def gaugeGrowth2 (kh : ℝ) : ℝ := 2 * kh / (1 - kh ^ 2) + 2 * kh / (1 - kh ^ 2) ^ 2

theorem gaugeGrowth2_nonneg {kh : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    0 ≤ gaugeGrowth2 kh := by
  have hsq : 0 < 1 - kh ^ 2 := by nlinarith
  have h1 : 0 ≤ 2 * kh / (1 - kh ^ 2) := by positivity
  have h2 : 0 ≤ 2 * kh / (1 - kh ^ 2) ^ 2 := by positivity
  simpa [gaugeGrowth2] using add_nonneg h1 h2

/-! ### The second gauge constant at a single time -/

/-- **The second gauge constant at time `t`.**  The time-slice form of
`RearOwnTangential.abs_partialX_partialX_frameTangential_le`: the two sup bounds
may depend on the time, and the conclusion then does too. -/
theorem abs_partialX_partialX_frameTangential_le_slice {etaF : ℝ → ℝ → ℝ}
    {E0 EF : ℝ → ℝ} {kh : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hK : ∀ t s, |K t s| ≤ kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hYdotC : ContDiff ℝ (2 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hE0 : ∀ t x, |frameNormal Ydot (rearOwnAngle Θ δ sf) t x| ≤ E0 t)
    (hEF : ∀ t s, |etaF t s| ≤ EF t) (t x : ℝ) :
    |partialX (partialX (frameTangential Ydot (rearOwnAngle Θ δ sf))) t x|
      ≤ (EF t / Real.sqrt (1 - kh ^ 2) + E0 t) * (kh / Real.sqrt (1 - kh ^ 2))
        + E0 t * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3) := by
  rw [partialX_partialX_frameTangential_rearOwn hF hΘ hsteer hsf hcos hYt hYdotC hangC hjac t x]
  have hE0nn : 0 ≤ E0 t := le_trans (abs_nonneg _) (hE0 t x)
  have hEFnn : 0 ≤ EF t := le_trans (abs_nonneg _) (hEF t (sf t x))
  have hcpos : 0 < Real.sqrt (1 - kh ^ 2) := (strip_bounds hkh0 hkh1
    (hstrip0 t (sf t x)) (hstrip1 t (sf t x))).2.2.1
  have hA : |etaF t (sf t x) / Real.cos (δ t (sf t x))
      - frameNormal Ydot (rearOwnAngle Θ δ sf) t x|
      ≤ EF t / Real.sqrt (1 - kh ^ 2) + E0 t := by
    refine le_trans (abs_sub _ _) (add_le_add ?_ (hE0 t x))
    exact abs_div_cos_le_strip hkh0 hkh1 (hstrip0 t (sf t x)) (hstrip1 t (sf t x))
      (hEF t (sf t x))
  have hAnn : 0 ≤ EF t / Real.sqrt (1 - kh ^ 2) + E0 t := by positivity
  calc |(etaF t (sf t x) / Real.cos (δ t (sf t x))
            - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) * Real.tan (δ t (sf t x))
        + frameNormal Ydot (rearOwnAngle Θ δ sf) t x
          * ((K t (sf t x) - Real.sin (δ t (sf t x))) / Real.cos (δ t (sf t x)) ^ 3)|
      ≤ |(etaF t (sf t x) / Real.cos (δ t (sf t x))
            - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) * Real.tan (δ t (sf t x))|
        + |frameNormal Ydot (rearOwnAngle Θ δ sf) t x
          * ((K t (sf t x) - Real.sin (δ t (sf t x))) / Real.cos (δ t (sf t x)) ^ 3)| :=
        abs_add_le _ _
    _ ≤ (EF t / Real.sqrt (1 - kh ^ 2) + E0 t) * (kh / Real.sqrt (1 - kh ^ 2))
        + E0 t * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3) := by
        rw [abs_mul, abs_mul]
        refine add_le_add (mul_le_mul hA
          (abs_tan_le_strip hkh0 hkh1 (hstrip0 t (sf t x)) (hstrip1 t (sf t x)))
          (abs_nonneg _) hAnn) (mul_le_mul (hE0 t x)
          (abs_curvDeriv_le_strip hkh0 hkh1 (hstrip0 t (sf t x)) (hstrip1 t (sf t x))
            (hK t (sf t x))) (abs_nonneg _) hE0nn)

/-! ### The rear normal velocity eliminated -/

/-- **The second gauge constant at time `t`, from the front normal velocity.**
The maximum principle for the inverse Jacobi ODE bounds the rear normal velocity
at time `t` by `E_F t/√(1−κ̂²)`, and the two occurrences of the square root
combine into the explicit coefficient `gaugeGrowth2 κ̂`. -/
theorem abs_partialX_partialX_frameTangential_le_front {etaF : ℝ → ℝ → ℝ}
    {EF Q : ℝ → ℝ} {kh : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hK : ∀ t s, |K t s| ≤ kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hYdotC : ContDiff ℝ (2 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hQpos : ∀ t, 0 < Q t)
    (hper : ∀ t, Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t) (Q t))
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hEF : ∀ t s, |etaF t s| ≤ EF t) (t x : ℝ) :
    |partialX (partialX (frameTangential Ydot (rearOwnAngle Θ δ sf))) t x|
      ≤ gaugeGrowth2 kh * EF t := by
  have hsq : 0 < 1 - kh ^ 2 := by nlinarith
  set s : ℝ := Real.sqrt (1 - kh ^ 2) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hsq
  have hs2 : s ^ 2 = 1 - kh ^ 2 := Real.sq_sqrt hsq.le
  have hs4 : s ^ 4 = (1 - kh ^ 2) ^ 2 := by
    have : s ^ 4 = (s ^ 2) ^ 2 := by ring
    rw [this, hs2]
  have h := abs_partialX_partialX_frameTangential_le_slice (K := K)
    (E0 := fun r => EF r / s) hkh0 hkh1 hstrip0 hstrip1 hK hF hΘ hsteer hsf hcos hYt hYdotC
    hangC hjac
    (fun r y => abs_frameNormal_le_slice (Q := Q) hkh0 hkh1 hstrip0 hstrip1 hQpos hper hjac
      hEF r y) hEF t x
  refine le_trans h (le_of_eq ?_)
  have hne : s ≠ 0 := hspos.ne'
  have hsqne : (1 : ℝ) - kh ^ 2 ≠ 0 := hsq.ne'
  have hkey : (EF t / s + EF t / s) * (kh / s) + EF t / s * (2 * kh / s ^ 3)
      = 2 * EF t * kh / s ^ 2 + 2 * EF t * kh / s ^ 4 := by
    field_simp
    ring
  rw [hkey, hs2, hs4, gaugeGrowth2]
  field_simp

/-! ### The bound against the cost density -/

/-- **The second arclength derivative of the tangential component of the motion
of the selected rears is at most `gaugeGrowth2 κ̂` times the cost density of the
path of fronts.**  This is the second coefficient consumed by the `C²` defect of
the gauge marking (`GaugeMarkingDefectFrameC2.dist_le_of_frameData_cost`), the
first being supplied by
`RearOwnTangentialCost.abs_gaugeRate_le_cost_density`. -/
theorem abs_partialX_partialX_frameTangential_le_cost_density {p q : Data}
    (Γ : NormalPath p q) {etaF : ℝ → ℝ → ℝ} {Q P : ℝ → ℝ} {kh : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hK : ∀ t s, |K t s| ≤ kh)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0)
    (hYt : ∀ t x, HasDerivAt (fun r => rearOwn F Θ δ sf r x) (Ydot t x) t)
    (hYdotC : ContDiff ℝ (2 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hQpos : ∀ t, 0 < Q t)
    (hper : ∀ t, Function.Periodic (frameNormal Ydot (rearOwnAngle Θ δ sf) t) (Q t))
    (hjac : ∀ t x, HasDerivAt (fun x' => frameNormal Ydot (rearOwnAngle Θ δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle Θ δ sf) t x) x)
    (hPpos : ∀ t, 0 < P t) (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u)) (t x : ℝ) :
    |partialX (partialX (frameTangential Ydot (rearOwnAngle Θ δ sf))) t x|
      ≤ gaugeGrowth2 kh * Γ.m t :=
  abs_partialX_partialX_frameTangential_le_front (K := K) (Q := Q) (EF := Γ.m) hkh0 hkh1
    hstrip0 hstrip1 hK hF hΘ hsteer hsf hcos hYt hYdotC hangC hQpos hper hjac
    (fun r y => abs_frontNormalVelocity_le_cost_density Γ hPpos hlink r y) t x

end RearOwnTangentialCostC2
