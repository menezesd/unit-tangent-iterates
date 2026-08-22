import Mathlib
import UnitTangentIterates.GaugeFlowVariableSpeedPartials
import UnitTangentIterates.GaugeFlowVariablePeriod

/-!
# The variable-speed assembly with every bound asked on one period only

`GaugeFlowVariableSpeedPartials.isVariableSpeedFamily_of_gauge_flow_partials`
produces a variable-speed family from a family of unit-speed slices read in the
gauge marking `Φ`, and it asks for its bounds *globally in the arclength*: the
field `h` of the marking, the two time derivatives `∂_tα`, `∂_t k` of the frame
data of the slices and the space derivative `∂_x k` are all required to be
bounded on the whole line at each time.

For a family of closed curves whose arclength period `Q t` **moves** those
hypotheses cannot hold.  Differentiating the closing relation gives the drift
relations

```
  h(t, x + Q t) = h(t, x) + Q'(t) ,
  ∂_tα(t, x + Q t) = ∂_tα(t, x) − k(t,x)·Q'(t) ,
  ∂_t k(t, x + Q t) = ∂_t k(t, x) − ∂_x k(t,x)·Q'(t) ,
```

so each of those three quantities grows linearly along the arclength unless
`Q' = 0` — which is exactly the rigidity of `SelInvDriftRigidity.lean` and
`GaugePeriodRigidity.lean`.

What survives is the *composite*: the two quantities the assembly really uses,

```
  d/dt α(t, Φ(t,u)) = ∂_tα + k·h ,   d/dt k(t, Φ(t,u)) = ∂_t k + ∂_x k·h ,
```

are `1`-periodic in the gauge parameter, the three drifts cancelling exactly.
Since the flow of a quasi-periodic field translates by the current period
(`GaugeFlowVariablePeriod.flow_translation_var`) and fixes the base point, the
unit parameter interval is carried onto one period `[0, Q t]`, so a bound on the
fundamental domain suffices for every parameter.

`isVariableSpeedFamily_of_gauge_flow_fundamental` is therefore the assembly with
all its pointwise bounds — on `k`, on `∂_x h`, on `∂²_x h`, on `∂_tα`, on
`∂_t k`, on `∂_x k` and on the field `h` itself — asked only for
`x ∈ [0, Q t]`, and with no constraint whatsoever on the motion of the period.

Main results:

* `bound_of_periodic` — a bound on one period of a periodic function is a bound
  everywhere;
* `partialTime_angle_shift`, `partialTime_curv_shift` — the drift relations of
  the two time derivatives, from the closing relations;
* `isVariableSpeedFamily_of_gauge_flow_fundamental` — the assembly.
-/

noncomputable section

open Set Function

namespace GaugeFlowFundamentalDomain

open FlowDerivative GaugeFlowTimeDerivative GaugeFlowVariableSpeedFamily
  GaugeReparamFrameTime NormalPathC2IncrementVariableSpeed GaugeFlowVariablePeriod

/-! ### Bounds on one period -/

/-- **A bound valid on one period of a periodic function is valid everywhere.** -/
theorem bound_of_periodic {F : ℝ → ℝ} {c B : ℝ} (hc : 0 < c)
    (hper : Function.Periodic F c) (hb : ∀ x ∈ Icc (0 : ℝ) c, |F x| ≤ B) (x : ℝ) :
    |F x| ≤ B := by
  have hfr : c * Int.fract (x / c) = x - (⌊x / c⌋ : ℝ) * c := by
    rw [Int.fract]
    field_simp
  have hval : F x = F (c * Int.fract (x / c)) := by
    rw [hfr, hper.sub_int_mul_eq ⌊x / c⌋]
  rw [hval]
  refine hb _ ⟨mul_nonneg hc.le (Int.fract_nonneg _), ?_⟩
  calc c * Int.fract (x / c) ≤ c * 1 :=
        mul_le_mul_of_nonneg_left (Int.fract_lt_one _).le hc.le
    _ = c := mul_one c

/-! ### The periodic data of a closed family -/

variable {alpha k alphaT kT kX : ℝ → ℝ → ℝ} {Q Q' : ℝ → ℝ}

/-- **The arclength derivative of a quasi-periodic function is periodic.**  The
field of the gauge marking of a family whose period moves drifts by `Q'(t)` over
one period, so its space derivatives carry no drift at all. -/
theorem periodic_deriv_of_quasiPeriodic {f fx : ℝ → ℝ → ℝ}
    (hfx : ∀ t x, HasDerivAt (f t) (fx t x) x)
    (hqp : ∀ t x, f t (x + Q t) = f t x + Q' t) (t : ℝ) :
    Function.Periodic (fx t) (Q t) := by
  intro x
  have h1 : HasDerivAt (fun y => f t (y + Q t)) (fx t (x + Q t)) x :=
    HasDerivAt.comp_add_const x (Q t) (hfx t (x + Q t))
  have h2 : HasDerivAt (fun y => f t (y + Q t)) (fx t x) x := by
    have heq : (fun y => f t (y + Q t)) = fun y => f t y + Q' t := funext fun y => hqp t y
    rw [heq]
    exact (hfx t x).add_const (Q' t)
  exact h1.unique h2

/-- **The arclength derivative of a periodic function is periodic.** -/
theorem periodic_deriv_of_periodic {f fx : ℝ → ℝ → ℝ}
    (hfx : ∀ t x, HasDerivAt (f t) (fx t x) x)
    (hper : ∀ t, Function.Periodic (f t) (Q t)) (t : ℝ) :
    Function.Periodic (fx t) (Q t) := by
  intro x
  have h1 : HasDerivAt (fun y => f t (y + Q t)) (fx t (x + Q t)) x :=
    HasDerivAt.comp_add_const x (Q t) (hfx t (x + Q t))
  have h2 : HasDerivAt (fun y => f t (y + Q t)) (fx t x) x := by
    have heq : (fun y => f t (y + Q t)) = f t := funext fun y => hper t y
    rw [heq]
    exact hfx t x
  exact h1.unique h2

/-! ### The drift relations of the two time derivatives -/

/-- **The drift of the time derivative of the tangent angle.**  If the tangent
angle of the slice at time `t` increases by the constant `turn` over one period
`Q t`, then differentiating that relation in the time gives
`∂_tα(t, x + Q t) = ∂_tα(t, x) − k(t,x)·Q'(t)`: the time derivative of the angle
is *not* periodic when the period moves. -/
theorem partialTime_angle_shift {turn : ℝ}
    (halphaC1 : ContDiff ℝ 1 (uncurry alpha))
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (halpha : ∀ t x, HasDerivAt (alpha t) (k t x) x)
    (hkper : ∀ t, Function.Periodic (k t) (Q t))
    (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (halphaper : ∀ t x, alpha t (x + Q t) = alpha t x + turn) (t x : ℝ) :
    alphaT t (x + Q t) = alphaT t x - k t x * Q' t := by
  have h1 : HasDerivAt (fun r => alpha r (x + Q r))
      (alphaT t (x + Q t) + k t (x + Q t) * Q' t) t :=
    hasDerivAt_along_flow (f := alpha) (ft := alphaT) (fx := k)
      (R := fun r _ => Q' r) (Phi := fun r _ => x + Q r)
      halphaC1 halphaT halpha (fun _ r => (hQd r).const_add x) 0 t
  have h2 : HasDerivAt (fun r => alpha r (x + Q r)) (alphaT t x) t := by
    have heq : (fun r => alpha r (x + Q r)) = fun r => alpha r x + turn :=
      funext fun r => halphaper r x
    rw [heq]
    exact (halphaT t x).add_const turn
  have h3 := h1.unique h2
  rw [hkper t x] at h3
  linarith

/-- **The drift of the time derivative of the curvature.**  Same computation for
a curvature that is periodic with the moving period:
`∂_t k(t, x + Q t) = ∂_t k(t, x) − ∂_x k(t,x)·Q'(t)`. -/
theorem partialTime_curv_shift
    (hkC1 : ContDiff ℝ 1 (uncurry k))
    (hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (hkXper : ∀ t, Function.Periodic (kX t) (Q t))
    (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hkper : ∀ t, Function.Periodic (k t) (Q t)) (t x : ℝ) :
    kT t (x + Q t) = kT t x - kX t x * Q' t := by
  have h1 : HasDerivAt (fun r => k r (x + Q r)) (kT t (x + Q t) + kX t (x + Q t) * Q' t) t :=
    hasDerivAt_along_flow (f := k) (ft := kT) (fx := kX)
      (R := fun r _ => Q' r) (Phi := fun r _ => x + Q r)
      hkC1 hkT hkX (fun _ r => (hQd r).const_add x) 0 t
  have h2 : HasDerivAt (fun r => k r (x + Q r)) (kT t x) t := by
    have heq : (fun r => k r (x + Q r)) = fun r => k r x := funext fun r => hkper r x
    rw [heq]
    exact hkT t x
  have h3 := h1.unique h2
  rw [hkXper t x] at h3
  linarith

/-! ### The assembly -/

/-- **The variable-speed assembly of a family read in its gauge marking, with
every bound asked on one period only.**

The hypotheses are those of
`GaugeFlowVariableSpeedPartials.isVariableSpeedFamily_of_gauge_flow_partials`,
except that

* the pointwise bounds on the curvature `k`, on the two space derivatives
  `∂_x h`, `∂²_x h` of the field, on the two time derivatives `∂_tα`, `∂_t k` of
  the frame data and on the field `h` itself are asked only for
  `x ∈ [0, Q t]` — one period of the slice at time `t`;
* in exchange, the closing structure of the family is given: the field is
  quasi-periodic (`h(t, x + Q t) = h(t,x) + Q'(t)`, the closing relation of
  `GaugeClosingRelations.lean`), the curvature is periodic, the tangent angle
  increases by a constant over one period, and the marking starts at the affine
  marking of period `Q 0` and fixes the base point.

Nothing is assumed about the motion of the period. -/
theorem isVariableSpeedFamily_of_gauge_flow_fundamental
    {Y : ℝ → ℝ → ℂ} {h hx hxx Phi : ℝ → ℝ → ℝ}
    {C C2 A Kt Kx Rb m : ℝ → ℝ} {K K2 : NNReal} {turn P0 P1 khat G1 Cg : ℝ}
    -- the slices, parametrized by their own arclength
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    -- the field and its flow
    (hlip : ∀ t, LipschitzWith K (h t)) (hcont : Continuous (uncurry h))
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q 0 * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x) (hxcont : Continuous (uncurry hx))
    (hxxd : ∀ s x, HasDerivAt (hx s) (hxx s x) x) (hxxcont : Continuous (uncurry hxx))
    (hxxK : ∀ s x, |hxx s x| ≤ (K2 : ℝ))
    -- the uniform bounds on the two flow derivatives
    (hP1 : ∀ t u, flowDeriv hx Phi (Q 0) t u ≤ P1)
    (hG1 : ∀ t u, |flowDeriv2 hx hxx Phi (Q 0) t u| ≤ G1)
    (hCnn : ∀ t, 0 ≤ C t) (hC2nn : ∀ t, 0 ≤ C2 t)
    -- the comparison of the field with the cost density
    (hcost : ∀ t, C t * P1 ≤ khat * P1 * m t)
    (hcost2 : ∀ t, C t * G1 + C2 t * P1 ^ 2 ≤ Cg * m t)
    -- the frame data of the slices, as partial derivatives
    (halphaC1 : ContDiff ℝ 1 (uncurry alpha)) (hkC1 : ContDiff ℝ 1 (uncurry k))
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (hkXc : Continuous (uncurry kX)) (hkc : Continuous (uncurry k))
    (hKxnn : ∀ t, 0 ≤ Kx t)
    (hcostA : ∀ t, A t + khat * Rb t ≤ 1 / P0 * m t)
    (hcostK : ∀ t, Kt t + Kx t * Rb t ≤ (1 / P0 ^ 2 + khat ^ 2) * m t)
    -- the closing structure of the family
    (hQpos : ∀ t, 0 < Q t) (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hqp : ∀ t x, h t (x + Q t) = h t x + Q' t)
    (hkper : ∀ t, Function.Periodic (k t) (Q t))
    (halphaper : ∀ t x, alpha t (x + Q t) = alpha t x + turn)
    (hbase : ∀ t, Phi t 0 = 0)
    -- the bounds, on one period only
    (hk : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |k t x| ≤ khat)
    (hC : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |hx t x| ≤ C t)
    (hC2 : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |hxx t x| ≤ C2 t)
    (hAbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |alphaT t x| ≤ A t)
    (hKtbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |kT t x| ≤ Kt t)
    (hKxbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |kX t x| ≤ Kx t)
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |h t x| ≤ Rb t) :
    IsVariableSpeedFamily P0 P1 khat G1 Cg (fun t u => Y t (Phi t u)) m := by
  have hell : (0 : ℝ) < Q 0 := hQpos 0
  have hkhat : 0 ≤ khat := le_trans (abs_nonneg _) (hk 0 0 ⟨le_rfl, (hQpos 0).le⟩)
  ------------------------------------------------------------------
  -- the flow carries the unit interval onto one period
  ------------------------------------------------------------------
  have htrans : ∀ u t, Phi t (u + 1) = Phi t u + Q t := fun u t =>
    flow_translation_var hlip hQd hqp hPhid hPhi0 u t
  have hPhiu : ∀ t u, HasDerivAt (Phi t) (flowDeriv hx Phi (Q 0) t u) u := fun t u =>
    hasDerivAt_flow_initial hlip hcont hPhid hell hPhi0 hxd u t
  have hmono : ∀ t, StrictMono (Phi t) := by
    intro t
    refine strictMono_of_deriv_pos fun u => ?_
    rw [(hPhiu t u).deriv]
    exact flowDeriv_pos hell t u
  have hmem : ∀ t, ∀ u ∈ Icc (0 : ℝ) 1, Phi t u ∈ Icc (0 : ℝ) (Q t) := by
    intro t u hu
    have h1 : Phi t 1 = Q t := by
      have := htrans 0 t
      rwa [zero_add, hbase t, zero_add] at this
    refine ⟨?_, ?_⟩
    · rw [← hbase t]
      exact (hmono t).monotone hu.1
    · rw [← h1]
      exact (hmono t).monotone hu.2
  ------------------------------------------------------------------
  -- the periodic data of the family
  ------------------------------------------------------------------
  have hxper : ∀ t, Function.Periodic (hx t) (Q t) :=
    periodic_deriv_of_quasiPeriodic hxd hqp
  have hxxper : ∀ t, Function.Periodic (hxx t) (Q t) :=
    periodic_deriv_of_periodic hxxd hxper
  have hkXper : ∀ t, Function.Periodic (kX t) (Q t) :=
    periodic_deriv_of_periodic hkX hkper
  ------------------------------------------------------------------
  -- the two bounds that are global because their data are periodic
  ------------------------------------------------------------------
  have hCg : ∀ t x, |hx t x| ≤ C t := fun t x =>
    bound_of_periodic (hQpos t) (hxper t) (hC t) x
  have hC2g : ∀ t x, |hxx t x| ≤ C2 t := fun t x =>
    bound_of_periodic (hQpos t) (hxxper t) (hC2 t) x
  have hkflowper : ∀ t, Function.Periodic (fun u => k t (Phi t u)) 1 := by
    intro t u
    simp only
    rw [htrans u t, hkper t (Phi t u)]
  have hkflow : ∀ t u, |k t (Phi t u)| ≤ khat := fun t u =>
    bound_of_periodic one_pos (hkflowper t)
      (fun u' hu' => hk t _ (hmem t u' hu')) u
  ------------------------------------------------------------------
  -- the two composites are periodic in the gauge parameter
  ------------------------------------------------------------------
  have halphaTshift : ∀ t x, alphaT t (x + Q t) = alphaT t x - k t x * Q' t :=
    fun t x => partialTime_angle_shift halphaC1 halphaT halpha hkper hQd halphaper t x
  have hkTshift : ∀ t x, kT t (x + Q t) = kT t x - kX t x * Q' t :=
    fun t x => partialTime_curv_shift hkC1 hkT hkX hkXper hQd hkper t x
  have hFaper : ∀ t, Function.Periodic
      (fun u => alphaT t (Phi t u) + k t (Phi t u) * h t (Phi t u)) 1 := by
    intro t u
    simp only
    rw [htrans u t, halphaTshift t (Phi t u), hkper t (Phi t u), hqp t (Phi t u)]
    ring
  have hFkper : ∀ t, Function.Periodic
      (fun u => kT t (Phi t u) + kX t (Phi t u) * h t (Phi t u)) 1 := by
    intro t u
    simp only
    rw [htrans u t, hkTshift t (Phi t u), hkXper t (Phi t u), hqp t (Phi t u)]
    ring
  have hFabd : ∀ t u, |alphaT t (Phi t u) + k t (Phi t u) * h t (Phi t u)|
      ≤ 1 / P0 * m t := by
    intro t u
    refine bound_of_periodic one_pos (hFaper t) (fun u' hu' => ?_) u
    exact le_trans (abs_deriv_along_flow_le (ft := alphaT) (fx := k) (R := h)
      t (Phi t u') (hAbd t _ (hmem t u' hu')) (hk t _ (hmem t u' hu'))
      (hRbd t _ (hmem t u' hu')) hkhat) (hcostA t)
  have hFkbd : ∀ t u, |kT t (Phi t u) + kX t (Phi t u) * h t (Phi t u)|
      ≤ (1 / P0 ^ 2 + khat ^ 2) * m t := by
    intro t u
    refine bound_of_periodic one_pos (hFkper t) (fun u' hu' => ?_) u
    exact le_trans (abs_deriv_along_flow_le (ft := kT) (fx := kX) (R := h)
      t (Phi t u') (hKtbd t _ (hmem t u' hu')) (hKxbd t _ (hmem t u' hu'))
      (hRbd t _ (hmem t u' hu')) (hKxnn t)) (hcostK t)
  ------------------------------------------------------------------
  -- the assembly
  ------------------------------------------------------------------
  have hflowc : ∀ u, Continuous fun t => Phi t u := fun u =>
    GaugeFlowTimeDerivative.continuous_flow_time hPhid u
  exact isVariableSpeedFamily_of_gauge_flow (ell := Q 0)
    (alphat := fun t u => alphaT t (Phi t u) + k t (Phi t u) * h t (Phi t u))
    (kappat := fun t u => kT t (Phi t u) + kX t (Phi t u) * h t (Phi t u))
    hY halpha hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxK hP1 hG1
    hkflow hCg hC2g hCnn hC2nn hcost hcost2
    (fun t u => hasDerivAt_along_flow halphaC1 halphaT halpha hPhid u t)
    (fun u => ((halphaTc.comp (continuous_id.prodMk (hflowc u))).add
      ((hkc.comp (continuous_id.prodMk (hflowc u))).mul
        (hcont.comp (continuous_id.prodMk (hflowc u))))))
    hFabd
    (fun t u => hasDerivAt_along_flow hkC1 hkT hkX hPhid u t)
    (fun u => ((hkTc.comp (continuous_id.prodMk (hflowc u))).add
      ((hkXc.comp (continuous_id.prodMk (hflowc u))).mul
        (hcont.comp (continuous_id.prodMk (hflowc u))))))
    hFkbd

end GaugeFlowFundamentalDomain
