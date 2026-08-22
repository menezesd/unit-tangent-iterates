import Mathlib
import UnitTangentIterates.FlowDerivative
import UnitTangentIterates.GaugeRate
import UnitTangentIterates.PathFunctionalsReparam

/-!
# The path functionals in the normal gauge

`NormalGaugeFamily.lean` puts a moving family of curves in normal gauge by
transporting the parameter along the flow `Φ` of the tangential rate, and
`PathFunctionalsReparam.lean` compares the densities of the functionals
`W, S₀, S₁, S₂` in a reparametrized variable with those in the original one,
for a reparametrization with bounded first and second derivatives and a
positive lower bound for the first one.

`FlowDerivative.lean` supplies exactly those bounds for the gauge flow: at time
`t`, the slice `u ↦ Φ(t,u)` has

`ℓe^{−K|t|} ≤ ∂_uΦ ≤ ℓe^{K|t|}`,  `|∂²_uΦ| ≤ K₂ℓ²|t|e^{2K|t|}`.

This file substitutes them, so that the comparison is available for the gauge
flow itself, with explicit constants:

```
  ‖η ∘ Φ(t,·)‖_∞     ≤ ‖η‖_∞,
  ‖(η ∘ Φ(t,·))'‖_∞  ≤ ‖η'‖_∞ · ℓe^{K|t|},
  ‖(η ∘ Φ(t,·))''‖_∞ ≤ ‖η''‖_∞ · ℓ²e^{2K|t|} + ‖η'‖_∞ · K₂ℓ²|t|e^{2K|t|},
  ∫_a^b |η ∘ Φ(t,·)| ≤ (ℓe^{−K|t|})⁻¹ ∫_{Φ(t,a)}^{Φ(t,b)} |η|.
```

Main results:

* `supNorm_gauge_le`, `supNorm_deriv_gauge_le`, `supNorm_deriv2_gauge_le` — the
  three sup-norm comparisons for the gauge flow;
* `integral_abs_gauge_le` — the `L¹` comparison;
* `gauge_functionals_comparison` — the four statements together.
-/

noncomputable section

open Set MeasureTheory MarkedTopology FlowDerivative PathFunctionalsReparam

namespace GaugeFunctionals

variable {h hx hxx : ℝ → ℝ → ℝ} {K : NNReal} {ell : ℝ} {Phi : ℝ → ℝ → ℝ}

section

variable {eta eta1 eta2 : ℝ → ℝ} {K2 : ℝ}
  (hlip : ∀ t, LipschitzWith K (h t))
  (hcont : Continuous (Function.uncurry h))
  (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
  (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
  (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x)
  (hxcont : Continuous (Function.uncurry hx))
  (hxxd : ∀ s x, HasDerivAt (hx s) (hxx s x) x)
  (hxxcont : Continuous (Function.uncurry hxx))
  (hxxbd : ∀ s x, |hxx s x| ≤ K2)

include hlip hcont hPhid hell hPhi0 hxd in
/-- The slice of the gauge flow is differentiable, with derivative
`flowDeriv`. -/
theorem hasDerivAt_gauge (t u : ℝ) :
    HasDerivAt (fun u' => Phi t u') (flowDeriv hx Phi ell t u) u :=
  hasDerivAt_flow_initial hlip hcont hPhid hell hPhi0 hxd u t

include hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxbd in
/-- The derivative of the slice of the gauge flow is itself differentiable. -/
theorem hasDerivAt_gauge_deriv (t u : ℝ) :
    HasDerivAt (fun u' => flowDeriv hx Phi ell t u')
      (flowDeriv hx Phi ell t u
        * ∫ s in (0:ℝ)..t, hxx s (Phi s u) * flowDeriv hx Phi ell s u) u :=
  hasDerivAt_flowDeriv hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxbd u t

/-! ### The sup-norm comparisons -/

/-- **The sup norm is unchanged by the gauge reparametrization.** -/
theorem supNorm_gauge_le (hbdd : BddAbove (Set.range fun x => |eta x|)) (t : ℝ) :
    supNorm (fun u => eta (Phi t u)) ≤ supNorm eta :=
  supNorm_comp_le hbdd _

include hlip hcont hPhid hell hPhi0 hxd in
/-- **The comparison of the first-derivative density in the normal gauge.** -/
theorem supNorm_deriv_gauge_le (heta1 : ∀ x, HasDerivAt eta (eta1 x) x)
    (hbdd1 : BddAbove (Set.range fun x => |eta1 x|)) (t : ℝ) :
    supNorm (deriv fun u => eta (Phi t u)) ≤ supNorm eta1 * (ell * Real.exp ((K : ℝ) * |t|)) := by
  refine supNorm_deriv_comp_le heta1 (hasDerivAt_gauge hlip hcont hPhid hell hPhi0 hxd t)
    hbdd1 (fun u => ?_)
  rw [abs_of_pos (flowDeriv_pos hell t u)]
  exact (flowDeriv_bounds hell (abs_hx_le hlip hxd) t u).2

include hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxbd in
/-- **The comparison of the second-derivative density in the normal gauge.** -/
theorem supNorm_deriv2_gauge_le (heta1 : ∀ x, HasDerivAt eta (eta1 x) x)
    (heta2 : ∀ x, HasDerivAt eta1 (eta2 x) x)
    (hbdd1 : BddAbove (Set.range fun x => |eta1 x|))
    (hbdd2 : BddAbove (Set.range fun x => |eta2 x|)) (t : ℝ) :
    supNorm (deriv (deriv fun u => eta (Phi t u)))
      ≤ supNorm eta2 * (ell * Real.exp ((K : ℝ) * |t|)) ^ 2
        + supNorm eta1 * (K2 * ell ^ 2 * |t| * Real.exp (2 * (K : ℝ) * |t|)) := by
  refine supNorm_deriv2_comp_le heta1 heta2 (hasDerivAt_gauge hlip hcont hPhid hell hPhi0 hxd t)
    (hasDerivAt_gauge_deriv hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxbd t)
    hbdd1 hbdd2 (fun u => ?_) (fun u => ?_)
  · rw [abs_of_pos (flowDeriv_pos hell t u)]
    exact (flowDeriv_bounds hell (abs_hx_le hlip hxd) t u).2
  · exact abs_flowDeriv_deriv_le hell (abs_hx_le hlip hxd) hxxbd u t

/-! ### The `L¹` comparison -/

include hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxbd in
/-- **The `L¹` comparison in the normal gauge.** -/
theorem integral_abs_gauge_le (hetac : Continuous eta) {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    (∫ u in a..b, |eta (Phi t u)|)
      ≤ (1 / (ell * Real.exp (-((K : ℝ) * |t|))))
          * ∫ x in (Phi t a)..(Phi t b), |eta x| := by
  have hm : 0 < ell * Real.exp (-((K : ℝ) * |t|)) := mul_pos hell (Real.exp_pos _)
  have hphi1c : Continuous fun u => flowDeriv hx Phi ell t u := by
    have hd : Differentiable ℝ fun u => flowDeriv hx Phi ell t u := fun u =>
      (hasDerivAt_gauge_deriv hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont
        hxxbd t u).differentiableAt
    exact hd.continuous
  exact integral_abs_comp_le hm hab hetac
    (hasDerivAt_gauge hlip hcont hPhid hell hPhi0 hxd t) hphi1c
    (fun u => (flowDeriv_bounds hell (abs_hx_le hlip hxd) t u).1)

include hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxbd in
/-- **The comparison of the path functionals in the normal gauge**, collected:
the sup norms of the normal velocity and of its first two derivatives grow at
most by the distortion of the gauge flow, and its `L¹` norm over an interval is
controlled by the `L¹` norm over the image interval. -/
theorem gauge_functionals_comparison (heta1 : ∀ x, HasDerivAt eta (eta1 x) x)
    (heta2 : ∀ x, HasDerivAt eta1 (eta2 x) x)
    (hetac : Continuous eta)
    (hbdd : BddAbove (Set.range fun x => |eta x|))
    (hbdd1 : BddAbove (Set.range fun x => |eta1 x|))
    (hbdd2 : BddAbove (Set.range fun x => |eta2 x|)) {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    supNorm (fun u => eta (Phi t u)) ≤ supNorm eta ∧
    supNorm (deriv fun u => eta (Phi t u))
        ≤ supNorm eta1 * (ell * Real.exp ((K : ℝ) * |t|)) ∧
    supNorm (deriv (deriv fun u => eta (Phi t u)))
        ≤ supNorm eta2 * (ell * Real.exp ((K : ℝ) * |t|)) ^ 2
          + supNorm eta1 * (K2 * ell ^ 2 * |t| * Real.exp (2 * (K : ℝ) * |t|)) ∧
    (∫ u in a..b, |eta (Phi t u)|)
        ≤ (1 / (ell * Real.exp (-((K : ℝ) * |t|))))
            * ∫ x in (Phi t a)..(Phi t b), |eta x| :=
  ⟨supNorm_gauge_le hbdd t,
   supNorm_deriv_gauge_le hlip hcont hPhid hell hPhi0 hxd heta1 hbdd1 t,
   supNorm_deriv2_gauge_le hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxbd
     heta1 heta2 hbdd1 hbdd2 t,
   integral_abs_gauge_le hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxbd
     hetac hab t⟩

end

/-! ### The comparison for the tangential rate of a frame -/

/-- **The comparison of the path functionals in the normal gauge, for the
tangential rate `−ξ/v` of a frame.**  All the hypotheses on the field of the
gauge flow are replaced by bounds on the frame data, through
`GaugeRate.gaugeRate_flow_hypotheses`, and the distortion constants become
explicit in those bounds: `C₁ = A₁/v₀ + A₀B₁/v₀²` is the Lipschitz constant of
the rate and `C₂ = A₂/v₀ + 2A₁B₁/v₀² + A₀(V₁B₂+2B₁²)/v₀³` bounds its second
space derivative. -/
theorem gauge_functionals_comparison_of_frame
    {xi xi1 xi2 v v1 v2 : ℝ → ℝ → ℝ} {A0 A1 A2 B1 B2 V1 v0 : ℝ}
    {eta eta1 eta2 : ℝ → ℝ} {Phi : ℝ → ℝ → ℝ} {ell : ℝ}
    (hxi : ∀ a x, HasDerivAt (xi a) (xi1 a x) x)
    (hxi1 : ∀ a x, HasDerivAt (xi1 a) (xi2 a x) x)
    (hv : ∀ a x, HasDerivAt (v a) (v1 a x) x)
    (hv1 : ∀ a x, HasDerivAt (v1 a) (v2 a x) x)
    (hvne : ∀ a x, v a x ≠ 0)
    (hxic : Continuous (Function.uncurry xi)) (hxi1c : Continuous (Function.uncurry xi1))
    (hxi2c : Continuous (Function.uncurry xi2)) (hvc : Continuous (Function.uncurry v))
    (hv1c : Continuous (Function.uncurry v1)) (hv2c : Continuous (Function.uncurry v2))
    (hv0 : 0 < v0) (hvlow : ∀ a x, v0 ≤ |v a x|) (hvup : ∀ a x, |v a x| ≤ V1)
    (hA0 : ∀ a x, |xi a x| ≤ A0) (hA1 : ∀ a x, |xi1 a x| ≤ A1)
    (hA2 : ∀ a x, |xi2 a x| ≤ A2)
    (hB1 : ∀ a x, |v1 a x| ≤ B1) (hB2 : ∀ a x, |v2 a x| ≤ B2)
    (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate xi v t (Phi t u)) t)
    (heta1 : ∀ x, HasDerivAt eta (eta1 x) x)
    (heta2 : ∀ x, HasDerivAt eta1 (eta2 x) x)
    (hetac : Continuous eta)
    (hbdd : BddAbove (Set.range fun x => |eta x|))
    (hbdd1 : BddAbove (Set.range fun x => |eta1 x|))
    (hbdd2 : BddAbove (Set.range fun x => |eta2 x|)) {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    supNorm (fun u => eta (Phi t u)) ≤ supNorm eta ∧
    supNorm (deriv fun u => eta (Phi t u))
        ≤ supNorm eta1 * (ell * Real.exp ((A1 / v0 + A0 * B1 / v0 ^ 2) * |t|)) ∧
    supNorm (deriv (deriv fun u => eta (Phi t u)))
        ≤ supNorm eta2 * (ell * Real.exp ((A1 / v0 + A0 * B1 / v0 ^ 2) * |t|)) ^ 2
          + supNorm eta1 * ((A2 / v0 + 2 * (A1 * B1) / v0 ^ 2
              + A0 * (V1 * B2 + 2 * B1 ^ 2) / v0 ^ 3) * ell ^ 2 * |t|
              * Real.exp (2 * (A1 / v0 + A0 * B1 / v0 ^ 2) * |t|)) ∧
    (∫ u in a..b, |eta (Phi t u)|)
        ≤ (1 / (ell * Real.exp (-((A1 / v0 + A0 * B1 / v0 ^ 2) * |t|))))
            * ∫ x in (Phi t a)..(Phi t b), |eta x| := by
  obtain ⟨hlip, hcont, hxd, hxcont, hxxd, hxxcont, hxxbd⟩ :=
    GaugeRate.gaugeRate_flow_hypotheses hxi hxi1 hv hv1 hvne hxic hxi1c hxi2c hvc hv1c hv2c
      hv0 hvlow hvup hA0 hA1 hA2 hB1 hB2
  have hC1 : (0:ℝ) ≤ A1 / v0 + A0 * B1 / v0 ^ 2 := by
    have := GaugeRate.abs_gaugeRate1_le (xi := xi) (xi1 := xi1) (v := v) (v1 := v1)
      hv0 hvlow hA0 hA1 hB1 0 0
    exact le_trans (abs_nonneg _) this
  have hkey := gauge_functionals_comparison (h := GaugeRate.gaugeRate xi v)
    (hx := GaugeRate.gaugeRate1 xi xi1 v v1) (hxx := GaugeRate.gaugeRate2 xi xi1 xi2 v v1 v2)
    (K := Real.toNNReal (A1 / v0 + A0 * B1 / v0 ^ 2)) (Phi := Phi) (ell := ell)
    hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxbd
    heta1 heta2 hetac hbdd hbdd1 hbdd2 hab t
  rwa [Real.coe_toNNReal _ hC1] at hkey

/-- The hypotheses above are satisfiable: the linear field `h(t,x) = x`, whose
flow started at `u` is `Φ(t,u) = ue^t`. -/
example : ∃ (h hx hxx Phi : ℝ → ℝ → ℝ) (K : NNReal) (ell K2 : ℝ),
    0 < ell ∧ (∀ t, LipschitzWith K (h t)) ∧ Continuous (Function.uncurry h) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t) ∧
      (∀ u, Phi 0 u = ell * u) ∧
      (∀ s x, HasDerivAt (h s) (hx s x) x) ∧ Continuous (Function.uncurry hx) ∧
      (∀ s x, HasDerivAt (hx s) (hxx s x) x) ∧ Continuous (Function.uncurry hxx) ∧
      (∀ s x, |hxx s x| ≤ K2) := by
  refine ⟨fun _ x => x, fun _ _ => 1, fun _ _ => 0, fun t u => u * Real.exp t, 1, 1, 0,
    one_pos, fun _ => LipschitzWith.id, continuous_snd, ?_, ?_, fun _ _ => hasDerivAt_id _,
    continuous_const, fun _ _ => hasDerivAt_const _ _, continuous_const, ?_⟩
  · exact fun u t => (Real.hasDerivAt_exp t).const_mul u
  · exact fun u => by simp
  · exact fun _ _ => by simp

end GaugeFunctionals
