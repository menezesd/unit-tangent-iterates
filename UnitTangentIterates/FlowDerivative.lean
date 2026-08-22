import Mathlib
import UnitTangentIterates.NormalGaugeFamily

/-!
# Differentiability of a scalar flow in its initial condition

The normal-gauge reparametrization of `NormalGaugeFamily.lean` is the flow of a
scalar field `h(t, x)`, started at `ℓ·u`.  To compare the path functionals in
the flowed parameter with those in arclength
(`PathFunctionalsReparam.lean`) one needs the derivative of the flow in the
parameter `u`, and bounds for it.

For a *scalar* equation the variational equation can be solved explicitly, and
the difference quotient can be computed in closed form before passing to the
limit: if `Φ(·, u)` and `Φ(·, u')` are two solutions, their difference `g`
satisfies the linear equation `g' = a g` with

`a(r) = (h(r, Φ(r,u')) − h(r, Φ(r,u))) / (Φ(r,u') − Φ(r,u))`,

a quotient which makes sense because the two solutions never meet, and which is
bounded by the Lipschitz constant of `h`.  Hence

`Φ(t,u') − Φ(t,u) = ℓ(u' − u) · exp ∫₀^t a`,

and letting `u' → u` — the integrand converges to `∂ₓh(s, Φ(s,u))` and is
dominated by `K` — gives the derivative in closed form.

Main results:

* `flow_difference_eq` — the closed form of the difference of two solutions;
* `hasDerivAt_flow_initial` — the flow is differentiable in its initial
  condition, with derivative `ℓ exp ∫₀^t ∂ₓh(s, Φ(s,u)) ds`;
* `flow_deriv_bounds` — the two-sided bound `ℓe^{−K|t|} ≤ ∂_uΦ ≤ ℓe^{K|t|}`;
* `hasDerivAt_flowDeriv` — the second derivative in the initial condition,
  obtained by differentiating the closed form under the integral sign;
* `abs_flowDeriv_deriv_le` — the bound `|∂²_uΦ| ≤ K₂ℓ²|t|e^{2K|t|}` for it.
-/

noncomputable section

open Set Filter Topology MeasureTheory intervalIntegral

namespace FlowDerivative

variable {h hx hxx : ℝ → ℝ → ℝ} {K : NNReal} {ell : ℝ} {Phi : ℝ → ℝ → ℝ}

/-- The logarithmic rate relating two solutions. -/
def rate (h : ℝ → ℝ → ℝ) (Phi : ℝ → ℝ → ℝ) (u u' : ℝ) (r : ℝ) : ℝ :=
  (h r (Phi r u') - h r (Phi r u)) / (Phi r u' - Phi r u)

section

variable (hlip : ∀ t, LipschitzWith K (h t))
  (hcont : Continuous (Function.uncurry h))
  (hPhi0 : ∀ u, Phi 0 u = ell * u)
  (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)

include hlip hPhid in
/-- Two solutions never meet: the lower Grönwall bound. -/
theorem flow_ne (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u) {u u' : ℝ}
    (huu : u ≠ u') (r : ℝ) : Phi r u' - Phi r u ≠ 0 := by
  intro hzero
  have h := NormalGaugeFamily.dist_ge_of_global_solutions (K := K)
    (f := fun t x => h t x) hlip (hPhid u') (hPhid u) 0 r
  rw [Real.dist_eq, Real.dist_eq, hPhi0, hPhi0] at h
  rw [show Phi r u' - Phi r u = 0 from hzero] at h
  simp only [abs_zero] at h
  have hne : ell * u' - ell * u ≠ 0 := by
    have : u' - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huu)
    rw [← mul_sub]
    exact mul_ne_zero (ne_of_gt hell) this
  have hpos : 0 < |ell * u' - ell * u| * Real.exp (-((K : ℝ) * |r - 0|)) :=
    mul_pos (abs_pos.mpr hne) (Real.exp_pos _)
  linarith

include hlip in
/-- The rate is bounded by the Lipschitz constant of the field. -/
theorem abs_rate_le {u u' : ℝ} (hne : ∀ r : ℝ, Phi r u' - Phi r u ≠ 0) (r : ℝ) :
    |rate h Phi u u' r| ≤ (K : ℝ) := by
  have hL : |h r (Phi r u') - h r (Phi r u)| ≤ (K : ℝ) * |Phi r u' - Phi r u| := by
    have := (hlip r).dist_le_mul (Phi r u') (Phi r u)
    rwa [Real.dist_eq, Real.dist_eq] at this
  rw [rate, abs_div]
  rw [div_le_iff₀ (abs_pos.mpr (hne r))]
  exact hL

include hcont hPhid in
/-- The rate is continuous in the time. -/
theorem continuous_rate {u u' : ℝ} (hne : ∀ r : ℝ, Phi r u' - Phi r u ≠ 0) :
    Continuous (rate h Phi u u') := by
  have hc1 : Continuous fun r => Phi r u := by
    have : Differentiable ℝ fun r => Phi r u := fun r => (hPhid u r).differentiableAt
    exact this.continuous
  have hc2 : Continuous fun r => Phi r u' := by
    have : Differentiable ℝ fun r => Phi r u' := fun r => (hPhid u' r).differentiableAt
    exact this.continuous
  have hnum : Continuous fun r => h r (Phi r u') - h r (Phi r u) :=
    (hcont.comp (continuous_id.prodMk hc2)).sub (hcont.comp (continuous_id.prodMk hc1))
  exact hnum.div (hc2.sub hc1) hne

include hlip hcont hPhid in
/-- **The closed form of the difference of two solutions.** -/
theorem flow_difference_eq (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    {u u' : ℝ} (huu : u ≠ u') (t : ℝ) :
    Phi t u' - Phi t u
      = ell * (u' - u) * Real.exp (∫ s in (0:ℝ)..t, rate h Phi u u' s) := by
  have hne : ∀ r : ℝ, Phi r u' - Phi r u ≠ 0 := flow_ne hlip hPhid hell hPhi0 huu
  set a := rate h Phi u u' with ha
  have hac : Continuous a := continuous_rate hcont hPhid hne
  -- the primitive of the rate
  set A : ℝ → ℝ := fun r => ∫ s in (0:ℝ)..r, a s with hA
  have hAd : ∀ r, HasDerivAt A (a r) r := by
    intro r
    exact intervalIntegral.integral_hasDerivAt_right
      (hac.intervalIntegrable 0 r) (hac.stronglyMeasurableAtFilter _ _)
      hac.continuousAt
  -- the difference of the two solutions
  set g : ℝ → ℝ := fun r => Phi r u' - Phi r u with hg
  have hgd : ∀ r, HasDerivAt g (a r * g r) r := by
    intro r
    have h1 := (hPhid u' r).sub (hPhid u r)
    refine h1.congr_deriv ?_
    simp only [ha, rate, hg]
    rw [div_mul_cancel₀ _ (hne r)]
  -- `g e^{-A}` is constant
  have hconst : ∀ r, g r * Real.exp (-A r) = g 0 * Real.exp (-A 0) := by
    have hzero : ∀ r, HasDerivAt (fun r' => g r' * Real.exp (-A r')) 0 r := by
      intro r
      have hE : HasDerivAt (fun r' => Real.exp (-A r')) (-(a r) * Real.exp (-A r)) r := by
        have := ((hAd r).neg).exp
        simpa [mul_comm] using this
      have := (hgd r).mul hE
      refine this.congr_deriv ?_
      ring
    intro r
    have hdiff : Differentiable ℝ fun r' => g r' * Real.exp (-A r') :=
      fun r' => (hzero r').differentiableAt
    exact is_const_of_deriv_eq_zero hdiff (fun r' => (hzero r').deriv) r 0
  have hA0 : A 0 = 0 := by simp [hA]
  have hg0 : g 0 = ell * (u' - u) := by
    show Phi 0 u' - Phi 0 u = ell * (u' - u)
    rw [hPhi0, hPhi0]; ring
  have := hconst t
  rw [hA0, hg0] at this
  simp only [neg_zero, Real.exp_zero, mul_one] at this
  have hEpos : Real.exp (-A t) ≠ 0 := (Real.exp_pos _).ne'
  field_simp at this ⊢
  rw [hg] at this
  calc Phi t u' - Phi t u = (Phi t u' - Phi t u) * Real.exp (-A t) * Real.exp (A t) := by
        rw [mul_assoc, ← Real.exp_add]; simp
    _ = ell * (u' - u) * Real.exp (A t) := by rw [this]

include hlip hPhid in
/-- The flow is Lipschitz in its initial condition, uniformly on compact time
intervals. -/
theorem continuous_flow_initial (hPhi0 : ∀ u, Phi 0 u = ell * u) (t : ℝ) :
    Continuous fun u => Phi t u := by
  have hL : ∀ u u' : ℝ, dist (Phi t u') (Phi t u)
      ≤ (|ell| * Real.exp ((K : ℝ) * |t|)) * dist u' u := by
    intro u u'
    have h := GlobalODE.dist_le_of_global_solutions (K := K) (f := fun t x => h t x)
      hlip (hPhid u') (hPhid u) 0 t
    rw [hPhi0, hPhi0] at h
    have hd : dist (ell * u') (ell * u) = |ell| * dist u' u := by
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
    rw [hd, sub_zero] at h
    calc dist (Phi t u') (Phi t u)
        ≤ |ell| * dist u' u * Real.exp ((K : ℝ) * |t|) := h
      _ = (|ell| * Real.exp ((K : ℝ) * |t|)) * dist u' u := by ring
  have hnn : (0:ℝ) ≤ |ell| * Real.exp ((K : ℝ) * |t|) :=
    mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (|ell| * Real.exp ((K : ℝ) * |t|)))
    ?_).continuous
  intro u' u
  rw [Real.coe_toNNReal _ hnn]
  exact hL u u'

include hlip hcont hPhid in
/-- **The flow is differentiable in its initial condition**, with the derivative
given in closed form by the variational equation. -/
theorem hasDerivAt_flow_initial (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x) (u t : ℝ) :
    HasDerivAt (fun u' => Phi t u')
      (ell * Real.exp (∫ s in (0:ℝ)..t, hx s (Phi s u))) u := by
  have hcu : ∀ s : ℝ, Continuous fun u' => Phi s u' :=
    fun s => continuous_flow_initial hlip hPhid hPhi0 s
  rw [hasDerivAt_iff_tendsto_slope]
  -- the slope, computed in closed form
  have hslope : ∀ᶠ u' in 𝓝[≠] u, slope (fun u' => Phi t u') u u'
      = ell * Real.exp (∫ s in (0:ℝ)..t, rate h Phi u u' s) := by
    filter_upwards [self_mem_nhdsWithin] with u' hu'
    have hne : u ≠ u' := fun hc => hu' hc.symm
    rw [slope_def_field, div_eq_iff (sub_ne_zero.mpr (fun hc => hu' hc))]
    rw [flow_difference_eq hlip hcont hPhid hell hPhi0 hne t]
    ring
  refine Tendsto.congr' (hslope.mono fun x hx => hx.symm) ?_
  -- it suffices to pass to the limit inside the integral
  have hkey : Tendsto (fun u' => ∫ s in (0:ℝ)..t, rate h Phi u u' s) (𝓝[≠] u)
      (𝓝 (∫ s in (0:ℝ)..t, hx s (Phi s u))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (K : ℝ)) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with u' hu'
      have hne : u ≠ u' := fun hc => hu' hc.symm
      exact ((continuous_rate hcont hPhid
        (flow_ne hlip hPhid hell hPhi0 hne)).aestronglyMeasurable).restrict
    · filter_upwards [self_mem_nhdsWithin] with u' hu'
      have hne : u ≠ u' := fun hc => hu' hc.symm
      filter_upwards with s _
      exact abs_rate_le hlip (flow_ne hlip hPhid hell hPhi0 hne) s
    · exact _root_.intervalIntegrable_const
    · filter_upwards with s _
      -- the rate is the slope of `h s` between the two solutions
      have hcomp : Tendsto (fun u' => Phi s u') (𝓝[≠] u) (𝓝[≠] (Phi s u)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (((hcu s).tendsto u).mono_left nhdsWithin_le_nhds) ?_
        filter_upwards [self_mem_nhdsWithin] with u' hu'
        have hne : u ≠ u' := fun hc => hu' hc.symm
        have := flow_ne hlip hPhid hell hPhi0 hne s
        simpa [sub_eq_zero] using this
      have hsl : Tendsto (slope (h s) (Phi s u)) (𝓝[≠] (Phi s u)) (𝓝 (hx s (Phi s u))) :=
        hasDerivAt_iff_tendsto_slope.mp (hxd s (Phi s u))
      have := hsl.comp hcomp
      refine this.congr fun u' => ?_
      simp [Function.comp, rate, slope_def_field]
  have := (Real.continuous_exp.continuousAt.tendsto.comp hkey)
  exact (this.const_mul ell)

include hlip hPhid in
/-- **The gauge flow commutes with a period translation.**  If the field is
`Pc`-periodic in the space variable then the flow started at `ℓ(u + Pc/ℓ)` is
the flow started at `ℓu`, translated by `Pc`; so the reparametrization descends
to the circle. -/
theorem flow_periodic_translate (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    {Pc : ℝ} (hper : ∀ t x, h t (x + Pc) = h t x) (t u : ℝ) :
    Phi t (u + Pc / ell) = Phi t u + Pc := by
  have h2 : ∀ r, HasDerivAt (fun r' => Phi r' u + Pc) (h r (Phi r u + Pc)) r := by
    intro r
    have := (hPhid u r).add_const Pc
    rwa [hper r (Phi r u)]
  have hdist := GlobalODE.dist_le_of_global_solutions (K := K) (f := fun t x => h t x)
    hlip (hPhid (u + Pc / ell)) h2 0 t
  have hzero : dist (Phi 0 (u + Pc / ell)) (Phi 0 u + Pc) = 0 := by
    rw [hPhi0, hPhi0, Real.dist_eq]
    rw [show ell * (u + Pc / ell) = ell * u + Pc by field_simp]
    simp
  rw [hzero, zero_mul] at hdist
  have := le_antisymm hdist dist_nonneg
  exact dist_eq_zero.mp this

include hlip in
/-- A globally Lipschitz field has a derivative bounded by the Lipschitz
constant. -/
theorem abs_hx_le (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x) (s x : ℝ) :
    |hx s x| ≤ (K : ℝ) := by
  have h1 := (hxd s x).le_of_lip' K.coe_nonneg (Filter.Eventually.of_forall (fun y => by
    have h2 := (hlip s).dist_le_mul y x
    rw [Real.dist_eq, Real.dist_eq] at h2
    simpa [Real.norm_eq_abs] using h2))
  simpa [Real.norm_eq_abs] using h1

/-- The closed form of the derivative of the flow in its initial condition. -/
def flowDeriv (hx : ℝ → ℝ → ℝ) (Phi : ℝ → ℝ → ℝ) (ell : ℝ) (t u : ℝ) : ℝ :=
  ell * Real.exp (∫ s in (0:ℝ)..t, hx s (Phi s u))

/-- The derivative of the flow in its initial condition is positive. -/
theorem flowDeriv_pos (hell : 0 < ell) (t u : ℝ) : 0 < flowDeriv hx Phi ell t u :=
  mul_pos hell (Real.exp_pos _)

/-- **Two-sided bounds for the derivative of the flow in its initial
condition**, in closed form. -/
theorem flowDeriv_bounds (hell : 0 < ell) (hbd : ∀ s x, |hx s x| ≤ (K : ℝ)) (t u : ℝ) :
    ell * Real.exp (-((K : ℝ) * |t|)) ≤ flowDeriv hx Phi ell t u ∧
      flowDeriv hx Phi ell t u ≤ ell * Real.exp ((K : ℝ) * |t|) := by
  have hint : |∫ s in (0:ℝ)..t, hx s (Phi s u)| ≤ (K : ℝ) * |t| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := t) (C := (K : ℝ)) (f := fun s => hx s (Phi s u))
      (fun s _ => by simpa [Real.norm_eq_abs] using hbd s (Phi s u))
    simpa [Real.norm_eq_abs] using this
  rw [abs_le] at hint
  exact ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hint.1) hell.le,
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hint.2) hell.le⟩

include hlip hcont hPhid in
/-- **Two-sided bounds for the derivative of the flow in its initial
condition.** -/
theorem flow_deriv_bounds (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x) (u t : ℝ) :
    ell * Real.exp (-((K : ℝ) * |t|)) ≤ deriv (fun u' => Phi t u') u ∧
      deriv (fun u' => Phi t u') u ≤ ell * Real.exp ((K : ℝ) * |t|) := by
  have hderiv : deriv (fun u' => Phi t u') u = flowDeriv hx Phi ell t u :=
    (hasDerivAt_flow_initial hlip hcont hPhid hell hPhi0 hxd u t).deriv
  rw [hderiv]
  exact flowDeriv_bounds hell (abs_hx_le hlip hxd) t u

include hlip hcont hPhid in
/-- The derivative of the flow in its initial condition is periodic in the
initial condition, with period `Pc/ℓ`, when the field is `Pc`-periodic. -/
theorem flowDeriv_periodic (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x)
    {Pc : ℝ} (hper : ∀ t x, h t (x + Pc) = h t x) (t u : ℝ) :
    flowDeriv hx Phi ell t (u + Pc / ell) = flowDeriv hx Phi ell t u := by
  have h1 : HasDerivAt (fun u' => Phi t u')
      (flowDeriv hx Phi ell t (u + Pc / ell)) (u + Pc / ell) :=
    hasDerivAt_flow_initial hlip hcont hPhid hell hPhi0 hxd (u + Pc / ell) t
  have hshift : HasDerivAt (fun u' : ℝ => u' + Pc / ell) 1 u :=
    (hasDerivAt_id u).add_const _
  have h2 : HasDerivAt (fun u' => Phi t (u' + Pc / ell))
      (flowDeriv hx Phi ell t (u + Pc / ell)) u := by
    simpa using h1.comp u hshift
  have h3 : HasDerivAt (fun u' => Phi t u' + Pc) (flowDeriv hx Phi ell t u) u :=
    (hasDerivAt_flow_initial hlip hcont hPhid hell hPhi0 hxd u t).add_const Pc
  have hfun : (fun u' => Phi t (u' + Pc / ell)) = fun u' => Phi t u' + Pc := by
    funext u'
    exact flow_periodic_translate hlip hPhid hell hPhi0 hper t u'
  rw [hfun] at h2
  exact h2.unique h3

/-! ### The second derivative in the initial condition -/

include hPhid in
/-- The primitive appearing in the closed form is continuous in the time, hence
so is the derivative of the flow. -/
theorem continuous_flowDeriv_time (hxcont : Continuous (Function.uncurry hx)) (u : ℝ) :
    Continuous fun s => flowDeriv hx Phi ell s u := by
  have hc1 : Continuous fun s => Phi s u := by
    have : Differentiable ℝ fun s => Phi s u := fun s => (hPhid u s).differentiableAt
    exact this.continuous
  have hg : Continuous fun s => hx s (Phi s u) := hxcont.comp (continuous_id.prodMk hc1)
  have hA : Continuous fun r => ∫ s in (0:ℝ)..r, hx s (Phi s u) := by
    have hd : ∀ r : ℝ, HasDerivAt (fun r' => ∫ s in (0:ℝ)..r', hx s (Phi s u))
        (hx r (Phi r u)) r := fun r =>
      intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 r)
        (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
    have : Differentiable ℝ fun r => ∫ s in (0:ℝ)..r, hx s (Phi s u) :=
      fun r => (hd r).differentiableAt
    exact this.continuous
  exact (Real.continuous_exp.comp hA).const_smul ell

include hlip hcont hPhid in
/-- **Differentiation under the integral sign** for the logarithmic derivative
of the flow. -/
theorem hasDerivAt_flowLog (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x)
    (hxcont : Continuous (Function.uncurry hx))
    (hxxd : ∀ s x, HasDerivAt (hx s) (hxx s x) x)
    (hxxcont : Continuous (Function.uncurry hxx))
    {K2 : ℝ} (hxxbd : ∀ s x, |hxx s x| ≤ K2) (u t : ℝ) :
    HasDerivAt (fun u' => ∫ s in (0:ℝ)..t, hx s (Phi s u'))
      (∫ s in (0:ℝ)..t, hxx s (Phi s u) * flowDeriv hx Phi ell s u) u := by
  have hbd := abs_hx_le hlip hxd
  -- continuity of the integrands
  have hcPhi : ∀ x : ℝ, Continuous fun s => Phi s x := by
    intro x
    have : Differentiable ℝ fun s => Phi s x := fun s => (hPhid x s).differentiableAt
    exact this.continuous
  have hF : ∀ x : ℝ, Continuous fun s => hx s (Phi s x) := fun x =>
    hxcont.comp (continuous_id.prodMk (hcPhi x))
  have hF' : ∀ x : ℝ, Continuous fun s => hxx s (Phi s x) * flowDeriv hx Phi ell s x := fun x =>
    (hxxcont.comp (continuous_id.prodMk (hcPhi x))).mul
      (continuous_flowDeriv_time hPhid hxcont x)
  have hbound : Continuous fun s : ℝ => K2 * (ell * Real.exp ((K : ℝ) * |s|)) :=
    (continuous_const.mul ((Real.continuous_exp.comp
      (continuous_const.mul continuous_abs)).const_smul ell))
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := (0:ℝ)) (b := t) (μ := volume)
    (F := fun x s => hx s (Phi s x))
    (F' := fun x s => hxx s (Phi s x) * flowDeriv hx Phi ell s x)
    (x₀ := u) (s := Set.univ) (bound := fun s => K2 * (ell * Real.exp ((K : ℝ) * |s|)))
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x => ((hF x).aestronglyMeasurable).restrict)
    ((hF u).intervalIntegrable 0 t)
    (((hF' u).aestronglyMeasurable).restrict)
    (Filter.Eventually.of_forall fun s _ x _ => by
      have h1 : |hxx s (Phi s x)| ≤ K2 := hxxbd s (Phi s x)
      have h2 : |flowDeriv hx Phi ell s x| ≤ ell * Real.exp ((K : ℝ) * |s|) := by
        rw [abs_of_pos (flowDeriv_pos hell s x)]
        exact (flowDeriv_bounds hell hbd s x).2
      calc ‖hxx s (Phi s x) * flowDeriv hx Phi ell s x‖
          = |hxx s (Phi s x)| * |flowDeriv hx Phi ell s x| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ K2 * (ell * Real.exp ((K : ℝ) * |s|)) := by
            refine mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
      )
    (hbound.intervalIntegrable 0 t)
    (Filter.Eventually.of_forall fun s _ x _ => by
      have hflow := hasDerivAt_flow_initial hlip hcont hPhid hell hPhi0 hxd x s
      exact (hxxd s (Phi s x)).comp x hflow)
  exact hmain.2

include hlip hcont hPhid in
/-- **The second derivative of the flow in its initial condition.** -/
theorem hasDerivAt_flowDeriv (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x)
    (hxcont : Continuous (Function.uncurry hx))
    (hxxd : ∀ s x, HasDerivAt (hx s) (hxx s x) x)
    (hxxcont : Continuous (Function.uncurry hxx))
    {K2 : ℝ} (hxxbd : ∀ s x, |hxx s x| ≤ K2) (u t : ℝ) :
    HasDerivAt (fun u' => flowDeriv hx Phi ell t u')
      (flowDeriv hx Phi ell t u
        * ∫ s in (0:ℝ)..t, hxx s (Phi s u) * flowDeriv hx Phi ell s u) u := by
  have hlog := hasDerivAt_flowLog hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxbd u t
  have := (hlog.exp).const_mul ell
  refine this.congr_deriv ?_
  simp only [flowDeriv]
  ring

/-- **A bound for the second derivative of the flow in its initial
condition.** -/
theorem abs_flowDeriv_deriv_le (hell : 0 < ell) (hbd : ∀ s x, |hx s x| ≤ (K : ℝ))
    {K2 : ℝ} (hxxbd : ∀ s x, |hxx s x| ≤ K2) (u t : ℝ) :
    |flowDeriv hx Phi ell t u
        * ∫ s in (0:ℝ)..t, hxx s (Phi s u) * flowDeriv hx Phi ell s u|
      ≤ K2 * ell ^ 2 * |t| * Real.exp (2 * (K : ℝ) * |t|) := by
  have hK2 : 0 ≤ K2 := le_trans (abs_nonneg _) (hxxbd 0 0)
  have h1 : |flowDeriv hx Phi ell t u| ≤ ell * Real.exp ((K : ℝ) * |t|) := by
    rw [abs_of_pos (flowDeriv_pos hell t u)]
    exact (flowDeriv_bounds hell hbd t u).2
  have h2 : |∫ s in (0:ℝ)..t, hxx s (Phi s u) * flowDeriv hx Phi ell s u|
      ≤ (K2 * (ell * Real.exp ((K : ℝ) * |t|))) * |t| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := t) (C := K2 * (ell * Real.exp ((K : ℝ) * |t|)))
      (f := fun s => hxx s (Phi s u) * flowDeriv hx Phi ell s u)
      (fun s hs => by
        have hs' : |s| ≤ |t| := by
          rcases le_total (0:ℝ) t with ht | ht
          · rw [Set.uIoc_of_le ht] at hs
            rw [abs_of_nonneg hs.1.le, abs_of_nonneg ht]
            exact hs.2
          · rw [Set.uIoc_of_ge ht] at hs
            rw [abs_of_nonpos hs.2, abs_of_nonpos ht]
            linarith [hs.1]
        have hb : |flowDeriv hx Phi ell s u| ≤ ell * Real.exp ((K : ℝ) * |t|) := by
          rw [abs_of_pos (flowDeriv_pos hell s u)]
          refine le_trans (flowDeriv_bounds hell hbd s u).2 ?_
          have : (K : ℝ) * |s| ≤ (K : ℝ) * |t| :=
            mul_le_mul_of_nonneg_left hs' K.coe_nonneg
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr this) hell.le
        calc ‖hxx s (Phi s u) * flowDeriv hx Phi ell s u‖
            = |hxx s (Phi s u)| * |flowDeriv hx Phi ell s u| := by
              rw [Real.norm_eq_abs, abs_mul]
          _ ≤ K2 * (ell * Real.exp ((K : ℝ) * |t|)) :=
              mul_le_mul (hxxbd s (Phi s u)) hb (abs_nonneg _) hK2)
    simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg t)] using this
  have hnn1 : (0:ℝ) ≤ ell * Real.exp ((K : ℝ) * |t|) :=
    mul_nonneg hell.le (Real.exp_pos _).le
  calc |flowDeriv hx Phi ell t u
        * ∫ s in (0:ℝ)..t, hxx s (Phi s u) * flowDeriv hx Phi ell s u|
      = |flowDeriv hx Phi ell t u|
          * |∫ s in (0:ℝ)..t, hxx s (Phi s u) * flowDeriv hx Phi ell s u| := abs_mul _ _
    _ ≤ (ell * Real.exp ((K : ℝ) * |t|)) * ((K2 * (ell * Real.exp ((K : ℝ) * |t|))) * |t|) :=
        mul_le_mul h1 h2 (abs_nonneg _) hnn1
    _ = K2 * ell ^ 2 * |t| * Real.exp (2 * (K : ℝ) * |t|) := by
        rw [show (2:ℝ) * (K : ℝ) * |t| = (K : ℝ) * |t| + (K : ℝ) * |t| by ring,
          Real.exp_add]
        ring

end

end FlowDerivative
