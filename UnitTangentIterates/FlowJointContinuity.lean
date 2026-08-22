import Mathlib
import UnitTangentIterates.GaugeFlowTimeDerivative

/-!
# Joint continuity of a scalar flow and of its derivatives in the initial
condition

`FlowDerivative.lean` gives the flow `Φ` of a globally Lipschitz scalar field
`h` in closed form together with its first two derivatives in the initial
condition, `flowDeriv` and `flowDeriv2`; the derivatives are exhibited as
`HasDerivAt` statements in the parameter and as continuous functions of the
*time*.  What is missing — and what is needed to read a curve in the marking
`Φ_T` as a member of the space of marked curves, whose three components are
*continuous* — is the continuity of `flowDeriv2` in the parameter.

The route is joint continuity.  The flow is Lipschitz in the initial condition
with the constant `|ℓ|e^{K|t|}`, locally bounded in the time, and continuous in
the time, hence jointly continuous (`continuous_flow_prod`); therefore
`(u,s) ↦ ∫₀^s ∂ₓh(r, Φ(r,u)) dr` is jointly continuous by continuity of a
parametric primitive, and so is `flowDeriv` (`continuous_flowDeriv_prod`).  The
integrand of the closed form of `flowDeriv2` is then jointly continuous and its
integral is continuous in the parameter, whence
`continuous_flowDeriv2_initial`.

Main results: `continuous_flow_prod`, `continuous_flowDeriv_prod`,
`continuous_flowDeriv_initial`, `continuous_flowDeriv2_initial`.
-/

noncomputable section

open Set Filter Topology MeasureTheory Function

namespace FlowJointContinuity

open FlowDerivative GaugeFlowTimeDerivative

variable {h hx hxx : ℝ → ℝ → ℝ} {K : NNReal} {ell : ℝ} {Phi : ℝ → ℝ → ℝ}

section

variable (hlip : ∀ t, LipschitzWith K (h t))
  (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)

include hlip hPhid

/-- The flow is Lipschitz in its initial condition, with the explicit constant
`|ℓ|e^{K|t|}`. -/
theorem dist_flow_le (hPhi0 : ∀ u, Phi 0 u = ell * u) (t u u' : ℝ) :
    dist (Phi t u') (Phi t u) ≤ |ell| * Real.exp ((K : ℝ) * |t|) * dist u' u := by
  have h := GlobalODE.dist_le_of_global_solutions (K := K) (f := fun t x => h t x)
    hlip (hPhid u') (hPhid u) 0 t
  rw [hPhi0, hPhi0] at h
  have hd : dist (ell * u') (ell * u) = |ell| * dist u' u := by
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
  rw [hd, sub_zero] at h
  calc dist (Phi t u') (Phi t u) ≤ |ell| * dist u' u * Real.exp ((K : ℝ) * |t|) := h
    _ = |ell| * Real.exp ((K : ℝ) * |t|) * dist u' u := by ring

/-- **The flow is jointly continuous** in the time and in the initial
condition. -/
theorem continuous_flow_prod (hPhi0 : ∀ u, Phi 0 u = ell * u) :
    Continuous fun p : ℝ × ℝ => Phi p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  -- the Lipschitz constant is bounded near the time `p.1`
  set L : ℝ := |ell| * Real.exp ((K : ℝ) * (|p.1| + 1)) with hL
  have hLpos : 0 ≤ L := by positivity
  have hnear : ∀ s : ℝ, |s| ≤ |p.1| + 1 →
      ∀ u u' : ℝ, dist (Phi s u') (Phi s u) ≤ L * dist u' u := by
    intro s hs u u'
    refine (dist_flow_le hlip hPhid hPhi0 s u u').trans ?_
    refine mul_le_mul_of_nonneg_right ?_ dist_nonneg
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left hs K.coe_nonneg)) (abs_nonneg _)
  -- continuity in the time at the base point
  have htime : ContinuousAt (fun s => Phi s p.2) p.1 :=
    (continuous_flow_time hPhid p.2).continuousAt
  have h1 : ∀ᶠ s in 𝓝 p.1, dist (Phi s p.2) (Phi p.1 p.2) < ε / 2 :=
    Metric.tendsto_nhds.1 htime (ε / 2) (by linarith)
  have h2 : ∀ᶠ s in 𝓝 p.1, |s| ≤ |p.1| + 1 := by
    have : ∀ᶠ s in 𝓝 p.1, |s - p.1| < 1 := by
      have := Metric.ball_mem_nhds p.1 (by norm_num : (0:ℝ) < 1)
      filter_upwards [this] with s hs
      simpa [Real.dist_eq] using hs
    filter_upwards [this] with s hs
    have := abs_sub_abs_le_abs_sub s p.1
    linarith
  have h3 : ∀ᶠ u in 𝓝 p.2, L * dist u p.2 < ε / 2 := by
    rcases eq_or_lt_of_le hLpos with hL0 | hLpos'
    · have : ∀ u : ℝ, L * dist u p.2 = 0 := by
        intro u; rw [← hL0]; ring
      filter_upwards with u
      rw [this u]; linarith
    · have : ∀ᶠ u in 𝓝 p.2, dist u p.2 < ε / (2 * L) := by
        have := Metric.ball_mem_nhds p.2 (show (0:ℝ) < ε / (2 * L) by positivity)
        filter_upwards [this] with u hu
        simpa [Real.dist_eq, dist_comm] using hu
      filter_upwards [this] with u hu
      rw [mul_comm]
      calc dist u p.2 * L < (ε / (2 * L)) * L :=
            mul_lt_mul_of_pos_right hu hLpos'
        _ = ε / 2 := by field_simp
  have hprod : ∀ᶠ z : ℝ × ℝ in 𝓝 p,
      dist (Phi z.1 p.2) (Phi p.1 p.2) < ε / 2 ∧ |z.1| ≤ |p.1| + 1
        ∧ L * dist z.2 p.2 < ε / 2 := by
    have e1 : ∀ᶠ z : ℝ × ℝ in 𝓝 p, dist (Phi z.1 p.2) (Phi p.1 p.2) < ε / 2 :=
      (continuous_fst.tendsto p) h1
    have e2 : ∀ᶠ z : ℝ × ℝ in 𝓝 p, |z.1| ≤ |p.1| + 1 := (continuous_fst.tendsto p) h2
    have e3 : ∀ᶠ z : ℝ × ℝ in 𝓝 p, L * dist z.2 p.2 < ε / 2 :=
      (continuous_snd.tendsto p) h3
    filter_upwards [e1, e2, e3] with z hz1 hz2 hz3 using ⟨hz1, hz2, hz3⟩
  filter_upwards [hprod] with z hz
  calc dist (Phi z.1 z.2) (Phi p.1 p.2)
      ≤ dist (Phi z.1 z.2) (Phi z.1 p.2) + dist (Phi z.1 p.2) (Phi p.1 p.2) :=
        dist_triangle _ _ _
    _ ≤ L * dist z.2 p.2 + dist (Phi z.1 p.2) (Phi p.1 p.2) := by
        have := hnear z.1 hz.2.1 p.2 z.2
        linarith
    _ < ε / 2 + ε / 2 := by linarith [hz.1, hz.2.2]
    _ = ε := by ring

/-- **The first flow derivative is jointly continuous.** -/
theorem continuous_flowDeriv_prod (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxcont : Continuous (uncurry hx)) :
    Continuous fun p : ℝ × ℝ => flowDeriv hx Phi ell p.1 p.2 := by
  have hflow : Continuous fun p : ℝ × ℝ => Phi p.1 p.2 :=
    continuous_flow_prod hlip hPhid hPhi0
  -- the integrand, as a function of the pair and of the integration variable
  have hint : Continuous
      (uncurry fun z : ℝ × ℝ => fun r : ℝ => hx r (Phi r z.2)) := by
    have : Continuous fun w : (ℝ × ℝ) × ℝ => hx w.2 (Phi w.2 w.1.2) := by
      refine hxcont.comp (continuous_snd.prodMk ?_)
      exact hflow.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
    simpa [uncurry] using this
  have hprim : Continuous fun z : ℝ × ℝ => ∫ r in (0 : ℝ)..z.1, hx r (Phi r z.2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := (0 : ℝ)) hint continuous_fst
  simpa [flowDeriv] using (hprim.rexp).const_smul ell

/-- The first flow derivative is continuous in the initial condition. -/
theorem continuous_flowDeriv_initial (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxcont : Continuous (uncurry hx)) (t : ℝ) :
    Continuous fun u => flowDeriv hx Phi ell t u :=
  (continuous_flowDeriv_prod hlip hPhid hPhi0 hxcont).comp
    (continuous_const.prodMk continuous_id)

/-- **The second flow derivative is continuous in the initial condition.** -/
theorem continuous_flowDeriv2_initial (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxcont : Continuous (uncurry hx)) (hxxcont : Continuous (uncurry hxx)) (t : ℝ) :
    Continuous fun u => flowDeriv2 hx hxx Phi ell t u := by
  have hflow : Continuous fun p : ℝ × ℝ => Phi p.1 p.2 :=
    continuous_flow_prod hlip hPhid hPhi0
  have hFD : Continuous fun p : ℝ × ℝ => flowDeriv hx Phi ell p.1 p.2 :=
    continuous_flowDeriv_prod hlip hPhid hPhi0 hxcont
  have hint : Continuous
      (uncurry fun u : ℝ => fun s : ℝ => hxx s (Phi s u) * flowDeriv hx Phi ell s u) := by
    have h1 : Continuous fun w : ℝ × ℝ => hxx w.2 (Phi w.2 w.1) :=
      hxxcont.comp (continuous_snd.prodMk
        (hflow.comp (continuous_snd.prodMk continuous_fst)))
    have h2 : Continuous fun w : ℝ × ℝ => flowDeriv hx Phi ell w.2 w.1 :=
      hFD.comp (continuous_snd.prodMk continuous_fst)
    simpa [uncurry] using h1.mul h2
  have hJ : Continuous fun u : ℝ =>
      ∫ s in (0 : ℝ)..t, hxx s (Phi s u) * flowDeriv hx Phi ell s u :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hint 0 t
  exact (continuous_flowDeriv_initial hlip hPhid hPhi0 hxcont t).mul hJ

end

end FlowJointContinuity
