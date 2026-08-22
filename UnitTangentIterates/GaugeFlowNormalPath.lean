import Mathlib
import UnitTangentIterates.PathMetric

/-!
# The normal path of a family of curves read in a gauge marking

`FrontNormalPath.exists_normalPath_of_front_normal_gauge` produces the normal
path of a family of fronts, but it *assumes* that the family read in the
normalized parameter already moves normally.  For the family of selected rears
that is not automatic: the rears move with a tangential component as well, and
the marking of the assembly is precisely the flow that removes it.

This file produces the normal path in that situation.  If the slices `Y t` are
parametrized by their own arclength, with tangent angle `α`, and move with the
velocity

```
  ∂_t Y = ξ · e^{iα} + η · i e^{iα}
```

(a tangential and a normal component), and if the marking `Φ` is the flow of the
field `−ξ`,

```
  ∂_t Φ(t,u) = −ξ(t, Φ(t,u)) ,
```

then the family read in the marking, `X(t,u) = Y(t, Φ(t,u))`, moves *normally*:

```
  ∂_t X = η(t,Φ) · i e^{iα(t,Φ)} ,
```

the tangential component being exactly cancelled by the motion of the marking.
Hence it is a normal path of the path metric, for any cost density dominating
the normal velocity and the sup norms of its first two derivatives.

Main results:

* `hasDerivAt_along_flow_complex` — the chain rule along a flow line for a
  jointly `C¹` complex-valued function of two variables;
* `hasDerivAt_gauge_normal` — the motion of the family read in the marking is
  purely normal;
* `exists_normalPath_of_gauge_marking` — the resulting normal path, between two
  prescribed marked data.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeFlowNormalPath

variable {Y Yt Ys : ℝ → ℝ → ℂ} {Phi R : ℝ → ℝ → ℝ}

/-- The total derivative of a jointly `C¹` complex-valued function of two real
variables, evaluated on the two coordinate directions, is the pair of its
partial derivatives. -/
private theorem fderiv_apply_eq (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s) (Yt t s) t)
    (hYs : ∀ t s, HasDerivAt (Y t) (Ys t s) s) (t x : ℝ) :
    fderiv ℝ (uncurry Y) (t, x) (1, 0) = Yt t x ∧
      fderiv ℝ (uncurry Y) (t, x) (0, 1) = Ys t x := by
  have hF : HasFDerivAt (uncurry Y) (fderiv ℝ (uncurry Y) (t, x)) (t, x) :=
    (hYC1.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  constructor
  · have hcurve : HasDerivAt (fun r : ℝ => (r, x)) ((1 : ℝ), (0 : ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    have h := hF.comp_hasDerivAt t hcurve
    exact (h.unique (hYt t x)).symm ▸ rfl
  · have hcurve : HasDerivAt (fun y : ℝ => (t, y)) ((0 : ℝ), (1 : ℝ)) x :=
      (hasDerivAt_const x t).prodMk (hasDerivAt_id x)
    have h := hF.comp_hasDerivAt x hcurve
    exact (h.unique (hYs t x)).symm ▸ rfl

/-- **The chain rule along a flow line, for a complex-valued function.**  The
counterpart of `GaugeReparamFrameTime.hasDerivAt_along_flow` for the moving
curve itself: `d/dt Y(t, Φ(t,u)) = ∂_t Y + ∂_s Y · R`. -/
theorem hasDerivAt_along_flow_complex (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s) (Yt t s) t)
    (hYs : ∀ t s, HasDerivAt (Y t) (Ys t s) s)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t) (u t : ℝ) :
    HasDerivAt (fun r => Y r (Phi r u))
      (Yt t (Phi t u) + (R t (Phi t u) : ℂ) * Ys t (Phi t u)) t := by
  set x := Phi t u with hx
  have hF : HasFDerivAt (uncurry Y) (fderiv ℝ (uncurry Y) (t, x)) (t, x) :=
    (hYC1.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hcurve : HasDerivAt (fun r : ℝ => (r, Phi r u)) ((1 : ℝ), R t x) t :=
    (hasDerivAt_id t).prodMk (hPhid u t)
  have h := hF.comp_hasDerivAt t hcurve
  refine h.congr_deriv ?_
  obtain ⟨h1, h2⟩ := fderiv_apply_eq hYC1 hYt hYs t x
  have hsplit : ((1 : ℝ), R t x) = ((1 : ℝ), (0 : ℝ)) + R t x • ((0 : ℝ), (1 : ℝ)) := by
    simp
  rw [hsplit, map_add, map_smul, h1, h2, Complex.real_smul]

variable {alpha xi en : ℝ → ℝ → ℝ}

/-- **The family read in the gauge marking moves normally.**  If the slices are
parametrized by their own arclength and move with tangential rate `ξ` and normal
rate `η`, and the marking is the flow of `−ξ`, then the tangential component of
the motion is cancelled and `∂_t X = η · i e^{iα}`. -/
theorem hasDerivAt_gauge_normal (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hYs : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      ((xi t s : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (-xi t (Phi t u)) t) (u t : ℝ) :
    HasDerivAt (fun r => Y r (Phi r u))
      ((en t (Phi t u) : ℂ)
        * (Complex.I * Complex.exp (Complex.I * (alpha t (Phi t u) : ℂ)))) t := by
  have h := hasDerivAt_along_flow_complex (R := fun t s => -xi t s) hYC1 hYt hYs hPhid u t
  refine h.congr_deriv ?_
  push_cast
  ring

/-- The unit normal of a curve of tangent angle `θ` is a unit vector. -/
theorem norm_normal (x : ℝ) : ‖Complex.I * Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [norm_mul, Complex.norm_I, one_mul, mul_comm, Complex.norm_exp_ofReal_mul_I]

/-- **The normal path of a family of curves read in a gauge marking.**

The slices `Y t` are parametrized by their own arclength, with tangent angle
`α`, and move with tangential rate `ξ` and normal rate `η`; the marking `Φ` is
the flow of `−ξ`, so that `X(t,u) = Y(t,Φ(t,u))` moves normally.  For any cost
density `m` dominating the normal rate and the sup norms of its first two
derivatives in the marked parameter, and vanishing outside the time window,
this is a normal path of the path metric between the two prescribed marked
data whose curves it interpolates, with cost `∫₀^T m`. -/
theorem exists_normalPath_of_gauge_marking {a b : Data} {m : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T)
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hYs : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      ((xi t s : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (-xi t (Phi t u)) t)
    (hPhiu : ∀ t, Continuous (Phi t))
    (hencont : Continuous (uncurry en)) (halphacont : Continuous (uncurry alpha))
    (hstart : ∀ u, Y 0 (Phi 0 u) = a.1 u) (hfinish : ∀ u, Y T (Phi T u) = b.1 u)
    (hmc : Continuous m) (hm0 : ∀ t, 0 ≤ m t) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0)
    (hmbd : ∀ t u, |en t (Phi t u)| ≤ m t)
    (hmsup : ∀ t, ∀ j ≤ 2,
      MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) :
    ∃ Γ : NormalPath a b, Γ.T = T ∧ (∀ t u, Γ.X t u = Y t (Phi t u)) ∧
      (∀ t u, Γ.eta t u = en t (Phi t u)) ∧
      (∀ t u, Γ.nu t u
        = Complex.I * Complex.exp (Complex.I * (alpha t (Phi t u) : ℂ))) ∧
      Γ.m = m ∧ cost Γ = ∫ t in (0 : ℝ)..T, m t := by
  -- the flow line is continuous in the time, being differentiable
  have hPhitc : ∀ u, Continuous fun t => Phi t u := fun u =>
    continuous_iff_continuousAt.2 fun t => (hPhid u t).continuousAt
  refine ⟨{ T := T
            T_pos := hT
            X := fun t u => Y t (Phi t u)
            eta := fun t u => en t (Phi t u)
            nu := fun t u => Complex.I * Complex.exp (Complex.I * (alpha t (Phi t u) : ℂ))
            m := m
            start := hstart
            finish := hfinish
            hasDerivAt_time := fun t u =>
              hasDerivAt_gauge_normal hYC1 hYs hYt hPhid u t
            cont_vel := ?_
            norm_nu := fun _ _ => norm_normal _
            cont_m := hmc
            m_nonneg := hm0
            m_stop := hmstop
            abs_eta_le := hmbd
            le_m_L1 := ?_
            le_m_sup := hmsup }, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  · intro u
    have h1 : Continuous fun t => en t (Phi t u) :=
      hencont.comp (continuous_id.prodMk (hPhitc u))
    have h2 : Continuous fun t => alpha t (Phi t u) :=
      halphacont.comp (continuous_id.prodMk (hPhitc u))
    exact (Complex.continuous_ofReal.comp h1).mul (continuous_const.mul
      (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp h2))))
  · intro t
    have hcont : Continuous fun u => |en t (Phi t u)| :=
      ((hencont.comp (continuous_const.prodMk (hPhiu t))) : Continuous
        fun u => en t (Phi t u)).abs
    have hle : (∫ u in (0 : ℝ)..1, |en t (Phi t u)|) ≤ ∫ _u in (0 : ℝ)..1, m t :=
      intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable _ _)
        intervalIntegrable_const (fun u _ => hmbd t u)
    simpa using hle

end GaugeFlowNormalPath
