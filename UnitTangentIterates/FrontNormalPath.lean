import Mathlib
import UnitTangentIterates.PathMetric
import UnitTangentIterates.MarkedSpaceReparam

/-!
# The normal path *of* a family of fronts

The assembly of the path metric in `RearOwnPathDistSlices.lean` and
`RearOwnPathDistNormalized.lean` relates the abstract normal path `Γ` of the
path metric to the family of fronts through the two geometric identifications

```
  X(t, u) = F(t, P(t) u) ,      ν(t, u) = i e^{iΘ(t, P(t) u)} ,
```

which are *hypotheses* there.  This file produces a normal path satisfying them.

What has to be assumed instead is that the family of fronts, read in the
normalized parameter, already moves **normally**: the time derivative of
`u ↦ F(t, P(t) u)` is `η_F(t, P(t)u) · i e^{iΘ(t,P(t)u)}`.  That is no loss of
generality — it is exactly what the reduction to normal gauge of
`NormalGauge.hasDerivAt_normalGauge` arranges, the tangential component of the
velocity being absorbed into the parametrization — and it is a property of the
front family alone, with no mention of an abstract path.  Besides it one needs a
cost density `m` for the path metric, that is, a continuous nonnegative function
vanishing outside the time window and dominating the normal velocity and the sup
norms of its first two arclength derivatives.

Main results:

* `exists_bound_of_periodic_continuous` — a continuous periodic function is
  bounded, so each front is a marked curve;
* `exists_normalPath_of_front_normal_gauge` — the normal path of the family of
  fronts, with the two identifications and with cost `∫₀^T m`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
open scoped BoundedContinuousFunction

namespace FrontNormalPath

/-- A continuous periodic function is bounded. -/
theorem exists_bound_of_periodic_continuous {f : ℝ → ℂ} (hper : Function.Periodic f 1)
    (hcont : Continuous f) : ∃ C : ℝ, ∀ u, ‖f u‖ ≤ C :=
  MarkedSpace.exists_bound_of_periodic hcont hper

/-- The unit normal of a front of tangent angle `θ` is a unit vector. -/
theorem norm_normal (x : ℝ) : ‖Complex.I * Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [norm_mul, Complex.norm_I, one_mul, mul_comm, Complex.norm_exp_ofReal_mul_I]

/-- **The normal path of a family of fronts.**

If the fronts `F(t, ·)` close up with period `P(t)`, and if the family read in
the normalized parameter `u ↦ F(t, P(t)u)` moves with the purely normal velocity
`η_F · i e^{iΘ}`, then it *is* a normal path of the path metric, from the front
at time `0` to the front at time `T`, for any cost density `m` dominating the
normal velocity and the sup norms of its first two arclength derivatives and
vanishing outside the time window.  Its slices are the fronts and its unit
normal is the standard one — the two geometric identifications consumed by the
assembly of the path metric — and its cost is `∫₀^T m`. -/
theorem exists_normalPath_of_front_normal_gauge
    {F : ℝ → ℝ → ℂ} {Θ etaF : ℝ → ℝ → ℝ} {P m : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T)
    (hFcont : ∀ t, Continuous (F t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hnormal : ∀ t u, HasDerivAt (fun r => F r (P r * u))
      ((etaF t (P t * u) : ℂ) * (Complex.I * Complex.exp (Complex.I * (Θ t (P t * u) : ℂ)))) t)
    (hetaCont : Continuous (uncurry etaF)) (hThetaCont : Continuous (uncurry Θ))
    (hPcont : Continuous P)
    (hmc : Continuous m) (hm0 : ∀ t, 0 ≤ m t) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0)
    (hmbd : ∀ t u, |etaF t (P t * u)| ≤ m t)
    (hmsup : ∀ t, ∀ j ≤ 2,
      MarkedTopology.supNorm (iteratedDeriv j (fun u => etaF t (P t * u))) ≤ m t) :
    ∃ (p q : Data) (Γ : NormalPath p q), Γ.T = T ∧
      (∀ t u, Γ.X t u = F t (P t * u)) ∧
      (∀ t u, Γ.eta t u = etaF t (P t * u)) ∧
      (∀ t u, Γ.nu t u = Complex.I * Complex.exp (Complex.I * (Θ t (P t * u) : ℂ))) ∧
      cost Γ = ∫ t in (0 : ℝ)..T, m t := by
  -- each slice, in the normalized parameter, is a bounded continuous function
  have hslicecont : ∀ t, Continuous fun u => F t (P t * u) :=
    fun t => (hFcont t).comp (continuous_const.mul continuous_id)
  have hsliceper : ∀ t, Function.Periodic (fun u => F t (P t * u)) 1 := by
    intro t u
    show F t (P t * (u + 1)) = F t (P t * u)
    have h : P t * (u + 1) = P t * u + P t := by ring
    rw [h, hFper]
  have hbdd : ∀ t, ∃ C : ℝ, ∀ u, ‖F t (P t * u)‖ ≤ C :=
    fun t => exists_bound_of_periodic_continuous (hsliceper t) (hslicecont t)
  set bcf : ℝ → (ℝ →ᵇ ℂ) := fun t =>
    BoundedContinuousFunction.ofNormedAddCommGroup (fun u => F t (P t * u)) (hslicecont t)
      (Classical.choose (hbdd t)) (Classical.choose_spec (hbdd t)) with hbcf
  -- continuity of the data in the time
  have hetaslice : ∀ u, Continuous fun t => etaF t (P t * u) := by
    intro u
    exact hetaCont.comp (continuous_id.prodMk (hPcont.mul continuous_const))
  have hThslice : ∀ u, Continuous fun t => Θ t (P t * u) := by
    intro u
    exact hThetaCont.comp (continuous_id.prodMk (hPcont.mul continuous_const))
  refine ⟨(bcf 0, 0, 0), (bcf T, 0, 0),
    { T := T
      T_pos := hT
      X := fun t u => F t (P t * u)
      eta := fun t u => etaF t (P t * u)
      nu := fun t u => Complex.I * Complex.exp (Complex.I * (Θ t (P t * u) : ℂ))
      m := m
      start := fun _ => rfl
      finish := fun _ => rfl
      hasDerivAt_time := hnormal
      cont_vel := ?_
      norm_nu := fun _ _ => norm_normal _
      cont_m := hmc
      m_nonneg := hm0
      m_stop := hmstop
      abs_eta_le := hmbd
      le_m_L1 := ?_
      le_m_sup := hmsup }, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩
  · intro u
    refine ((Complex.continuous_ofReal.comp (hetaslice u)).mul ?_)
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (hThslice u))))
  · intro t
    have hcont : Continuous fun u => |etaF t (P t * u)| :=
      (((hetaCont.comp (continuous_const.prodMk (continuous_const.mul continuous_id))) : Continuous
        fun u => etaF t (P t * u))).abs
    have hle : (∫ u in (0 : ℝ)..1, |etaF t (P t * u)|) ≤ ∫ _u in (0 : ℝ)..1, m t := by
      refine intervalIntegral.integral_mono_on (by norm_num)
        (hcont.intervalIntegrable _ _) (intervalIntegrable_const) ?_
      intro u _
      exact hmbd t u
    simpa using hle

end FrontNormalPath
