import Mathlib
import UnitTangentIterates.GaugeFlowVariablePeriod

/-!
# The closing relations of a family of closed curves whose length changes

`GaugeFlowVariablePeriod.lean` takes as input the two relations satisfied by the
frame data of a family of closed curves whose arclength period `Q t` changes
with the time:

* the normal component of the velocity is `Q t`-periodic,
* the tangential component satisfies `ξ(t, x + Q t) = ξ(t, x) − Q'(t)`.

This file proves them.  If the slices close up, `X(t, x + Q t) = X(t, x)`, then
differentiating that identity in the time gives

`∂_t X(t, x + Q t) + Q'(t) ∂_x X(t, x + Q t) = ∂_t X(t, x)`,

and since `∂_x X = τ` is the tangent and the frame `(τ, iτ)` is periodic, the
tangential components differ by exactly `Q'(t)` while the normal components
agree.  The rate at which the parameter of a material point slides in the
arclength of the moving slice therefore picks up the growth of the length —
which is what makes the gauge flow translate by the *current* period.

Main result: `closing_relations`.
-/

noncomputable section

open Set Function

namespace GaugeClosingRelations

/-- **The closing relations of a moving family of closed curves.**  For a `C¹`
family `X` whose slice at time `t` closes after the arclength period `Q t`,
whose space derivative is the (nonvanishing, `Q t`-periodic) tangent `τ` and
whose velocity decomposes as `ξ τ + η (iτ)` in the frame of the slice, the
normal component `η` is `Q t`-periodic and the tangential component `ξ`
satisfies `ξ(t, x + Q t) = ξ(t, x) − Q'(t)`. -/
theorem closing_relations {X tau : ℝ → ℝ → ℂ} {xi eta : ℝ → ℝ → ℝ} {Q Q' : ℝ → ℝ}
    (hX : ContDiff ℝ (1 : ℕ) (Function.uncurry X))
    (hXx : ∀ t x, HasDerivAt (X t) (tau t x) x)
    (hXt : ∀ t x, HasDerivAt (fun r => X r x)
      ((xi t x : ℂ) * tau t x + (eta t x : ℂ) * (Complex.I * tau t x)) t)
    (htau0 : ∀ t x, tau t x ≠ 0)
    (htauper : ∀ t, Function.Periodic (tau t) (Q t))
    (hclose : ∀ t x, X t (x + Q t) = X t x)
    (hQd : ∀ t, HasDerivAt Q (Q' t) t) (t x : ℝ) :
    xi t (x + Q t) = xi t x - Q' t ∧ eta t (x + Q t) = eta t x := by
  have hdiff : Differentiable ℝ (Function.uncurry X) := hX.differentiable (by norm_num)
  set y : ℝ := x + Q t with hy
  set L := fderiv ℝ (Function.uncurry X) (t, y) with hLdef
  have hL : HasFDerivAt (Function.uncurry X) L (t, y) := (hdiff (t, y)).hasFDerivAt
  -- the two partial derivatives are the components of the total derivative
  have hpt : HasDerivAt (fun r => X r y) (L (1, 0)) t := by
    have hg : HasDerivAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    simpa [Function.comp] using hL.comp_hasDerivAt t hg
  have hpx : HasDerivAt (X t) (L (0, 1)) y := by
    have hg : HasDerivAt (fun r : ℝ => (t, r)) ((0 : ℝ), (1 : ℝ)) y :=
      (hasDerivAt_const y t).prodMk (hasDerivAt_id y)
    simpa [Function.comp] using hL.comp_hasDerivAt y hg
  have hLt : L (1, 0) = (xi t y : ℂ) * tau t y + (eta t y : ℂ) * (Complex.I * tau t y) :=
    hpt.unique (hXt t y)
  have hLx : L (0, 1) = tau t y := hpx.unique (hXx t y)
  -- the derivative along the closing curve `r ↦ (r, x + Q r)`
  have hpath : HasDerivAt (fun r : ℝ => (r, x + Q r)) ((1 : ℝ), Q' t) t :=
    (hasDerivAt_id t).prodMk ((hQd t).const_add x)
  have hcomp : HasDerivAt (fun r => X r (x + Q r)) (L (1, Q' t)) t := by
    simpa [Function.comp, hy] using hL.comp_hasDerivAt t hpath
  -- but that curve is constant in the space variable, by the closing relation
  have hconst : (fun r => X r (x + Q r)) = fun r => X r x := funext fun r => hclose r x
  rw [hconst] at hcomp
  have hsplit : L (1, Q' t) = L (1, 0) + Q' t • L (0, 1) := by
    have : ((1 : ℝ), Q' t) = ((1 : ℝ), (0 : ℝ)) + Q' t • ((0 : ℝ), (1 : ℝ)) := by
      simp
    rw [this, map_add, map_smul]
  -- comparing the two expressions for the velocity at `x`
  have hkey : (xi t x : ℂ) * tau t x + (eta t x : ℂ) * (Complex.I * tau t x)
      = ((xi t y : ℂ) * tau t y + (eta t y : ℂ) * (Complex.I * tau t y))
        + (Q' t : ℂ) * tau t y := by
    have h1 := hcomp.unique (hXt t x)
    rw [hsplit, hLt, hLx] at h1
    simpa [Complex.real_smul, mul_comm] using h1.symm
  -- the frame is periodic, so everything is read at `x`
  have htaueq : tau t y = tau t x := by
    rw [hy]; exact htauper t x
  rw [htaueq] at hkey
  -- the two components must agree
  have hzero : (((xi t x - xi t y - Q' t : ℝ) : ℂ)
      + ((eta t x - eta t y : ℝ) : ℂ) * Complex.I) * tau t x = 0 := by
    have h := sub_eq_zero.mpr hkey
    push_cast
    linear_combination h
  have hfac : ((xi t x - xi t y - Q' t : ℝ) : ℂ)
      + ((eta t x - eta t y : ℝ) : ℂ) * Complex.I = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h (htau0 t x)
  have hre : xi t x - xi t y - Q' t = 0 := by
    have := congrArg Complex.re hfac
    simpa using this
  have him : eta t x - eta t y = 0 := by
    have := congrArg Complex.im hfac
    simpa using this
  constructor
  · linarith [hre]
  · linarith [him]

/-- **The quasi-periodicity of the tangential rate, from the closing
relations.**  In arclength the speed is one, so the tangential rate `−ξ` of the
gauge flow of a family of closed curves whose length changes satisfies the
hypothesis of `GaugeFlowVariablePeriod.flow_translation_var`. -/
theorem gaugeRate_quasiPeriodic_of_closing {X tau : ℝ → ℝ → ℂ} {xi eta : ℝ → ℝ → ℝ}
    {Q Q' : ℝ → ℝ}
    (hX : ContDiff ℝ (1 : ℕ) (Function.uncurry X))
    (hXx : ∀ t x, HasDerivAt (X t) (tau t x) x)
    (hXt : ∀ t x, HasDerivAt (fun r => X r x)
      ((xi t x : ℂ) * tau t x + (eta t x : ℂ) * (Complex.I * tau t x)) t)
    (htau0 : ∀ t x, tau t x ≠ 0)
    (htauper : ∀ t, Function.Periodic (tau t) (Q t))
    (hclose : ∀ t x, X t (x + Q t) = X t x)
    (hQd : ∀ t, HasDerivAt Q (Q' t) t) (t x : ℝ) :
    GaugeRate.gaugeRate xi (fun _ _ => 1) t (x + Q t)
      = GaugeRate.gaugeRate xi (fun _ _ => 1) t x + Q' t := by
  have h := (closing_relations hX hXx hXt htau0 htauper hclose hQd t x).1
  simp only [GaugeRate.gaugeRate, h]
  ring

/-- **The closing relations are non-vacuous with a genuinely changing period.**
The family `X(t, x) = e^{ixe^t}`, a circle traversed faster and faster, is a
closed family of arclength period `Q t = 2πe^{−t}`; its tangential rate is
`ξ(t,x) = x`, and the conclusion of `closing_relations` reads
`x + Q t = x − Q'(t)`, which is exactly the shrinking of the period. -/
example (t x : ℝ) :
    (x + 2 * Real.pi * Real.exp (-t) = x - (-(2 * Real.pi * Real.exp (-t)))) ∧
      (0 : ℝ) = 0 := by
  have hclose : ∀ (r y : ℝ),
      Complex.exp (Complex.I * ((y + 2 * Real.pi * Real.exp (-r) : ℝ) : ℂ)
          * ((Real.exp r : ℝ) : ℂ))
        = Complex.exp (Complex.I * (y : ℂ) * ((Real.exp r : ℝ) : ℂ)) := by
    intro r y
    have hrr : Complex.exp (-(r : ℂ)) * Complex.exp ((r : ℂ)) = 1 := by
      rw [← Complex.exp_add]; simp
    have : Complex.I * ((y + 2 * Real.pi * Real.exp (-r) : ℝ) : ℂ) * ((Real.exp r : ℝ) : ℂ)
        = Complex.I * (y : ℂ) * ((Real.exp r : ℝ) : ℂ) + 2 * Real.pi * Complex.I := by
      push_cast
      ring_nf
      linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hrr
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  refine closing_relations (X := fun r y => Complex.exp (Complex.I * (y : ℂ) * (Real.exp r : ℂ)))
    (tau := fun r y => Complex.I * (Real.exp r : ℂ)
      * Complex.exp (Complex.I * (y : ℂ) * (Real.exp r : ℂ)))
    (xi := fun _ y => y) (eta := fun _ _ => 0)
    (Q := fun r => 2 * Real.pi * Real.exp (-r))
    (Q' := fun r => -(2 * Real.pi * Real.exp (-r)))
    ?_ ?_ ?_ ?_ ?_ hclose ?_ t x
  · -- joint smoothness
    apply Complex.contDiff_exp.comp
    refine ContDiff.mul (ContDiff.mul contDiff_const ?_) ?_
    · exact Complex.ofRealCLM.contDiff.comp contDiff_snd
    · exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_fst)
  · -- the tangent
    intro r y
    have h1 : HasDerivAt (fun z : ℝ => Complex.I * (z : ℂ) * ((Real.exp r : ℝ) : ℂ))
        (Complex.I * ((Real.exp r : ℝ) : ℂ)) y := by
      have h : HasDerivAt (fun z : ℝ => (z : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
      simpa using ((h.const_mul Complex.I).mul_const ((Real.exp r : ℝ) : ℂ))
    simpa [mul_comm, mul_assoc, mul_left_comm] using h1.cexp
  · -- the velocity
    intro r y
    have h1 : HasDerivAt (fun s : ℝ => Complex.I * (y : ℂ) * ((Real.exp s : ℝ) : ℂ))
        (Complex.I * (y : ℂ) * ((Real.exp r : ℝ) : ℂ)) r := by
      have h : HasDerivAt (fun s : ℝ => ((Real.exp s : ℝ) : ℂ)) ((Real.exp r : ℝ) : ℂ) r :=
        (Real.hasDerivAt_exp r).ofReal_comp
      simpa using h.const_mul (Complex.I * (y : ℂ))
    simpa [mul_comm, mul_assoc, mul_left_comm] using h1.cexp
  · -- the tangent does not vanish
    intro r y
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero
      (by exact_mod_cast (Real.exp_pos r).ne')) (Complex.exp_ne_zero _)
  · -- the tangent is periodic
    intro r y
    simp only
    rw [hclose r y]
  · -- the period is differentiable
    intro r
    have h : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-r)) r := by
      simpa using (Real.hasDerivAt_exp (-r)).comp r (hasDerivAt_neg r)
    simpa [mul_comm] using h.const_mul (2 * Real.pi)

end GaugeClosingRelations
