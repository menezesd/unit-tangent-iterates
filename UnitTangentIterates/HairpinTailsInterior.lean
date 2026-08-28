import Mathlib
import UnitTangentIterates.HairpinPulseDecay
import UnitTangentIterates.HairpinInteriorRegularity

/-!
# Exponential tails of the hairpin pulse, without endpoint regularity

The lemma *Hairpin pulse estimates* asserts that `y` and all its derivatives
decay exponentially at both ends.  In the paper this costs nothing beyond the
relative bounds: once `|y^{(j)}| ≤ D_j y` is known and `y` itself decays, *every*
derivative decays — "the exponential bounds for `K_*` therefore extend to every
derivative".

`decay_of_relative` already records that implication, and it is
profile-free.  What is not profile-free in `HairpinPulseDecay` is the chain
producing the order-zero decay: `hasDerivAt_frontArclength`, `frontArclength_le`,
`le_frontArclength`, `abs_frontArclength_le`, `abs_pulseState_ge` and
`pulse_decay` all take `ContDiff ℝ ∞ f` together with positivity of `f` on the
whole line.

They do not need it.  Each uses those hypotheses for exactly one thing —
continuity of `curvField f ∘ θ` — and, where positivity is needed at all, only
pointwise along the angle map.  This file restates the chain that way, so the
order-zero tail, and hence the tails of every order, are available from the
regularity the paper actually proves.

Main results: `hasDerivAt_frontArclength_of_comp`, `abs_pulseState_ge_of_comp`,
`pulse_decay_of_comp`, `abs_iteratedDeriv_pulse_decay_of_relative`.
-/

noncomputable section

open Set Real HairpinRelative

namespace HairpinTailsInterior

variable {f theta : ℝ → ℝ} {A M : ℝ}

/-- Continuity of the front-arclength integrand from continuity of the
curvature field along the angle map. -/
theorem continuous_integrand (hkc : Continuous fun t => curvField f (theta t)) :
    Continuous fun t => Real.sqrt (1 + curvField f (theta t) ^ 2) :=
  (continuous_const.add (hkc.pow 2)).sqrt

/-- **The front arclength differentiates**, from interior data. -/
theorem hasDerivAt_frontArclength_of_comp
    (hkc : Continuous fun t => curvField f (theta t)) (u : ℝ) :
    HasDerivAt (frontArclength f theta)
      (Real.sqrt (1 + curvField f (theta u) ^ 2)) u := by
  have hg := continuous_integrand hkc
  exact intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
    (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt

/-- `σ(u) ≤ u + A²M/2` for `u ≥ 0`, from interior data. -/
theorem frontArclength_le_of_comp
    (hkc : Continuous fun t => curvField f (theta t))
    (hnn : ∀ u, 0 ≤ curvField f (theta u))
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M)
    {u : ℝ} (hu : 0 ≤ u) :
    frontArclength f theta u ≤ u + A ^ 2 * M / 2 := by
  have hg := continuous_integrand hkc
  have hbnd : Continuous fun t : ℝ => A ^ 2 / 2 * Real.exp (-t / M) :=
    continuous_const.mul (Real.continuous_exp.comp (by continuity))
  have hsplit : frontArclength f theta u - u
      = ∫ t in (0:ℝ)..u, (Real.sqrt (1 + curvField f (theta t) ^ 2) - 1) := by
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _)
      intervalIntegrable_const]
    simp [frontArclength]
  have hmono : (∫ t in (0:ℝ)..u, (Real.sqrt (1 + curvField f (theta t) ^ 2) - 1))
      ≤ ∫ t in (0:ℝ)..u, A ^ 2 / 2 * Real.exp (-t / M) := by
    refine intervalIntegral.integral_mono_on hu
      ((hg.sub continuous_const).intervalIntegrable _ _)
      (hbnd.intervalIntegrable _ _) ?_
    intro t ht
    exact sqrt_integrand_le hnn hdecay hM ht.1
  have hlast : (∫ t in (0:ℝ)..u, A ^ 2 / 2 * Real.exp (-t / M)) ≤ A ^ 2 / 2 * M := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_exp_neg_le hM u)
      (by positivity)
  have hres : frontArclength f theta u - u ≤ A ^ 2 / 2 * M := by
    rw [hsplit]; exact le_trans hmono hlast
  linarith

/-- `σ(u) ≥ u − A²M/2` for `u ≤ 0`, from interior data. -/
theorem le_frontArclength_of_comp
    (hkc : Continuous fun t => curvField f (theta t))
    (hnn : ∀ u, 0 ≤ curvField f (theta u))
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M)
    {u : ℝ} (hu : u ≤ 0) :
    u - A ^ 2 * M / 2 ≤ frontArclength f theta u := by
  have hg := continuous_integrand hkc
  have hbnd : Continuous fun t : ℝ => A ^ 2 / 2 * Real.exp (t / M) :=
    continuous_const.mul (Real.continuous_exp.comp (by continuity))
  have hsplit : frontArclength f theta u - u
      = -∫ t in u..(0:ℝ), (Real.sqrt (1 + curvField f (theta t) ^ 2) - 1) := by
    rw [← intervalIntegral.integral_symm, intervalIntegral.integral_sub
      (hg.intervalIntegrable _ _) intervalIntegrable_const]
    simp [frontArclength]
  have hmono : (∫ t in u..(0:ℝ), (Real.sqrt (1 + curvField f (theta t) ^ 2) - 1))
      ≤ ∫ t in u..(0:ℝ), A ^ 2 / 2 * Real.exp (t / M) := by
    refine intervalIntegral.integral_mono_on hu
      ((hg.sub continuous_const).intervalIntegrable _ _)
      (hbnd.intervalIntegrable _ _) ?_
    intro t ht
    exact sqrt_integrand_le' hnn hdecay hM ht.2
  have hlast : (∫ t in u..(0:ℝ), A ^ 2 / 2 * Real.exp (t / M)) ≤ A ^ 2 / 2 * M := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_exp_le hM u)
      (by positivity)
  have hres : -(A ^ 2 / 2 * M) ≤ frontArclength f theta u - u := by
    rw [hsplit]
    linarith [le_trans hmono hlast]
  linarith

/-- `|σ(u)| ≤ |u| + A²M/2`, from interior data. -/
theorem abs_frontArclength_le_of_comp
    (hkc : Continuous fun t => curvField f (theta t))
    (hnn : ∀ u, 0 ≤ curvField f (theta u))
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M)
    (u : ℝ) : |frontArclength f theta u| ≤ |u| + A ^ 2 * M / 2 := by
  have hderiv := hasDerivAt_frontArclength_of_comp hkc
  have hge : ∀ t, (1:ℝ) ≤ Real.sqrt (1 + curvField f (theta t) ^ 2) := by
    intro t
    have h1 : (1:ℝ) ≤ 1 + curvField f (theta t) ^ 2 := by
      nlinarith [sq_nonneg (curvField f (theta t))]
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ _ := Real.sqrt_le_sqrt h1
  rcases le_or_gt 0 u with hu | hu
  · have h1 : u ≤ frontArclength f theta u := by
      have h := ArclengthInverse.le_of_deriv_ge (c := 1) hderiv hge hu
      rw [frontArclength_zero] at h
      linarith
    have h2 := frontArclength_le_of_comp hkc hnn hdecay hM hu
    rw [abs_of_nonneg (le_trans hu h1), abs_of_nonneg hu]
    linarith
  · have h1 : frontArclength f theta u ≤ u := by
      have h := ArclengthInverse.ge_of_deriv_ge (c := 1) hderiv hge hu.le
      rw [frontArclength_zero] at h
      linarith
    have h2 := le_frontArclength_of_comp hkc hnn hdecay hM hu.le
    rw [abs_of_nonpos (le_trans h1 hu.le), abs_of_nonpos hu.le]
    linarith

/-- `|x(s)| ≥ |s| − A²M/2`, from interior data. -/
theorem abs_pulseState_ge_of_comp
    (hkc : Continuous fun t => curvField f (theta t))
    (hnn : ∀ u, 0 ≤ curvField f (theta u))
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M)
    {x : ℝ → ℝ} (hxinv : ∀ s, frontArclength f theta (x s) = s) (s : ℝ) :
    |s| - A ^ 2 * M / 2 ≤ |x s| := by
  have h := abs_frontArclength_le_of_comp hkc hnn hdecay hM (x s)
  rw [hxinv s] at h
  linarith

/-- **Exponential decay of the steering pulse, from interior data.**  This is the
order-zero tail of the lemma *Hairpin pulse estimates*, with no regularity of the
profile at or beyond the endpoints of `(0,π)`. -/
theorem pulse_decay_of_comp
    (hkc : Continuous fun t => curvField f (theta t))
    (hnn : ∀ u, 0 ≤ curvField f (theta u))
    (hle : ∀ u, pulseField f (theta u) ≤ curvField f (theta u))
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (hA : 0 ≤ A) (hM : 0 < M)
    {x : ℝ → ℝ} (hxinv : ∀ s, frontArclength f theta (x s) = s) (s : ℝ) :
    pulseField f (theta (x s)) ≤ A * Real.exp (A ^ 2 / 2) * Real.exp (-|s| / M) := by
  have h1 : pulseField f (theta (x s)) ≤ curvField f (theta (x s)) := hle _
  have h2 : curvField f (theta (x s)) ≤ A * Real.exp (-|x s| / M) := hdecay _
  have h3 : |s| - A ^ 2 * M / 2 ≤ |x s| :=
    abs_pulseState_ge_of_comp hkc hnn hdecay hM hxinv s
  have h4 : -|x s| / M ≤ -|s| / M + A ^ 2 / 2 := by
    rw [div_add' _ _ _ hM.ne', div_le_div_iff_of_pos_right hM]
    nlinarith
  have h5 : Real.exp (-|x s| / M) ≤ Real.exp (-|s| / M) * Real.exp (A ^ 2 / 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  calc pulseField f (theta (x s)) ≤ A * Real.exp (-|x s| / M) := le_trans h1 h2
    _ ≤ A * (Real.exp (-|s| / M) * Real.exp (A ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left h5 hA
    _ = A * Real.exp (A ^ 2 / 2) * Real.exp (-|s| / M) := by ring

/-- **The tails of every order, from a relative bound and the order-zero tail.**
This is the paper's "the exponential bounds therefore extend to every
derivative": no new analysis, just `decay_of_relative`.  Since
the relative bounds are available on the endpoint-free Harnack route at every
order the development consumes, so are the tails. -/
theorem abs_iteratedDeriv_pulse_decay_of_relative {w : ℝ → ℝ} {A' D : ℝ} {j : ℕ}
    (hdecay : ∀ s, pulseField f (w s) ≤ A' * Real.exp (-|s| / M)) (hD0 : 0 ≤ D)
    (hrel : ∀ s, |iteratedDeriv j (fun r => pulseField f (w r)) s|
      ≤ D * pulseField f (w s)) (s : ℝ) :
    |iteratedDeriv j (fun r => pulseField f (w r)) s|
      ≤ D * A' * Real.exp (-|s| / M) :=
  decay_of_relative hdecay hD0 hrel s

end HairpinTailsInterior
