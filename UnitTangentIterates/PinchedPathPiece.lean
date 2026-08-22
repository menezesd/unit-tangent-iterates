import Mathlib
import UnitTangentIterates.PinchedSliceData

/-!
# Restricting an admissible path to a subinterval of its time

The cost density of a normal path is required to vanish outside the open time
interval, so a path cannot simply be restricted to a subinterval: at the two
cut points its density is in general positive.  The remedy is the one of
`PinchedPathSlow.lean`: run the restricted motion on a *flat* time profile, so
that it stands still near the two ends of the new time interval.

This file first isolates that construction in general — `reparamPath`, a normal
path run on an arbitrary nondecreasing smooth profile that is flat outside its
time window — and then applies it to the profile
`w(t) = a + flatTime (b − a) t`, which increases from `a` to `b`.  The result
(`piece`) is a normal path from the slice datum at time `a` to the slice datum
at time `b`, of cost `∫_a^b m` (`cost_piece`), and admissible whenever the path
is (`isPinchedPath_piece`).

Main results: `reparamPath`, `cost_reparamPath`, `isPinchedPath_reparamPath`,
`piece`, `cost_piece`, `isPinchedPath_piece`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath

namespace PinchedPath

open RearOwnHigherRegularity FrontFromPath SelInvPathRegularityC2
  SelInvPathCurvatureC2 SelInvPathPerimC2 SelInvTubePathDist

variable {kminP kh : ℝ} {p q p' q' : Data}

/-! ### A path run on an arbitrary flat profile -/

section Reparam

variable (Γ : NormalPath p q) {T' : ℝ} {w : ℝ → ℝ}

/-- The derivative of a `C⁶` profile is continuous. -/
theorem continuous_deriv_of_contDiff6 (hw : ContDiff ℝ (6 : ℕ) w) : Continuous (deriv w) := by
  have h : ContDiff ℝ (5 : ℕ) (deriv w) :=
    ContDiff.deriv' (n := (5 : ℕ)) (by exact_mod_cast hw)
  exact h.continuous

/-- **A normal path run on a nondecreasing profile that is flat outside the new
time window.**  The motion is the same, reparametrized in the time. -/
def reparamPath (hT' : 0 < T') (hw : ContDiff ℝ (6 : ℕ) w)
    (hwmono : ∀ t, 0 ≤ deriv w t) (hwout : ∀ t ∉ Ioo (0 : ℝ) T', deriv w t = 0)
    (hstart : ∀ u, Γ.X (w 0) u = p'.1 u) (hfinish : ∀ u, Γ.X (w T') u = q'.1 u) :
    NormalPath p' q' where
  T := T'
  T_pos := hT'
  X := fun t u => Γ.X (w t) u
  eta := fun t u => deriv w t * Γ.eta (w t) u
  nu := fun t u => Γ.nu (w t) u
  m := fun t => deriv w t * Γ.m (w t)
  start := hstart
  finish := hfinish
  hasDerivAt_time := by
    intro t u
    have hd : HasDerivAt w (deriv w t) t :=
      ((hw.differentiable (by norm_num)) t).hasDerivAt
    have h := (Γ.hasDerivAt_time (w t) u).scomp t hd
    refine h.congr_deriv ?_
    simp [Complex.real_smul]
    ring
  cont_vel := by
    intro u
    have hcont : Continuous w := hw.continuous
    have hcomp : Continuous fun t => ((Γ.eta (w t) u : ℂ) * Γ.nu (w t) u) :=
      (Γ.cont_vel u).comp hcont
    have hfun : (fun t => ((deriv w t * Γ.eta (w t) u : ℝ) : ℂ) * Γ.nu (w t) u)
        = fun t => ((deriv w t : ℝ) : ℂ) * ((Γ.eta (w t) u : ℂ) * Γ.nu (w t) u) := by
      funext t; push_cast; ring
    rw [hfun]
    exact (Complex.continuous_ofReal.comp (continuous_deriv_of_contDiff6 hw)).mul hcomp
  norm_nu := fun t u => Γ.norm_nu _ u
  cont_m := (continuous_deriv_of_contDiff6 hw).mul (Γ.cont_m.comp hw.continuous)
  m_nonneg := fun t => mul_nonneg (hwmono t) (Γ.m_nonneg _)
  m_stop := fun t ht => by rw [hwout t ht, zero_mul]
  abs_eta_le := by
    intro t u
    rw [abs_mul, abs_of_nonneg (hwmono t)]
    exact mul_le_mul_of_nonneg_left (Γ.abs_eta_le _ u) (hwmono t)
  le_m_L1 := by
    intro t
    have hfun : (∫ u in (0:ℝ)..1, |deriv w t * Γ.eta (w t) u|)
        = deriv w t * ∫ u in (0:ℝ)..1, |Γ.eta (w t) u| := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      rw [abs_mul, abs_of_nonneg (hwmono t)]
    rw [hfun]
    exact mul_le_mul_of_nonneg_left (Γ.le_m_L1 _) (hwmono t)
  le_m_sup := by
    intro t j hj
    rw [PathMetric.iteratedDeriv_const_mul' _ _ j,
      PathMetric.supNorm_const_mul (hwmono t)]
    exact mul_le_mul_of_nonneg_left (Γ.le_m_sup _ j hj) (hwmono t)

/-- **The cost of the reparametrized path is the cost of the motion it
covers.** -/
theorem cost_reparamPath (hT' : 0 < T') (hw : ContDiff ℝ (6 : ℕ) w)
    (hwmono : ∀ t, 0 ≤ deriv w t) (hwout : ∀ t ∉ Ioo (0 : ℝ) T', deriv w t = 0)
    (hstart : ∀ u, Γ.X (w 0) u = p'.1 u) (hfinish : ∀ u, Γ.X (w T') u = q'.1 u) :
    cost (reparamPath Γ hT' hw hwmono hwout hstart hfinish)
      = ∫ s in (w 0)..(w T'), Γ.m s := by
  have hsub : (∫ t in (0:ℝ)..T', deriv w t • (Γ.m ∘ w) t)
      = ∫ s in (w 0)..(w T'), Γ.m s :=
    intervalIntegral.integral_comp_smul_deriv
      (fun x _ => ((hw.differentiable (by norm_num)) x).hasDerivAt)
      (continuous_deriv_of_contDiff6 hw).continuousOn Γ.cont_m
  simpa [cost, reparamPath, Function.comp_def, smul_eq_mul] using hsub

/-- **The reparametrized path is admissible whenever the path is.** -/
theorem isPinchedPath_reparamPath (hΓ : IsPinchedPath kminP kh Γ) (hT' : 0 < T')
    (hw : ContDiff ℝ (6 : ℕ) w) (hwmono : ∀ t, 0 ≤ deriv w t)
    (hwout : ∀ t ∉ Ioo (0 : ℝ) T', deriv w t = 0)
    (hstart : ∀ u, Γ.X (w 0) u = p'.1 u) (hfinish : ∀ u, Γ.X (w T') u = q'.1 u) :
    IsPinchedPath kminP kh (reparamPath Γ hT' hw hwmono hwout hstart hfinish) := by
  have hX6 : ContDiff ℝ (6 : ℕ) (uncurry Γ.X) := hΓ.smooth
  have hX2 : ContDiff ℝ (2 : ℕ) (uncurry Γ.X) := hX6.of_le (by norm_num)
  have hd : Differentiable ℝ (uncurry Γ.X) := hX2.differentiable (by norm_num)
  have hphi : Differentiable ℝ w := hw.differentiable (by norm_num)
  refine
    { smooth := by
        show ContDiff ℝ (6 : ℕ) (uncurry fun t u => Γ.X (w t) u)
        exact contDiff_uncurry_timeComp hX6 hw
      speed := fun t u => ?_
      per := fun t => hΓ.per (w t)
      normal := fun t u => ?_
      kmin := fun t σ => ?_
      kmax := fun t σ => ?_
      short := fun t => ?_
      slit := fun t => ?_
      rest := fun t => ?_ }
  · show ‖pathVel (fun t u => Γ.X (w t) u) t u‖ = ‖pathVel (fun t u => Γ.X (w t) u) t 0‖
    rw [pathVel_timeComp hd hphi, pathVel_timeComp hd hphi]
    exact hΓ.speed (w t) u
  · show Γ.nu (w t) u
      = Complex.I * (pathVel (fun t u => Γ.X (w t) u) t u
          / ((pathPerim (fun t u => Γ.X (w t) u) t : ℝ) : ℂ))
    rw [pathVel_timeComp hd hphi, pathPerim_timeComp hd hphi]
    exact hΓ.normal (w t) u
  · show kminP ≤ pathKn (fun t u => Γ.X (w t) u) (pathPerim fun t u => Γ.X (w t) u) t σ
    rw [pathKn_timeComp hX2 hphi]
    exact hΓ.kmin (w t) σ
  · show pathKn (fun t u => Γ.X (w t) u) (pathPerim fun t u => Γ.X (w t) u) t σ ≤ kh
    rw [pathKn_timeComp hX2 hphi]
    exact hΓ.kmax (w t) σ
  · show kh * pathPerim (fun t u => Γ.X (w t) u) t < 4 * Real.pi
    rw [pathPerim_timeComp hd hphi]
    exact hΓ.short (w t)
  · show pathVel (fun t u => Γ.X (w t) u) t 0 ∈ Complex.slitPlane
    rw [pathVel_timeComp hd hphi]
    exact hΓ.slit (w t)
  · show deriv w t * Γ.eta (w t) 0 = 0
    rw [hΓ.rest (w t), mul_zero]

end Reparam

/-! ### The profile of a subinterval -/

/-- The flat profile increasing from `a` to `b`. -/
def segTime (a b : ℝ) : ℝ → ℝ := fun t => a + flatTime (b - a) t

theorem contDiff_segTime {n : ℕ} (a b : ℝ) : ContDiff ℝ (n : ℕ) (segTime a b) :=
  contDiff_const.add (contDiff_flatTime (n := n) (b - a))

theorem hasDerivAt_segTime (a b t : ℝ) : HasDerivAt (segTime a b) (flatSpeed (b - a) t) t := by
  have h : HasDerivAt (fun s => a + flatTime (b - a) s) (flatSpeed (b - a) t) t := by
    simpa using (hasDerivAt_flatTime (b - a) t).const_add a
  exact h

theorem deriv_segTime (a b : ℝ) : deriv (segTime a b) = flatSpeed (b - a) :=
  funext fun t => (hasDerivAt_segTime a b t).deriv

theorem segTime_zero {a b : ℝ} (hab : a < b) : segTime a b 0 = a := by
  simp [segTime, flatTime_zero (by linarith : (0:ℝ) < b - a)]

theorem segTime_final {a b : ℝ} (hab : a < b) : segTime a b (b - a) = b := by
  rw [segTime, flatTime_final (by linarith : (0:ℝ) < b - a)]; ring

/-! ### The restriction of an admissible path to a subinterval -/

variable {Γ : NormalPath p q}

/-- **An admissible path restricted to a subinterval of its time**, run on the
flat profile: a normal path from the slice datum at `a` to the slice datum at
`b`. -/
def piece (hΓ : IsPinchedPath kminP kh Γ) {a b : ℝ} (hab : a < b) :
    NormalPath (pinchedSliceData hΓ a) (pinchedSliceData hΓ b) :=
  reparamPath Γ (by linarith : (0:ℝ) < b - a) (contDiff_segTime (n := 6) a b)
    (fun t => by rw [deriv_segTime]; exact flatSpeed_nonneg (by linarith) t)
    (fun t ht => by
      rw [deriv_segTime]; exact flatSpeed_eq_zero_outside (by linarith) ht)
    (fun u => by rw [segTime_zero hab]; rfl)
    (fun u => by rw [segTime_final hab]; rfl)

/-- **The cost of a piece is the cost of the motion over that time
interval.** -/
theorem cost_piece (hΓ : IsPinchedPath kminP kh Γ) {a b : ℝ} (hab : a < b) :
    cost (piece hΓ hab) = ∫ s in a..b, Γ.m s := by
  rw [piece, cost_reparamPath, segTime_zero hab, segTime_final hab]

/-- **A piece of an admissible path is admissible.** -/
theorem isPinchedPath_piece (hΓ : IsPinchedPath kminP kh Γ) {a b : ℝ} (hab : a < b) :
    IsPinchedPath kminP kh (piece hΓ hab) :=
  isPinchedPath_reparamPath Γ hΓ _ _ _ _ _ _

end PinchedPath
