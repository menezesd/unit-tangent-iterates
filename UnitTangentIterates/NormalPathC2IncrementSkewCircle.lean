import Mathlib
import UnitTangentIterates.NormalPathC2IncrementVariableSpeed
import UnitTangentIterates.PathMetricCircle

/-!
# A normal path whose slices really have a variable speed

`NormalPathC2IncrementVariableSpeed.dist_le_cost_variableSpeed` bounds the
marked distance of the two ends of a normal path whose slices are closed curves
of variable speed.  This file checks that its hypothesis block is satisfiable
with a **nonconstant** speed — that is, with `g_u ≠ 0`, the term the
constant-speed estimate does not see — and with a path of nonzero cost.

The path is the radial dilation of `PathMetricCircle.lean` again, but the
circles are now read in the *skew* parametrization

```
  u ↦ r e^{iφ(u)} ,      φ(u) = 2πu + a sin(2πu) ,
```

whose speed `r φ'(u) = 2π r (1 + a cos 2πu)` is not constant in `u`.  The time
derivative is still radial, hence normal, so this is a normal path with the same
cost density `|R − r| w(t)` and the same cost `|R − r|` as the dilation of the
circles in their arclength parametrization.

Main results: `isVariableSpeedNormalPath_skewDilation` and
`dist_skewCircleData_le`.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2IncrementVariableSpeed PathMetricCircle

namespace NormalPathC2IncrementSkewCircle

/-! ### The skew angle -/

/-- The skew reparametrization of the circle: `φ(u) = 2πu + a sin 2πu`. -/
def phi (a u : ℝ) : ℝ := 2 * Real.pi * u + a * Real.sin (2 * Real.pi * u)

/-- Its derivative. -/
def phi1 (a u : ℝ) : ℝ := 2 * Real.pi * (1 + a * Real.cos (2 * Real.pi * u))

/-- Its second derivative. -/
def phi2 (a u : ℝ) : ℝ := -(4 * Real.pi ^ 2 * a * Real.sin (2 * Real.pi * u))

theorem hasDerivAt_phi (a u : ℝ) : HasDerivAt (phi a) (phi1 a u) u := by
  have hlin : HasDerivAt (fun x : ℝ => 2 * Real.pi * x) (2 * Real.pi) u := by
    simpa using (hasDerivAt_id u).const_mul (2 * Real.pi)
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (2 * Real.pi * x))
      (Real.cos (2 * Real.pi * u) * (2 * Real.pi)) u := (Real.hasDerivAt_sin _).comp u hlin
  have h := hlin.add (hsin.const_mul a)
  refine h.congr_deriv ?_
  rw [phi1]; ring

theorem hasDerivAt_phi1 (a u : ℝ) : HasDerivAt (phi1 a) (phi2 a u) u := by
  have hlin : HasDerivAt (fun x : ℝ => 2 * Real.pi * x) (2 * Real.pi) u := by
    simpa using (hasDerivAt_id u).const_mul (2 * Real.pi)
  have hcos : HasDerivAt (fun x : ℝ => Real.cos (2 * Real.pi * x))
      (-Real.sin (2 * Real.pi * u) * (2 * Real.pi)) u := (Real.hasDerivAt_cos _).comp u hlin
  have h := ((hcos.const_mul a).const_add (1 : ℝ)).const_mul (2 * Real.pi)
  refine h.congr_deriv ?_
  rw [phi2]; ring

theorem abs_phi1_le (a u : ℝ) : |phi1 a u| ≤ 2 * Real.pi * (1 + |a|) := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [phi1, abs_mul, abs_of_nonneg hpi]
  refine mul_le_mul_of_nonneg_left ?_ hpi
  have h : |a * Real.cos (2 * Real.pi * u)| ≤ |a| := by
    rw [abs_mul]
    have := Real.abs_cos_le_one (2 * Real.pi * u)
    nlinarith [abs_nonneg a, abs_nonneg (Real.cos (2 * Real.pi * u))]
  calc |1 + a * Real.cos (2 * Real.pi * u)| ≤ |(1 : ℝ)| + |a * Real.cos (2 * Real.pi * u)| :=
        abs_add_le _ _
    _ ≤ 1 + |a| := by rw [abs_one]; linarith

theorem abs_phi2_le (a u : ℝ) : |phi2 a u| ≤ 4 * Real.pi ^ 2 * |a| := by
  rw [phi2, abs_neg, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.pi ^ 2)]
  have hs := Real.abs_sin_le_one (2 * Real.pi * u)
  have h0 : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * |a| := by positivity
  calc 4 * Real.pi ^ 2 * |a| * |Real.sin (2 * Real.pi * u)|
      ≤ 4 * Real.pi ^ 2 * |a| * 1 := mul_le_mul_of_nonneg_left hs h0
    _ = 4 * Real.pi ^ 2 * |a| := mul_one _

/-- The skew parametrization of the unit circle. -/
def skewExp (a u : ℝ) : ℂ := Complex.exp (Complex.I * ((phi a u : ℝ) : ℂ))

@[simp] theorem norm_skewExp (a u : ℝ) : ‖skewExp a u‖ = 1 := by
  rw [skewExp, Complex.norm_exp]; simp

theorem continuous_skewExp (a : ℝ) : Continuous (skewExp a) := by
  unfold skewExp phi
  fun_prop

theorem hasDerivAt_skewExp (a u : ℝ) :
    HasDerivAt (skewExp a) (Complex.I * ((phi1 a u : ℝ) : ℂ) * skewExp a u) u := by
  have h1 : HasDerivAt (fun v => Complex.I * ((phi a v : ℝ) : ℂ))
      (Complex.I * ((phi1 a u : ℝ) : ℂ)) u :=
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u (hasDerivAt_phi a u)).const_mul Complex.I
  simpa [skewExp, mul_comm] using h1.cexp

/-- The tangent of the skew parametrization, in the form `e^{i(φ+π/2)}`. -/
theorem exp_I_theta (a u : ℝ) :
    Complex.exp (Complex.I * ((phi a u + Real.pi / 2 : ℝ) : ℂ)) = Complex.I * skewExp a u := by
  have hsplit : Complex.I * ((phi a u + Real.pi / 2 : ℝ) : ℂ)
      = Complex.I * ((phi a u : ℝ) : ℂ) + Complex.I * ((Real.pi / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
    rw [show Complex.I * ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by ring,
      Complex.exp_mul_I]
    push_cast
    simp
  rw [hsplit, Complex.exp_add, h2, skewExp]
  ring

/-! ### The circle in the skew parametrization, as a marked datum -/

/-- The circle of radius `r`, read in the skew parametrization of rate `a`. -/
def skewCircleData (r a : ℝ) : Data :=
  (BoundedContinuousFunction.ofNormedAddCommGroup (fun u => (r : ℂ) * skewExp a u)
      (by exact continuous_const.mul (continuous_skewExp a)) |r| (fun u => by simp),
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun u => ((r * phi1 a u : ℝ) : ℂ) * Complex.I * skewExp a u)
      (by
        refine Continuous.mul (Continuous.mul ?_ continuous_const) (continuous_skewExp a)
        refine Complex.continuous_ofReal.comp ?_
        unfold phi1
        fun_prop)
      (|r| * (2 * Real.pi * (1 + |a|)))
      (fun u => by
        rw [norm_mul, norm_mul, norm_skewExp, mul_one, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_phi1_le a u) (abs_nonneg r)),
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun u => (((r * phi2 a u : ℝ) : ℂ) * Complex.I - ((r * phi1 a u ^ 2 : ℝ) : ℂ))
        * skewExp a u)
      (by
        refine Continuous.mul (Continuous.sub (Continuous.mul ?_ continuous_const) ?_)
          (continuous_skewExp a)
        · refine Complex.continuous_ofReal.comp ?_
          unfold phi2
          fun_prop
        · refine Complex.continuous_ofReal.comp ?_
          unfold phi1
          fun_prop)
      (|r| * (4 * Real.pi ^ 2 * |a|) + |r| * (2 * Real.pi * (1 + |a|)) ^ 2)
      (fun u => by
        rw [norm_mul, norm_skewExp, mul_one]
        refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
        · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_phi2_le a u) (abs_nonneg r)
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg r)
          have h := abs_phi1_le a u
          nlinarith [abs_nonneg (phi1 a u)]))

@[simp] theorem skewCircleData_fst (r a u : ℝ) :
    (skewCircleData r a).1 u = (r : ℂ) * skewExp a u := rfl

@[simp] theorem skewCircleData_vel (r a u : ℝ) :
    (skewCircleData r a).2.1 u = ((r * phi1 a u : ℝ) : ℂ) * Complex.I * skewExp a u := rfl

@[simp] theorem skewCircleData_acc (r a u : ℝ) :
    (skewCircleData r a).2.2 u
      = (((r * phi2 a u : ℝ) : ℂ) * Complex.I - ((r * phi1 a u ^ 2 : ℝ) : ℂ))
          * skewExp a u := rfl

theorem hasDerivAt_skewCircleData_curve (r a u : ℝ) :
    HasDerivAt (⇑(skewCircleData r a).1) ((skewCircleData r a).2.1 u) u := by
  have h : HasDerivAt (fun v => (r : ℂ) * skewExp a v)
      ((r : ℂ) * (Complex.I * ((phi1 a u : ℝ) : ℂ) * skewExp a u)) u :=
    (hasDerivAt_skewExp a u).const_mul (r : ℂ)
  have hfun : ⇑(skewCircleData r a).1 = fun v => (r : ℂ) * skewExp a v := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  rw [skewCircleData_vel]
  push_cast
  ring

theorem hasDerivAt_skewCircleData_vel (r a u : ℝ) :
    HasDerivAt (⇑(skewCircleData r a).2.1) ((skewCircleData r a).2.2 u) u := by
  have hfun : ⇑(skewCircleData r a).2.1
      = fun v => ((r * phi1 a v : ℝ) : ℂ) * Complex.I * skewExp a v := rfl
  have hc : HasDerivAt (fun v => ((r * phi1 a v : ℝ) : ℂ) * Complex.I)
      (((r * phi2 a u : ℝ) : ℂ) * Complex.I) u := by
    have h1 : HasDerivAt (fun v => ((r * phi1 a v : ℝ) : ℂ)) ((r * phi2 a u : ℝ) : ℂ) u := by
      exact ((hasDerivAt_phi1 a u).const_mul r).ofReal_comp
    exact h1.mul_const Complex.I
  have h := hc.mul (hasDerivAt_skewExp a u)
  rw [hfun]
  refine h.congr_deriv ?_
  rw [skewCircleData_acc]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ### The dilation in the skew parametrization -/

/-- **The radial dilation, read in the skew parametrization.**  The circles move
with purely radial — hence normal — velocity, exactly as in
`PathMetricCircle.dilation`; only the parametrization of the slices differs, and
it is no longer a constant-speed one. -/
def skewDilation (r R a : ℝ) : NormalPath (skewCircleData r a) (skewCircleData R a) where
  T := 1
  T_pos := one_pos
  X := fun t u => ((r + (R - r) * B t : ℝ) : ℂ) * skewExp a u
  eta := fun t _ => (R - r) * w t
  nu := fun _ u => skewExp a u
  m := fun t => |R - r| * w t
  start := fun u => by simp
  finish := fun u => by simp
  hasDerivAt_time := by
    intro t u
    have hB : HasDerivAt (fun s => r + (R - r) * B s) ((R - r) * w t) t :=
      (((hasDerivAt_B t).const_mul (R - r)).const_add r)
    simpa using (hB.ofReal_comp.mul_const (skewExp a u))
  cont_vel := fun u => by
    have h : Continuous fun t : ℝ => ((R - r) * w t : ℝ) := continuous_const.mul continuous_w
    exact (Complex.continuous_ofReal.comp h).mul continuous_const
  norm_nu := fun _ u => norm_skewExp a u
  cont_m := continuous_const.mul continuous_w
  m_nonneg := fun t => mul_nonneg (abs_nonneg _) (w_nonneg t)
  m_stop := fun t ht => by rw [w_eq_zero ht, mul_zero]
  abs_eta_le := fun t _ => by
    rw [abs_mul, abs_of_nonneg (w_nonneg t)]
  le_m_L1 := fun t => by
    have h : (∫ _u in (0:ℝ)..1, |(R - r) * w t|) = |(R - r) * w t| := by simp
    rw [h, abs_mul, abs_of_nonneg (w_nonneg t)]
  le_m_sup := fun t j _ => by
    match j with
    | 0 =>
      rw [iteratedDeriv_zero, supNorm_const, abs_mul, abs_of_nonneg (w_nonneg t)]
    | (n + 1) =>
      rw [iteratedDeriv_succ_const, supNorm_const]
      simpa using mul_nonneg (abs_nonneg (R - r)) (w_nonneg t)

theorem cost_skewDilation (r R a : ℝ) : cost (skewDilation r R a) = |R - r| := by
  have h : cost (skewDilation r R a) = ∫ t in (0:ℝ)..1, |R - r| * w t := rfl
  rw [h, intervalIntegral.integral_const_mul, integral_w, mul_one]

/-! ### The path has slices of variable speed -/

/-- The radius of the dilation at time `t`. -/
def rad (r R t : ℝ) : ℝ := r + (R - r) * B t

theorem rad_ge_one (t : ℝ) : 1 ≤ rad 1 2 t := by
  have h0 := B_nonneg t
  rw [rad]; norm_num; linarith

theorem rad_le_two (t : ℝ) : rad 1 2 t ≤ 2 := by
  have h1 := B_le_one t
  rw [rad]; norm_num; linarith

theorem rad_pos (t : ℝ) : 0 < rad 1 2 t := lt_of_lt_of_le one_pos (rad_ge_one t)

theorem continuous_rad (r R : ℝ) : Continuous (rad r R) := by
  unfold rad
  exact continuous_const.add (continuous_const.mul continuous_B)

theorem hasDerivAt_rad (r R t : ℝ) : HasDerivAt (rad r R) ((R - r) * w t) t :=
  ((hasDerivAt_B t).const_mul (R - r)).const_add r

theorem phi1_half_nonneg (u : ℝ) : 0 ≤ phi1 (1 / 2) u := by
  have hpi := Real.pi_pos
  have hc : -1 ≤ Real.cos (2 * Real.pi * u) := Real.neg_one_le_cos _
  rw [phi1]
  nlinarith

theorem phi1_half_le (u : ℝ) : phi1 (1 / 2) u ≤ 3 * Real.pi := by
  have hpi := Real.pi_pos
  have hc : Real.cos (2 * Real.pi * u) ≤ 1 := Real.cos_le_one _
  rw [phi1]
  nlinarith

theorem abs_phi2_half (u : ℝ) : |phi2 (1 / 2) u| ≤ 2 * Real.pi ^ 2 := by
  have h := abs_phi2_le (1 / 2 : ℝ) u
  rw [show |(1 / 2 : ℝ)| = 1 / 2 by norm_num] at h
  linarith

theorem m_skewDilation (r R a t : ℝ) : (skewDilation r R a).m t = |R - r| * w t := rfl

/-- **The skew dilation from the unit circle to the circle of radius two has
slices of variable speed**, with the explicit constants
`P₀ = 1`, `P₁ = 6π`, `κ̂ = 1`, `G₁ = 4π²`, `C_g = 2π²`.  In particular the
hypothesis block of `dist_le_cost_variableSpeed` is satisfiable with a speed
that really depends on the parameter. -/
theorem isVariableSpeedNormalPath_skewDilation :
    IsVariableSpeedNormalPath 1 (6 * Real.pi) 1 (4 * Real.pi ^ 2) (2 * Real.pi ^ 2)
      (skewDilation 1 2 (1 / 2)) := by
  have hpi := Real.pi_pos
  have hm : ∀ t, (skewDilation 1 2 (1 / 2)).m t = w t := by
    intro t
    rw [m_skewDilation]
    norm_num
  refine ⟨fun t u => rad 1 2 t * phi1 (1/2) u, fun t u => rad 1 2 t * phi2 (1/2) u,
    fun t u => w t * phi1 (1/2) u, fun t u => w t * phi2 (1/2) u,
    fun _ u => phi (1/2) u + Real.pi / 2, fun t _ => (rad 1 2 t)⁻¹,
    fun _ _ => 0, fun t _ => -(w t) / rad 1 2 t ^ 2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun t u => mul_nonneg (rad_pos t).le (phi1_half_nonneg u)
  · intro t u
    nlinarith [rad_le_two t, rad_pos t, phi1_half_le u, phi1_half_nonneg u]
  · intro t u
    rw [abs_mul, abs_of_pos (rad_pos t)]
    have h1 := abs_phi2_half u
    have h2 := rad_le_two t
    nlinarith [abs_nonneg (phi2 (1/2) u), rad_pos t, sq_nonneg Real.pi]
  · intro t u
    rw [abs_of_pos (inv_pos.2 (rad_pos t))]
    rw [inv_le_one_iff₀]
    exact Or.inr (rad_ge_one t)
  · intro t u
    have hX : (skewDilation 1 2 (1 / 2)).X t
        = fun v => ((rad 1 2 t : ℝ) : ℂ) * skewExp (1/2) v := rfl
    rw [hX]
    have h := (hasDerivAt_skewExp (1/2) u).const_mul ((rad 1 2 t : ℝ) : ℂ)
    refine h.congr_deriv ?_
    rw [exp_I_theta]
    push_cast
    ring
  · exact fun t u => (hasDerivAt_phi1 (1/2) u).const_mul (rad 1 2 t)
  · intro t u
    have h := hasDerivAt_phi (1/2) u
    have h2 : HasDerivAt (fun v => phi (1/2) v + Real.pi / 2) (phi1 (1/2) u) u :=
      h.add_const (Real.pi / 2)
    refine h2.congr_deriv ?_
    field_simp
    rw [mul_div_assoc, div_self (rad_pos t).ne', mul_one]
  · intro t u
    exact (hasDerivAt_rad 1 2 t).mul_const (phi1 (1/2) u) |>.congr_deriv (by norm_num)
  · exact fun u => continuous_w.mul continuous_const
  · intro t u
    rw [hm, abs_mul, abs_of_nonneg (w_nonneg t), abs_of_nonneg (phi1_half_nonneg u)]
    nlinarith [w_nonneg t, phi1_half_le u]
  · intro t u
    exact (hasDerivAt_rad 1 2 t).mul_const (phi2 (1/2) u) |>.congr_deriv (by norm_num)
  · exact fun u => continuous_w.mul continuous_const
  · intro t u
    rw [hm, abs_mul, abs_of_nonneg (w_nonneg t)]
    nlinarith [w_nonneg t, abs_phi2_half u]
  · exact fun t u => hasDerivAt_const t _
  · exact fun u => continuous_const
  · intro t u
    rw [hm, abs_zero]
    nlinarith [w_nonneg t]
  · intro t u
    exact ((hasDerivAt_rad 1 2 t).inv (rad_pos t).ne').congr_deriv (by norm_num)
  · intro u
    refine Continuous.div (continuous_neg.comp continuous_w)
      ((continuous_rad 1 2).pow 2) fun t => ?_
    exact ne_of_gt (pow_pos (rad_pos t) 2)
  · intro t u
    rw [hm, abs_div, abs_neg, abs_of_nonneg (w_nonneg t),
      abs_of_pos (pow_pos (rad_pos t) 2)]
    have h1 : 1 ≤ rad 1 2 t ^ 2 := by nlinarith [rad_ge_one t]
    have h2 : w t / rad 1 2 t ^ 2 ≤ w t := by
      rw [div_le_iff₀ (pow_pos (rad_pos t) 2)]
      nlinarith [w_nonneg t]
    nlinarith [w_nonneg t]

/-! ### The resulting marked distance bound -/

theorem skewExp_zero (a : ℝ) : skewExp a 0 = 1 := by
  have h : phi a 0 = 0 := by rw [phi]; simp
  rw [skewExp, h]
  simp

/-- The two ends are genuinely distinct: their marked distance is at least `1`.
-/
theorem one_le_dist_skewCircleData :
    1 ≤ dist (skewCircleData 1 (1 / 2)) (skewCircleData 2 (1 / 2)) := by
  have h0 : dist ((skewCircleData 1 (1/2)).1 0) ((skewCircleData 2 (1/2)).1 0) = 1 := by
    rw [skewCircleData_fst, skewCircleData_fst, skewExp_zero, mul_one, mul_one,
      Complex.dist_eq]
    norm_num
  have h1 : (1 : ℝ) ≤ dist (skewCircleData 1 (1/2)).1 (skewCircleData 2 (1/2)).1 := by
    have hle := BoundedContinuousFunction.dist_coe_le_dist
      (f := (skewCircleData 1 (1/2)).1) (g := (skewCircleData 2 (1/2)).1) 0
    rwa [h0] at hle
  refine le_trans h1 ?_
  rw [Prod.dist_eq]
  exact le_max_left _ _

/-- **The marked distance of the two skew circles is at most the constant of the
variable-speed increment times the cost of the dilation joining them.**  The
cost is `1`, and the left-hand side is at least `1`, so the estimate is applied
here to a pair of genuinely distinct marked curves along a path of nonzero cost,
with slices whose speed really depends on the parameter. -/
theorem dist_skewCircleData_le :
    dist (skewCircleData 1 (1 / 2)) (skewCircleData 2 (1 / 2))
      ≤ c2ConstVar 1 (6 * Real.pi) 1 (4 * Real.pi ^ 2) (2 * Real.pi ^ 2) := by
  have h := dist_le_cost_variableSpeed (skewDilation 1 2 (1 / 2))
    (fun u => hasDerivAt_skewCircleData_curve 1 (1/2) u)
    (fun u => hasDerivAt_skewCircleData_curve 2 (1/2) u)
    (fun u => hasDerivAt_skewCircleData_vel 1 (1/2) u)
    (fun u => hasDerivAt_skewCircleData_vel 2 (1/2) u)
    isVariableSpeedNormalPath_skewDilation
  rwa [cost_skewDilation, show |(2 : ℝ) - 1| = 1 by norm_num, mul_one] at h

end NormalPathC2IncrementSkewCircle
