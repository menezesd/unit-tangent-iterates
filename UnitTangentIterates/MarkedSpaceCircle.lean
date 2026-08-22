import Mathlib
import UnitTangentIterates.MarkedSpace

/-!
# Circles are marked curves: the tube of `MarkedSpace.lean` is not empty

`MarkedSpace.lean` constructs the space of marked curves of the shadowing
scheme of *A Noncircular Oval with Convex Unit-Tangent Iterates* as a tube
`tube c kmin delta` of closed `C²` curves in the normalized parameter, and
shows that it is a complete metric space all of whose members are ovals.  This
file checks that the tube is inhabited, by exhibiting the standard example: the
circle of radius `r`, in the normalized parameter

```
  X(u) = r e^{2πiu},   V = X' ,   A = V' ,
```

belongs to `tube (2πr) (1/r) (4r)` — its perimeter is `2πr`, its curvature is
`1/r`, and its chord-arc constant is `4r`.

Main results:

* `norm_exp_mul_I_sub_one` : `|e^{iθ} − 1| = 2|sin(θ/2)|`;
* `two_min_le_sin` : `2·min(a, 1−a) ≤ sin(πa)` for `a ∈ [0,1]`, the concavity
  bound giving the chord-arc constant of a circle;
* `circleData_mem_tube` : the circle of radius `r` lies in `tube (2πr) (1/r)
  (4r)`;
* `tube_nonempty` : the tube of the marked space is nonempty.
-/

noncomputable section

open Set Function Filter Topology
open scoped BoundedContinuousFunction

namespace MarkedSpace

/-! ### Two elementary estimates -/

/-- The chord of the unit circle: `|e^{iθ} − 1| = 2|sin(θ/2)|`. -/
theorem norm_exp_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have hsq : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 = 2 - 2 * Real.cos θ := by
    rw [Complex.exp_mul_I, Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h2 := Real.sin_sq_add_cos_sq (θ / 2)
    have h3 : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
      have h := Real.cos_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at h
      exact h
    nlinarith
  have h2 : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 = (2 * |Real.sin (θ / 2)|) ^ 2 := by
    rw [hsq, hcos, mul_pow, sq_abs]; ring
  have hnn1 : (0 : ℝ) ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ := norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ 2 * |Real.sin (θ / 2)| := by positivity
  nlinarith [h2, hnn1, hnn2]

/-- **The concavity bound** `sin(πa) ≥ 2·min(a, 1−a)` on `[0,1]`: the chord of
the unit circle subtending an arc `a` is at least `2·min(a,1−a)`. -/
theorem two_min_le_sin (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    2 * min a (1 - a) ≤ Real.sin (Real.pi * a) := by
  rcases le_or_gt a (1 / 2) with h | h
  · have hmin : min a (1 - a) = a := min_eq_left (by linarith)
    rw [hmin]
    have hb := Real.mul_le_sin (x := Real.pi * a) (by positivity) (by nlinarith [Real.pi_pos])
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    calc 2 * a = 2 / Real.pi * (Real.pi * a) := by field_simp
      _ ≤ Real.sin (Real.pi * a) := hb
  · have hmin : min a (1 - a) = 1 - a := min_eq_right (by linarith)
    rw [hmin]
    have hs : Real.sin (Real.pi * a) = Real.sin (Real.pi * (1 - a)) := by
      rw [show Real.pi * (1 - a) = Real.pi - Real.pi * a by ring, Real.sin_pi_sub]
    rw [hs]
    have hb := Real.mul_le_sin (x := Real.pi * (1 - a)) (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    calc 2 * (1 - a) = 2 / Real.pi * (Real.pi * (1 - a)) := by field_simp
      _ ≤ _ := hb

/-- `|sin(πd)| = sin(π|d|)` for `|d| ≤ 1`. -/
theorem abs_sin_pi_mul {d : ℝ} (h : |d| ≤ 1) :
    |Real.sin (Real.pi * d)| = Real.sin (Real.pi * |d|) := by
  rcases le_or_gt 0 d with hd | hd
  · rw [abs_of_nonneg hd]
    refine abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_)
    rw [abs_of_nonneg hd] at h
    nlinarith [Real.pi_pos]
  · rw [abs_of_neg hd]
    have hd' : Real.pi * d = -(Real.pi * -d) := by ring
    rw [hd', Real.sin_neg, abs_neg]
    refine abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) ?_)
    rw [abs_of_neg hd] at h
    nlinarith [Real.pi_pos]

/-! ### The normalized exponential -/

/-- The unit circle traversed once as `u` runs over a period: `e(u) = e^{2πiu}`. -/
def normExp (u : ℝ) : ℂ := Complex.exp (2 * Real.pi * (u : ℂ) * Complex.I)

theorem normExp_eq (u : ℝ) : normExp u = Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I) := by
  rw [normExp]
  congr 1
  push_cast
  ring

@[simp] theorem norm_normExp (u : ℝ) : ‖normExp u‖ = 1 := by
  rw [normExp_eq, Complex.norm_exp_ofReal_mul_I]

theorem continuous_normExp : Continuous normExp := by unfold normExp; fun_prop

theorem hasDerivAt_normExp (u : ℝ) :
    HasDerivAt normExp (2 * Real.pi * Complex.I * normExp u) u := by
  have h : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
  have h2 : HasDerivAt (fun u : ℝ => 2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))
      (2 * (Real.pi : ℂ) * Complex.I) u := by
    simpa using h.const_mul (2 * (Real.pi : ℂ) * Complex.I)
  have h3 := h2.cexp
  have he : (fun u : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))) = normExp := by
    funext u; rw [normExp]; ring_nf
  rw [he] at h3
  have hv : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ)) = normExp u := by
    rw [normExp]; ring_nf
  rw [hv] at h3
  convert h3 using 1
  ring

theorem conj_mul_normExp (u : ℝ) : (starRingEnd ℂ) (normExp u) * normExp u = 1 := by
  rw [mul_comm, Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq, norm_normExp u]
  norm_num

theorem periodic_normExp : Periodic normExp 1 := by
  intro u
  rw [normExp, normExp,
    show (2 * (Real.pi : ℂ) * ((u + 1 : ℝ) : ℂ) * Complex.I)
      = 2 * (Real.pi : ℂ) * (u : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add]
  have h2pi : Complex.exp (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
    simpa [mul_comm] using Complex.exp_two_pi_mul_I
  rw [h2pi, mul_one]

theorem normExp_sub (u v : ℝ) : normExp u - normExp v = normExp v * (normExp (u - v) - 1) := by
  have hmul : normExp u = normExp v * normExp (u - v) := by
    rw [normExp, normExp, normExp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hmul]
  ring

/-! ### The circle as a member of the tube -/

/-- The circle of radius `r`, in the normalized parameter, as marked data. -/
def circleData (r : ℝ) : Data :=
  (BoundedContinuousFunction.ofNormedAddCommGroup (fun u => (r : ℂ) * normExp u)
      (by unfold normExp; fun_prop) |r| (fun u => by simp),
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun u => ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I * normExp u)
      (by unfold normExp; fun_prop) |2 * Real.pi * r| (fun u => by simp),
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun u => -((4 * Real.pi ^ 2 * r : ℝ) : ℂ) * normExp u)
      (by unfold normExp; fun_prop) |4 * Real.pi ^ 2 * r| (fun u => by simp))

@[simp] theorem circleData_fst (r u : ℝ) : (circleData r).1 u = (r : ℂ) * normExp u := rfl

@[simp] theorem circleData_vel (r u : ℝ) :
    (circleData r).2.1 u = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I * normExp u := rfl

@[simp] theorem circleData_acc (r u : ℝ) :
    (circleData r).2.2 u = -((4 * Real.pi ^ 2 * r : ℝ) : ℂ) * normExp u := rfl

/-- **The circle of radius `r` is a marked curve**: it lies in the tube with
perimeter `2πr`, curvature `1/r` and chord-arc constant `4r`. -/
theorem circleData_mem_tube {r : ℝ} (hr : 0 < r) :
    circleData r ∈ tube (2 * Real.pi * r) (1 / r) (4 * r) := by
  have hpi := Real.pi_pos
  have hspeed : ∀ u : ℝ, ‖(circleData r).2.1 u‖ = 2 * Real.pi * r := by
    intro u
    rw [circleData_vel]
    simp [abs_of_pos hpi, abs_of_pos hr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `X' = V`
    intro u
    have h := (hasDerivAt_normExp u).const_mul (r : ℂ)
    have hfun : ⇑(circleData r).1 = fun u : ℝ => (r : ℂ) * normExp u := rfl
    rw [hfun]
    convert h using 1
    rw [circleData_vel]
    push_cast
    ring
  · -- `V' = A`
    intro u
    have h := (hasDerivAt_normExp u).const_mul (((2 * Real.pi * r : ℝ) : ℂ) * Complex.I)
    have hfun : ⇑(circleData r).2.1
        = fun u : ℝ => ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I * normExp u := rfl
    rw [hfun]
    convert h using 1
    rw [circleData_acc]
    push_cast
    linear_combination (-(4 * (Real.pi : ℂ) ^ 2 * (r : ℂ) * normExp u)) * Complex.I_sq
  · -- periodicity
    intro u
    simp only [circleData_fst]
    rw [periodic_normExp u]
  · -- constant speed
    intro u v
    rw [hspeed u, hspeed v]
  · -- speed bounded below
    intro u
    rw [hspeed u]
  · -- curvature
    intro u
    rw [hspeed u]
    have hconj : (starRingEnd ℂ) ((circleData r).2.1 u) * (circleData r).2.2 u
        = ((8 * Real.pi ^ 3 * r ^ 2 : ℝ) : ℂ) * Complex.I := by
      rw [circleData_vel, circleData_acc]
      have hEE := conj_mul_normExp u
      have hstep : (starRingEnd ℂ) (((2 * Real.pi * r : ℝ) : ℂ) * Complex.I * normExp u)
          * (-((4 * Real.pi ^ 2 * r : ℝ) : ℂ) * normExp u)
          = ((starRingEnd ℂ) (((2 * Real.pi * r : ℝ) : ℂ) * Complex.I)
              * -((4 * Real.pi ^ 2 * r : ℝ) : ℂ)) * ((starRingEnd ℂ) (normExp u) * normExp u) := by
        rw [map_mul]
        ring
      rw [hstep, hEE, mul_one, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    rw [hconj]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    have hval : 1 / r * (2 * Real.pi * r) ^ 3 = 8 * Real.pi ^ 3 * r ^ 2 := by
      field_simp
      ring
    rw [hval]
    linarith
  · -- the chord-arc bound
    intro u hu v hv
    have hd : |u - v| ≤ 1 := by
      rcases hu with ⟨hu0, hu1⟩
      rcases hv with ⟨hv0, hv1⟩
      rw [abs_le]
      constructor <;> linarith
    have hchord : ‖(circleData r).1 u - (circleData r).1 v‖
        = r * (2 * |Real.sin (Real.pi * (u - v))|) := by
      simp only [circleData_fst]
      rw [show (r : ℂ) * normExp u - (r : ℂ) * normExp v = (r : ℂ) * (normExp u - normExp v) by
        ring, normExp_sub u v]
      rw [normExp_eq (u - v)]
      rw [norm_mul, norm_mul, norm_normExp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr, one_mul, norm_exp_mul_I_sub_one]
      congr 2
      ring_nf
    rw [hchord, cyc]
    have hsin : 2 * min |u - v| (1 - |u - v|) ≤ |Real.sin (Real.pi * (u - v))| := by
      rw [abs_sin_pi_mul hd]
      exact two_min_le_sin _ (abs_nonneg _) hd
    nlinarith [abs_nonneg (Real.sin (Real.pi * (u - v)))]

/-- **The space of marked curves is not empty.** -/
theorem tube_nonempty {r : ℝ} (hr : 0 < r) :
    (tube (2 * Real.pi * r) (1 / r) (4 * r)).Nonempty :=
  ⟨circleData r, circleData_mem_tube hr⟩

/-- The perimeter of the circle of radius `r`, as a member of the marked space,
is `2πr`. -/
theorem perim_circleData {r : ℝ} (hr : 0 < r) : perim (circleData r) = 2 * Real.pi * r := by
  rw [perim, circleData_vel]
  simp [abs_of_pos Real.pi_pos, abs_of_pos hr]

end MarkedSpace
