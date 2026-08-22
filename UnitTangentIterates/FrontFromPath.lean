import Mathlib
import UnitTangentIterates.RearOwnPathDistSlices

/-!
# The family of fronts of a normal path

`RearOwnPathDistSlices.pathDist_le_of_front_slices` bounds the path
pseudodistance of the selected rears of a path of fronts, the only remaining
link between the normal path `Γ` of the path metric and the family of fronts
being the *geometric identification of the slices*

```
  X(t, u) = F(t, P(t) u) ,        ν(t, u) = i e^{iΘ(t, P(t) u)} .
```

This file produces that identification from intrinsic data of the path.  A
slice of a normal path in the space of marked curves is a closed curve of
period one in the normalized parameter, of constant speed `P t` (the
perimeter); rescaling the parameter by the perimeter,

```
  F(t, s) = X(t, s / P t) ,
```

gives the same curve written in its own arclength, and the tangent-angle
lifting of `MarkedSpace.exists_angle` turns its unit tangent into `e^{iΘ}`.
The only global input is the **turning number**: the total turning of a slice
is `2π`, which is carried — following the convention of the project — as an
explicit hypothesis on the given frame data.

Main results.

* `frontOfPath`, `angleOfPath` : the front family and the tangent angle of a
  path, in the arclength of each slice;
* `hasDerivAt_frontOfPath_tangent`, `exp_angleOfPath` : `∂_s F = e^{iΘ}`, i.e.
  `F t` is unit speed of tangent angle `Θ t`;
* `periodic_frontOfPath`, `angleOfPath_add_period` : `F t` has period `P t` and
  the angle increases by `2π` over one period;
* `exists_front_of_path` : the packaged statement — a normal path whose slices
  are closed constant-speed curves of turning number one, moving along their
  standard unit normal, *is* a path of fronts in the sense of the geometric
  identification above;
* `pathDist_le_of_path_intrinsic` : the resulting path-distance bound for the
  selected rears, in which the front family, its tangent angle and its
  curvature are the canonical ones attached to the path, so that the geometric
  identification of the slices is discharged.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace PathMetric
  PathMetric.NormalPath

namespace FrontFromPath

/-- The front family of a path of closed curves: the slice at time `t`, written
in its own arclength, the normalized parameter being rescaled by the perimeter
`P t`. -/
def frontOfPath (X : ℝ → ℝ → ℂ) (P : ℝ → ℝ) : ℝ → ℝ → ℂ := fun t s => X t (s / P t)

/-- The unit tangent of the slice at time `t`, in its own arclength. -/
def tangentOfPath (V : ℝ → ℝ → ℂ) (P : ℝ → ℝ) : ℝ → ℝ → ℂ :=
  fun t s => V t (s / P t) / (P t : ℂ)

/-- The curvature of the slice at time `t`, in its own arclength. -/
def curvOfPath (V A : ℝ → ℝ → ℂ) (P : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t s => ((starRingEnd ℂ) (V t (s / P t)) * A t (s / P t)).im / P t ^ 3

/-- The tangent angle of the slice at time `t`, in its own arclength: the
primitive of the curvature normalized by the argument of the tangent at the
marked point. -/
def angleOfPath (V A : ℝ → ℝ → ℂ) (P : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t s => (tangentOfPath V P t 0).arg + ∫ x in (0 : ℝ)..s, curvOfPath V A P t x

variable {X V A : ℝ → ℝ → ℂ} {P : ℝ → ℝ}

section Slice

variable {t : ℝ}

theorem norm_tangentOfPath (hspeed : ∀ u, ‖V t u‖ = P t) (hP : 0 < P t) (s : ℝ) :
    ‖tangentOfPath V P t s‖ = 1 := by
  rw [tangentOfPath, norm_div, hspeed]
  simp [abs_of_pos hP, hP.ne']

/-- The arclength derivative of the slice is its unit tangent. -/
theorem hasDerivAt_frontOfPath_tangent (hV : ∀ u, HasDerivAt (X t) (V t u) u) (hP : 0 < P t)
    (s : ℝ) : HasDerivAt (frontOfPath X P t) (tangentOfPath V P t s) s := by
  have hdiv : HasDerivAt (fun s : ℝ => s / P t) (1 / P t) s := by
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id s).div_const (P t)
  have h := (hV (s / P t)).scomp s hdiv
  refine h.congr_deriv ?_
  have hPne : (P t : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  simp [tangentOfPath, div_eq_mul_inv]
  ring

/-- The arclength derivative of the unit tangent. -/
theorem hasDerivAt_tangentOfPath (hA : ∀ u, HasDerivAt (V t) (A t u) u) (hP : 0 < P t) (s : ℝ) :
    HasDerivAt (tangentOfPath V P t) (A t (s / P t) / (P t : ℂ) ^ 2) s := by
  have hdiv : HasDerivAt (fun s : ℝ => s / P t) (1 / P t) s := by
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id s).div_const (P t)
  have h := ((hA (s / P t)).scomp s hdiv).div_const (P t : ℂ)
  refine h.congr_deriv ?_
  have hPne : (P t : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  simp [div_eq_mul_inv]
  ring

theorem continuous_curvOfPath (hVcont : Continuous (V t)) (hAcont : Continuous (A t)) :
    Continuous (curvOfPath V A P t) := by
  have h1 : Continuous fun x : ℝ => (starRingEnd ℂ) (V t (x / P t)) * A t (x / P t) :=
    (Complex.continuous_conj.comp (hVcont.comp (continuous_id.div_const _))).mul
      (hAcont.comp (continuous_id.div_const _))
  exact (Complex.continuous_im.comp h1).div_const _

theorem hasDerivAt_angleOfPath (hcont : Continuous (curvOfPath V A P t)) (s : ℝ) :
    HasDerivAt (angleOfPath V A P t) (curvOfPath V A P t s) s := by
  have h := (hcont.integral_hasStrictDerivAt 0 s).hasDerivAt
  have he : angleOfPath V A P t
      = fun s => (tangentOfPath V P t 0).arg + ∫ x in (0 : ℝ)..s, curvOfPath V A P t x := rfl
  rw [he]
  simpa using h.const_add ((tangentOfPath V P t 0).arg)

/-- The angular velocity of the unit tangent is the curvature. -/
theorem im_conj_tangent_mul (hP : 0 < P t) (x : ℝ) :
    ((starRingEnd ℂ) (tangentOfPath V P t x) * (A t (x / P t) / (P t : ℂ) ^ 2)).im
      = curvOfPath V A P t x := by
  have hPne : (P t : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  have hcast : (starRingEnd ℂ) (tangentOfPath V P t x) * (A t (x / P t) / (P t : ℂ) ^ 2)
      = ((starRingEnd ℂ) (V t (x / P t)) * A t (x / P t)) / ((P t : ℂ) ^ 3) := by
    rw [tangentOfPath, map_div₀, Complex.conj_ofReal]
    field_simp
  rw [hcast, curvOfPath,
    show ((P t : ℂ) ^ 3) = ((P t ^ 3 : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im]

/-- **The tangent angle lifts the unit tangent**: `e^{iΘ} = τ`. -/
theorem exp_angleOfPath (hA : ∀ u, HasDerivAt (V t) (A t u) u) (hAcont : Continuous (A t))
    (hVcont : Continuous (V t)) (hspeed : ∀ u, ‖V t u‖ = P t) (hP : 0 < P t) (s : ℝ) :
    Complex.exp (Complex.I * (angleOfPath V A P t s : ℂ)) = tangentOfPath V P t s := by
  have hDcont : Continuous fun s : ℝ => A t (s / P t) / (P t : ℂ) ^ 2 :=
    (hAcont.comp (continuous_id.div_const _)).div_const _
  -- the abstract lifting
  obtain ⟨theta, hth, hexp⟩ :=
    MarkedSpace.exists_angle (tau := tangentOfPath V P t)
      (D := fun s => A t (s / P t) / (P t : ℂ) ^ 2)
      (fun s => norm_tangentOfPath hspeed hP s) (fun s => hasDerivAt_tangentOfPath hA hP s) hDcont
  have hthd : ∀ x, HasDerivAt theta (curvOfPath V A P t x) x := fun x => by
    simpa [im_conj_tangent_mul (V := V) (A := A) hP x] using hth x
  have hcurvcont : Continuous (curvOfPath V A P t) := continuous_curvOfPath hVcont hAcont
  -- the two angles differ by a constant
  have hdiffconst : ∀ x, angleOfPath V A P t x - theta x = angleOfPath V A P t 0 - theta 0 := by
    intro x
    have hderiv : ∀ y : ℝ, HasDerivAt (fun z => angleOfPath V A P t z - theta z) 0 y := fun y => by
      simpa using (hasDerivAt_angleOfPath hcurvcont y).sub (hthd y)
    exact is_const_of_deriv_eq_zero (fun y => (hderiv y).differentiableAt)
      (fun y => (hderiv y).deriv) x 0
  -- and the constant is a multiple of `2π`, since both lift the tangent at `0`
  have harg : Complex.exp (Complex.I * ((tangentOfPath V P t 0).arg : ℂ))
      = tangentOfPath V P t 0 := by
    have h := Complex.norm_mul_exp_arg_mul_I (tangentOfPath V P t 0)
    rw [norm_tangentOfPath hspeed hP 0] at h
    rw [mul_comm]
    simpa using h
  have h0 : Complex.exp (Complex.I * ((angleOfPath V A P t 0 : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((theta 0 : ℝ) : ℂ)) := by
    have hzero : angleOfPath V A P t 0 = (tangentOfPath V P t 0).arg := by
      simp [angleOfPath]
    rw [hzero, harg, hexp 0]
  have hconst : Complex.exp (Complex.I * ((angleOfPath V A P t 0 - theta 0 : ℝ) : ℂ)) = 1 := by
    rw [show ((angleOfPath V A P t 0 - theta 0 : ℝ) : ℂ)
        = ((angleOfPath V A P t 0 : ℝ) : ℂ) - ((theta 0 : ℝ) : ℂ) by push_cast; ring,
      mul_sub, Complex.exp_sub, h0]
    exact div_self (Complex.exp_ne_zero _)
  have hsplit : ((angleOfPath V A P t s : ℝ) : ℂ)
      = ((theta s : ℝ) : ℂ) + ((angleOfPath V A P t 0 - theta 0 : ℝ) : ℂ) := by
    have h : angleOfPath V A P t s = theta s + (angleOfPath V A P t 0 - theta 0) := by
      have := hdiffconst s; linarith
    rw [h]; push_cast; ring
  rw [hsplit, mul_add, Complex.exp_add, hconst, mul_one, hexp s]

end Slice

/-! ### Periodicity -/

theorem periodic_frontOfPath {t : ℝ} (hXper : Periodic (X t) 1) (hP : 0 < P t) (s : ℝ) :
    frontOfPath X P t (s + P t) = frontOfPath X P t s := by
  have h : (s + P t) / P t = s / P t + 1 := by field_simp
  rw [frontOfPath, frontOfPath, h, hXper]

theorem curvOfPath_periodic {t : ℝ} (hVper : Periodic (V t) 1) (hAper : Periodic (A t) 1)
    (hP : 0 < P t) (s : ℝ) :
    curvOfPath V A P t (s + P t) = curvOfPath V A P t s := by
  have hs : (s + P t) / P t = s / P t + 1 := by field_simp
  rw [curvOfPath, curvOfPath, hs, hVper, hAper]

/-- **The increment of the tangent angle over one period does not depend on the
point**: the curvature is periodic, so the difference has vanishing
derivative. -/
theorem angleOfPath_increment_const {t : ℝ} (hVper : Periodic (V t) 1) (hAper : Periodic (A t) 1)
    (hVcont : Continuous (V t)) (hAcont : Continuous (A t)) (hP : 0 < P t) (x : ℝ) :
    angleOfPath V A P t (x + P t) - angleOfPath V A P t x
      = angleOfPath V A P t (0 + P t) - angleOfPath V A P t 0 := by
  have hcurvcont : Continuous (curvOfPath V A P t) := continuous_curvOfPath hVcont hAcont
  have hderiv : ∀ y : ℝ,
      HasDerivAt (fun z => angleOfPath V A P t (z + P t) - angleOfPath V A P t z) 0 y := by
    intro y
    have h1 : HasDerivAt (fun z : ℝ => angleOfPath V A P t (z + P t))
        (curvOfPath V A P t (y + P t)) y := by
      simpa using (hasDerivAt_angleOfPath hcurvcont (y + P t)).comp y
        ((hasDerivAt_id y).add_const (P t))
    simpa [curvOfPath_periodic hVper hAper hP y] using
      h1.sub (hasDerivAt_angleOfPath hcurvcont y)
  exact is_const_of_deriv_eq_zero (fun y => (hderiv y).differentiableAt)
    (fun y => (hderiv y).deriv) x 0

/-- **The total turning of a closed slice is an integer multiple of `2π`.**
The unit tangent is periodic, so the two lifts of it differ by a multiple of
`2π`; the turning number is that integer, and asking it to be `1` — as
`angleOfPath_add_period` does — is the normalization of a closed embedded
convex slice. -/
theorem exists_int_turning {t : ℝ} (hA : ∀ u, HasDerivAt (V t) (A t u) u)
    (hVper : Periodic (V t) 1) (hAper : Periodic (A t) 1)
    (hVcont : Continuous (V t)) (hAcont : Continuous (A t))
    (hspeed : ∀ u, ‖V t u‖ = P t) (hP : 0 < P t) :
    ∃ n : ℤ, ∀ s, angleOfPath V A P t (s + P t) = angleOfPath V A P t s + 2 * Real.pi * n := by
  set c : ℝ := angleOfPath V A P t (0 + P t) - angleOfPath V A P t 0 with hc
  -- the tangent is periodic, so the two lifts agree
  have htan : tangentOfPath V P t (0 + P t) = tangentOfPath V P t 0 := by
    have h0 : (0 + P t) / P t = 0 / P t + 1 := by field_simp
    rw [tangentOfPath, tangentOfPath, h0, hVper]
  have hexp : Complex.exp (Complex.I * (c : ℂ)) = 1 := by
    have h1 := exp_angleOfPath hA hAcont hVcont hspeed hP (0 + P t)
    have h2 := exp_angleOfPath hA hAcont hVcont hspeed hP 0
    have hne : Complex.exp (Complex.I * ((angleOfPath V A P t 0 : ℝ) : ℂ)) ≠ 0 :=
      Complex.exp_ne_zero _
    rw [hc, show (((angleOfPath V A P t (0 + P t) - angleOfPath V A P t 0 : ℝ)) : ℂ)
        = ((angleOfPath V A P t (0 + P t) : ℝ) : ℂ) - ((angleOfPath V A P t 0 : ℝ) : ℂ) by
      push_cast; ring, mul_sub, Complex.exp_sub, h1, h2, htan]
    exact div_self (by
      rw [← h2]; exact hne)
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨n, fun s => ?_⟩
  have hcn : c = 2 * Real.pi * n := by
    have : (c : ℂ) = ((2 * Real.pi * n : ℝ) : ℂ) := by
      have hIne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
      have h := hn
      field_simp at h ⊢
      push_cast
      rw [h]
      ring
    exact_mod_cast this
  have h := angleOfPath_increment_const hVper hAper hVcont hAcont hP s
  rw [← hc] at h
  rw [← hcn]
  linarith

/-- **The tangent angle increases by `2π` over one period**, the total turning
of the slice being `2π`. -/
theorem angleOfPath_add_period {t : ℝ} (hVper : Periodic (V t) 1) (hAper : Periodic (A t) 1)
    (hVcont : Continuous (V t)) (hAcont : Continuous (A t)) (hP : 0 < P t)
    (hturn : (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2)
      = 2 * Real.pi) (s : ℝ) :
    angleOfPath V A P t (s + P t) = angleOfPath V A P t s + 2 * Real.pi := by
  have hconst := fun x => angleOfPath_increment_const hVper hAper hVcont hAcont hP x
  -- the increment is the total turning of the slice
  have hval : angleOfPath V A P t (0 + P t) - angleOfPath V A P t 0 = 2 * Real.pi := by
    have hzero : angleOfPath V A P t 0 = (tangentOfPath V P t 0).arg := by simp [angleOfPath]
    have hPt : angleOfPath V A P t (0 + P t)
        = (tangentOfPath V P t 0).arg + ∫ x in (0 : ℝ)..(P t), curvOfPath V A P t x := by
      simp [angleOfPath]
    -- change of variables `s = P t · u`
    have hchange : (∫ x in (0 : ℝ)..(P t), curvOfPath V A P t x)
        = ∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2 := by
      have h := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
        (curvOfPath V A P t) (P t)
      simp only [mul_zero, mul_one, smul_eq_mul] at h
      rw [← h, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      have hu : P t * u / P t = u := by field_simp
      rw [curvOfPath, hu]
      field_simp
    rw [hPt, hzero, hchange, hturn]
    ring
  have h := hconst s
  rw [hval] at h
  linarith

/-! ### The identification of the slices -/

/-- **A normal path of closed constant-speed curves is a path of fronts.**

If every slice of a normal path is a closed curve of period one in the
normalized parameter, of constant speed `P t`, of turning number one, and if
the path moves along the standard unit normal `i τ`, then there are a family of
fronts `F` — the slices written in their own arclength — and a tangent angle
`Θ` for which the geometric identification

```
  X(t, u) = F(t, P(t) u) ,      ν(t, u) = i e^{iΘ(t, P(t) u)}
```

of `RearOwnPathDistSlices` holds, with `F t` unit speed of period `P t` and
`Θ t` increasing by `2π` over one period. -/
theorem exists_front_of_path {p q : Data} (Γ : NormalPath p q)
    (hV : ∀ t u, HasDerivAt (Γ.X t) (V t u) u)
    (hA : ∀ t u, HasDerivAt (V t) (A t u) u)
    (hAcont : ∀ t, Continuous (A t))
    (hspeed : ∀ t u, ‖V t u‖ = P t) (hPpos : ∀ t, 0 < P t)
    (hXper : ∀ t, Periodic (Γ.X t) 1) (hVper : ∀ t, Periodic (V t) 1)
    (hAper : ∀ t, Periodic (A t) 1)
    (hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2)
      = 2 * Real.pi)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * (V t u / (P t : ℂ))) :
    ∃ F : ℝ → ℝ → ℂ, ∃ Θ : ℝ → ℝ → ℝ,
      (∀ t u, Γ.X t u = F t (P t * u)) ∧
      (∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s) ∧
      (∀ t u, Γ.nu t u = Complex.I * Complex.exp (Complex.I * (Θ t (P t * u) : ℂ))) ∧
      (∀ t s, F t (s + P t) = F t s) ∧
      (∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi) := by
  have hVcont : ∀ t, Continuous (V t) := fun t =>
    continuous_iff_continuousAt.2 fun u => (hA t u).continuousAt
  refine ⟨frontOfPath Γ.X P, angleOfPath V A P, ?_, ?_, ?_, ?_, ?_⟩
  · intro t u
    have hu : P t * u / P t = u := by
      have := hPpos t; field_simp
    rw [frontOfPath, hu]
  · intro t s
    rw [exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) s]
    exact hasDerivAt_frontOfPath_tangent (hV t) (hPpos t) s
  · intro t u
    have hu : P t * u / P t = u := by
      have := hPpos t; field_simp
    rw [hnu t u, exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) (P t * u),
      tangentOfPath, hu]
  · intro t s
    exact periodic_frontOfPath (hXper t) (hPpos t) s
  · intro t s
    exact angleOfPath_add_period (hVper t) (hAper t) (hVcont t) (hAcont t) (hPpos t) (hturn t) s

/-! ### Paths whose slices are marked curves of the tube -/

/-- The derivative of a periodic function is periodic. -/
theorem periodic_of_hasDerivAt {f Vf : ℝ → ℂ} {c : ℝ} (hf : Periodic f c)
    (hV : ∀ u, HasDerivAt f (Vf u) u) : Periodic Vf c := by
  intro u
  have hshift : HasDerivAt (fun x : ℝ => x + c) 1 u := (hasDerivAt_id u).add_const c
  have h1 : HasDerivAt (fun x => f (x + c)) (Vf (u + c)) u := by
    simpa using (hV (u + c)).scomp u hshift
  have h2 : (fun x => f (x + c)) = f := funext hf
  rw [h2] at h1
  exact h1.unique (hV u)

/-- **A normal path through the tube of marked curves is a path of fronts.**

Same conclusion as `exists_front_of_path`, with the frame data of the slices
taken from the space of marked curves: if every slice of the path is the curve
of a member `S t` of the tube — so that it is closed of period one, of
constant speed, twice differentiable — of turning number one, and if the path
moves along the standard unit normal of that member, then it is a path of
fronts of perimeter `perim (S t)`. -/
theorem exists_front_of_path_of_tube {p q : Data} (Γ : NormalPath p q) {c kmin delta : ℝ}
    (hc : 0 < c) (S : ℝ → Data) (hS : ∀ t, IsTubeMember c kmin delta (S t))
    (hXS : ∀ t u, Γ.X t u = (S t).1 u)
    (hturn : ∀ t, (∫ u in (0 : ℝ)..1,
        ((starRingEnd ℂ) ((S t).2.1 u) * (S t).2.2 u).im / perim (S t) ^ 2) = 2 * Real.pi)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((S t).2.1 u / (perim (S t) : ℂ))) :
    ∃ F : ℝ → ℝ → ℂ, ∃ Θ : ℝ → ℝ → ℝ,
      (∀ t u, Γ.X t u = F t (perim (S t) * u)) ∧
      (∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s) ∧
      (∀ t u, Γ.nu t u
        = Complex.I * Complex.exp (Complex.I * (Θ t (perim (S t) * u) : ℂ))) ∧
      (∀ t s, F t (s + perim (S t)) = F t s) ∧
      (∀ t s, Θ t (s + perim (S t)) = Θ t s + 2 * Real.pi) := by
  have hXfun : ∀ t, Γ.X t = ⇑(S t).1 := fun t => funext (hXS t)
  have hV : ∀ t u, HasDerivAt (Γ.X t) ((S t).2.1 u) u := by
    intro t u
    rw [hXfun t]
    exact (hS t).hasDerivAt_curve u
  have hVper : ∀ t, Periodic (fun u => (S t).2.1 u) 1 := fun t =>
    periodic_of_hasDerivAt (hS t).periodic (hS t).hasDerivAt_curve
  have hAper : ∀ t, Periodic (fun u => (S t).2.2 u) 1 := fun t =>
    periodic_of_hasDerivAt (hVper t) (hS t).hasDerivAt_vel
  refine exists_front_of_path (V := fun t u => (S t).2.1 u) (A := fun t u => (S t).2.2 u)
    (P := fun t => perim (S t)) Γ hV (fun t u => (hS t).hasDerivAt_vel u)
    (fun t => map_continuous (S t).2.2) (fun t u => norm_vel_eq_perim (hS t) u)
    (fun t => perim_pos hc (hS t)) (fun t => ?_) hVper hAper hturn hnu
  rw [hXfun t]
  exact (hS t).periodic

/-! ### The path-distance bound for the selected rears of a path -/

open RearTrack ArclengthInverse RearOwnArclength UniformFrameBounds RearOwnHigherRegularity
  GaugePathDistVariable RearOwnPathDistSmooth SelectedInverseJacobiODE
  RearOwnPathDistIntrinsic RearFamilyFrame

/-- **The path pseudodistance of the selected rears of a normal path.**

The bound of `RearOwnPathDistSlices.pathDist_le_of_front_slices`, with the
family of fronts, its tangent angle and its curvature replaced by the canonical
data of the path itself: the slices written in their own arclength
(`frontOfPath`), their tangent angle (`angleOfPath`) and their curvature
(`curvOfPath`).  The geometric identification of the slices — which that
statement carries as a hypothesis — is discharged here by
`exists_front_of_path`; what is left to assume of the path is that its slices
are closed curves of constant speed `P t` and turning number one, moving along
their standard unit normal, and the analytic hypotheses on the steering angle
and on the regularity of the front data. -/
theorem pathDist_le_of_path_intrinsic {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh Md Klip CK : ℝ} {δ Kd sf : ℝ → ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hV : ∀ t u, HasDerivAt (Γ.X t) (V t u) u)
    (hA : ∀ t u, HasDerivAt (V t) (A t u) u)
    (hAcont : ∀ t, Continuous (A t))
    (hspeed : ∀ t u, ‖V t u‖ = P t)
    (hXper : ∀ t, Periodic (Γ.X t) 1) (hVper : ∀ t, Periodic (V t) 1)
    (hAper : ∀ t, Periodic (A t) 1)
    (hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2)
      = 2 * Real.pi)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * (V t u / (P t : ℂ)))
    (hsteer : ∀ t s, HasDerivAt (δ t) (curvOfPath V A P t s - Real.sin (δ t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hK : ∀ t s, |curvOfPath V A P t s| ≤ kh)
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry (frontOfPath Γ.X P)))
    (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry (angleOfPath V A P)))
    (hKdper : ∀ t, Function.Periodic (Kd t) (P t))
    (hKdbd : ∀ t s, |Kd t s| ≤ Md)
    (hKlip : ∀ a b s, |curvOfPath V A P a s - curvOfPath V A P b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s,
      |curvOfPath V A P a s - curvOfPath V A P b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hPC3 : ContDiff ℝ (3 : ℕ) P)
    (hKC3 : ContDiff ℝ (3 : ℕ) (uncurry (curvOfPath V A P)))
    (hKdC3 : ContDiff ℝ (3 : ℕ) (uncurry Kd))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hstart : ∀ u, p'.1 u
      = rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf 0
          (rearArclength (δ 0) (P 0) * u)) :
    ∃ EF : ℝ, 0 ≤ EF ∧
      (∀ t s, |frontNormalVelocityAt (partialTime (frontOfPath Γ.X P))
        (angleOfPath V A P) δ t s| ≤ EF) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
        ((∀ t, Γ.eta t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
        ∀ q' : Data, (∀ u, q'.1 u
            = rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf Γ.T (Phi Γ.T u)) →
          pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
              (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
              ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                  * (kh / Real.sqrt (1 - kh ^ 2))
                + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
            (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hVcont : ∀ t, Continuous (V t) := fun t =>
    continuous_iff_continuousAt.2 fun u => (hA t u).continuousAt
  have hcurvcont : ∀ t, Continuous (curvOfPath V A P t) := fun t =>
    continuous_curvOfPath (hVcont t) (hAcont t)
  refine RearOwnPathDistSlices.pathDist_le_of_front_slices Γ p' hP0 hkh0 hkh1 hPl hPu
    (fun t s => ?_) (fun t s => hasDerivAt_angleOfPath (hcurvcont t) s) hsteer hstrip0
    hstrip1 hdper hK (fun t => hcurvcont t) (fun t s => periodic_frontOfPath (hXper t) (hPpos t) s)
    (fun t s => angleOfPath_add_period (hVper t) (hAper t) (hVcont t) (hAcont t) (hPpos t)
      (hturn t) s)
    hFc4 hΘc4 hKdper hKdbd hKlip hKtaylor hCK hPC3 hKC3 hKdC3 hsfinv (fun t u => ?_)
    (fun t u => ?_) hstart
  · rw [exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) s]
    exact hasDerivAt_frontOfPath_tangent (hV t) (hPpos t) s
  · have hu : P t * u / P t = u := by have := hPpos t; field_simp
    rw [frontOfPath, hu]
  · have hu : P t * u / P t = u := by have := hPpos t; field_simp
    rw [hnu t u, exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) (P t * u),
      tangentOfPath, hu]

end FrontFromPath
