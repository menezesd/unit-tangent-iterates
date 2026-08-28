import UnitTangentIterates.HairpinPulseIdentity
import UnitTangentIterates.FrontPeriodization
import UnitTangentIterates.CurvFieldDerivBound
import UnitTangentIterates.PulseRelativeInterior

/-!
# The relative pulse bounds by the paper's own route

The paper proves `eq:relative-y-derivatives` **without any bound on the
derivatives of the profile**.  Its argument (§`lem:pulse`) is:

* the bounded-shift Harnack estimate `eq:bounded-shift-Harnack`, which follows
  from `(log r)_u = 1/f(θ)` and the two-sided barriers `m ≤ f ≤ M` alone;
* the translator curvature identity `eq:translator-curvature-identity`, which
  expresses the curvature at the shifted point in terms of the pulse and its
  derivative;
* solving that identity for the derivative.

This matters, and it is worth stating why.  Writing `K_* = G ∘ θ` with
`G = sin t / f t`, the chain rule gives `K_*' = G'(θ)·K_*`, so a bound
`|K_*'| ≤ C K_*` is equivalent to `|G'| ≤ C`, i.e.

```
  |cos t · f − sin t · f'| ≤ C f²   on (0, π).
```

That constrains `sin t · f'`, **not** `f'`.  A hypothesis `|f'| ≤ F₁` on
`(0, π)` is therefore strictly stronger than what the paper proves, and whether
it holds for the constructed profile is not established anywhere in this
development.  `HairpinRelative.relK_of_profile_barriers` takes exactly that
stronger hypothesis; it is sound, but it should not be read as the paper's
route, and it should not be assumed dischargeable.

The route below avoids the issue entirely: it uses only the identity, the
Harnack comparison, and `sup y ≤ b < 1`.
-/

noncomputable section

open Set Real HairpinRelative FrontPeriodization

open scoped ContDiff

namespace HairpinRelative

/-- The order-zero relative bound is trivial. -/
theorem rel_pulse_zero {f theta x : ℝ → ℝ}
    (hy0 : ∀ s, 0 ≤ pulseField f (theta (x s))) :
    ∀ s, |pulseField f (theta (x s))| ≤ 1 * pulseField f (theta (x s)) := by
  intro s
  rw [abs_of_nonneg (hy0 s), one_mul]

theorem rel_pulse_one_of_identity {f theta x yp : ℝ → ℝ} {s0 b Ch : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hCh : 0 ≤ Ch)
    (hy0 : ∀ s, 0 ≤ pulseField f (theta (x s)))
    (hsup : ∀ s, pulseField f (theta (x s)) ≤ b)
    (hKnn : ∀ s, 0 ≤ curvField f (theta (s + s0)))
    (hident : ∀ s, curvField f (theta (s + s0))
      = pulseField f (theta (x s)) + G (pulseField f (theta (x s))) * yp s)
    (hharnack : ∀ s, curvField f (theta (s + s0))
      ≤ Ch * curvField f (theta (x s))) :
    ∀ s, |yp s| ≤ (Ch / Real.sqrt (1 - b ^ 2) + 1) * pulseField f (theta (x s)) := by
  intro s
  set y := pulseField f (theta (x s)) with hydef
  set K := curvField f (theta (s + s0)) with hKdef
  have hy0s : 0 ≤ y := hy0 s
  have hyb : y ≤ b := hsup s
  have hsq : (0:ℝ) < 1 - y ^ 2 := by nlinarith
  have hsb : (0:ℝ) < 1 - b ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - y ^ 2) := Real.sqrt_pos.mpr hsq
  have hsbp : 0 < Real.sqrt (1 - b ^ 2) := Real.sqrt_pos.mpr hsb
  have hs1 : Real.sqrt (1 - y ^ 2) ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show 1 - y ^ 2 ≤ 1 by nlinarith)
    simpa using h
  -- solve the identity for `yp`
  have hG : G y = (Real.sqrt (1 - y ^ 2))⁻¹ := rfl
  have hyp : yp s = Real.sqrt (1 - y ^ 2) * (K - y) := by
    have h := hident s
    rw [hG] at h
    field_simp at h
    linarith [h]
  -- the curvature at the front point in terms of `y`
  have hKx : curvField f (theta (x s)) = y / Real.sqrt (1 - y ^ 2) := by
    have h := HairpinPulseIdentity.pulseField_eq_speed_mul_curvField f (theta (x s))
    rw [← hydef] at h
    field_simp
    linarith [h]
  have hmono : Real.sqrt (1 - b ^ 2) ≤ Real.sqrt (1 - y ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hKle : K ≤ Ch * (y / Real.sqrt (1 - b ^ 2)) := by
    refine le_trans (hharnack s) ?_
    rw [hKx]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hy0s hsbp hmono) hCh
  have habs : |yp s| ≤ K + y := by
    rw [hyp, abs_mul, abs_of_nonneg hs.le]
    have h1 : |K - y| ≤ K + y := by
      rw [abs_le]; constructor <;> linarith [hKnn s, hy0s]
    nlinarith [abs_nonneg (K - y), hs.le, hs1]
  have hfin : Ch * (y / Real.sqrt (1 - b ^ 2)) + y
      = (Ch / Real.sqrt (1 - b ^ 2) + 1) * y := by field_simp
  linarith [habs, hKle, hfin.ge, hfin.le]

theorem curvField_eq_pulse_div (f : ℝ → ℝ) :
    curvField f = fun s => pulseField f s / Real.sqrt (1 - pulseField f s ^ 2) := by
  funext s
  have h := HairpinPulseIdentity.pulseField_eq_speed_mul_curvField f s
  have hpos : 0 < Real.sqrt (1 - pulseField f s ^ 2) := by
    rw [HairpinPulseIdentity.sqrt_one_sub_pulseField_sq]
    exact div_pos one_pos (sqrt_one_add_sq_pos _)
  field_simp
  linarith [h]

theorem abs_deriv_curvField_le_of_pulse {f : ℝ → ℝ} {t b D1 : ℝ}
    (hp : HasDerivAt (pulseField f) (deriv (pulseField f) t) t)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy : |pulseField f t| ≤ b)
    (hd : |deriv (pulseField f) t| ≤ D1) :
    |deriv (curvField f) t| ≤ D1 / Real.sqrt (1 - b ^ 2) ^ 3 := by
  set p := pulseField f t with hpdef
  set pd := deriv (pulseField f) t with hpddef
  have hpb : |p| ≤ b := hy
  have hsq : (0:ℝ) < 1 - p ^ 2 := by
    have : p ^ 2 ≤ b ^ 2 := by nlinarith [abs_nonneg p, le_abs_self p, neg_abs_le p]
    nlinarith
  have hsb : (0:ℝ) < 1 - b ^ 2 := by nlinarith [abs_nonneg p]
  have hs : 0 < Real.sqrt (1 - p ^ 2) := Real.sqrt_pos.mpr hsq
  have hsbp : 0 < Real.sqrt (1 - b ^ 2) := Real.sqrt_pos.mpr hsb
  have hs2 : Real.sqrt (1 - p ^ 2) ^ 2 = 1 - p ^ 2 := Real.sq_sqrt hsq.le
  -- the derivative of the composite
  have hin : HasDerivAt (fun s => 1 - pulseField f s ^ 2) (-(2 * p * pd)) t := by
    simpa using ((hp.pow 2).const_sub 1)
  have hsqrt : HasDerivAt (fun s => Real.sqrt (1 - pulseField f s ^ 2))
      (-(2 * p * pd) / (2 * Real.sqrt (1 - p ^ 2))) t := hin.sqrt hsq.ne'
  have hdiv : HasDerivAt (fun s => pulseField f s / Real.sqrt (1 - pulseField f s ^ 2))
      ((pd * Real.sqrt (1 - p ^ 2)
        - p * (-(2 * p * pd) / (2 * Real.sqrt (1 - p ^ 2))))
        / Real.sqrt (1 - p ^ 2) ^ 2) t := hp.div hsqrt hs.ne'
  rw [curvField_eq_pulse_div f]
  rw [hdiv.deriv]
  -- simplify the quotient
  have hnum : pd * Real.sqrt (1 - p ^ 2)
      - p * (-(2 * p * pd) / (2 * Real.sqrt (1 - p ^ 2)))
      = pd / Real.sqrt (1 - p ^ 2) := by
    field_simp
    linear_combination pd * hs2
  have hval : (pd * Real.sqrt (1 - p ^ 2)
      - p * (-(2 * p * pd) / (2 * Real.sqrt (1 - p ^ 2))))
      / Real.sqrt (1 - p ^ 2) ^ 2 = pd / Real.sqrt (1 - p ^ 2) ^ 3 := by
    rw [hnum, div_div]
    congr 1
    ring
  rw [hval, abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.sqrt (1 - p ^ 2) ^ 3)]
  have hmono : Real.sqrt (1 - b ^ 2) ≤ Real.sqrt (1 - p ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith [abs_nonneg p, le_abs_self p, neg_abs_le p]
  refine div_le_div₀ (le_trans (abs_nonneg _) hd) hd (by positivity) ?_
  exact pow_le_pow_left₀ hsbp.le hmono 3

/-- **The relative curvature bound from the relative pulse bound.**  This is the
paper's route to `eq:relative-Kstar-derivatives` at order one: no bound on any
derivative of the profile is used.  The chain rule turns a bound on
`(pulseField f)'` into one on `(curvField f)'`, because
`curvField f = h ∘ pulseField f` with `h z = z/√(1−z²)` and `h' z = (1−z²)^{-3/2}`,
which the uniform bound `sup y ≤ b < 1` controls. -/
theorem relK_of_pulse_deriv_bound {f theta : ℝ → ℝ} {b D1 : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hyb : ∀ t ∈ Ioo (0:ℝ) π, |pulseField f t| ≤ b)
    (hdb : ∀ t ∈ Ioo (0:ℝ) π, |deriv (pulseField f) t| ≤ D1)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u) :
    ∀ u, |deriv (fun r => curvField f (theta r)) u| ≤
      (D1 / Real.sqrt (1 - b ^ 2) ^ 3) * curvField f (theta u) := by
  refine abs_deriv_curv_along_theta_le hf hfpos hmem hderiv ?_
  intro t ht
  have hpd : HasDerivAt (pulseField f) (deriv (pulseField f) t) t :=
    ((((contDiffOn_pulseField hf hfpos).contDiffAt
      (isOpen_Ioo.mem_nhds ht)).differentiableAt (by norm_num))).hasDerivAt
  exact abs_deriv_curvField_le_of_pulse hpd hb0 hb1 (hyb t ht) (hdb t ht)

/-- `K_* ≤ y/√(1−b²)` : the curvature is a bounded multiple of the pulse
wherever the pulse is uniformly below one.  This is `h z / z = 1/√(1−z²)`
bounded, and it is what lets curvature-side estimates be read off pulse-side
ones without a lower Harnack bound. -/
theorem curvField_le_pulse_div {f : ℝ → ℝ} {t b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hy0 : 0 ≤ pulseField f t)
    (hyb : pulseField f t ≤ b) :
    curvField f t ≤ pulseField f t / Real.sqrt (1 - b ^ 2) := by
  have hsq : (0:ℝ) < 1 - pulseField f t ^ 2 := by nlinarith
  have hsb : (0:ℝ) < 1 - b ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - pulseField f t ^ 2) := Real.sqrt_pos.mpr hsq
  have hsbp : 0 < Real.sqrt (1 - b ^ 2) := Real.sqrt_pos.mpr hsb
  have hmono : Real.sqrt (1 - b ^ 2) ≤ Real.sqrt (1 - pulseField f t ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hKx : curvField f t = pulseField f t / Real.sqrt (1 - pulseField f t ^ 2) := by
    have h := HairpinPulseIdentity.pulseField_eq_speed_mul_curvField f t
    field_simp
    linarith [h]
  rw [hKx]
  exact div_le_div_of_nonneg_left hy0 hsbp hmono

end HairpinRelative
