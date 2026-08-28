import Mathlib
import UnitTangentIterates.MarkedDistanceCurvature
import UnitTangentIterates.MarkingDeviation
import UnitTangentIterates.NormalPathC2Increment

/-!
# The marking defect in the `C²` metric of the space of marked curves

`MarkingDeviation.lean` measures the defect of a gauge marking in the uniform
(`C⁰`) norm: a curve read in a marking `φ` deviating from the affine marking
`u ↦ L·u` by at most `ε` is within `ε` of the curve itself, at every parameter.
That is enough for the uniform comparison of the two marked selected inverses
of `SelInvMarkingDefect.lean`, but not for a comparison in the metric of the
space of marked curves, which also compares the velocities and the
accelerations.

This file supplies the missing two components.  For a member `q` of the tube of
perimeter `L`, with tangent angle `Θ` and curvature `k` in arclength, and for
a `C²` datum `r` carrying the reparametrized curve

```
  r.1 u = q.1 (φ u / L) = ev q (φ u) ,
```

the velocity and the acceleration of `r` are computed in closed form
(`vel_reparam_eq`, `acc_reparam_eq`), and the three components are compared
with those of `q` under the three defect bounds

```
  |φ u − L u| ≤ ε₀ ,   |φ' u − L| ≤ ε₁ ,   |φ'' u| ≤ ε₂ ,
```

giving

```
  dist r q ≤ max ε₀ (max (ε₁ + L k_b ε₀)
                         (ε₂ + k_b ε₁(2L + ε₁) + L²(k_L + k_b²) ε₀)) ,
```

`k_b` a bound for the curvature and `k_L` a Lipschitz constant for it
(`dist_le_of_marking_defect_c2`).  With `ε₀ = ε₁ = ε₂ = 0` the marking is the
affine one and the bound is `0`: the reparametrized datum is `q` itself
(`eq_of_marking_affine`).

Main results: `dist_le_of_marking_defect_c2`, `eq_of_marking_affine`.
-/

noncomputable section

open Set Function

namespace MarkingDeviationC2

open MarkedSpace

/-! ### An elementary mean-value bound -/

/-- A real function whose derivative is bounded by `M` is `M`-Lipschitz. -/
theorem abs_sub_le_of_abs_deriv_le {f g : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, |g x| ≤ M) (a b : ℝ) :
    |f a - f b| ≤ M * |a - b| := by
  have h := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := g) (C := M) (fun x _ => (hf x).hasDerivWithinAt)
    (fun x _ => by simpa [Real.norm_eq_abs] using hg x) (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using h

/-! ### The `C²` data of a reparametrized curve -/

/-- The velocity of a curve read in a marking: `r' = φ' e^{iΘ(φ)}`. -/
theorem vel_reparam_eq {q r : Data} {Θ phi phi1 : ℝ → ℝ}
    (hev : ∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hr1 : ∀ u, r.1 u = ev q (phi u))
    (hrd : ∀ u, HasDerivAt (⇑r.1) (r.2.1 u) u)
    (hphi : ∀ u, HasDerivAt phi (phi1 u) u) (u : ℝ) :
    r.2.1 u = ((phi1 u : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (phi u) : ℂ)) := by
  have hcomp : HasDerivAt (fun t : ℝ => ev q (phi t))
      (((phi1 u : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (phi u) : ℂ))) u := by
    have h := (hev (phi u)).scomp u (hphi u)
    have hcast : (phi1 u : ℝ) • Complex.exp (Complex.I * (Θ (phi u) : ℂ))
        = ((phi1 u : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (phi u) : ℂ)) := by
      rw [Complex.real_smul]
    simpa [Function.comp_def, hcast] using h
  have heq : (fun t : ℝ => ev q (phi t)) = ⇑r.1 := funext fun t => (hr1 t).symm
  rw [heq] at hcomp
  exact (hrd u).unique hcomp

/-- The derivative of the unit tangent along the arclength parameter. -/
theorem hasDerivAt_exp_angle {Θ k : ℝ → ℝ} (hΘ : ∀ s, HasDerivAt Θ (k s) s) (s : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.exp (Complex.I * (Θ r : ℂ)))
      (Complex.I * (k s : ℂ) * Complex.exp (Complex.I * (Θ s : ℂ))) s := by
  have h0 : HasDerivAt (fun r : ℝ => Complex.I * (Θ r : ℂ)) (Complex.I * (k s : ℂ)) s := by
    have h1 : HasDerivAt (fun r : ℝ => ((Θ r : ℝ) : ℂ)) ((k s : ℝ) : ℂ) s :=
      (Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt s (hΘ s)
    simpa using h1.const_mul Complex.I
  simpa [mul_comm] using h0.cexp

/-- The acceleration of a curve read in a marking:
`r'' = φ'' e^{iΘ(φ)} + (φ')² i k(φ) e^{iΘ(φ)}`. -/
theorem acc_reparam_eq {q r : Data} {Θ k phi phi1 phi2 : ℝ → ℝ}
    (hev : ∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (k s) s)
    (hr1 : ∀ u, r.1 u = ev q (phi u))
    (hrd : ∀ u, HasDerivAt (⇑r.1) (r.2.1 u) u)
    (hrv : ∀ u, HasDerivAt (⇑r.2.1) (r.2.2 u) u)
    (hphi : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi1 : ∀ u, HasDerivAt phi1 (phi2 u) u) (u : ℝ) :
    r.2.2 u = ((phi2 u : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (phi u) : ℂ))
      + ((phi1 u ^ 2 : ℝ) : ℂ) *
        (Complex.I * (k (phi u) : ℂ) * Complex.exp (Complex.I * (Θ (phi u) : ℂ))) := by
  have hveq : ⇑r.2.1
      = fun t : ℝ => ((phi1 t : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (phi t) : ℂ)) :=
    funext fun t => vel_reparam_eq hev hr1 hrd hphi t
  have hinner : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (Θ (phi t) : ℂ)))
      ((phi1 u : ℝ) • (Complex.I * (k (phi u) : ℂ)
        * Complex.exp (Complex.I * (Θ (phi u) : ℂ)))) u :=
    (hasDerivAt_exp_angle hΘ (phi u)).scomp u (hphi u)
  have hcast : HasDerivAt (fun t : ℝ => ((phi1 t : ℝ) : ℂ)) ((phi2 u : ℝ) : ℂ) u :=
    (Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt u (hphi1 u)
  have hprod := hcast.mul hinner
  have hval : ((phi2 u : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (phi u) : ℂ))
      + ((phi1 u : ℝ) : ℂ) * ((phi1 u : ℝ) • (Complex.I * (k (phi u) : ℂ)
        * Complex.exp (Complex.I * (Θ (phi u) : ℂ))))
      = ((phi2 u : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (phi u) : ℂ))
        + ((phi1 u ^ 2 : ℝ) : ℂ) *
          (Complex.I * (k (phi u) : ℂ) * Complex.exp (Complex.I * (Θ (phi u) : ℂ))) := by
    rw [Complex.real_smul]
    push_cast
    ring
  have hd : HasDerivAt (⇑r.2.1)
      (((phi2 u : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (phi u) : ℂ))
        + ((phi1 u ^ 2 : ℝ) : ℂ) *
          (Complex.I * (k (phi u) : ℂ) * Complex.exp (Complex.I * (Θ (phi u) : ℂ)))) u := by
    rw [hveq]
    have := hprod
    rw [add_comm] at this
    exact this.congr_deriv (by rw [← hval]; ring)
  exact (hrv u).unique hd

/-! ### The three componentwise bounds -/

/-- The constant of the `C²` marking defect: the largest of the position, the
velocity and the acceleration errors. -/
def markingC2Bound (e0 e1 e2 L kb kL : ℝ) : ℝ :=
  max e0 (max (e1 + L * kb * e0) (e2 + kb * e1 * (2 * L + e1) + L ^ 2 * (kL + kb ^ 2) * e0))

theorem markingC2Bound_nonneg {e0 e1 e2 L kb kL : ℝ} (he0 : 0 ≤ e0) :
    0 ≤ markingC2Bound e0 e1 e2 L kb kL := le_trans he0 (le_max_left _ _)

/-- Uniform linearization of the marking bound on a bounded cost interval.
The only nonlinear term is quadratic in the first-derivative defect; it is
absorbed by `x² ≤ Mx`. -/
theorem markingC2Bound_le_mul_of_component_linear
    {e0 e1 e2 x M A B D L kb kL : ℝ}
    (hx0 : 0 ≤ x) (hxM : x ≤ M)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hL : 0 ≤ L) (hkb : 0 ≤ kb) (hkL : 0 ≤ kL)
    (he0 : 0 ≤ e0) (he1 : 0 ≤ e1)
    (he0bd : e0 ≤ A * x) (he1bd : e1 ≤ B * x) (he2bd : e2 ≤ D * x) :
    markingC2Bound e0 e1 e2 L kb kL ≤
      max A (max (B + L * kb * A)
        (D + kb * B * (2 * L + B * M) + L ^ 2 * (kL + kb ^ 2) * A)) * x := by
  have hM0 : 0 ≤ M := hx0.trans hxM
  have he1Bx : 0 ≤ B * x := mul_nonneg hB hx0
  have hquad : e1 * e1 ≤ B ^ 2 * M * x := by
    have he1sq : e1 ^ 2 ≤ (B * x) ^ 2 :=
      (sq_le_sq₀ he1 he1Bx).2 he1bd
    have hxx : x ^ 2 ≤ M * x := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hxx (sq_nonneg B)]
  unfold markingC2Bound
  apply max_le
  · exact he0bd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0)
  apply max_le
  · have : e1 + L * kb * e0 ≤ (B + L * kb * A) * x := by
      nlinarith [mul_le_mul_of_nonneg_left he0bd (mul_nonneg hL hkb)]
    exact this.trans (mul_le_mul_of_nonneg_right
      (le_trans (le_max_left _ _) (le_max_right _ _)) hx0)
  · have hcross : kb * e1 * (2 * L + e1) ≤
        (kb * B * (2 * L + B * M)) * x := by
      have hlin := mul_le_mul_of_nonneg_left he1bd
        (mul_nonneg hkb (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL))
      have hquad' := mul_le_mul_of_nonneg_left hquad hkb
      nlinarith
    have hpos : L ^ 2 * (kL + kb ^ 2) * e0 ≤
        (L ^ 2 * (kL + kb ^ 2) * A) * x := by
      nlinarith [mul_le_mul_of_nonneg_left he0bd (by positivity :
        0 ≤ L ^ 2 * (kL + kb ^ 2))]
    have : e2 + kb * e1 * (2 * L + e1) + L ^ 2 * (kL + kb ^ 2) * e0 ≤
        (D + kb * B * (2 * L + B * M) + L ^ 2 * (kL + kb ^ 2) * A) * x := by
      nlinarith
    exact this.trans (mul_le_mul_of_nonneg_right
      (le_trans (le_max_right _ _) (le_max_right _ _)) hx0)

/-- The bound is monotone in the three defects. -/
theorem markingC2Bound_mono {e0 e1 e2 e0' e1' e2' L kb kL : ℝ} (hL : 0 ≤ L) (hkb : 0 ≤ kb)
    (hkL : 0 ≤ kL) (he1 : 0 ≤ e1) (h0 : e0 ≤ e0') (h1 : e1 ≤ e1') (h2 : e2 ≤ e2') :
    markingC2Bound e0 e1 e2 L kb kL ≤ markingC2Bound e0' e1' e2' L kb kL := by
  have hA : L * kb * e0 ≤ L * kb * e0' :=
    mul_le_mul_of_nonneg_left h0 (mul_nonneg hL hkb)
  have hC : L ^ 2 * (kL + kb ^ 2) * e0 ≤ L ^ 2 * (kL + kb ^ 2) * e0' :=
    mul_le_mul_of_nonneg_left h0 (by positivity)
  have hB : kb * e1 * (2 * L + e1) ≤ kb * e1' * (2 * L + e1') := by
    have hd : kb * e1' * (2 * L + e1') - kb * e1 * (2 * L + e1)
        = kb * ((e1' - e1) * (2 * L) + (e1' - e1) * (e1' + e1)) := by ring
    nlinarith [mul_nonneg hkb (mul_nonneg (sub_nonneg.2 h1) hL),
      mul_nonneg hkb (mul_nonneg (sub_nonneg.2 h1) (by linarith : (0:ℝ) ≤ e1' + e1))]
  have hstep1 : e1 + L * kb * e0 ≤ e1' + L * kb * e0' := by linarith
  have hstep2 : e2 + kb * e1 * (2 * L + e1) + L ^ 2 * (kL + kb ^ 2) * e0
      ≤ e2' + kb * e1' * (2 * L + e1') + L ^ 2 * (kL + kb ^ 2) * e0' := by linarith
  unfold markingC2Bound
  exact max_le_max h0 (max_le_max hstep1 hstep2)

/-- **The bound vanishes with the three defects.** -/
theorem tendsto_markingC2Bound_zero {ι : Type*} {l : Filter ι} {a b c : ι → ℝ} {L kb kL : ℝ}
    (ha : Filter.Tendsto a l (nhds 0)) (hb : Filter.Tendsto b l (nhds 0))
    (hc : Filter.Tendsto c l (nhds 0)) :
    Filter.Tendsto (fun n => markingC2Bound (a n) (b n) (c n) L kb kL) l (nhds 0) := by
  have h1 : Filter.Tendsto (fun n => b n + L * kb * a n) l (nhds 0) := by
    simpa using hb.add (ha.const_mul (L * kb))
  have h2 : Filter.Tendsto
      (fun n => c n + kb * b n * (2 * L + b n) + L ^ 2 * (kL + kb ^ 2) * a n) l (nhds 0) := by
    have hbb : Filter.Tendsto (fun n => kb * b n * (2 * L + b n)) l (nhds 0) := by
      have := ((hb.const_mul kb).mul (hb.const_add (2 * L)))
      simpa using this
    simpa using (hc.add hbb).add (ha.const_mul (L ^ 2 * (kL + kb ^ 2)))
  have := ha.max (h1.max h2)
  simpa [markingC2Bound] using this

variable {c kmin dlt : ℝ} {q r : Data} {Θ k phi phi1 phi2 : ℝ → ℝ} {e0 e1 e2 L kb kL : ℝ}

/-- **The position error of a curve read in a marking**: at most the deviation
of the marking from the affine one. -/
theorem norm_curve_sub_le (hc : 0 < c) (hq : IsTubeMember c kmin dlt q) (hL : perim q = L)
    (hev : ∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hr1 : ∀ u, r.1 u = ev q (phi u))
    (hdev : ∀ u, |phi u - L * u| ≤ e0) (u : ℝ) :
    ‖r.1 u - q.1 u‖ ≤ e0 := by
  have hLpos : 0 < L := hL ▸ perim_pos hc hq
  have hone : ∀ s : ℝ, ‖Complex.exp (Complex.I * (Θ s : ℂ))‖ ≤ 1 := by
    intro s; rw [Complex.norm_exp]; simp
  have h := MarkingDeviation.norm_sub_le_of_norm_deriv_le (c := ev q)
    (v := fun s => Complex.exp (Complex.I * (Θ s : ℂ))) (L := 1) hev hone (phi u) (L * u)
  have hqe : q.1 u = ev q (L * u) := by
    rw [curve_eq_ev q u (by rw [hL]; exact ne_of_gt hLpos), hL]
  rw [hr1 u, hqe]
  calc ‖ev q (phi u) - ev q (L * u)‖ ≤ 1 * |phi u - L * u| := h
    _ ≤ e0 := by rw [one_mul]; exact hdev u

/-- **The velocity error of a curve read in a marking.** -/
theorem norm_vel_sub_le (hc : 0 < c) (hq : IsTubeMember c kmin dlt q) (hL : perim q = L)
    (hev : ∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (k s) s) (hkb : ∀ s, |k s| ≤ kb)
    (hr1 : ∀ u, r.1 u = ev q (phi u))
    (hrd : ∀ u, HasDerivAt (⇑r.1) (r.2.1 u) u)
    (hphi : ∀ u, HasDerivAt phi (phi1 u) u)
    (hdev : ∀ u, |phi u - L * u| ≤ e0) (hdev1 : ∀ u, |phi1 u - L| ≤ e1) (u : ℝ) :
    ‖r.2.1 u - q.2.1 u‖ ≤ e1 + L * kb * e0 := by
  have hLpos : 0 < L := hL ▸ perim_pos hc hq
  have hrv := vel_reparam_eq hev hr1 hrd hphi u
  have hqv : q.2.1 u = ((L : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (L * u) : ℂ)) := by
    rw [vel_eq hc hq hev u, hL]
  have hsplit : ((phi1 u : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (phi u) : ℂ))
      - ((L : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (L * u) : ℂ))
      = ((phi1 u - L : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (phi u) : ℂ))
        + ((L : ℝ) : ℂ) * (Complex.exp (Complex.I * (Θ (phi u) : ℂ))
            - Complex.exp (Complex.I * (Θ (L * u) : ℂ))) := by
    push_cast; ring
  have he1 : ‖Complex.exp (Complex.I * (Θ (phi u) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hangle : |Θ (phi u) - Θ (L * u)| ≤ kb * e0 := by
    have h := abs_sub_le_of_abs_deriv_le hΘ hkb (phi u) (L * u)
    exact le_trans h (mul_le_mul_of_nonneg_left (hdev u)
      (le_trans (abs_nonneg _) (hkb 0)))
  have hexp : ‖Complex.exp (Complex.I * (Θ (phi u) : ℂ))
      - Complex.exp (Complex.I * (Θ (L * u) : ℂ))‖ ≤ kb * e0 :=
    le_trans (NormalPathC2Increment.norm_exp_I_sub_le _ _) hangle
  rw [hrv, hqv, hsplit]
  calc ‖((phi1 u - L : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (phi u) : ℂ))
        + ((L : ℝ) : ℂ) * (Complex.exp (Complex.I * (Θ (phi u) : ℂ))
            - Complex.exp (Complex.I * (Θ (L * u) : ℂ)))‖
      ≤ ‖((phi1 u - L : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (phi u) : ℂ))‖
        + ‖((L : ℝ) : ℂ) * (Complex.exp (Complex.I * (Θ (phi u) : ℂ))
            - Complex.exp (Complex.I * (Θ (L * u) : ℂ)))‖ := norm_add_le _ _
    _ ≤ e1 + L * (kb * e0) := by
        have h1 : ‖((phi1 u - L : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (phi u) : ℂ))‖ ≤ e1 := by
          rw [norm_mul, he1, mul_one, Complex.norm_real, Real.norm_eq_abs]
          exact hdev1 u
        have h2 : ‖((L : ℝ) : ℂ) * (Complex.exp (Complex.I * (Θ (phi u) : ℂ))
            - Complex.exp (Complex.I * (Θ (L * u) : ℂ)))‖ ≤ L * (kb * e0) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos]
          exact mul_le_mul_of_nonneg_left hexp hLpos.le
        linarith
    _ = e1 + L * kb * e0 := by ring

/-- **The acceleration error of a curve read in a marking.** -/
theorem norm_acc_sub_le (hc : 0 < c) (hq : IsTubeMember c kmin dlt q) (hL : perim q = L)
    (hev : ∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (k s) s) (hkb : ∀ s, |k s| ≤ kb)
    (hklip : ∀ s t, |k s - k t| ≤ kL * |s - t|)
    (hr1 : ∀ u, r.1 u = ev q (phi u))
    (hrd : ∀ u, HasDerivAt (⇑r.1) (r.2.1 u) u)
    (hrv : ∀ u, HasDerivAt (⇑r.2.1) (r.2.2 u) u)
    (hphi : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi1 : ∀ u, HasDerivAt phi1 (phi2 u) u)
    (hdev : ∀ u, |phi u - L * u| ≤ e0) (hdev1 : ∀ u, |phi1 u - L| ≤ e1)
    (hdev2 : ∀ u, |phi2 u| ≤ e2) (u : ℝ) :
    ‖r.2.2 u - q.2.2 u‖ ≤ e2 + kb * e1 * (2 * L + e1) + L ^ 2 * (kL + kb ^ 2) * e0 := by
  have hLpos : 0 < L := hL ▸ perim_pos hc hq
  have hkb0 : 0 ≤ kb := le_trans (abs_nonneg _) (hkb 0)
  have he00 : 0 ≤ e0 := le_trans (abs_nonneg _) (hdev 0)
  have he10 : 0 ≤ e1 := le_trans (abs_nonneg _) (hdev1 0)
  have hkL0 : 0 ≤ kL := by
    have h := hklip 1 0
    have h0 : |k 1 - k 0| ≤ kL * |(1 : ℝ) - 0| := h
    simp only [sub_zero, abs_one, mul_one] at h0
    exact le_trans (abs_nonneg _) h0
  have hracc := acc_reparam_eq hev hΘ hr1 hrd hrv hphi hphi1 u
  have hqacc : q.2.2 u = ((L ^ 2 : ℝ) : ℂ) *
      (Complex.I * (k (L * u) : ℂ) * Complex.exp (Complex.I * (Θ (L * u) : ℂ))) := by
    rw [acc_eq hc hq hev hΘ u, hL]
  -- abbreviations
  set E1 : ℂ := Complex.exp (Complex.I * (Θ (phi u) : ℂ)) with hE1
  set E2 : ℂ := Complex.exp (Complex.I * (Θ (L * u) : ℂ)) with hE2
  have hnE1 : ‖E1‖ = 1 := by rw [hE1, Complex.norm_exp]; simp
  have hnE2 : ‖E2‖ = 1 := by rw [hE2, Complex.norm_exp]; simp
  have hangle : |Θ (phi u) - Θ (L * u)| ≤ kb * e0 := by
    have h := abs_sub_le_of_abs_deriv_le hΘ hkb (phi u) (L * u)
    exact le_trans h (mul_le_mul_of_nonneg_left (hdev u) hkb0)
  have hexp : ‖E1 - E2‖ ≤ kb * e0 := by
    rw [hE1, hE2]
    exact le_trans (NormalPathC2Increment.norm_exp_I_sub_le _ _) hangle
  have hkdiff : |k (phi u) - k (L * u)| ≤ kL * e0 :=
    le_trans (hklip _ _) (mul_le_mul_of_nonneg_left (hdev u) hkL0)
  have hsplit : ((phi2 u : ℝ) : ℂ) * E1
        + ((phi1 u ^ 2 : ℝ) : ℂ) * (Complex.I * (k (phi u) : ℂ) * E1)
        - ((L ^ 2 : ℝ) : ℂ) * (Complex.I * (k (L * u) : ℂ) * E2)
      = ((phi2 u : ℝ) : ℂ) * E1
        + ((phi1 u ^ 2 - L ^ 2 : ℝ) : ℂ) * (Complex.I * (k (phi u) : ℂ) * E1)
        + ((L ^ 2 : ℝ) : ℂ) * (Complex.I * ((k (phi u) - k (L * u) : ℝ) : ℂ) * E1)
        + ((L ^ 2 : ℝ) : ℂ) * (Complex.I * (k (L * u) : ℂ) * (E1 - E2)) := by
    push_cast; ring
  rw [hracc, hqacc, hsplit]
  have hb1 : ‖((phi2 u : ℝ) : ℂ) * E1‖ ≤ e2 := by
    rw [norm_mul, hnE1, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hdev2 u
  have hb2 : ‖((phi1 u ^ 2 - L ^ 2 : ℝ) : ℂ) * (Complex.I * (k (phi u) : ℂ) * E1)‖
      ≤ kb * e1 * (2 * L + e1) := by
    rw [norm_mul, norm_mul, norm_mul, hnE1, Complex.norm_I, one_mul, mul_one,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
    have hfac : |phi1 u ^ 2 - L ^ 2| ≤ e1 * (2 * L + e1) := by
      have hid : phi1 u ^ 2 - L ^ 2 = (phi1 u - L) * (phi1 u + L) := by ring
      have hsum : |phi1 u + L| ≤ 2 * L + e1 := by
        have h1 : |phi1 u - L| ≤ e1 := hdev1 u
        have h2 : |phi1 u| ≤ L + e1 := by
          have := abs_sub_abs_le_abs_sub (phi1 u) L
          have hLabs : |L| = L := abs_of_pos hLpos
          rw [hLabs] at this
          linarith [h1]
        calc |phi1 u + L| ≤ |phi1 u| + |L| := abs_add_le _ _
          _ ≤ (L + e1) + L := by rw [abs_of_pos hLpos]; linarith
          _ = 2 * L + e1 := by ring
      rw [hid, abs_mul]
      exact mul_le_mul (hdev1 u) hsum (abs_nonneg _) he10
    calc |phi1 u ^ 2 - L ^ 2| * |k (phi u)| ≤ (e1 * (2 * L + e1)) * kb :=
          mul_le_mul hfac (hkb _) (abs_nonneg _) (by positivity)
      _ = kb * e1 * (2 * L + e1) := by ring
  have hb3 : ‖((L ^ 2 : ℝ) : ℂ) * (Complex.I * ((k (phi u) - k (L * u) : ℝ) : ℂ) * E1)‖
      ≤ L ^ 2 * kL * e0 := by
    rw [norm_mul, norm_mul, norm_mul, hnE1, Complex.norm_I, one_mul, mul_one,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < L ^ 2)]
    calc L ^ 2 * |k (phi u) - k (L * u)| ≤ L ^ 2 * (kL * e0) :=
          mul_le_mul_of_nonneg_left hkdiff (by positivity)
      _ = L ^ 2 * kL * e0 := by ring
  have hb4 : ‖((L ^ 2 : ℝ) : ℂ) * (Complex.I * (k (L * u) : ℂ) * (E1 - E2))‖
      ≤ L ^ 2 * kb ^ 2 * e0 := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < L ^ 2)]
    have h1 : |k (L * u)| * ‖E1 - E2‖ ≤ kb * (kb * e0) :=
      mul_le_mul (hkb _) hexp (norm_nonneg _) hkb0
    calc L ^ 2 * (|k (L * u)| * ‖E1 - E2‖) ≤ L ^ 2 * (kb * (kb * e0)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = L ^ 2 * kb ^ 2 * e0 := by ring
  calc ‖((phi2 u : ℝ) : ℂ) * E1
        + ((phi1 u ^ 2 - L ^ 2 : ℝ) : ℂ) * (Complex.I * (k (phi u) : ℂ) * E1)
        + ((L ^ 2 : ℝ) : ℂ) * (Complex.I * ((k (phi u) - k (L * u) : ℝ) : ℂ) * E1)
        + ((L ^ 2 : ℝ) : ℂ) * (Complex.I * (k (L * u) : ℂ) * (E1 - E2))‖
      ≤ ‖((phi2 u : ℝ) : ℂ) * E1
          + ((phi1 u ^ 2 - L ^ 2 : ℝ) : ℂ) * (Complex.I * (k (phi u) : ℂ) * E1)
          + ((L ^ 2 : ℝ) : ℂ) * (Complex.I * ((k (phi u) - k (L * u) : ℝ) : ℂ) * E1)‖
        + ‖((L ^ 2 : ℝ) : ℂ) * (Complex.I * (k (L * u) : ℂ) * (E1 - E2))‖ := norm_add_le _ _
    _ ≤ (‖((phi2 u : ℝ) : ℂ) * E1
          + ((phi1 u ^ 2 - L ^ 2 : ℝ) : ℂ) * (Complex.I * (k (phi u) : ℂ) * E1)‖
        + ‖((L ^ 2 : ℝ) : ℂ) * (Complex.I * ((k (phi u) - k (L * u) : ℝ) : ℂ) * E1)‖)
        + ‖((L ^ 2 : ℝ) : ℂ) * (Complex.I * (k (L * u) : ℂ) * (E1 - E2))‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ((‖((phi2 u : ℝ) : ℂ) * E1‖
          + ‖((phi1 u ^ 2 - L ^ 2 : ℝ) : ℂ) * (Complex.I * (k (phi u) : ℂ) * E1)‖)
        + ‖((L ^ 2 : ℝ) : ℂ) * (Complex.I * ((k (phi u) - k (L * u) : ℝ) : ℂ) * E1)‖)
        + ‖((L ^ 2 : ℝ) : ℂ) * (Complex.I * (k (L * u) : ℂ) * (E1 - E2))‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ e2 + kb * e1 * (2 * L + e1) + L ^ 2 * (kL + kb ^ 2) * e0 := by
        have : L ^ 2 * (kL + kb ^ 2) * e0 = L ^ 2 * kL * e0 + L ^ 2 * kb ^ 2 * e0 := by ring
        linarith

/-! ### The bound in the metric of the space of marked curves -/

/-- **The `C²` marking defect.**  A member `q` of the tube of perimeter `L`,
curvature bounded by `k_b` and `k_L`-Lipschitz, read in a marking `φ` whose
deviation from the affine marking `u ↦ L·u` is bounded by `ε₀` in position, by
`ε₁` in the first derivative and by `ε₂` in the second, is at marked distance at
most `markingC2Bound ε₀ ε₁ ε₂ L k_b k_L` from `q` itself. -/
theorem dist_le_of_marking_defect_c2 (hc : 0 < c) (hq : IsTubeMember c kmin dlt q)
    (hL : perim q = L)
    (hev : ∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (k s) s) (hkb : ∀ s, |k s| ≤ kb)
    (hklip : ∀ s t, |k s - k t| ≤ kL * |s - t|)
    (hr1 : ∀ u, r.1 u = ev q (phi u))
    (hrd : ∀ u, HasDerivAt (⇑r.1) (r.2.1 u) u)
    (hrv : ∀ u, HasDerivAt (⇑r.2.1) (r.2.2 u) u)
    (hphi : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi1 : ∀ u, HasDerivAt phi1 (phi2 u) u)
    (hdev : ∀ u, |phi u - L * u| ≤ e0) (hdev1 : ∀ u, |phi1 u - L| ≤ e1)
    (hdev2 : ∀ u, |phi2 u| ≤ e2) :
    dist r q ≤ markingC2Bound e0 e1 e2 L kb kL := by
  have he00 : 0 ≤ e0 := le_trans (abs_nonneg _) (hdev 0)
  have hM0 : 0 ≤ markingC2Bound e0 e1 e2 L kb kL := markingC2Bound_nonneg he00
  have hd1 : dist r.1 q.1 ≤ markingC2Bound e0 e1 e2 L kb kL :=
    (BoundedContinuousFunction.dist_le hM0).2 fun u => by
      rw [dist_eq_norm]
      exact le_trans (norm_curve_sub_le hc hq hL hev hr1 hdev u) (le_max_left _ _)
  have hd2 : dist r.2.1 q.2.1 ≤ markingC2Bound e0 e1 e2 L kb kL :=
    (BoundedContinuousFunction.dist_le hM0).2 fun u => by
      rw [dist_eq_norm]
      exact le_trans (norm_vel_sub_le hc hq hL hev hΘ hkb hr1 hrd hphi hdev hdev1 u)
        (le_trans (le_max_left _ _) (le_max_right _ _))
  have hd3 : dist r.2.2 q.2.2 ≤ markingC2Bound e0 e1 e2 L kb kL :=
    (BoundedContinuousFunction.dist_le hM0).2 fun u => by
      rw [dist_eq_norm]
      exact le_trans
        (norm_acc_sub_le hc hq hL hev hΘ hkb hklip hr1 hrd hrv hphi hphi1 hdev hdev1 hdev2 u)
        (le_trans (le_max_right _ _) (le_max_right _ _))
  rw [Prod.dist_eq, Prod.dist_eq]
  exact max_le hd1 (max_le hd2 hd3)

/-- **Rigidity: a curve read in the affine marking is the curve itself.**  The
case `ε₀ = ε₁ = ε₂ = 0` of `dist_le_of_marking_defect_c2`. -/
theorem eq_of_marking_affine (hc : 0 < c) (hq : IsTubeMember c kmin dlt q)
    (hL : perim q = L)
    (hev : ∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (k s) s) (hkb : ∀ s, |k s| ≤ kb)
    (hklip : ∀ s t, |k s - k t| ≤ kL * |s - t|)
    (hr1 : ∀ u, r.1 u = ev q (phi u))
    (hrd : ∀ u, HasDerivAt (⇑r.1) (r.2.1 u) u)
    (hrv : ∀ u, HasDerivAt (⇑r.2.1) (r.2.2 u) u)
    (hphi : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi1 : ∀ u, HasDerivAt phi1 (phi2 u) u)
    (haff : ∀ u, phi u = L * u) (haff1 : ∀ u, phi1 u = L) (haff2 : ∀ u, phi2 u = 0) :
    r = q := by
  have h := dist_le_of_marking_defect_c2 (e0 := 0) (e1 := 0) (e2 := 0) hc hq hL hev hΘ hkb
    hklip hr1 hrd hrv hphi hphi1 (fun u => by rw [haff u]; simp)
    (fun u => by rw [haff1 u]; simp) (fun u => by rw [haff2 u]; simp)
  have hzero : markingC2Bound 0 0 0 L kb kL = 0 := by
    simp [markingC2Bound]
  rw [hzero] at h
  exact dist_le_zero.1 h

end MarkingDeviationC2
