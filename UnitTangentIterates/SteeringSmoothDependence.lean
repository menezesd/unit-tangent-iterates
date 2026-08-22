import Mathlib
import UnitTangentIterates.PeriodicParameterDeriv

/-!
# Smooth dependence of the selected steering angle on the front

This file specializes `PeriodicParameterDeriv.hasDerivAt_param_periodic` to the
steering equation of the paper *A Noncircular Oval with Convex Unit-Tangent
Iterates*.  Parametrizing each front by its tangent angle and writing
`q = 1/K` for its radius of curvature, the selected steering angle satisfies

```
  δ_φ = 1 - q(φ) sin δ ,
```

and on the selected strip `0 ≤ δ ≤ arcsin κ̂` the linearization
`w_φ + q cos δ · w = -q̇ sin δ` has zeroth-order coefficient bounded below by
`κ̂⁻¹√(1-κ̂²) > 0`.  This is exactly the dissipativity required by
`hasDerivAt_param_periodic`, so along a path of fronts whose radius of
curvature is differentiable in the path parameter — with a quadratic Taylor
remainder, uniformly in `φ` — the selected steering angle is differentiable in
the path parameter, and its derivative is the periodic solution of the
linearized equation.  This is the paper's lemma *Smooth dependence of the
selected rear* at the level of the steering angle.

Main results:

* `abs_sin_taylor` — the first-order Taylor bound `|sin(x+k) - sin x - cos x k|
  ≤ k²`;
* `hasDerivAt_selected_steering` — the smooth dependence.
-/

noncomputable section

open Real Set

namespace SteeringSmoothDependence

/-- The first-order Taylor bound for the sine, with the (non-optimal but
sufficient) constant `1`. -/
theorem abs_sin_taylor (x k : ℝ) : |Real.sin (x + k) - Real.sin x - Real.cos x * k| ≤ k ^ 2 := by
  set g : ℝ → ℝ := fun t => Real.sin (x + t) - Real.sin x - Real.cos x * t with hg
  have hd : ∀ t, HasDerivAt g (Real.cos (x + t) - Real.cos x) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Real.sin (x + t)) (Real.cos (x + t)) t := by
      simpa using (Real.hasDerivAt_sin (x + t)).comp t ((hasDerivAt_id t).const_add x)
    simpa [hg] using (h1.sub_const (Real.sin x)).sub ((hasDerivAt_id t).const_mul (Real.cos x))
  have habs : ∀ t ∈ uIcc (0:ℝ) k, |t| ≤ |k| := by
    intro t ht
    rcases le_total 0 k with hk | hk
    · rw [uIcc_of_le hk] at ht
      rw [abs_of_nonneg ht.1, abs_of_nonneg hk]
      exact ht.2
    · rw [uIcc_of_ge hk] at ht
      rw [abs_of_nonpos ht.2, abs_of_nonpos hk]
      linarith [ht.1]
  have hbd : ∀ t ∈ uIcc (0:ℝ) k, ‖Real.cos (x + t) - Real.cos x‖ ≤ |k| := by
    intro t ht
    have h1 : |Real.cos (x + t) - Real.cos x| ≤ |t| := by
      have := Real.lipschitzWith_cos.dist_le_mul (x + t) x
      simpa [Real.dist_eq] using this
    simpa using h1.trans (habs t ht)
  have hmain := (convex_uIcc (0:ℝ) k).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := fun t => Real.cos (x + t) - Real.cos x)
    (fun t _ => (hd t).hasDerivWithinAt) hbd left_mem_uIcc right_mem_uIcc
  have hg0 : g 0 = 0 := by simp [hg]
  rw [hg0] at hmain
  have hgk : |g k| ≤ |k| * |k| := by simpa using hmain
  calc |Real.sin (x + k) - Real.sin x - Real.cos x * k| = |g k| := by rw [hg]
    _ ≤ |k| * |k| := hgk
    _ = k ^ 2 := by rw [← abs_mul, abs_of_nonneg (mul_self_nonneg k)]; ring

set_option maxHeartbeats 1600000 in
/-- **Smooth dependence of the selected steering angle.**  Let `δ(a, ·)` be, for
each value `a` of the path parameter, the `P`-periodic solution of the steering
equation `δ_φ = 1 - q(a,φ) sin δ` inside the selected strip
`0 ≤ δ ≤ arcsin κ̂`, with the radius of curvature bounded by
`κ̂⁻¹ ≤ q ≤ Q`, Lipschitz in the parameter and with a first-order expansion
`q(a,φ) = q(a₀,φ) + (a-a₀) q̇(φ) + O((a-a₀)²)` uniform in `φ`.  Let `w` be the
periodic solution of the linearized equation
`w_φ = -q cos δ · w - q̇ sin δ`.  Then `a ↦ δ(a, φ)` is differentiable at `a₀`,
with derivative `w φ`. -/
theorem hasDerivAt_selected_steering
    {q delta : ℝ → ℝ → ℝ} {qdot w : ℝ → ℝ} {a0 P kap Q Qd Qlip Cq : ℝ}
    (hP : 0 < P) (hkap : 0 < kap) (hkap1 : kap < 1)
    (hsol : ∀ a x, HasDerivAt (delta a) (1 - q a x * Real.sin (delta a x)) x)
    (hper : ∀ a, Function.Periodic (delta a) P)
    (hstrip : ∀ a x, delta a x ∈ Icc (0:ℝ) (Real.arcsin kap))
    (hqlow : ∀ a x, kap⁻¹ ≤ q a x) (hqup : ∀ a x, q a x ≤ Q)
    (hqlip : ∀ a x, |q a x - q a0 x| ≤ Qlip * |a - a0|)
    (hqtaylor : ∀ a x, |q a x - q a0 x - (a - a0) * qdot x| ≤ Cq * (a - a0) ^ 2)
    (hqdot : ∀ x, |qdot x| ≤ Qd) (hCq : 0 ≤ Cq)
    (hw : ∀ x, HasDerivAt w
      (-(q a0 x * Real.cos (delta a0 x)) * w x - qdot x * Real.sin (delta a0 x)) x)
    (hwper : Function.Periodic w P) (x : ℝ) :
    HasDerivAt (fun a => delta a x) (w x) a0 := by
  set m : ℝ := Real.sqrt (1 - kap ^ 2) with hm
  have hmpos : 0 < m := by
    rw [hm]
    exact Real.sqrt_pos.mpr (by nlinarith)
  have hm1 : m ≤ 1 := by
    rw [hm]
    have : Real.sqrt (1 - kap ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith)
    simpa using this
  set c : ℝ := m / kap with hc
  have hcpos : 0 < c := div_pos hmpos hkap
  have hQnn : 0 ≤ Q := le_trans (by positivity) (le_trans (hqlow a0 x) (hqup a0 x))
  have hQdnn : 0 ≤ Qd := le_trans (abs_nonneg _) (hqdot x)
  -- the steering angles differ by at most `π/2 ≤ 2`
  have hdiff2 : ∀ a s, |delta a s - delta a0 s| ≤ 2 := by
    intro a s
    have h1 := hstrip a s
    have h2 := hstrip a0 s
    have harc : Real.arcsin kap ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two kap
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    rw [abs_le]
    constructor <;> [linarith [h1.1, h2.2]; linarith [h1.2, h2.1]]
  refine PeriodicParameterDeriv.hasDerivAt_param_periodic
    (f := fun a s u => 1 - q a s * Real.sin u)
    (fa := fun _ s _ => -(qdot s * Real.sin (delta a0 s)))
    (fy := fun a s u => -(q a s * Real.cos u))
    (y := delta) (w := w) (a0 := a0) (P := P) (c := c)
    (C := Q + 2 * Qd + 7 * Cq) (A := Qlip)
    hP hcpos (by positivity) hsol hper ?_ ?_ ?_ ?_ ?_ hwper x
  · -- dissipativity
    intro a s
    have hsin := SelectedRear.sin_sub_mul_self_ge (kap := kap) (hstrip a s) (hstrip a0 s)
    have hq : kap⁻¹ ≤ q a s := hqlow a s
    have hqpos : 0 < q a s := lt_of_lt_of_le (by positivity) hq
    have hstep : m * (delta a s - delta a0 s) ^ 2
        ≤ (Real.sin (delta a s) - Real.sin (delta a0 s)) * (delta a s - delta a0 s) := hsin
    have hmul : q a s * (m * (delta a s - delta a0 s) ^ 2)
        ≤ q a s * ((Real.sin (delta a s) - Real.sin (delta a0 s)) * (delta a s - delta a0 s)) :=
      mul_le_mul_of_nonneg_left hstep hqpos.le
    have hlow : c * (delta a s - delta a0 s) ^ 2 ≤ q a s * (m * (delta a s - delta a0 s) ^ 2) := by
      have h1 : c ≤ q a s * m := by
        rw [hc]
        have : kap⁻¹ * m ≤ q a s * m := mul_le_mul_of_nonneg_right hq hmpos.le
        calc m / kap = kap⁻¹ * m := by field_simp
          _ ≤ q a s * m := this
      nlinarith [sq_nonneg (delta a s - delta a0 s)]
    have hexp : (1 - q a s * Real.sin (delta a s) - (1 - q a s * Real.sin (delta a0 s)))
        * (delta a s - delta a0 s)
        = -(q a s * ((Real.sin (delta a s) - Real.sin (delta a0 s))
          * (delta a s - delta a0 s))) := by ring
    rw [hexp]
    linarith
  · -- Lipschitz dependence on the parameter
    intro a s
    have hexp : (1 - q a s * Real.sin (delta a0 s)) - (1 - q a0 s * Real.sin (delta a0 s))
        = -((q a s - q a0 s) * Real.sin (delta a0 s)) := by ring
    rw [hexp, abs_neg, abs_mul]
    calc |q a s - q a0 s| * |Real.sin (delta a0 s)| ≤ (Qlip * |a - a0|) * 1 := by
          refine mul_le_mul (hqlip a s) (Real.abs_sin_le_one _) (abs_nonneg _) ?_
          exact le_trans (abs_nonneg _) (hqlip a s)
      _ = Qlip * |a - a0| := by ring
  · -- the linearized coefficient is bounded below
    intro s
    have hcos : m ≤ Real.cos (delta a0 s) :=
      Shadowing.cos_ge_of_mem_strip (hstrip a0 s).1 (hstrip a0 s).2
    have hq : kap⁻¹ ≤ q a0 s := hqlow a0 s
    have hqpos : 0 < q a0 s := lt_of_lt_of_le (by positivity) hq
    have h1 : kap⁻¹ * m ≤ q a0 s * Real.cos (delta a0 s) := by
      refine mul_le_mul hq hcos hmpos.le hqpos.le
    have h2 : c = kap⁻¹ * m := by rw [hc]; field_simp
    simp only [neg_neg]
    rw [h2]
    exact h1
  · -- the Taylor remainder is quadratic
    intro a s
    set h : ℝ := a - a0 with hhdef
    set k : ℝ := delta a s - delta a0 s with hkdef
    set S : ℝ := Real.sin (delta a0 s) with hS
    set Cc : ℝ := Real.cos (delta a0 s) with hCc
    set sigma : ℝ := Real.sin (delta a s) - S - Cc * k with hsigma
    set rho : ℝ := q a s - q a0 s - h * qdot s with hrho
    have hsigmabd : |sigma| ≤ k ^ 2 := by
      have := abs_sin_taylor (delta a0 s) k
      have hks : delta a0 s + k = delta a s := by rw [hkdef]; ring
      rw [hks] at this
      simpa [hsigma, hS, hCc] using this
    have hrhobd : |rho| ≤ Cq * h ^ 2 := by
      have := hqtaylor a s
      simpa [hrho, hhdef] using this
    have hkbd : |k| ≤ 2 := hdiff2 a s
    have hSbd : |S| ≤ 1 := Real.abs_sin_le_one _
    have hCcbd : |Cc| ≤ 1 := Real.abs_cos_le_one _
    have hq0bd : |q a0 s| ≤ Q := by
      rw [abs_of_nonneg (le_trans (by positivity) (hqlow a0 s))]
      exact hqup a0 s
    have hqdotbd : |qdot s| ≤ Qd := hqdot s
    -- the exact decomposition of the remainder
    have hid : (1 - q a s * Real.sin (delta a s)) - (1 - q a0 s * Real.sin (delta a0 s))
        - (-(qdot s * Real.sin (delta a0 s))) * h - (-(q a0 s * Real.cos (delta a0 s))) * k
        = -(q a0 s * sigma) - qdot s * h * (Cc * k + sigma)
          - rho * (S + Cc * k + sigma) := by
      simp only [hsigma, hrho, hS, hCc, hkdef, hhdef]
      ring
    rw [hid]
    -- bound the three terms
    have hb1 : |q a0 s * sigma| ≤ Q * k ^ 2 := by
      rw [abs_mul]
      exact mul_le_mul hq0bd hsigmabd (abs_nonneg _) hQnn
    have hb2 : |qdot s * h * (Cc * k + sigma)| ≤ Qd * |h| * (|k| + k ^ 2) := by
      rw [abs_mul, abs_mul]
      have hfac : |Cc * k + sigma| ≤ |k| + k ^ 2 := by
        calc |Cc * k + sigma| ≤ |Cc * k| + |sigma| := abs_add_le _ _
          _ ≤ |k| + k ^ 2 := by
              refine add_le_add ?_ hsigmabd
              rw [abs_mul]
              calc |Cc| * |k| ≤ 1 * |k| := mul_le_mul_of_nonneg_right hCcbd (abs_nonneg _)
                _ = |k| := one_mul _
      refine mul_le_mul (mul_le_mul hqdotbd le_rfl (abs_nonneg _) hQdnn) hfac (abs_nonneg _) ?_
      positivity
    have hb3 : |rho * (S + Cc * k + sigma)| ≤ Cq * h ^ 2 * (1 + |k| + k ^ 2) := by
      rw [abs_mul]
      have hfac : |S + Cc * k + sigma| ≤ 1 + |k| + k ^ 2 := by
        calc |S + Cc * k + sigma| ≤ |S + Cc * k| + |sigma| := abs_add_le _ _
          _ ≤ (|S| + |Cc * k|) + |sigma| := by gcongr; exact abs_add_le _ _
          _ ≤ 1 + |k| + k ^ 2 := by
              refine add_le_add (add_le_add hSbd ?_) hsigmabd
              rw [abs_mul]
              calc |Cc| * |k| ≤ 1 * |k| := mul_le_mul_of_nonneg_right hCcbd (abs_nonneg _)
                _ = |k| := one_mul _
      refine mul_le_mul hrhobd hfac (abs_nonneg _) ?_
      positivity
    have hksq : k ^ 2 ≤ 2 * |k| := by
      have : k ^ 2 = |k| * |k| := by
        rw [← abs_mul, abs_of_nonneg (mul_self_nonneg k)]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hkbd (abs_nonneg _)
    have hkh : |h| * |k| ≤ (h ^ 2 + k ^ 2) / 2 := by
      have h1 : (|h| - |k|) ^ 2 ≥ 0 := sq_nonneg _
      have h2 : |h| ^ 2 = h ^ 2 := sq_abs h
      have h3 : |k| ^ 2 = k ^ 2 := sq_abs k
      nlinarith
    have hktwo : k ^ 2 ≤ 4 := by
      have h1 : |k| * |k| ≤ 2 * 2 := mul_self_le_mul_self (abs_nonneg k) hkbd
      have h2 : |k| * |k| = k ^ 2 := by rw [← abs_mul, abs_of_nonneg (mul_self_nonneg k)]; ring
      linarith [h2 ▸ h1]
    have habs3 : ∀ u v z : ℝ, |u - v - z| ≤ |u| + |v| + |z| := by
      intro u v z
      have e1 : |u - v - z| ≤ |u - v| + |z| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (u - v) (-z)
      have e2 : |u - v| ≤ |u| + |v| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le u (-v)
      linarith
    have hsum := habs3 (-(q a0 s * sigma)) (qdot s * h * (Cc * k + sigma))
      (rho * (S + Cc * k + sigma))
    rw [abs_neg] at hsum
    refine le_trans hsum ?_
    have hQk : Qd * |h| * (|k| + k ^ 2) ≤ Qd * (3 * ((h ^ 2 + k ^ 2) / 2)) := by
      have h1 : |k| + k ^ 2 ≤ 3 * |k| := by linarith
      have h2 : |h| * (|k| + k ^ 2) ≤ |h| * (3 * |k|) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      have h3 : |h| * (3 * |k|) = 3 * (|h| * |k|) := by ring
      have h4 : 3 * (|h| * |k|) ≤ 3 * ((h ^ 2 + k ^ 2) / 2) := by linarith
      calc Qd * |h| * (|k| + k ^ 2) = Qd * (|h| * (|k| + k ^ 2)) := by ring
        _ ≤ Qd * (3 * ((h ^ 2 + k ^ 2) / 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ hQdnn
            linarith
    have hCqk : Cq * h ^ 2 * (1 + |k| + k ^ 2) ≤ Cq * (7 * h ^ 2) := by
      have h1 : 1 + |k| + k ^ 2 ≤ 7 := by nlinarith [abs_nonneg k]
      have h2 : h ^ 2 * (1 + |k| + k ^ 2) ≤ h ^ 2 * 7 :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg h)
      calc Cq * h ^ 2 * (1 + |k| + k ^ 2) = Cq * (h ^ 2 * (1 + |k| + k ^ 2)) := by ring
        _ ≤ Cq * (h ^ 2 * 7) := mul_le_mul_of_nonneg_left h2 hCq
        _ = Cq * (7 * h ^ 2) := by ring
    have t1 : Q * k ^ 2 ≤ Q * (h ^ 2 + k ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith [sq_nonneg h]) hQnn
    have t2 : Qd * (3 * ((h ^ 2 + k ^ 2) / 2)) ≤ 2 * Qd * (h ^ 2 + k ^ 2) := by
      have : 0 ≤ Qd * (h ^ 2 + k ^ 2) :=
        mul_nonneg hQdnn (by positivity)
      nlinarith
    have t3 : Cq * (7 * h ^ 2) ≤ 7 * Cq * (h ^ 2 + k ^ 2) := by
      have : 0 ≤ Cq * k ^ 2 := mul_nonneg hCq (sq_nonneg k)
      nlinarith
    have hgoal : Q * (h ^ 2 + k ^ 2) + 2 * Qd * (h ^ 2 + k ^ 2) + 7 * Cq * (h ^ 2 + k ^ 2)
        = (Q + 2 * Qd + 7 * Cq) * (h ^ 2 + k ^ 2) := by ring
    linarith [hb1, hb2, hb3, hQk, hCqk, t1, t2, t3]
  · -- the linearized equation
    intro s
    refine (hw s).congr_deriv ?_
    ring

/-- The hypotheses of `hasDerivAt_selected_steering` are consistent and the
conclusion is meaningful.  Take `κ̂ = 1/2` and the (spatially constant) family of
radii of curvature `q(a) = 2 + a²/(1+a²) ∈ [2,3] = [κ̂⁻¹, Q]`.  The selected
steering angle is then the constant `arcsin (1/q(a))`, and the theorem yields its
differentiability at `a = 0`, with derivative `0`. -/
example : HasDerivAt (fun a : ℝ => Real.arcsin (1 / (2 + a ^ 2 / (1 + a ^ 2)))) 0 0 := by
  have hden : ∀ a : ℝ, (0:ℝ) < 1 + a ^ 2 := fun a => by positivity
  have hfrac0 : ∀ a : ℝ, 0 ≤ a ^ 2 / (1 + a ^ 2) := fun a => by positivity
  have hfrac1 : ∀ a : ℝ, a ^ 2 / (1 + a ^ 2) ≤ 1 := by
    intro a; rw [div_le_one (hden a)]; linarith
  have hq2 : ∀ a : ℝ, (2:ℝ) ≤ 2 + a ^ 2 / (1 + a ^ 2) := fun a => by linarith [hfrac0 a]
  have hq3 : ∀ a : ℝ, 2 + a ^ 2 / (1 + a ^ 2) ≤ 3 := fun a => by linarith [hfrac1 a]
  have hinv0 : ∀ a : ℝ, 0 ≤ 1 / (2 + a ^ 2 / (1 + a ^ 2)) := fun a => by
    have := hq2 a; positivity
  have hinv2 : ∀ a : ℝ, 1 / (2 + a ^ 2 / (1 + a ^ 2)) ≤ 1 / 2 := fun a =>
    one_div_le_one_div_of_le (by norm_num) (hq2 a)
  have hsinval : ∀ a : ℝ,
      Real.sin (Real.arcsin (1 / (2 + a ^ 2 / (1 + a ^ 2))))
        = 1 / (2 + a ^ 2 / (1 + a ^ 2)) := by
    intro a
    refine Real.sin_arcsin ?_ ?_
    · linarith [hinv0 a]
    · linarith [hinv2 a]
  have hprod : ∀ a : ℝ,
      1 - (2 + a ^ 2 / (1 + a ^ 2)) * Real.sin (Real.arcsin (1 / (2 + a ^ 2 / (1 + a ^ 2))))
        = 0 := by
    intro a
    have h : (2 + a ^ 2 / (1 + a ^ 2)) ≠ 0 := by linarith [hq2 a]
    rw [hsinval a, mul_one_div, div_self h, sub_self]
  exact hasDerivAt_selected_steering
    (q := fun a _ => 2 + a ^ 2 / (1 + a ^ 2))
    (delta := fun a _ => Real.arcsin (1 / (2 + a ^ 2 / (1 + a ^ 2))))
    (qdot := fun _ => 0) (w := fun _ => 0) (a0 := 0) (P := 1) (kap := 1/2)
    (Q := 3) (Qd := 0) (Qlip := 1) (Cq := 1)
    one_pos (by norm_num) (by norm_num)
    (fun a x => by rw [hprod a]; exact hasDerivAt_const x _)
    (fun a x => rfl)
    (fun a x => by
      constructor
      · exact Real.arcsin_nonneg.mpr (hinv0 a)
      · exact Real.arcsin_le_arcsin (hinv2 a))
    (fun a x => by rw [show ((1:ℝ)/2)⁻¹ = 2 by norm_num]; exact hq2 a)
    (fun a x => hq3 a)
    (fun a x => by
      have h : (2 + a ^ 2 / (1 + a ^ 2)) - (2 + 0 ^ 2 / (1 + 0 ^ 2))
          = a ^ 2 / (1 + a ^ 2) := by norm_num
      rw [h, abs_of_nonneg (hfrac0 a), sub_zero, one_mul]
      rw [div_le_iff₀ (hden a)]
      nlinarith [abs_nonneg a, sq_abs a, sq_nonneg (|a| - 1), abs_nonneg a])
    (fun a x => by
      have h : (2 + a ^ 2 / (1 + a ^ 2)) - (2 + 0 ^ 2 / (1 + 0 ^ 2)) - (a - 0) * 0
          = a ^ 2 / (1 + a ^ 2) := by ring_nf
      rw [h, abs_of_nonneg (hfrac0 a), sub_zero, one_mul]
      exact div_le_self (sq_nonneg a) (by linarith [sq_nonneg a]))
    (fun x => by norm_num) zero_le_one
    (fun x => by simpa using hasDerivAt_const x (0:ℝ))
    (fun x => rfl) 0

end SteeringSmoothDependence
