import Mathlib
import UnitTangentIterates.SelectedRear

/-!
# Existence of the periodic linearized solution

The lemma *Smooth dependence of the selected rear* (`lem:path-inverse`) of
*A Noncircular Oval with Convex Unit-Tangent Iterates* argues that

> The periodic linear operator is invertible, with a positive Green kernel and
> uniform bounds.

The uniform bound is `SelectedRear.periodic_linear_sup_bound`.  The EXISTENCE
half of the invertibility — a periodic solution of `w' + a·w = f` for a
positive coefficient `a` — was not yet constructed anywhere in the project.
This file supplies it, by the integrating-factor fixed-point ansatz:

* `exists_periodic_linear_solution` : if `a`, `f` are continuous and
  `P`-periodic with `a ≥ c > 0`, there is a `P`-periodic `w` solving
  `w' + a·w = f`;
* `existsUnique_periodic_linear_solution` : combined with
  `SelectedRear.periodic_linear_sup_bound` applied with `f = 0`, the periodic
  solution is unique — the periodic linearization really is invertible.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace SelectedRearSmoothDependence

variable {a f : ℝ → ℝ}

/-- An antiderivative of a continuous function, normalized at `0`. -/
private theorem exists_antideriv (hac : Continuous a) :
    ∃ A : ℝ → ℝ, (∀ x, HasDerivAt A (a x) x) ∧ Continuous A ∧
      ∀ x, A x = ∫ y in (0:ℝ)..x, a y := by
  refine ⟨fun x => ∫ y in (0:ℝ)..x, a y, fun x => ?_, ?_, fun _ => rfl⟩
  · exact intervalIntegral.integral_hasDerivAt_right (hac.intervalIntegrable _ _)
      (hac.stronglyMeasurableAtFilter _ _) hac.continuousAt
  · exact (intervalIntegral.differentiable_integral_of_continuous hac).continuous

/-- Two solutions of the homogeneous equation `v' + a·v = 0` agreeing at one
point agree everywhere. -/
private theorem eq_of_linear_hom_eq_at {v z : ℝ → ℝ} {a : ℝ → ℝ}
    (hac : Continuous a)
    (hv : ∀ x, HasDerivAt v (-(a x * v x)) x)
    (hz : ∀ x, HasDerivAt z (-(a x * z x)) x) (x₀ y : ℝ) (he : v x₀ = z x₀) :
    v y = z y := by
  obtain ⟨A, hA, hAc, -⟩ := exists_antideriv (a := a) hac
  set g : ℝ → ℝ := fun t => Real.exp (A t) * (v t - z t) with hgdef
  have hgderiv : ∀ t, HasDerivAt g 0 t := by
    intro t
    have h1 : HasDerivAt (fun t => Real.exp (A t)) (Real.exp (A t) * a t) t :=
      (hA t).exp
    have h2 : HasDerivAt (fun t => v t - z t) (-(a t * v t) - -(a t * z t)) t :=
      (hv t).sub (hz t)
    have h3 := h1.mul h2
    refine h3.congr_deriv ?_
    ring
  have hgconst : ∀ t, g t = g x₀ := by
    intro t
    have hdiff : Differentiable ℝ g := fun s => (hgderiv s).differentiableAt
    exact (is_const_of_deriv_eq_zero hdiff (fun s => (hgderiv s).deriv) x₀ t).symm
  have hexpmul : ∀ t, Real.exp (-A t) * Real.exp (A t) = 1 := fun t =>
    by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hsplit : ∀ t, v t - z t = Real.exp (-A t) * g t := by
    intro t
    show v t - z t = Real.exp (-A t) * (Real.exp (A t) * (v t - z t))
    rw [← mul_assoc, hexpmul t]
    ring
  have hg0 : Real.exp (-A x₀) * g x₀ = 0 := by
    rw [← hsplit x₀, he, sub_self]
  calc v y = z y + (v y - z y) := by ring
    _ = z y + Real.exp (-A y) * g y := by rw [hsplit y]
    _ = z y + Real.exp (-A y) * g x₀ := by rw [hgconst y]
    _ = z y := by
        have hx := hg0
        have hzero : g x₀ = 0 := by
          by_contra hcon
          exact Real.exp_ne_zero (-A x₀) (mul_eq_zero.mp hx |>.resolve_right hcon)
        rw [hzero, mul_zero, add_zero]

/-- **Existence of the periodic solution of the linearized equation.**
If `a` and `f` are continuous and `P`-periodic with `a ≥ c > 0`, the equation
`w' + a·w = f` has a `P`-periodic solution. -/
theorem exists_periodic_linear_solution (hac : Continuous a) (hfc : Continuous f)
    (hper_a : Function.Periodic a P) (hper_f : Function.Periodic f P)
    (hP : 0 < P) (hc : 0 < c) (ha : ∀ x, c ≤ a x) :
    ∃ w : ℝ → ℝ, (∀ x, HasDerivAt w (f x - a x * w x) x) ∧ Function.Periodic w P := by
  obtain ⟨A, hA, hAc, hintA⟩ := exists_antideriv (a := a) hac
  have hA0 : A 0 = 0 := by simpa using hintA 0
  -- the one-period growth `A P` is positive
  have hAPge : c * P ≤ A P := by
    rw [hintA P]
    have hc1 : (∫ y in (0:ℝ)..P, (c:ℝ)) ≤ ∫ y in (0:ℝ)..P, a y :=
      intervalIntegral.integral_mono hP.le
        (continuous_const.intervalIntegrable _ P) (hac.intervalIntegrable _ P)
        (fun y => ha y)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm] at hc1
    exact hc1
  have hAPpos : 0 < A P := lt_of_lt_of_le (by nlinarith) hAPge
  -- the weighted primitive of `e^{A} f`
  have hGcont : Continuous (fun x => Real.exp (A x) * f x) :=
    (Real.continuous_exp.comp hAc).mul hfc
  have hGderiv : ∀ t : ℝ, HasDerivAt
      (fun u => ∫ y in (0:ℝ)..u, Real.exp (A y) * f y) (Real.exp (A t) * f t) t :=
    fun t => intervalIntegral.integral_hasDerivAt_right (hGcont.intervalIntegrable _ _)
      (hGcont.stronglyMeasurableAtFilter _ _) hGcont.continuousAt
  -- the fixed-point initial value
  have hone : Real.exp (A P) - 1 ≠ 0 := by
    have hlt : (1:ℝ) < Real.exp (A P) :=
      calc (1:ℝ) = Real.exp 0 := by rw [Real.exp_zero]
        _ < Real.exp (A P) := Real.exp_strictMono hAPpos
    linarith
  set β : ℝ := (∫ y in (0:ℝ)..P, Real.exp (A y) * f y) / (Real.exp (A P) - 1) with hβdef
  have hGPβ : (∫ y in (0:ℝ)..P, Real.exp (A y) * f y)
      = β * (Real.exp (A P) - 1) := by
    rw [hβdef, div_mul_cancel₀ _ hone]
  -- the candidate solution
  set W : ℝ → ℝ := fun x => Real.exp (-A x) * (β + ∫ y in (0:ℝ)..x, Real.exp (A y) * f y)
    with hWdef
  have hwderiv : ∀ t, HasDerivAt W (f t - a t * W t) t := by
    intro t
    have h1 : HasDerivAt (fun u => Real.exp (-A u)) (Real.exp (-A t) * -(a t)) t :=
      ((hA t).neg).exp
    have h2 : HasDerivAt (fun u => β + ∫ y in (0:ℝ)..u, Real.exp (A y) * f y)
        (Real.exp (A t) * f t) t := by
      exact HasDerivAt.const_add β (hGderiv t)
    have heq : Real.exp (-A t) * Real.exp (A t) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [hWdef]
    refine (h1.mul h2).congr_deriv ?_
    show Real.exp (-A t) * -(a t) * (β + ∫ y in (0:ℝ)..t, Real.exp (A y) * f y)
        + Real.exp (-A t) * (Real.exp (A t) * f t)
        = f t - a t * (Real.exp (-A t) * (β + ∫ y in (0:ℝ)..t, Real.exp (A y) * f y))
    rw [← mul_assoc, heq, one_mul]
    ring
  -- periodicity: the shifted solution agrees with `W` at `0`, hence everywhere
  have hwper : Function.Periodic W P := by
    intro x
    have hwP : ∀ t, HasDerivAt (fun r => W (r + P)) (f t - a t * W (t + P)) t := by
      intro t
      have hcomp : HasDerivAt (fun r => r + P) (1:ℝ) t := by
        simpa using (hasDerivAt_id t).add_const P
      have hbase := (hwderiv (t + P)).scomp t hcomp
      rw [hper_f t, hper_a t] at hbase
      refine hbase.congr_deriv ?_
      simp
    have hvzero : ∀ t, W t - W (t + P) = 0 := by
      intro t
      refine eq_of_linear_hom_eq_at (a := a) hac
        (v := fun r => W r - W (r + P)) (z := fun _ => (0:ℝ))
        (x₀ := 0) (y := t) ?_ ?_ ?_
      · intro s
        refine ((hwderiv s).sub (hwP s)).congr_deriv ?_
        show (f s - a s * W s) - (f s - a s * W (s + P))
            = -(a s * (W s - W (s + P)))
        ring
      · intro s
        refine (hasDerivAt_const s (0:ℝ)).congr_deriv ?_
        simp
      · have hW0 : W 0 = β := by
          rw [hWdef]
          show Real.exp (-A 0) * (β + ∫ y in (0:ℝ)..0, Real.exp (A y) * f y) = β
          rw [hA0]
          simp
        have hWP : W P = β := by
          have hy0 : Real.exp (A P) ≠ 0 := Real.exp_ne_zero _
          rw [hWdef]
          show Real.exp (-A P) * (β + ∫ y in (0:ℝ)..P, Real.exp (A y) * f y) = β
          rw [hGPβ, Real.exp_neg (A P)]
          field_simp
          ring
        show W 0 - W (0 + P) = 0
        rw [zero_add, hW0, hWP]
        ring
    linarith [hvzero x]
  exact ⟨W, hwderiv, hwper⟩

/-- **Invertibility of the periodic linearization**: the periodic solution of
`w' + a·w = f` exists and is unique. -/
theorem existsUnique_periodic_linear_solution (hac : Continuous a) (hfc : Continuous f)
    (hper_a : Function.Periodic a P) (hper_f : Function.Periodic f P)
    (hP : 0 < P) (hc : 0 < c) (ha : ∀ x, c ≤ a x) :
    ∃! w : ℝ → ℝ, (∀ x, HasDerivAt w (f x - a x * w x) x) ∧ Function.Periodic w P := by
  obtain ⟨W₀, hd₀, hp₀⟩ :=
    exists_periodic_linear_solution hac hfc hper_a hper_f hP hc ha
  refine ⟨W₀, ⟨hd₀, hp₀⟩, ?_⟩
  rintro w₁ ⟨hd₁, hp₁⟩
  set v : ℝ → ℝ := fun x => w₁ x - W₀ x with hvdef
  have hvhom : ∀ x, HasDerivAt v ((0:ℝ) - a x * v x) x := by
    intro x
    have hsub := (hd₁ x).sub (hd₀ x)
    refine hsub.congr_deriv ?_
    show f x - a x * w₁ x - (f x - a x * W₀ x) = 0 - a x * (w₁ x - W₀ x)
    ring
  have hper_v : Function.Periodic v P := fun x => by
    show w₁ (x + P) - W₀ (x + P) = w₁ x - W₀ x
    rw [hp₁ x, hp₀ x]
  have hbound := SelectedRear.periodic_linear_sup_bound (w := v)
    (a := a) (f := fun _ => (0:ℝ)) (P := P) (c := c) (M := 0)
    hP hvhom hper_v hc ha (fun x => by simp)
  funext x
  have hx := hbound x
  have hvn := abs_nonneg (v x)
  show w₁ x = W₀ x
  rw [zero_div] at hx
  obtain ⟨h1, h2⟩ := abs_le.mp hx
  linarith

/-- **Continuous dependence in the normalized convention.**  Two periodic
solutions of `δ' = 1 − qᵢ·sin δ`, each with its own curvature radius `qᵢ`,
both inside the selected strip `[0, arcsin κ̂]` and with `q² ≥ κ̂^{-1}`,
satisfy `‖δ¹ − δ²‖_∞ ≤ κ̂ ‖q¹ − q²‖_∞ / √(1−κ̂²)`. -/
private theorem steering_q_sub_le {q1 q2 d1 d2 : ℝ → ℝ} {P kap M : ℝ}
    (hP : 0 < P) (hkap1 : kap < 1) (hkap0 : 0 < kap)
    (h1 : ∀ s, HasDerivAt d1 (1 - q1 s * Real.sin (d1 s)) s)
    (h2 : ∀ s, HasDerivAt d2 (1 - q2 s * Real.sin (d2 s)) s)
    (hp1 : Function.Periodic d1 P) (hp2 : Function.Periodic d2 P)
    (hs1 : ∀ s, d1 s ∈ Icc (0:ℝ) (arcsin kap)) (hs2 : ∀ s, d2 s ∈ Icc (0:ℝ) (arcsin kap))
    (hM : ∀ s, |q1 s - q2 s| ≤ M) (hq2 : ∀ s, kap⁻¹ ≤ q2 s) :
    ∀ s, |d1 s - d2 s| ≤ kap * M / Real.sqrt (1 - kap ^ 2) := by
  have hmpos : 0 < Real.sqrt (1 - kap ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  have hkap00 : (0:ℝ) ≤ kap := le_of_lt hkap0
  have hMnn : 0 ≤ M := le_trans (abs_nonneg (q1 0 - q2 0)) (hM 0)
  have hpipos : (0:ℝ) < π := Real.pi_pos
  have harc : Real.arcsin kap ≤ π / 2 := Real.arcsin_le_pi_div_two kap
  have hq2pos : ∀ s, 0 < q2 s := fun s => lt_of_lt_of_le (inv_pos.mpr hkap0) (hq2 s)
  set w : ℝ → ℝ := fun s => d1 s - d2 s with hwdef
  have hwd : ∀ s, HasDerivAt w (q2 s * Real.sin (d2 s) - q1 s * Real.sin (d1 s)) s := by
    intro s
    simpa [hwdef] using ((h1 s).sub (h2 s)).congr_deriv (by ring)
  have hdiff : Differentiable ℝ w := fun s => (hwd s).differentiableAt
  have hwper : Function.Periodic w P := fun s => by simp [hwdef, hp1 s, hp2 s]
  obtain ⟨t0, ht0mem, ht0⟩ := isCompact_Icc.exists_isMaxOn (s := Icc (0:ℝ) P)
    (Set.nonempty_Icc.mpr hP.le) hdiff.continuous.continuousOn
  have hglobal : ∀ s, w s ≤ w t0 := by
    intro s
    obtain ⟨y, hy, hys⟩ := hwper.exists_mem_Ico₀ hP s
    rw [hys]
    exact ht0 ⟨hy.1, hy.2.le⟩
  have hmax : IsLocalMax w t0 := Filter.Eventually.of_forall hglobal
  have hzero : q2 t0 * Real.sin (d2 t0) - q1 t0 * Real.sin (d1 t0) = 0 :=
    hmax.hasDerivAt_eq_zero (hwd t0)
  have hle : w t0 ≤ kap * M / Real.sqrt (1 - kap ^ 2) := by
    rcases le_or_gt (w t0) 0 with h | h
    · exact le_trans h (div_nonneg (mul_nonneg hkap00 hMnn) hmpos.le)
    · have hd12 : d2 t0 ≤ d1 t0 := by simpa [hwdef, sub_nonneg] using h.le
      have hd1ub : d1 t0 ≤ π / 2 := le_trans (hs1 t0).2 harc
      have hslope : Real.sqrt (1 - kap ^ 2) * (d1 t0 - d2 t0)
          ≤ Real.sin (d1 t0) - Real.sin (d2 t0) :=
        SelectedRear.sin_sub_sin_ge_of_strip (hs1 t0) (hs2 t0) hd12
      have hsinD1nn : 0 ≤ Real.sin (d1 t0) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (hs1 t0).1 (le_trans hd1ub (by linarith))
      have hsinub : Real.sin (d1 t0) ≤ kap := by
        calc Real.sin (d1 t0)
            ≤ Real.sin (Real.arcsin kap) :=
              Real.sin_le_sin_of_le_of_le_pi_div_two
                (by linarith [(hs1 t0).1, Real.pi_pos]) harc (hs1 t0).2
          _ = kap := Real.sin_arcsin (by linarith) hkap1.le
      have e1 : q2 t0 * Real.sin (d2 t0) = q1 t0 * Real.sin (d1 t0) := by linarith
      have hqrel : q2 t0 * (Real.sin (d1 t0) - Real.sin (d2 t0))
          = (q2 t0 - q1 t0) * Real.sin (d1 t0) := by
        calc q2 t0 * (Real.sin (d1 t0) - Real.sin (d2 t0))
            = q2 t0 * Real.sin (d1 t0) - q2 t0 * Real.sin (d2 t0) := by ring
          _ = q2 t0 * Real.sin (d1 t0) - q1 t0 * Real.sin (d1 t0) := by rw [e1]
          _ = (q2 t0 - q1 t0) * Real.sin (d1 t0) := by ring
      have h1b : q2 t0 * (Real.sin (d1 t0) - Real.sin (d2 t0)) ≤ M * kap := by
        calc q2 t0 * (Real.sin (d1 t0) - Real.sin (d2 t0))
            = (q2 t0 - q1 t0) * Real.sin (d1 t0) := hqrel
          _ ≤ |q2 t0 - q1 t0| * Real.sin (d1 t0) :=
                mul_le_mul_of_nonneg_right (le_abs_self _) hsinD1nn
          _ ≤ M * kap := mul_le_mul (by simpa [abs_sub_comm] using hM t0)
            hsinub hsinD1nn hMnn
      have hq2ge : (1:ℝ) ≤ kap * q2 t0 := by
        have h1' : kap⁻¹ ≤ q2 t0 := hq2 t0
        have h2' : (1:ℝ) = kap⁻¹ * kap := (inv_mul_cancel₀ (ne_of_gt hkap0)).symm
        calc (1:ℝ) = kap⁻¹ * kap := h2'
          _ ≤ q2 t0 * kap := mul_le_mul_of_nonneg_right h1' hkap00
          _ = kap * q2 t0 := by ring
      have hX : Real.sqrt (1 - kap ^ 2) * (d1 t0 - d2 t0) ≤ M * kap := by
        have P1 : Real.sqrt (1 - kap ^ 2) * (d1 t0 - d2 t0) * q2 t0
            ≤ q2 t0 * (Real.sin (d1 t0) - Real.sin (d2 t0)) :=
          by
            have hp := mul_le_mul_of_nonneg_right hslope (hq2pos t0).le
            simpa [mul_comm, mul_left_comm] using hp
        have P2 : Real.sqrt (1 - kap ^ 2) * (d1 t0 - d2 t0) * (kap * q2 t0)
            ≤ M * kap * kap := by
          have s1 : Real.sqrt (1 - kap ^ 2) * (d1 t0 - d2 t0) * (kap * q2 t0)
              = kap * (Real.sqrt (1 - kap ^ 2) * (d1 t0 - d2 t0) * q2 t0) := by ring
          rw [s1]
          calc kap * (Real.sqrt (1 - kap ^ 2) * (d1 t0 - d2 t0) * q2 t0)
              ≤ kap * (q2 t0 * (Real.sin (d1 t0) - Real.sin (d2 t0))) :=
                mul_le_mul_of_nonneg_left P1 hkap00
            _ ≤ kap * (M * kap) := mul_le_mul_of_nonneg_left h1b hkap00
            _ = M * kap * kap := by ring
        rcases le_or_gt (0:ℝ) (Real.sqrt (1 - kap ^ 2) * (d1 t0 - d2 t0)) with hxpos | hxneg
        · have P4 : Real.sqrt (1 - kap ^ 2) * (d1 t0 - d2 t0)
              ≤ Real.sqrt (1 - kap ^ 2) * (d1 t0 - d2 t0) * (kap * q2 t0) :=
            by simpa using mul_le_mul_of_nonneg_left hq2ge hxpos
          refine le_trans (le_trans P4 P2) ?_
          calc M * kap * kap ≤ M * 1 * kap :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hkap1.le hMnn) hkap00
            _ = M * kap := by ring
        · exfalso
          exact (not_lt_of_ge (mul_nonneg hmpos.le (sub_nonneg.mpr hd12))) hxneg
      rw [le_div_iff₀ hmpos]
      simpa [hwdef, mul_comm] using hX
  obtain ⟨t1, ht1mem, ht1⟩ := isCompact_Icc.exists_isMinOn (s := Icc (0:ℝ) P)
    (Set.nonempty_Icc.mpr hP.le) hdiff.continuous.continuousOn
  have hglobalMin : ∀ s, w t1 ≤ w s := by
    intro s
    obtain ⟨y, hy, hys⟩ := hwper.exists_mem_Ico₀ hP s
    rw [hys]
    exact ht1 ⟨hy.1, hy.2.le⟩
  have hmin : IsLocalMin w t1 := Filter.Eventually.of_forall hglobalMin
  have hzeroMin : q2 t1 * Real.sin (d2 t1) - q1 t1 * Real.sin (d1 t1) = 0 :=
    hmin.hasDerivAt_eq_zero (hwd t1)
  have hlo : -(kap * M / Real.sqrt (1 - kap ^ 2)) ≤ w t1 := by
    rcases le_or_gt 0 (w t1) with h | h
    · have hB0 : 0 ≤ kap * M / Real.sqrt (1 - kap ^ 2) :=
        div_nonneg (mul_nonneg hkap00 hMnn) hmpos.le
      linarith
    · have hd21 : d1 t1 ≤ d2 t1 := by simpa [hwdef, sub_nonpos] using h.le
      have hslope : Real.sqrt (1 - kap ^ 2) * (d2 t1 - d1 t1)
          ≤ Real.sin (d2 t1) - Real.sin (d1 t1) :=
        SelectedRear.sin_sub_sin_ge_of_strip (hs2 t1) (hs1 t1) hd21
      have hsinD1nn : 0 ≤ Real.sin (d1 t1) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (hs1 t1).1
          (le_trans (le_trans (hs1 t1).2 harc) (by linarith [Real.pi_pos]))
      have hsinub : Real.sin (d1 t1) ≤ kap := by
        calc Real.sin (d1 t1) ≤ Real.sin (Real.arcsin kap) :=
              Real.sin_le_sin_of_le_of_le_pi_div_two
                (by linarith [(hs1 t1).1, Real.pi_pos]) harc (hs1 t1).2
          _ = kap := Real.sin_arcsin (by linarith) hkap1.le
      have e1 : q2 t1 * Real.sin (d2 t1) = q1 t1 * Real.sin (d1 t1) := by
        linarith
      have hqrel : q2 t1 * (Real.sin (d2 t1) - Real.sin (d1 t1))
          = (q1 t1 - q2 t1) * Real.sin (d1 t1) := by
        rw [mul_sub, e1]
        ring
      have h1b : q2 t1 * (Real.sin (d2 t1) - Real.sin (d1 t1)) ≤ M * kap := by
        calc q2 t1 * (Real.sin (d2 t1) - Real.sin (d1 t1))
            = (q1 t1 - q2 t1) * Real.sin (d1 t1) := hqrel
          _ ≤ |q1 t1 - q2 t1| * Real.sin (d1 t1) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) hsinD1nn
          _ ≤ M * kap := mul_le_mul (hM t1) hsinub hsinD1nn hMnn
      have hq2ge : (1:ℝ) ≤ kap * q2 t1 := by
        calc (1:ℝ) = kap⁻¹ * kap := (inv_mul_cancel₀ (ne_of_gt hkap0)).symm
          _ ≤ q2 t1 * kap := mul_le_mul_of_nonneg_right (hq2 t1) hkap00
          _ = kap * q2 t1 := by ring
      let X : ℝ := Real.sqrt (1 - kap ^ 2) * (d2 t1 - d1 t1)
      have hX0 : 0 ≤ X := mul_nonneg hmpos.le (sub_nonneg.mpr hd21)
      have hP1 : X * q2 t1 ≤ q2 t1 * (Real.sin (d2 t1) - Real.sin (d1 t1)) := by
        have hp := mul_le_mul_of_nonneg_right hslope (hq2pos t1).le
        simpa [X, mul_comm, mul_left_comm] using hp
      have hP2 : X * (kap * q2 t1) ≤ M * kap * kap := by
        calc X * (kap * q2 t1) = kap * (X * q2 t1) := by ring
          _ ≤ kap * (q2 t1 * (Real.sin (d2 t1) - Real.sin (d1 t1))) :=
            mul_le_mul_of_nonneg_left hP1 hkap00
          _ ≤ kap * (M * kap) := mul_le_mul_of_nonneg_left h1b hkap00
          _ = M * kap * kap := by ring
      have hX : X ≤ M * kap := by
        have hgrow : X ≤ X * (kap * q2 t1) := by
          simpa using mul_le_mul_of_nonneg_left hq2ge hX0
        calc X ≤ X * (kap * q2 t1) := hgrow
          _ ≤ M * kap * kap := hP2
          _ ≤ M * 1 * kap :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hkap1.le hMnn) hkap00
          _ = M * kap := by ring
      have hdiff : d2 t1 - d1 t1 ≤ kap * M / Real.sqrt (1 - kap ^ 2) := by
        rw [le_div_iff₀ hmpos]
        simpa [X, mul_comm] using hX
      simp only [hwdef]
      linarith
  intro s
  rw [abs_le]
  exact ⟨by simpa [hwdef] using le_trans hlo (hglobalMin s),
    by simpa [hwdef] using le_trans (hglobal s) hle⟩

/-! ### Smooth dependence of the selected steering on the path parameter

With invertibility of the periodic linearization available, the difference
quotients of a family of selected steerings are shown to converge to the
linearized solution — the analytic core of the paper's Lemma *Smooth
dependence of the selected rear* (`lem:path-inverse`). -/

section TimeDependence

variable {delta q qdot : ℝ → ℝ → ℝ}

/-- `cos` is `1`-Lipschitz. -/
private theorem abs_cos_sub_cos_le (a b : ℝ) :
    |Real.cos a - Real.cos b| ≤ |a - b| := by
  have hdiff : ∀ r ∈ (univ:Set ℝ), DifferentiableAt ℝ Real.cos r := fun r _ =>
    Real.differentiable_cos r
  have hbdd : ∀ r ∈ (univ:Set ℝ), ‖deriv Real.cos r‖ ≤ 1 := by
    intro r _
    rw [Real.deriv_cos, norm_neg, Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbdd convex_univ
    (mem_univ b) (mem_univ a)
  simpa using h

/-- `sin` is `1`-Lipschitz. -/
private theorem abs_sin_sub_sin_le (a b : ℝ) :
    |Real.sin a - Real.sin b| ≤ |a - b| := by
  have hdiff : ∀ r ∈ (univ:Set ℝ), DifferentiableAt ℝ Real.sin r := fun r _ =>
    Real.differentiable_sin r
  have hbdd : ∀ r ∈ (univ:Set ℝ), ‖deriv Real.sin r‖ ≤ 1 := by
    intro r _
    rw [Real.deriv_sin, Real.norm_eq_abs]
    exact Real.abs_cos_le_one r
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbdd convex_univ
    (mem_univ b) (mem_univ a)
  simpa using h

/-- First-order Taylor remainder for `sin`: `sin u − sin v − cos v·(u − v)` is
quadratic in `u − v`. -/
private theorem abs_sin_sub_sin_sub_cos_mul_le {u v : ℝ} :
    |Real.sin u - Real.sin v - Real.cos v * (u - v)| ≤ (u - v) ^ 2 := by
  set C : ℝ := |u - v| with hCdef
  set g : ℝ → ℝ := fun r => Real.sin r - Real.cos v * r with hgdef
  have hg : ∀ r, HasDerivAt g (Real.cos r - Real.cos v) r := by
    intro r
    have hs : HasDerivAt Real.sin (Real.cos r) r := Real.hasDerivAt_sin r
    have hc : HasDerivAt (fun r : ℝ => Real.cos v * r) (Real.cos v) r :=
      by simpa using (hasDerivAt_id r).const_mul (Real.cos v)
    simpa [hgdef] using hs.sub hc
  have hdist : ∀ r ∈ Icc (min u v) (max u v), |r - v| ≤ C := by
    intro r hr
    rcases le_total u v with huv | huv
    · rw [min_eq_left huv, max_eq_right huv] at hr
      have hn : C = v - u := by
        rw [hCdef, abs_of_nonpos (by linarith : u - v ≤ 0)]
        ring
      rw [abs_le, hn]
      constructor <;> linarith [hr.1, hr.2]
    · rw [(min_eq_right huv : min u v = v), (max_eq_left huv : max u v = u)] at hr
      have hn : C = u - v := by
        rw [hCdef, abs_of_nonneg (by linarith : 0 ≤ u - v)]
      rw [abs_le, hn]
      constructor <;> linarith [hn, hr.1, hr.2]
  have hseg : ∀ x ∈ Icc (min u v) (max u v),
      ‖g x - g (min u v)‖ ≤ C * (x - min u v) := by
    intro x hx
    have hf' : ∀ r ∈ Icc (min u v) (max u v),
        HasDerivWithinAt g (Real.cos r - Real.cos v) (Icc (min u v) (max u v)) r :=
      fun r hr => (hg r).hasDerivWithinAt
    have hbdd : ∀ r ∈ Ico (min u v) (max u v), ‖Real.cos r - Real.cos v‖ ≤ C := by
      intro r hr
      rw [Real.norm_eq_abs]
      calc |Real.cos r - Real.cos v| ≤ |r - v| := abs_cos_sub_cos_le r v
        _ ≤ C := hdist r ⟨hr.1, hr.2.le⟩
    exact norm_image_sub_le_of_norm_deriv_le_segment' hf' hbdd x hx
  rcases le_total u v with huv | huv
  · have hv : v ∈ Icc (min u v) (max u v) := by
      rw [(min_eq_left huv : min u v = u), (max_eq_right huv : max u v = v)]
      exact ⟨huv, le_rfl⟩
    have hv := hseg v hv
    have hvn : v - min u v = v - u := by rw [(min_eq_left huv : min u v = u)]
    have hn : C = v - u := by
      rw [hCdef, abs_of_nonpos (by linarith : u - v ≤ 0)]
      ring
    have heq : Real.sin u - Real.sin v - Real.cos v * (u - v)
        = -(g v - g (min u v)) := by
      rw [(min_eq_left huv : min u v = u), hgdef]
      ring
    show |Real.sin u - Real.sin v - Real.cos v * (u - v)| ≤ (u - v) ^ 2
    calc |Real.sin u - Real.sin v - Real.cos v * (u - v)|
        = ‖g v - g (min u v)‖ := by rw [heq, ← Real.norm_eq_abs, norm_neg]
      _ ≤ C * (v - min u v) := hv
      _ = (u - v) ^ 2 := by rw [hvn, hn]; ring
  · have hu : u ∈ Icc (min u v) (max u v) := by
      rw [(min_eq_right huv : min u v = v), (max_eq_left huv : max u v = u)]
      exact ⟨huv, le_rfl⟩
    have hu := hseg u hu
    have hn : C = u - v := by
      rw [hCdef, abs_of_nonneg (by linarith : 0 ≤ u - v)]
    have heq : Real.sin u - Real.sin v - Real.cos v * (u - v)
        = g u - g (min u v) := by
      rw [(min_eq_right huv : min u v = v), hgdef]
      ring
    show |Real.sin u - Real.sin v - Real.cos v * (u - v)| ≤ (u - v) ^ 2
    calc |Real.sin u - Real.sin v - Real.cos v * (u - v)|
        = ‖g u - g (min u v)‖ := by rw [heq, ← Real.norm_eq_abs]
      _ ≤ C * (u - min u v) := hu
      _ = (u - v) ^ 2 := by rw [(min_eq_right huv : min u v = v), hn]; ring

set_option maxHeartbeats 1000000 in
/-- **Smooth dependence of the selected steering on the path parameter** (the
analytic core of paper Lemma `lem:path-inverse`).  Along a family of curvature
data whose time derivative is uniform on the circle, the selected steering is
differentiable in the parameter, with derivative the periodic solution of the
linearized equation `w' + q·cos δ·w = -q̇·sin δ`, subject to the variation
bound `‖w‖_∞ ≤ κ̂‖q̇‖_∞/√(1−κ̂²)` of
`SelectedRear.selected_steering_variation_bound`. -/
theorem hasDerivAt_selected_steering_time
    {t₀ P kap M Q : ℝ}
    (hP : 0 < P) (hkap : 0 < kap) (hkap1 : kap < 1)
    (hdelta : ∀ t, ∀ x, HasDerivAt (delta t)
      (1 - q t x * Real.sin (delta t x)) x)
    (hstrip : ∀ t x, delta t x ∈ Icc (0:ℝ) (arcsin kap))
    (hperd : ∀ t, Function.Periodic (delta t) P)
    (hperq : ∀ t, Function.Periodic (q t) P)
    (hqc : Continuous (q t₀))
    (hqlow : ∀ x, kap⁻¹ ≤ q t₀ x)
    (hqup : ∀ x, q t₀ x ≤ Q)
    (hqdotbdd : ∀ x, |qdot t₀ x| ≤ M)
    (hperqd : Function.Periodic (qdot t₀) P)
    (hqdc : Continuous (qdot t₀))
    (hqconv : ∀ ε > 0, ∃ ρ > 0, ∀ h : ℝ, h ≠ 0 → |h| < ρ →
      ∀ x, |(q (t₀ + h) x - q t₀ x) / h - qdot t₀ x| ≤ ε) :
    ∃ w : ℝ → ℝ,
      (∀ x, HasDerivAt w (-(qdot t₀ x * Real.sin (delta t₀ x))
          - q t₀ x * Real.cos (delta t₀ x) * w x) x) ∧
      Function.Periodic w P ∧
      (∀ x, HasDerivAt (fun t => delta t x) (w x) t₀) ∧
      (∀ x, |w x| ≤ kap * M / Real.sqrt (1 - kap ^ 2)) := by
  have hdc : Continuous (delta t₀) :=
    continuous_iff_continuousAt.2 fun p =>
      DifferentiableAt.continuousAt ((hdelta t₀ p).differentiableAt)
  have hspos : 0 < Real.sqrt (1 - kap ^ 2) := by
    refine Real.sqrt_pos.mpr ?_
    nlinarith
  -- in particular `Q` is positive as well
  have hQpos : 0 < Q := by
    have h1 : (0:ℝ) < kap⁻¹ := by simpa using div_pos one_pos hkap
    exact lt_of_lt_of_le h1 (le_trans (hqlow 0) (hqup 0))
  have hMnonneg : 0 ≤ M := le_trans (abs_nonneg (qdot t₀ 0)) (hqdotbdd 0)
  -- the linearized equation: `w' + q·cos δ·w = -q̇·sin δ`
  obtain ⟨w, hwlin, hwper⟩ :=
    exists_periodic_linear_solution
      (a := fun x => q t₀ x * Real.cos (delta t₀ x))
      (f := fun x => -(qdot t₀ x * Real.sin (delta t₀ x)))
      ((hqc.mul (Real.continuous_cos.comp hdc)))
      (Continuous.neg (hqdc.mul (Real.continuous_sin.comp hdc)))
      (fun x => by
        show q t₀ (x + P) * Real.cos (delta t₀ (x + P))
            = q t₀ x * Real.cos (delta t₀ x)
        rw [hperq t₀ x, hperd t₀ x])
      (fun x => by
        show -(qdot t₀ (x + P) * Real.sin (delta t₀ (x + P)))
            = -(qdot t₀ x * Real.sin (delta t₀ x))
        rw [hperqd x, hperd t₀ x])
      hP (c := kap⁻¹ * Real.sqrt (1 - kap ^ 2))
      (by simpa using mul_pos (div_pos one_pos hkap) hspos)
      (fun x => by
        have h2 := Shadowing.cos_ge_of_mem_strip (hstrip t₀ x).1 (hstrip t₀ x).2
        have hqnn : (0:ℝ) ≤ q t₀ x :=
          le_trans (le_of_lt (inv_pos.mpr hkap)) (hqlow x)
        calc kap⁻¹ * Real.sqrt (1 - kap ^ 2)
            ≤ q t₀ x * Real.sqrt (1 - kap ^ 2) :=
              mul_le_mul_of_nonneg_right (hqlow x) hspos.le
          _ ≤ q t₀ x * Real.cos (delta t₀ x) :=
              mul_le_mul_of_nonneg_left h2 hqnn)
  -- displacement of the slices under a small parameter shift
  have hdq : ∀ ε > 0, ∃ ρ > 0, ∀ h : ℝ, h ≠ 0 → |h| < ρ → ∀ x,
      |delta (t₀ + h) x - delta t₀ x| ≤ |h| * (M + ε) / Real.sqrt (1 - kap ^ 2) := by
    intro ε hεpos
    obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := hqconv ε hεpos
    refine ⟨ρ₁, hρ₁pos, fun h hh hl x => ?_⟩
    have hη : ∀ y, |q (t₀ + h) y - q t₀ y| ≤ |h| * (M + ε) := by
      intro y
      have h1 := hρ₁ h hh hl y
      have hexp : q (t₀ + h) y - q t₀ y
          = h * (((q (t₀ + h) y - q t₀ y)/h - qdot t₀ y) + qdot t₀ y) := by
        field_simp
        ring
      calc |q (t₀ + h) y - q t₀ y|
          = |h * (((q (t₀ + h) y - q t₀ y)/h - qdot t₀ y) + qdot t₀ y)| :=
              abs_eq_abs.mpr (Or.inl hexp)
        _ = |h| * |((q (t₀ + h) y - q t₀ y)/h - qdot t₀ y) + qdot t₀ y| := by
              rw [abs_mul]
        _ ≤ |h| * (ε + M) := by
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg h)
              calc |((q (t₀ + h) y - q t₀ y)/h - qdot t₀ y) + qdot t₀ y|
                  ≤ |(q (t₀ + h) y - q t₀ y)/h - qdot t₀ y| + |qdot t₀ y| :=
                    abs_add_le _ _
                _ ≤ ε + M := by linarith [h1, hqdotbdd y]
        _ = |h| * (M + ε) := by ring
    have hub := steering_q_sub_le (q1 := q (t₀+h)) (q2 := q t₀)
      (d1 := delta (t₀+h)) (d2 := delta t₀) hP hkap1 hkap
      (hdelta _) (hdelta t₀) (hperd _) (hperd t₀) (hstrip _) (hstrip t₀)
      hη (fun y => hqlow y)
    have hDpos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
    have hApos : 0 ≤ (|h| * (M + ε)) / Real.sqrt (1 - kap ^ 2) :=
      div_nonneg (mul_nonneg (abs_nonneg h) (by linarith [hMnonneg])) (by positivity)
    refine le_trans (hub x) ?_
    have hx : kap * (|h| * (M + ε)) / Real.sqrt (1 - kap ^ 2)
        = (|h| * (M + ε)) / Real.sqrt (1 - kap ^ 2) * kap := by ring
    rw [hx]
    calc _ ≤ (|h| * (M + ε)) / Real.sqrt (1 - kap ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hkap1.le hApos
      _ = (|h| * (M + ε)) / Real.sqrt (1 - kap ^ 2) := by ring
  -- difference quotients converge to the linearized solution
  have hkey : ∀ ε > 0, ∃ ρ > 0, ∀ h : ℝ, h ≠ 0 → |h| < ρ → ∀ x,
      |(delta (t₀ + h) x - delta t₀ x)/h - w x| ≤ ε := by
    intro ε hε
    -- abbreviations
    set s : ℝ := Real.sqrt (1 - kap ^ 2) with hsdef
    set c₀ : ℝ := kap⁻¹ * s with hc₀def
    have hc₀p : 0 < c₀ := by rw [hc₀def]; exact mul_pos (inv_pos.mpr hkap) hspos
    have hk2 : kap ^ 2 < 1 := by nlinarith
    have hs2eq : s ^ 2 = 1 - kap ^ 2 := by rw [hsdef]; exact Real.sq_sqrt (le_of_lt (by linarith))
    have hM0 : (0:ℝ) ≤ M := le_trans (abs_nonneg (qdot t₀ 0)) (hqdotbdd 0)
    -- the smallness level of the data-derivative error
    obtain ⟨ε₁, hε₁pos, hε₁one, hε₁e1, hε₁e2⟩ :
        ∃ e : ℝ,
          0 < e ∧ e ≤ 1 ∧ e ≤ ε * c₀ / 8 ∧ e * (M + 1) / s ≤ ε * c₀ / 8 :=
      ⟨min (min 1 (ε * c₀ / 8)) (ε * c₀ * s / (8 * (M + 2))),
       lt_min (lt_min one_pos (div_pos (mul_pos hε hc₀p) (by norm_num)))
         (div_pos (mul_pos (mul_pos hε hc₀p) hspos) (by linarith [hM0])),
       le_trans (min_le_left _ _) (min_le_left _ _),
       le_trans (min_le_left _ _) (min_le_right _ _),
       by
         have hB : min (min 1 (ε * c₀ / 8)) (ε * c₀ * s / (8 * (M + 2)))
             ≤ ε * c₀ * s / (8 * (M + 2)) := min_le_right _ _
         have h2 : min (min 1 (ε * c₀ / 8)) (ε * c₀ * s / (8 * (M + 2))) * (M + 1)
             ≤ (ε * c₀ * s / (8 * (M + 2))) * (M + 1) :=
           mul_le_mul_of_nonneg_right hB (by positivity)
         have h3 : min (min 1 (ε * c₀ / 8)) (ε * c₀ * s / (8 * (M + 2))) * (M + 1) / s
             ≤ (ε * c₀ * s / (8 * (M + 2))) * (M + 1) / s := by
           gcongr
         have h4 : (ε * c₀ * s / (8 * (M + 2))) * (M + 1) / s
             = ε * c₀ / 8 * ((M + 1) / (M + 2)) := by field_simp
         rw [h4] at h3
         have hratio : (M + 1) / (M + 2) ≤ 1 :=
           (div_le_one (by linarith [hM0])).2 (by linarith)
         have hfac : 0 ≤ ε * c₀ / 8 :=
           (div_pos (mul_pos hε hc₀p) (by norm_num)).le
         exact le_trans h3 (by
           simpa using mul_le_mul_of_nonneg_left hratio hfac)⟩
    obtain ⟨ρε, hρεpos, hρε⟩ := hqconv ε₁ hε₁pos
    -- the unified window for the quadratic remainder groups
    obtain ⟨ρ₂, hρ₂pos, hρ₂⟩ :
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ h : ℝ, |h| < ρ →
          (M * (M + 1) * s + (Q + (M + 1)) * (M + 1) ^ 2) * |h| / (s * s)
            ≤ ε * c₀ / 4 :=
      ⟨ε * c₀ * s ^ 2 / (4 * (M * (M + 1) * s + (Q + (M + 1)) * (M + 1) ^ 2)),
       div_pos (mul_pos (mul_pos hε hc₀p) (pow_pos hspos 2)) (by positivity),
       by
         intro h hl
         set K : ℝ := M * (M + 1) * s + (Q + (M + 1)) * (M + 1) ^ 2 with hKdef
         have hm1 : (0:ℝ) < M + 1 := by linarith
         have hq1 : (0:ℝ) < Q + (M + 1) := by linarith [hQpos]
         have hKpos : (0:ℝ) < K := by
           rw [hKdef]
           have e1 : (0:ℝ) ≤ M * (M + 1) * s :=
             mul_nonneg (mul_nonneg hM0 hm1.le) hspos.le
           have e2 : (0:ℝ) < (Q + (M + 1)) * ((M + 1) ^ 2) := mul_pos hq1 (pow_pos hm1 2)
           linarith
         have hKne : K ≠ 0 := ne_of_gt hKpos
         have hss : (0:ℝ) < s * s := mul_pos hspos hspos
         rw [div_le_iff₀ hss]
         -- goal: K*|h| ≤ ε*c₀/4*(s*s)
         have h2 : K * |h| ≤ K * (ε * c₀ * s ^ 2 / (4 * K)) :=
           mul_le_mul_of_nonneg_left hl.le hKpos.le
         have h3 : K * (ε * c₀ * s ^ 2 / (4 * K)) = ε * c₀ * s ^ 2 / 4 := by
           field_simp
         rw [h3] at h2
         calc K * |h| ≤ ε * c₀ * s ^ 2 / 4 := h2
           _ = ε * c₀ / 4 * (s * s) := by ring⟩
    -- the displacement window at level ε₁
    obtain ⟨ρd, hρdpos, hρd⟩ := hdq ε₁ hε₁pos
    refine ⟨min (min (min ρε ρd) 1) ρ₂,
      lt_min (lt_min (lt_min hρεpos hρdpos) one_pos) hρ₂pos,
      fun h hh hl x => ?_⟩
    have ha_re : |h| < ρε :=
      lt_of_lt_of_le hl (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
    have ha_d : |h| < ρd :=
      lt_of_lt_of_le hl (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
    have ha_1 : |h| ≤ 1 :=
      lt_of_lt_of_le hl (le_trans (min_le_left _ _) (min_le_right _ _)) |>.le
    have ha_2 : |h| < ρ₂ := lt_of_lt_of_le hl (min_le_right _ _)
    -- scale facts
    have hqe : ∀ y, |(q (t₀ + h) y - q t₀ y)/h - qdot t₀ y| ≤ ε₁ := hρε h hh ha_re
    have hdisp : ∀ y, |delta (t₀ + h) y - delta t₀ y| ≤ |h| * (M + ε₁) / s := hρd h hh ha_d
    -- upper bound for the shifted curvature data
    have hqh : ∀ y, q (t₀ + h) y ≤ Q + (M + 1) := by
      intro y
      have hexp : q (t₀ + h) y - q t₀ y
          = h * (((q (t₀ + h) y - q t₀ y)/h - qdot t₀ y) + qdot t₀ y) := by
        field_simp
        ring
      have hbound : |q (t₀ + h) y - q t₀ y| ≤ |h| * (M + ε₁) := by
        calc |q (t₀ + h) y - q t₀ y|
            = |h * (((q (t₀ + h) y - q t₀ y)/h - qdot t₀ y) + qdot t₀ y)| :=
              abs_eq_abs.mpr (Or.inl hexp)
          _ ≤ |h| * (ε₁ + M) := by
                rw [abs_mul]
                refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg h)
                calc |((q (t₀ + h) y - q t₀ y)/h - qdot t₀ y) + qdot t₀ y|
                    ≤ |(q (t₀ + h) y - q t₀ y)/h - qdot t₀ y| + |qdot t₀ y| :=
                      abs_add_le _ _
                  _ ≤ ε₁ + M := by linarith [hqe y, hqdotbdd y]
          _ = |h| * (M + ε₁) := by ring
      have hsmall : |h| * (M + ε₁) ≤ M + 1 := by
        have hme : M + ε₁ ≤ M + 1 := by linarith
        calc |h| * (M + ε₁) ≤ |h| * (M + 1) :=
              mul_le_mul_of_nonneg_left hme (abs_nonneg h)
          _ ≤ 1 * (M + 1) := mul_le_mul_of_nonneg_right ha_1 (by linarith)
          _ = M + 1 := by ring
      linarith [hqup y, hbound, hsmall, le_abs_self (q (t₀ + h) y - q t₀ y)]
    -- the difference quotient satisfies the linearized equation
    have huEq : ∀ z : ℝ,
        HasDerivAt (fun y => (delta (t₀ + h) y - delta t₀ y) / h - w y)
          ((((1 - q (t₀ + h) z * Real.sin (delta (t₀ + h) z))
                - (1 - q t₀ z * Real.sin (delta t₀ z))) / h
              + qdot t₀ z * Real.sin (delta t₀ z)
              + q t₀ z * Real.cos (delta t₀ z) * ((delta (t₀ + h) z - delta t₀ z) / h))
            - q t₀ z * Real.cos (delta t₀ z)
              * ((delta (t₀ + h) z - delta t₀ z) / h - w z)) z := by
      intro z
      refine ((((hdelta (t₀ + h) z).sub (hdelta t₀ z)).div_const h).sub (hwlin z)).congr_deriv ?_
      ring
    have huper : Function.Periodic
        (fun y => (delta (t₀ + h) y - delta t₀ y) / h - w y) P := by
      intro y
      show (delta (t₀ + h) (y + P) - delta t₀ (y + P)) / h - w (y + P)
          = (delta (t₀ + h) y - delta t₀ y) / h - w y
      rw [hperd (t₀ + h) y, hperd t₀ y, hwper y]
    have hacoeff : ∀ y, c₀ ≤ q t₀ y * Real.cos (delta t₀ y) := by
      intro y
      have h2 := Shadowing.cos_ge_of_mem_strip (hstrip t₀ y).1 (hstrip t₀ y).2
      have hqnn : (0:ℝ) ≤ q t₀ y := le_trans (le_of_lt (inv_pos.mpr hkap)) (hqlow y)
      calc c₀ = kap⁻¹ * Real.sqrt (1 - kap ^ 2) := hc₀def.symm
        _ ≤ q t₀ y * Real.sqrt (1 - kap ^ 2) :=
              mul_le_mul_of_nonneg_right (hqlow y) hspos.le
        _ = q t₀ y * s := by rw [hsdef]
        _ ≤ q t₀ y * Real.cos (delta t₀ y) := mul_le_mul_of_nonneg_left h2 hqnn
    -- bound on the inhomogeneity of the difference-quotient equation
    have hFb : ∀ y : ℝ,
        |(((1 - q (t₀ + h) y * Real.sin (delta (t₀ + h) y))
              - (1 - q t₀ y * Real.sin (delta t₀ y))) / h
            + qdot t₀ y * Real.sin (delta t₀ y)
            + q t₀ y * Real.cos (delta t₀ y) * ((delta (t₀ + h) y - delta t₀ y) / h))|
          ≤ ε * c₀ / 2 := by
      intro y
      have hdec : (((1 - q (t₀ + h) y * Real.sin (delta (t₀ + h) y))
              - (1 - q t₀ y * Real.sin (delta t₀ y))) / h
            + qdot t₀ y * Real.sin (delta t₀ y)
            + q t₀ y * Real.cos (delta t₀ y) * ((delta (t₀ + h) y - delta t₀ y) / h))
          = (-(((q (t₀ + h) y - q t₀ y)/h - qdot t₀ y)
                * Real.sin (delta (t₀ + h) y)))
            + (-(qdot t₀ y * (Real.sin (delta (t₀ + h) y) - Real.sin (delta t₀ y))))
            + (-(q t₀ y * ((Real.sin (delta (t₀ + h) y) - Real.sin (delta t₀ y)
                  - Real.cos (delta t₀ y) * (delta (t₀ + h) y - delta t₀ y)) / h))) := by
        field_simp
        ring
      rw [hdec]
      have hdsin : |Real.sin (delta (t₀ + h) y) - Real.sin (delta t₀ y)|
          ≤ |delta (t₀ + h) y - delta t₀ y| := abs_sin_sub_sin_le _ _
      have htay := abs_sin_sub_sin_sub_cos_mul_le
        (u := delta (t₀ + h) y) (v := delta t₀ y)
      have hg1 : |(-(((q (t₀ + h) y - q t₀ y)/h - qdot t₀ y)
              * Real.sin (delta (t₀ + h) y)))| ≤ ε₁ := by
        rw [abs_neg, abs_mul]
        calc |((q (t₀ + h) y - q t₀ y)/h - qdot t₀ y)| * |Real.sin (delta (t₀ + h) y)|
            ≤ ε₁ * 1 :=
              mul_le_mul (hqe y) (Real.abs_sin_le_one _) (abs_nonneg _) hε₁pos.le
          _ ≤ ε₁ := by simp
      have hg2 : |(-(qdot t₀ y * (Real.sin (delta (t₀ + h) y) - Real.sin (delta t₀ y))))|
          ≤ M * (M + 1) * |h| / s := by
        rw [abs_neg, abs_mul]
        have step1 : |qdot t₀ y| * |Real.sin (delta (t₀ + h) y) - Real.sin (delta t₀ y)|
            ≤ M * |delta (t₀ + h) y - delta t₀ y| :=
          mul_le_mul (hqdotbdd y) hdsin (abs_nonneg _) hM0
        calc |qdot t₀ y| * |Real.sin (delta (t₀ + h) y) - Real.sin (delta t₀ y)|
            ≤ M * |delta (t₀ + h) y - delta t₀ y| := step1
          _ ≤ M * (|h| * (M + ε₁) / s) := mul_le_mul_of_nonneg_left (hdisp y) hM0
          _ ≤ M * ((M + 1) * |h| / s) := by
                have hme : M + ε₁ ≤ M + 1 := by linarith only [hε₁one]
                have h1 : |h| * (M + ε₁) ≤ (M + 1) * |h| := by
                  rw [mul_comm (M + 1) |h|]
                  exact mul_le_mul_of_nonneg_left hme (abs_nonneg h)
                have h2 : |h| * (M + ε₁) / s ≤ (M + 1) * |h| / s := by
                  rw [div_eq_mul_inv, div_eq_mul_inv]
                  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hspos.le)
                exact mul_le_mul_of_nonneg_left h2 hM0
          _ = M * (M + 1) * |h| / s := by ring
      have hg3 : |(-(q t₀ y * ((Real.sin (delta (t₀ + h) y) - Real.sin (delta t₀ y)
                - Real.cos (delta t₀ y) * (delta (t₀ + h) y - delta t₀ y)) / h)))|
          ≤ (Q + (M + 1)) * (M + 1) ^ 2 * |h| / (s * s) := by
        rw [abs_neg, abs_mul]
        have hqnn : (0:ℝ) ≤ q t₀ y := le_trans (le_of_lt (inv_pos.mpr hkap)) (hqlow y)
        have hdd2 : (delta (t₀ + h) y - delta t₀ y) ^ 2 ≤ (|h| * (M + ε₁) / s) ^ 2 := by
          have h0 : (0:ℝ) ≤ |delta (t₀ + h) y - delta t₀ y| := abs_nonneg _
          have h3 : (delta (t₀ + h) y - delta t₀ y) ^ 2
              = |delta (t₀ + h) y - delta t₀ y| * |delta (t₀ + h) y - delta t₀ y| := by
            rw [abs_mul_abs_self]; ring
          rw [h3, pow_two]
          exact mul_self_le_mul_self h0 (hdisp y)
        calc |q t₀ y| * |(Real.sin (delta (t₀ + h) y) - Real.sin (delta t₀ y)
                - Real.cos (delta t₀ y) * (delta (t₀ + h) y - delta t₀ y)) / h|
            ≤ (Q + (M + 1)) * (delta (t₀ + h) y - delta t₀ y) ^ 2 / |h| := by
              rw [abs_div, abs_of_nonneg hqnn, mul_div_assoc]
              have hq' : q t₀ y ≤ Q + (M + 1) := by linarith only [hqup y, hM0]
              have hN : |Real.sin (delta (t₀ + h) y) - Real.sin (delta t₀ y)
                    - Real.cos (delta t₀ y) * (delta (t₀ + h) y - delta t₀ y)| / |h|
                  ≤ (delta (t₀ + h) y - delta t₀ y) ^ 2 / |h| := by
                rw [div_eq_mul_inv, div_eq_mul_inv]
                exact mul_le_mul_of_nonneg_right htay (inv_nonneg.mpr (abs_nonneg h))
              exact mul_le_mul hq' hN (by positivity) (by linarith only [hQpos, hM0])
          _ ≤ (Q + (M + 1)) * (|h| * (M + ε₁) / s) ^ 2 / |h| := by
              have hQM : (0:ℝ) ≤ Q + (M + 1) := by linarith only [hQpos, hM0]
              have hnum := mul_le_mul_of_nonneg_left hdd2 hQM
              rw [div_eq_mul_inv, div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (abs_nonneg h))
          _ = (Q + (M + 1)) * (M + ε₁) ^ 2 * |h| / (s * s) := by
              field_simp
          _ ≤ (Q + (M + 1)) * (M + 1) ^ 2 * |h| / (s * s) := by
              have hme : M + ε₁ ≤ M + 1 := by linarith only [hε₁one]
              have hsq : (M + ε₁) ^ 2 ≤ (M + 1) ^ 2 := by
                have h0 : (0:ℝ) ≤ M + ε₁ := by linarith only [hM0, hε₁pos]
                simpa [pow_two] using mul_self_le_mul_self h0 hme
              have hQM : (0:ℝ) ≤ Q + (M + 1) := by linarith only [hQpos, hM0]
              have hnum : (Q + (M + 1)) * (M + ε₁) ^ 2 * |h|
                  ≤ (Q + (M + 1)) * (M + 1) ^ 2 * |h| :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hQM)
                  (abs_nonneg h)
              rw [div_eq_mul_inv, div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right hnum
                (inv_nonneg.mpr (mul_pos hspos hspos).le)
      have hKsplit : (M * (M + 1) * s + (Q + (M + 1)) * (M + 1) ^ 2) * |h| / (s * s)
          = M * (M + 1) * |h| / s + (Q + (M + 1)) * (M + 1) ^ 2 * |h| / (s * s) := by
        field_simp
      have hKb := hρ₂ h ha_2
      rw [hKsplit] at hKb
      set A : ℝ := -(((q (t₀ + h) y - q t₀ y)/h - qdot t₀ y)
        * Real.sin (delta (t₀ + h) y))
      set B : ℝ := -(qdot t₀ y * (Real.sin (delta (t₀ + h) y) - Real.sin (delta t₀ y)))
      set C : ℝ := -(q t₀ y * ((Real.sin (delta (t₀ + h) y) - Real.sin (delta t₀ y)
        - Real.cos (delta t₀ y) * (delta (t₀ + h) y - delta t₀ y)) / h))
      set T1 : ℝ := M * (M + 1) * |h| / s
      set T2 : ℝ := (Q + (M + 1)) * (M + 1) ^ 2 * |h| / (s * s)
      clear_value A B C T1 T2
      have hεc : (0:ℝ) < ε * c₀ := mul_pos hε hc₀p
      calc |A + B + C| ≤ |A + B| + |C| := abs_add_le _ _
        _ ≤ |A| + |B| + |C| := by linarith only [abs_add_le A B]
        _ ≤ ε₁ + T1 + T2 := by linarith only [hg1, hg2, hg3]
        _ ≤ ε * c₀ / 8 + ε * c₀ / 4 := by linarith only [hε₁e1, hKb]
        _ ≤ ε * c₀ / 2 := by linarith only [hεc]
    -- the sup-bound on the difference quotients
    have hbnd := SelectedRear.periodic_linear_sup_bound
      (w := fun y => (delta (t₀ + h) y - delta t₀ y) / h - w y)
      (a := fun y => q t₀ y * Real.cos (delta t₀ y))
      (f := fun y => (((1 - q (t₀ + h) y * Real.sin (delta (t₀ + h) y))
            - (1 - q t₀ y * Real.sin (delta t₀ y))) / h
          + qdot t₀ y * Real.sin (delta t₀ y)
          + q t₀ y * Real.cos (delta t₀ y) * ((delta (t₀ + h) y - delta t₀ y) / h)))
      hP huEq huper (c := c₀) hc₀p hacoeff hFb
    have hx := hbnd x
    have hsimp : (ε * c₀ / 2) / c₀ = ε / 2 := by field_simp
    rw [hsimp] at hx
    linarith
  refine ⟨w, hwlin, hwper, ?_, ?_⟩
  · intro x
    rw [hasDerivAt_iff_tendsto_slope_zero, Metric.tendsto_nhdsWithin_nhds]
    intro r hr
    obtain ⟨ρ, hρpos, hρ⟩ := hkey (r / 2) (by linarith)
    refine ⟨ρ, hρpos, ?_⟩
    intro t ht hdist
    have hne : t ≠ 0 := ht
    have habs : |t| < ρ := by simpa [Real.dist_eq] using hdist
    have hb := hρ t hne habs x
    have heq : t⁻¹ • (delta (t₀ + t) x - delta t₀ x)
        = (delta (t₀ + t) x - delta t₀ x) / t := by
      rw [smul_eq_mul]
      ring
    rw [Real.dist_eq, heq]
    linarith
  · intro x
    exact SelectedRear.selected_steering_variation_bound hP hkap hkap1 hqlow
      (hstrip t₀) hqdotbdd hwlin hwper x

end TimeDependence

end SelectedRearSmoothDependence
