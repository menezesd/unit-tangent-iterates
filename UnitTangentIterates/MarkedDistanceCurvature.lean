import Mathlib
import UnitTangentIterates.MarkedSpace
import UnitTangentIterates.CurvatureStability

/-!
# The marked distance from a bound on the curvatures

The defect estimate of the paper *A Noncircular Oval with Convex Unit-Tangent
Iterates* compares two curves through their curvatures, while the space of
marked curves of `MarkedSpace.lean` is metrized by the uniform `C²` distance of
the normalized data.  This file converts the one into the other.

For two members of the tube of the **same perimeter `L`**, whose arclength
parametrizations agree in position and direction at the marked point and whose
curvatures differ by at most `ε` (the second being bounded by `kb`),

```
  dist p q ≤ ε L² (1 + kb L).
```

The proof is the `C²` stability of `CurvatureStability.lean` together with the
identification of the normalized data:

* `vel_eq` , `acc_eq` : `V(u) = L e^{iΘ(Lu)}` and `A(u) = i L² k(Lu) e^{iΘ(Lu)}`
  for a member of the tube whose arclength parametrization has tangent angle
  `Θ` and curvature `k`;
* `periodic_vel`, `periodic_acc` : the velocity and the acceleration are
  `1`-periodic, so the estimates on one period suffice;
* `dist_le_of_curvature_close` : the bound itself.

What is *not* claimed here is the defect estimate of the paper: this is only
the passage from a uniform bound on the difference of the curvatures to the
metric of the space of marked curves.
-/

noncomputable section

open Set Function

namespace MarkedSpace

/-! ### Periodicity of the derivatives -/

/-- The velocity of a marked curve is `1`-periodic. -/
theorem periodic_vel {c kmin delta : ℝ} {p : Data} (hp : IsTubeMember c kmin delta p) :
    Periodic (⇑p.2.1) 1 := by
  intro u
  have hin : HasDerivAt (fun t : ℝ => t + 1) 1 u := by
    simpa using (hasDerivAt_id u).add_const (1 : ℝ)
  have hshift : HasDerivAt (fun t : ℝ => p.1 (t + 1)) (p.2.1 (u + 1)) u := by
    have h := (hp.hasDerivAt_curve (u + 1)).scomp u hin
    simpa [Function.comp_def] using h
  have heq : (fun t : ℝ => p.1 (t + 1)) = ⇑p.1 := funext fun t => hp.periodic t
  rw [heq] at hshift
  exact hshift.unique (hp.hasDerivAt_curve u)

/-- The acceleration of a marked curve is `1`-periodic. -/
theorem periodic_acc {c kmin delta : ℝ} {p : Data} (hp : IsTubeMember c kmin delta p) :
    Periodic (⇑p.2.2) 1 := by
  intro u
  have hper := periodic_vel hp
  have hin : HasDerivAt (fun t : ℝ => t + 1) 1 u := by
    simpa using (hasDerivAt_id u).add_const (1 : ℝ)
  have hshift : HasDerivAt (fun t : ℝ => p.2.1 (t + 1)) (p.2.2 (u + 1)) u := by
    have h := (hp.hasDerivAt_vel (u + 1)).scomp u hin
    simpa [Function.comp_def] using h
  have heq : (fun t : ℝ => p.2.1 (t + 1)) = ⇑p.2.1 := funext fun t => hper t
  rw [heq] at hshift
  exact hshift.unique (hp.hasDerivAt_vel u)

/-! ### The normalized data in terms of the arclength parametrization -/

/-- The normalized curve is the arclength parametrization rescaled. -/
theorem curve_eq_ev (p : Data) (u : ℝ) (hL : perim p ≠ 0) :
    p.1 u = ev p (perim p * u) := by
  simp only [ev]
  congr 1
  field_simp

/-- **The velocity of a marked curve is `L e^{iΘ(Ls)}`**, `L` its perimeter and
`Θ` the tangent angle of its arclength parametrization. -/
theorem vel_eq {c kmin delta : ℝ} (hc : 0 < c) {p : Data} (hp : IsTubeMember c kmin delta p)
    {Θ : ℝ → ℝ} (hev : ∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (u : ℝ) :
    p.2.1 u = ((perim p : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (perim p * u) : ℂ)) := by
  have hLpos : 0 < perim p := perim_pos hc hp
  have hLne : perim p ≠ 0 := ne_of_gt hLpos
  have hcomp : HasDerivAt (fun t : ℝ => ev p (perim p * t))
      (((perim p : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (perim p * u) : ℂ))) u := by
    have hinner : HasDerivAt (fun t : ℝ => perim p * t) (perim p) u := by
      simpa using (hasDerivAt_id u).const_mul (perim p)
    have h := (hev (perim p * u)).scomp u hinner
    have hcast : (perim p : ℝ) • Complex.exp (Complex.I * (Θ (perim p * u) : ℂ))
        = ((perim p : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (perim p * u) : ℂ)) := by
      rw [Complex.real_smul]
    simpa [Function.comp_def, hcast] using h
  have heq : (fun t : ℝ => ev p (perim p * t)) = ⇑p.1 :=
    funext fun t => (curve_eq_ev p t hLne).symm
  rw [heq] at hcomp
  exact (hp.hasDerivAt_curve u).unique hcomp

/-- **The acceleration of a marked curve is `i L² k(Ls) e^{iΘ(Ls)}`.** -/
theorem acc_eq {c kmin delta : ℝ} (hc : 0 < c) {p : Data} (hp : IsTubeMember c kmin delta p)
    {Θ k : ℝ → ℝ} (hev : ∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (k s) s) (u : ℝ) :
    p.2.2 u = ((perim p ^ 2 : ℝ) : ℂ) *
      (Complex.I * (k (perim p * u) : ℂ) * Complex.exp (Complex.I * (Θ (perim p * u) : ℂ))) := by
  set L : ℝ := perim p with hLdef
  have hLpos : 0 < L := perim_pos hc hp
  -- the derivative of `t ↦ L e^{iΘ(Lt)}`
  have hexp : ∀ s : ℝ, HasDerivAt (fun r : ℝ => Complex.exp (Complex.I * (Θ r : ℂ)))
      (Complex.I * (k s : ℂ) * Complex.exp (Complex.I * (Θ s : ℂ))) s := by
    intro s
    have h0 : HasDerivAt (fun r : ℝ => Complex.I * (Θ r : ℂ)) (Complex.I * (k s : ℂ)) s := by
      have h1 : HasDerivAt (fun r : ℝ => ((Θ r : ℝ) : ℂ)) ((k s : ℝ) : ℂ) s :=
        (Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt s (hΘ s)
      simpa using h1.const_mul Complex.I
    simpa [mul_comm] using h0.cexp
  have hcomp : HasDerivAt (fun t : ℝ => ((L : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (L * t) : ℂ)))
      (((L ^ 2 : ℝ) : ℂ) *
        (Complex.I * (k (L * u) : ℂ) * Complex.exp (Complex.I * (Θ (L * u) : ℂ)))) u := by
    have hinner : HasDerivAt (fun t : ℝ => L * t) L u := by
      simpa using (hasDerivAt_id u).const_mul L
    have h := ((hexp (L * u)).scomp u hinner).const_mul (((L : ℝ) : ℂ))
    have hcast : ((L : ℝ) : ℂ) * ((L : ℝ) •
        (Complex.I * (k (L * u) : ℂ) * Complex.exp (Complex.I * (Θ (L * u) : ℂ))))
        = ((L ^ 2 : ℝ) : ℂ) *
          (Complex.I * (k (L * u) : ℂ) * Complex.exp (Complex.I * (Θ (L * u) : ℂ))) := by
      rw [Complex.real_smul]
      push_cast
      ring
    exact h.congr_deriv hcast
  have heq : (fun t : ℝ => ((L : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (L * t) : ℂ)))
      = ⇑p.2.1 := funext fun t => (vel_eq hc hp hev t).symm
  rw [heq] at hcomp
  exact (hp.hasDerivAt_vel u).unique hcomp

/-! ### The bound on the marked distance -/

/-- A bound valid on one period is a bound everywhere, for `1`-periodic data. -/
theorem forall_of_forall_Icc {f : ℝ → ℂ} {M : ℝ} (hf : Periodic f 1)
    (h : ∀ u ∈ Icc (0 : ℝ) 1, ‖f u‖ ≤ M) (u : ℝ) : ‖f u‖ ≤ M := by
  have hfrac : f (u - (⌊u⌋ : ℤ) * 1) = f u := hf.sub_int_mul_eq (⌊u⌋ : ℤ)
  have hmem : u - (⌊u⌋ : ℤ) * 1 ∈ Icc (0 : ℝ) 1 := by
    have h1 : (0 : ℝ) ≤ Int.fract u := Int.fract_nonneg u
    have h2 : Int.fract u < 1 := Int.fract_lt_one u
    have he : u - ((⌊u⌋ : ℤ) : ℝ) * 1 = Int.fract u := by
      rw [Int.fract]; ring
    rw [he]
    exact ⟨h1, h2.le⟩
  rw [← hfrac]
  exact h _ hmem

/-- **The marked distance from a uniform bound on the curvatures.**  Two members
of the tube of the same perimeter `L`, whose arclength parametrizations agree in
position and direction at the marked point and whose curvatures differ by at
most `ε` — the second being bounded by `kb` — are at marked distance at most
`ε L² (1 + kb L)`. -/
theorem dist_le_of_curvature_close {c kmin delta : ℝ} (hc : 0 < c) {p q : Data}
    (hp : IsTubeMember c kmin delta p) (hq : IsTubeMember c kmin delta q)
    {Θ₁ Θ₂ k₁ k₂ : ℝ → ℝ} {eps kb L : ℝ}
    (hLp : perim p = L) (hLq : perim q = L)
    (hevp : ∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ₁ s : ℂ))) s)
    (hevq : ∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ₂ s : ℂ))) s)
    (hΘ1 : ∀ s, HasDerivAt Θ₁ (k₁ s) s) (hΘ2 : ∀ s, HasDerivAt Θ₂ (k₂ s) s)
    (hF0 : ev p 0 = ev q 0) (hΘ0 : Θ₁ 0 = Θ₂ 0)
    (heps : 0 ≤ eps) (hk : ∀ s, |k₁ s - k₂ s| ≤ eps) (hkb : ∀ s, |k₂ s| ≤ kb) :
    dist p q ≤ eps * L ^ 2 * (1 + kb * L) := by
  have hLpos : 0 < L := hLp ▸ perim_pos hc hp
  have hkb0 : 0 ≤ kb := le_trans (abs_nonneg _) (hkb 0)
  set M : ℝ := eps * L ^ 2 * (1 + kb * L) with hM
  have hM0 : 0 ≤ M := by positivity
  -- the `C²` stability estimates on the window `[−L, L]`
  have hstab : ∀ s ∈ Icc (-L) L,
      ‖ev p s - ev q s‖ ≤ eps * L ^ 2 ∧
        ‖Complex.exp (Complex.I * (Θ₁ s : ℂ)) - Complex.exp (Complex.I * (Θ₂ s : ℂ))‖
          ≤ eps * L ∧
        ‖Complex.I * (k₁ s : ℂ) * Complex.exp (Complex.I * (Θ₁ s : ℂ))
          - Complex.I * (k₂ s : ℂ) * Complex.exp (Complex.I * (Θ₂ s : ℂ))‖
          ≤ eps * (1 + kb * L) := fun s hs =>
    CurvatureStability.c2_close_of_curvature_close hevp hevq hΘ1 hΘ2 hF0 hΘ0 heps
      hLpos.le hk hkb hs
  have hwindow : ∀ u ∈ Icc (0 : ℝ) 1, L * u ∈ Icc (-L) L := by
    intro u hu
    constructor
    · nlinarith [hu.1]
    · nlinarith [hu.2]
  -- the three components
  have hbound1 : ∀ u, ‖p.1 u - q.1 u‖ ≤ M := by
    refine forall_of_forall_Icc (f := fun u => p.1 u - q.1 u)
      (fun u => by simp [hp.periodic u, hq.periodic u]) ?_
    intro u hu
    show ‖p.1 u - q.1 u‖ ≤ M
    have h := (hstab (L * u) (hwindow u hu)).1
    have hpe : p.1 u = ev p (L * u) := by
      rw [curve_eq_ev p u (by rw [hLp]; exact ne_of_gt hLpos), hLp]
    have hqe : q.1 u = ev q (L * u) := by
      rw [curve_eq_ev q u (by rw [hLq]; exact ne_of_gt hLpos), hLq]
    rw [hpe, hqe]
    refine le_trans h ?_
    have : eps * L ^ 2 * 1 ≤ eps * L ^ 2 * (1 + kb * L) := by
      refine mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    linarith [this]
  have hbound2 : ∀ u, ‖p.2.1 u - q.2.1 u‖ ≤ M := by
    refine forall_of_forall_Icc (f := fun u => p.2.1 u - q.2.1 u)
      (fun u => by simp [periodic_vel hp u, periodic_vel hq u]) ?_
    intro u hu
    show ‖p.2.1 u - q.2.1 u‖ ≤ M
    have h := (hstab (L * u) (hwindow u hu)).2.1
    rw [vel_eq hc hp hevp u, vel_eq hc hq hevq u, hLp, hLq, ← mul_sub, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos]
    calc L * ‖Complex.exp (Complex.I * (Θ₁ (L * u) : ℂ))
              - Complex.exp (Complex.I * (Θ₂ (L * u) : ℂ))‖
        ≤ L * (eps * L) := by exact mul_le_mul_of_nonneg_left h hLpos.le
      _ ≤ M := by
        rw [hM]
        nlinarith [mul_nonneg (mul_nonneg heps (sq_nonneg L)) (mul_nonneg hkb0 hLpos.le)]
  have hbound3 : ∀ u, ‖p.2.2 u - q.2.2 u‖ ≤ M := by
    refine forall_of_forall_Icc (f := fun u => p.2.2 u - q.2.2 u)
      (fun u => by simp [periodic_acc hp u, periodic_acc hq u]) ?_
    intro u hu
    show ‖p.2.2 u - q.2.2 u‖ ≤ M
    have h := (hstab (L * u) (hwindow u hu)).2.2
    rw [acc_eq hc hp hevp hΘ1 u, acc_eq hc hq hevq hΘ2 u, hLp, hLq, ← mul_sub, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < L ^ 2)]
    calc L ^ 2 * ‖Complex.I * (k₁ (L * u) : ℂ) * Complex.exp (Complex.I * (Θ₁ (L * u) : ℂ))
              - Complex.I * (k₂ (L * u) : ℂ) * Complex.exp (Complex.I * (Θ₂ (L * u) : ℂ))‖
        ≤ L ^ 2 * (eps * (1 + kb * L)) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = M := by rw [hM]; ring
  -- assemble the three sup bounds
  have hd1 : dist p.1 q.1 ≤ M :=
    (BoundedContinuousFunction.dist_le hM0).2 fun u => by
      rw [dist_eq_norm]; exact hbound1 u
  have hd2 : dist p.2.1 q.2.1 ≤ M :=
    (BoundedContinuousFunction.dist_le hM0).2 fun u => by
      rw [dist_eq_norm]; exact hbound2 u
  have hd3 : dist p.2.2 q.2.2 ≤ M :=
    (BoundedContinuousFunction.dist_le hM0).2 fun u => by
      rw [dist_eq_norm]; exact hbound3 u
  rw [Prod.dist_eq, Prod.dist_eq]
  exact max_le hd1 (max_le hd2 hd3)

/-! ### Rigidity -/

/-- **Two marked curves with the same perimeter and the same curvature, aligned
at the marked point, coincide.**  The case `ε = 0` of
`dist_le_of_curvature_close`. -/
theorem eq_of_curvature_eq {c kmin delta : ℝ} (hc : 0 < c) {p q : Data}
    (hp : IsTubeMember c kmin delta p) (hq : IsTubeMember c kmin delta q)
    {Θ₁ Θ₂ k : ℝ → ℝ} {L : ℝ}
    (hLp : perim p = L) (hLq : perim q = L)
    (hevp : ∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ₁ s : ℂ))) s)
    (hevq : ∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ₂ s : ℂ))) s)
    (hΘ1 : ∀ s, HasDerivAt Θ₁ (k s) s) (hΘ2 : ∀ s, HasDerivAt Θ₂ (k s) s)
    (hF0 : ev p 0 = ev q 0) (hΘ0 : Θ₁ 0 = Θ₂ 0)
    {kb : ℝ} (hkb : ∀ s, |k s| ≤ kb) :
    p = q := by
  have h := dist_le_of_curvature_close hc hp hq hLp hLq hevp hevq hΘ1 hΘ2 hF0 hΘ0
    (eps := 0) le_rfl (fun s => by simp) hkb
  have h0 : dist p q ≤ 0 := by simpa using h
  exact dist_le_zero.1 h0

end MarkedSpace
