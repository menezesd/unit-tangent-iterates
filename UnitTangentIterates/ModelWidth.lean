import Mathlib
import UnitTangentIterates.TwoCapMarked
import UnitTangentIterates.WidthUniform

/-!
# The transverse displacement of the model *is* its geometric width

The lemma *Uniform transverse width* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* bounds the transverse displacement

`W_H = ∫_{−H/2}^{H/2} sin Θ_H`

of the model front over its centred cell (`WidthUniform.lean`), while the
closing argument (`ClosingArgument.lean`, `CurveDistance.lean`,
`MarkedSchemeTheoremRange.lean`) consumes a bound on the **geometric width**
`width (range F) e = h_F(e) + h_F(−e)` of the model in some unit direction.

This file identifies the two.  For a front whose tangent angle stays in `(0,π)`
on the centred cell and increases by `π` over a half period — the geometry of an
exact two-cap pair — the vertical coordinate `Im F` increases on the cell and
decreases on the next one, so it attains its maximum at `H/2` and its minimum at
`−H/2`, and therefore

`width (range F) i = Im F(H/2) − Im F(−H/2) = ∫_{−H/2}^{H/2} sin Θ = W_H`

(`width_range_eq_integral`).  Composing with the lemma
(`exists_uniform_width_bound_model`) gives what the closing argument asks for:
past a threshold the model fronts have geometric width at most `C₀ + 1` in the
transverse direction, however large their perimeter `2H`.
-/

noncomputable section

open Set Function Real MeasureTheory intervalIntegral

namespace ModelWidth

open TwoCapPairsAssembly CurvatureInterpolation

/-! ### The real inner product of the plane against the vertical direction -/

theorem inner_I (x : ℂ) : (inner ℝ x Complex.I : ℝ) = x.im := by
  simp [real_inner_eq_re_inner (𝕜 := ℂ)]

theorem inner_neg_I (x : ℂ) : (inner ℝ x (-Complex.I) : ℝ) = -x.im := by
  rw [inner_neg_right, inner_I]

theorem im_exp_mul_I (θ : ℝ) : (Complex.exp (Complex.I * (θ : ℂ))).im = Real.sin θ := by
  rw [mul_comm, Complex.exp_ofReal_mul_I_im]

/-- An integral of a nonpositive function over an increasing interval is
nonpositive. -/
theorem integral_nonpos_of_nonpos {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ u ∈ Icc a b, f u ≤ 0) : (∫ x in a..b, f x) ≤ 0 := by
  have h2 : 0 ≤ ∫ x in a..b, -f x :=
    intervalIntegral.integral_nonneg hab (fun u hu => by linarith [h u hu])
  rw [intervalIntegral.integral_neg] at h2
  linarith

/-! ### The width of a two-cap front -/

variable {F : ℝ → ℂ} {Θ : ℝ → ℝ} {H : ℝ}

/-- **The geometric width of a two-cap front in the transverse direction is its
transverse displacement.**  If the tangent angle of a closed unit-speed curve of
period `2H` increases by `π` over a half period and the vertical component of
its tangent is nonnegative on the centred cell, then the width of the curve in
the direction `i` is the rise of its vertical coordinate over that cell. -/
theorem width_range_eq (hH : 0 < H)
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘc : Continuous Θ) (hFper : Periodic F (2 * H))
    (hhalf : ∀ s, Θ (s + H) = Θ s + Real.pi)
    (hcell : ∀ s ∈ Icc (-(H / 2)) (H / 2), 0 ≤ Real.sin (Θ s)) :
    Width.width (range F) Complex.I = (F (H / 2)).im - (F (-(H / 2))).im := by
  set p : ℝ → ℝ := fun s => (F s).im with hp
  have hpderiv : ∀ s, HasDerivAt p (Real.sin (Θ s)) s := by
    intro s
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s (hF s)
    simpa [hp, im_exp_mul_I] using h
  have hsincont : Continuous fun s => Real.sin (Θ s) := Real.continuous_sin.comp hΘc
  have hint : ∀ a b : ℝ, p b - p a = ∫ s in a..b, Real.sin (Θ s) := by
    intro a b
    rw [integral_eq_sub_of_hasDerivAt (fun s _ => hpderiv s)
      (hsincont.intervalIntegrable _ _)]
  -- the sign of the vertical velocity on the two half periods
  have hsecond : ∀ s ∈ Icc (H / 2) (3 * H / 2), Real.sin (Θ s) ≤ 0 := by
    intro s hs
    have hmem : s - H ∈ Icc (-(H / 2)) (H / 2) := by
      constructor <;> [linarith [hs.1]; linarith [hs.2]]
    have h := hcell _ hmem
    have hΘs : Θ s = Θ (s - H) + Real.pi := by
      have := hhalf (s - H)
      simpa using this
    rw [hΘs, Real.sin_add_pi]
    linarith
  -- the maximum is at `H/2`, the minimum at `−H/2`
  have hper' : p (3 * H / 2) = p (-(H / 2)) := by
    have h : F (-(H / 2) + 2 * H) = F (-(H / 2)) := hFper _
    have he : -(H / 2) + 2 * H = 3 * H / 2 := by ring
    rw [he] at h
    simp [hp, h]
  have hmax : ∀ s ∈ Icc (-(H / 2)) (3 * H / 2), p s ≤ p (H / 2) := by
    intro s hs
    rcases le_total s (H / 2) with hle | hge
    · have h := hint s (H / 2)
      have hnn : 0 ≤ ∫ r in s..(H / 2), Real.sin (Θ r) := by
        apply intervalIntegral.integral_nonneg hle
        intro r hr
        exact hcell r ⟨le_trans hs.1 hr.1, hr.2⟩
      linarith
    · have h := hint (H / 2) s
      have hnp : (∫ r in (H / 2)..s, Real.sin (Θ r)) ≤ 0 :=
        integral_nonpos_of_nonpos hge (fun r hr => hsecond r ⟨hr.1, le_trans hr.2 hs.2⟩)
      linarith
  have hmin : ∀ s ∈ Icc (-(H / 2)) (3 * H / 2), p (-(H / 2)) ≤ p s := by
    intro s hs
    rcases le_total s (H / 2) with hle | hge
    · have h := hint (-(H / 2)) s
      have hnn : 0 ≤ ∫ r in (-(H / 2))..s, Real.sin (Θ r) := by
        apply intervalIntegral.integral_nonneg hs.1
        intro r hr
        exact hcell r ⟨hr.1, le_trans hr.2 hle⟩
      linarith
    · have h := hint s (3 * H / 2)
      have hnp : (∫ r in s..(3 * H / 2), Real.sin (Θ r)) ≤ 0 :=
        integral_nonpos_of_nonpos hs.2 (fun r hr => hsecond r ⟨le_trans hge hr.1, hr.2⟩)
      rw [hper'] at h
      linarith
  -- every value of `p` is attained on the window `[−H/2, 3H/2)`
  have hpper : Periodic p (2 * H) := fun s => by simp [hp, hFper s]
  have hreduce : ∀ s : ℝ, ∃ t ∈ Icc (-(H / 2)) (3 * H / 2), p s = p t := by
    intro s
    have hshift : Periodic (fun u => p (u - H / 2)) (2 * H) := by
      intro u
      show p (u + 2 * H - H / 2) = p (u - H / 2)
      have hu : u + 2 * H - H / 2 = (u - H / 2) + 2 * H := by ring
      rw [hu]
      exact hpper _
    obtain ⟨y, hy, hxy⟩ := hshift.exists_mem_Ico₀ (by linarith) (s + H / 2)
    refine ⟨y - H / 2, ⟨by linarith [hy.1], by linarith [hy.2]⟩, ?_⟩
    simpa using hxy
  -- the support function in the two directions
  have hupper : ∀ s : ℝ, p s ≤ p (H / 2) := by
    intro s
    obtain ⟨t, ht, hst⟩ := hreduce s
    rw [hst]
    exact hmax t ht
  have hlower : ∀ s : ℝ, p (-(H / 2)) ≤ p s := by
    intro s
    obtain ⟨t, ht, hst⟩ := hreduce s
    rw [hst]
    exact hmin t ht
  have hsup1 : Width.support (range F) Complex.I = p (H / 2) := by
    refine IsGreatest.csSup_eq ⟨⟨F (H / 2), ⟨H / 2, rfl⟩, inner_I _⟩, ?_⟩
    rintro y ⟨x, ⟨s, rfl⟩, rfl⟩
    simpa [inner_I] using hupper s
  have hsup2 : Width.support (range F) (-Complex.I) = -p (-(H / 2)) := by
    refine IsGreatest.csSup_eq ⟨⟨F (-(H / 2)), ⟨-(H / 2), rfl⟩, inner_neg_I _⟩, ?_⟩
    rintro y ⟨x, ⟨s, rfl⟩, rfl⟩
    have := hlower s
    simp only [inner_neg_I]
    linarith
  rw [Width.width, hsup1, hsup2]
  ring

/-- **The width of a two-cap front is its transverse displacement**, in the form
of the lemma *Uniform transverse width*. -/
theorem width_range_eq_integral (hH : 0 < H)
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘc : Continuous Θ) (hFper : Periodic F (2 * H))
    (hhalf : ∀ s, Θ (s + H) = Θ s + Real.pi)
    (hcell : ∀ s ∈ Icc (-(H / 2)) (H / 2), 0 ≤ Real.sin (Θ s)) :
    Width.width (range F) Complex.I = ∫ s in (-(H / 2))..(H / 2), Real.sin (Θ s) := by
  have hpderiv : ∀ s, HasDerivAt (fun r => (F r).im) (Real.sin (Θ s)) s := by
    intro s
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s (hF s)
    simpa [im_exp_mul_I] using h
  have hsincont : Continuous fun s => Real.sin (Θ s) := Real.continuous_sin.comp hΘc
  rw [width_range_eq hH hF hΘc hFper hhalf hcell,
    integral_eq_sub_of_hasDerivAt (fun s _ => hpderiv s) (hsincont.intervalIntegrable _ _)]

/-! ### The width of the model front -/

/-- **The width of the model front of a two-cap pair.**  For a continuous
`H`-periodic front curvature of total turning `π` over one period whose tangent
angle stays in `[0,π]` on the centred cell, the geometric width of the front in
the transverse direction is its transverse displacement. -/
theorem width_front_eq_integral {kappa : ℝ → ℝ} {theta0 : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = Real.pi)
    (hcell : ∀ s ∈ Icc (-(H / 2)) (H / 2), 0 ≤ Real.sin (frontAngle kappa theta0 s)) :
    Width.width (range (front kappa theta0 H)) Complex.I
      = ∫ s in (-(H / 2))..(H / 2), Real.sin (frontAngle kappa theta0 s) :=
  width_range_eq_integral hH (fun s => front_hasDerivAt (theta0 := theta0) (H := H) hk s)
    (continuous_tangentAngle hk) (front_periodic hk hper htotal)
    (fun s => frontAngle_add_halfPeriod (theta0 := theta0) hk hper htotal s) hcell

/-- **Uniform transverse width, geometrically.**  Under the hypotheses of the
lemma — the model tangent angles converge exponentially to that of the isolated
hairpin and stay in `(0,π)` on the centred cell — the model fronts have, past a
threshold, geometric width at most `C₀ + 1` in the transverse direction, however
large their perimeter `2H`. -/
theorem exists_uniform_width_bound_model {kappas : ℝ → ℝ → ℝ} {theta0 : ℝ → ℝ}
    {Θs : ℝ → ℝ} {C0 C beta : ℝ} (hbeta : 0 < beta) (hC : 0 ≤ C)
    (hk : ∀ H, Continuous (kappas H)) (hper : ∀ H, Periodic (kappas H) H)
    (htotal : ∀ H, (∫ r in (0:ℝ)..H, kappas H r) = Real.pi)
    (hΘs : Continuous Θs)
    (hmodel : ∀ H, (∫ t in (-(H / 2))..(H / 2), Real.sin (Θs t)) ≤ C0)
    (hclose : ∀ H, ∀ t ∈ uIoc (-(H / 2)) (H / 2),
      |frontAngle (kappas H) (theta0 H) t - Θs t| ≤ C * Real.exp (-beta * H))
    (hpos : ∀ H, ∀ t ∈ Ioo (-(H / 2)) (H / 2),
      frontAngle (kappas H) (theta0 H) t ∈ Ioo 0 Real.pi) :
    ∃ Hstar : ℝ, 0 < Hstar ∧ ∀ H, Hstar ≤ H → 0 < H →
      0 < Width.width (range (front (kappas H) (theta0 H) H)) Complex.I ∧
        Width.width (range (front (kappas H) (theta0 H) H)) Complex.I ≤ C0 + 1 := by
  obtain ⟨Hstar, hHstar, hbound⟩ :=
    WidthUniform.exists_uniform_width_bound (Θ := fun H => frontAngle (kappas H) (theta0 H))
      hbeta hC (fun H => continuous_tangentAngle (hk H)) hΘs hmodel hclose hpos
  refine ⟨Hstar, hHstar, fun H hHs hH => ?_⟩
  -- the tangent angle stays in `[0,π]` on the closed cell, by continuity
  have hΘc : Continuous (frontAngle (kappas H) (theta0 H)) := continuous_tangentAngle (hk H)
  have hsub : Ioo (-(H / 2)) (H / 2)
      ⊆ {s | 0 ≤ Real.sin (frontAngle (kappas H) (theta0 H) s)} := by
    intro s hs
    exact Real.sin_nonneg_of_nonneg_of_le_pi (hpos H s hs).1.le (hpos H s hs).2.le
  have hcell : ∀ s ∈ Icc (-(H / 2)) (H / 2),
      0 ≤ Real.sin (frontAngle (kappas H) (theta0 H) s) := by
    have hclosed : IsClosed {s | 0 ≤ Real.sin (frontAngle (kappas H) (theta0 H) s)} :=
      isClosed_Ici.preimage (Real.continuous_sin.comp hΘc)
    have hne : -(H / 2) ≠ H / 2 := by intro h; linarith
    have : Icc (-(H / 2)) (H / 2) ⊆ {s | 0 ≤ Real.sin (frontAngle (kappas H) (theta0 H) s)} := by
      rw [← closure_Ioo hne]
      exact hclosed.closure_subset_iff.2 hsub
    exact fun s hs => this hs
  rw [width_front_eq_integral hH (hk H) (hper H) (htotal H) hcell]
  exact hbound H hHs

/-! ### The identity on a genuine curve -/

theorem sin_pi_div_two_add' (x : ℝ) : Real.sin (Real.pi / 2 + x) = Real.cos x := by
  rw [Real.sin_add]
  simp

open TwoCapMarked in
/-- The tangent angle of the constant-curvature front marked at `π/2`. -/
theorem frontAngle_kcirc (s : ℝ) : frontAngle kcirc (Real.pi / 2) s = Real.pi / 2 + s / 2 := by
  simp [frontAngle, tangentAngle, kcirc]
  ring

open TwoCapMarked in
/-- **The identity is not vacuous.**  For the circle of radius `2`, written as
the two-cap front of constant curvature `1/2` and half-period `2π` and marked so
that its cell is centred, the width in the transverse direction is `4` — the
diameter of that circle. -/
theorem width_front_kcirc :
    Width.width (range (front kcirc (Real.pi / 2) (2 * Real.pi))) Complex.I = 4 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcell : ∀ s ∈ Icc (-(2 * Real.pi / 2)) (2 * Real.pi / 2),
      0 ≤ Real.sin (frontAngle kcirc (Real.pi / 2) s) := by
    intro s hs
    rw [frontAngle_kcirc, sin_pi_div_two_add']
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · have := hs.1; linarith
    · have := hs.2; linarith
  rw [width_front_eq_integral (by positivity) continuous_kcirc kcirc_periodic kcirc_total hcell]
  have hG : ∀ s : ℝ, HasDerivAt (fun r : ℝ => -2 * Real.cos (Real.pi / 2 + r / 2))
      (Real.sin (frontAngle kcirc (Real.pi / 2) s)) s := by
    intro s
    have hinner : HasDerivAt (fun r : ℝ => Real.pi / 2 + r / 2) (1 / 2 : ℝ) s :=
      ((hasDerivAt_id s).div_const 2).const_add _
    have h := (Real.hasDerivAt_cos (Real.pi / 2 + s / 2)).comp s hinner
    have h2 := h.const_mul (-2 : ℝ)
    rw [frontAngle_kcirc]
    convert h2 using 1
    ring
  rw [integral_eq_sub_of_hasDerivAt (fun s _ => hG s)
    ((Real.continuous_sin.comp (continuous_tangentAngle continuous_kcirc)).intervalIntegrable
      _ _)]
  have h1 : Real.pi / 2 + (2 * Real.pi / 2) / 2 = Real.pi / 2 + Real.pi / 2 := by ring
  have h2 : Real.pi / 2 + (-(2 * Real.pi / 2)) / 2 = Real.pi / 2 - Real.pi / 2 := by ring
  rw [h1, h2]
  rw [show Real.pi / 2 + Real.pi / 2 = Real.pi by ring]
  norm_num

end ModelWidth
