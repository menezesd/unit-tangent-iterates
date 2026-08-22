import Mathlib

/-!
# The large-separation threshold and the final width contradiction

This file formalizes the self-contained cores of the lemma *Large-separation
threshold* and of the closing argument of the paper *A Noncircular Oval with
Convex Unit-Tangent Iterates*.

The paper's half-perimeter recursion is `P(H_{n+1}) = H_n`, where `P` is the
rear half-perimeter of the two-cap pair of separation `H`.  For large `H` one
has `P' ≥ 1/2` and `P(H) ≤ H - Δ/2`, which makes the recursion uniquely
solvable and forces the linear growth `H_n ≥ H_0 + (Δ/2)n`.  The defect
quantities are then summed by a polynomially weighted geometric series, giving
`r_0 ≤ C(1+H_0)² e^{-βH_0} → 0`, and the final contradiction is that the
transverse width of the shadowing orbit stays bounded while a circle of the
same perimeter would have width `(2H_0 - C r_0)/π → ∞`.

Main results:

* `strictMonoOn_of_deriv_ge_half`, `le_of_deriv_ge_half`,
  `existsUnique_recursion_step` : the recursion step `P(x) = t` has exactly one
  solution `x ≥ H_*`;
* `recursion_growth` : `H_0 + (Δ/2) n ≤ H_n`;
* `summable_weighted_geometric`, `tail_bound`, `tendsto_tail_zero` : the
  synchronized tail estimate `r_0 ≤ C(1+H_0)²e^{-βH_0} → 0`;
* `eventually_width_gap`, `width_lt_circle_width` : the closing contradiction.
-/

noncomputable section

open Filter Real Set

namespace MainThresholds

/-! ### The half-perimeter recursion -/

section Recursion

variable {P Pp : ℝ → ℝ} {Hstar : ℝ}

/-- A function whose derivative is at least `1/2` on `[H_*,∞)` is strictly
increasing there; in particular the recursion step has at most one solution. -/
theorem strictMonoOn_of_deriv_ge_half (hP : ∀ x, HasDerivAt P (Pp x) x)
    (hPp : ∀ x, Hstar ≤ x → 1 / 2 ≤ Pp x) :
    StrictMonoOn P (Ici Hstar) := by
  have hdiff : Differentiable ℝ P := fun x => (hP x).differentiableAt
  apply strictMonoOn_of_deriv_pos (convex_Ici Hstar) hdiff.continuous.continuousOn
  intro x hx
  rw [interior_Ici] at hx
  rw [(hP x).deriv]
  linarith [hPp x (le_of_lt hx)]

/-- A quantitative form of the same statement: `P` grows at least at rate
`1/2`. -/
theorem le_of_deriv_ge_half (hP : ∀ x, HasDerivAt P (Pp x) x)
    (hPp : ∀ x, Hstar ≤ x → 1 / 2 ≤ Pp x) {x : ℝ} (hx : Hstar ≤ x) :
    P Hstar + (x - Hstar) / 2 ≤ P x := by
  have hdiff : Differentiable ℝ P := fun t => (hP t).differentiableAt
  have hmono : MonotoneOn (fun t => P t - t / 2) (Ici Hstar) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici Hstar)
    · exact (hdiff.continuous.sub (continuous_id.div_const 2)).continuousOn
    · exact fun t _ => (((hP t).sub ((hasDerivAt_id t).div_const 2)).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have hd : HasDerivAt (fun r => P r - r / 2) (Pp t - 1 / 2) t := by
        simpa using (hP t).sub ((hasDerivAt_id t).div_const 2)
      rw [hd.deriv]
      linarith [hPp t (le_of_lt ht)]
  have := hmono (Set.self_mem_Ici) (mem_Ici.mpr hx) hx
  simp only at this
  linarith

/-- **The recursion step is uniquely solvable.**  If `P' ≥ 1/2` on `[H_*,∞)`,
then for every target value `t ≥ P(H_*)` there is exactly one `x ≥ H_*` with
`P(x) = t`. -/
theorem existsUnique_recursion_step (hP : ∀ x, HasDerivAt P (Pp x) x)
    (hPp : ∀ x, Hstar ≤ x → 1 / 2 ≤ Pp x) {t : ℝ} (ht : P Hstar ≤ t) :
    ∃! x, Hstar ≤ x ∧ P x = t := by
  have hdiff : Differentiable ℝ P := fun x => (hP x).differentiableAt
  set b : ℝ := Hstar + 2 * (t - P Hstar) with hb
  have hbge : Hstar ≤ b := by simp only [hb]; linarith
  have hPb : t ≤ P b := by
    have := le_of_deriv_ge_half hP hPp hbge
    simp only [hb] at this ⊢
    linarith
  have hsub : Icc (P Hstar) (P b) ⊆ P '' Icc Hstar b :=
    intermediate_value_Icc hbge hdiff.continuous.continuousOn
  obtain ⟨x, hx, hxt⟩ := hsub ⟨ht, hPb⟩
  refine ⟨x, ⟨hx.1, hxt⟩, ?_⟩
  rintro y ⟨hy, hyt⟩
  have hmono := strictMonoOn_of_deriv_ge_half hP hPp
  exact hmono.injOn (mem_Ici.mpr hy) (mem_Ici.mpr hx.1) (by rw [hyt, hxt])

/-- **Linear growth of the cap sequence.**  If `P(H) ≤ H - Δ/2` on the range of
the sequence and `P(H_{n+1}) = H_n`, then `H_n ≥ H_0 + (Δ/2) n`. -/
theorem recursion_growth {H : ℕ → ℝ} {Delta : ℝ}
    (hPle : ∀ x, Hstar ≤ x → P x ≤ x - Delta / 2)
    (hmem : ∀ n, Hstar ≤ H n) (hrec : ∀ n, P (H (n + 1)) = H n) (n : ℕ) :
    H 0 + Delta / 2 * n ≤ H n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hstep : H k + Delta / 2 ≤ H (k + 1) := by
      have h := hPle (H (k + 1)) (hmem (k + 1))
      rw [hrec k] at h
      linarith
    have : H 0 + Delta / 2 * k + Delta / 2 ≤ H (k + 1) := by linarith
    calc H 0 + Delta / 2 * (k + 1 : ℕ) = H 0 + Delta / 2 * k + Delta / 2 := by
          push_cast; ring
      _ ≤ H (k + 1) := this

end Recursion

/-! ### The synchronized tail estimate -/

section Tail

variable {d beta H0 : ℝ}

/-- A polynomially weighted geometric series converges. -/
theorem summable_weighted_geometric (hd : 0 < d) (hbeta : 0 < beta) :
    Summable (fun n : ℕ => (1 + d * n) ^ 2 * Real.exp (-(beta * d) * n)) := by
  set q : ℝ := Real.exp (-(beta * d)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hq0, hq]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hq1
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hq1
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hq1
  have hsum := (h0.add ((h1.mul_left (2 * d)))).add (h2.mul_left (d ^ 2))
  apply hsum.congr
  intro n
  have hexp : Real.exp (-(beta * d) * n) = q ^ n := by
    rw [hq, ← Real.exp_nat_mul]
    ring_nf
  rw [hexp]
  ring

/-- The constant of the synchronized tail estimate. -/
noncomputable def tailConst (d beta : ℝ) : ℝ :=
  ∑' n : ℕ, (1 + d * n) ^ 2 * Real.exp (-(beta * d) * n)

/-- **The synchronized tail estimate.**  Along a sequence growing at least
linearly, `∑_n (1 + H_n)² e^{-βH_n} ≤ C (1+H_0)² e^{-βH_0}`. -/
theorem tail_bound (hd : 0 < d) (hbeta : 0 < beta) (hH0 : 0 ≤ H0) :
    ∑' n : ℕ, (1 + H0 + d * n) ^ 2 * Real.exp (-beta * (H0 + d * n))
      ≤ (1 + H0) ^ 2 * Real.exp (-beta * H0) * tailConst d beta := by
  have hmaj : Summable (fun n : ℕ => (1 + d * n) ^ 2 * Real.exp (-(beta * d) * n)) :=
    summable_weighted_geometric hd hbeta
  have hpoint : ∀ n : ℕ, (1 + H0 + d * n) ^ 2 * Real.exp (-beta * (H0 + d * n))
      ≤ ((1 + H0) ^ 2 * Real.exp (-beta * H0)) * ((1 + d * n) ^ 2 * Real.exp (-(beta * d) * n)) := by
    intro n
    have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hpoly : (1 + H0 + d * n) ^ 2 ≤ (1 + H0) ^ 2 * (1 + d * n) ^ 2 := by
      have hbase : 1 + H0 + d * n ≤ (1 + H0) * (1 + d * n) := by
        nlinarith [mul_nonneg (mul_nonneg hH0 hd.le) hn]
      have h0 : 0 ≤ 1 + H0 + d * n := by positivity
      calc (1 + H0 + d * n) ^ 2 ≤ ((1 + H0) * (1 + d * n)) ^ 2 := by
            exact pow_le_pow_left₀ h0 hbase 2
        _ = (1 + H0) ^ 2 * (1 + d * n) ^ 2 := by rw [mul_pow]
    have hexp : Real.exp (-beta * (H0 + d * n))
        = Real.exp (-beta * H0) * Real.exp (-(beta * d) * n) := by
      rw [← Real.exp_add]
      ring_nf
    rw [hexp]
    have hE : 0 < Real.exp (-beta * H0) * Real.exp (-(beta * d) * n) := by positivity
    calc (1 + H0 + d * n) ^ 2 * (Real.exp (-beta * H0) * Real.exp (-(beta * d) * n))
        ≤ ((1 + H0) ^ 2 * (1 + d * n) ^ 2) * (Real.exp (-beta * H0)
            * Real.exp (-(beta * d) * n)) := by
          exact mul_le_mul_of_nonneg_right hpoly hE.le
      _ = ((1 + H0) ^ 2 * Real.exp (-beta * H0))
            * ((1 + d * n) ^ 2 * Real.exp (-(beta * d) * n)) := by ring
  have hsumL : Summable (fun n : ℕ => (1 + H0 + d * n) ^ 2 * Real.exp (-beta * (H0 + d * n))) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) hpoint ?_
    exact hmaj.mul_left _
  calc ∑' n : ℕ, (1 + H0 + d * n) ^ 2 * Real.exp (-beta * (H0 + d * n))
      ≤ ∑' n : ℕ, ((1 + H0) ^ 2 * Real.exp (-beta * H0))
          * ((1 + d * n) ^ 2 * Real.exp (-(beta * d) * n)) :=
        hsumL.tsum_le_tsum hpoint (hmaj.mul_left _)
    _ = (1 + H0) ^ 2 * Real.exp (-beta * H0) * tailConst d beta := by
        rw [tsum_mul_left, tailConst]

/-- The tail bound tends to zero as the initial separation grows. -/
theorem tendsto_tail_zero (hbeta : 0 < beta) :
    Tendsto (fun x : ℝ => (1 + x) ^ 2 * Real.exp (-beta * x)) atTop (nhds 0) := by
  have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have hF : Tendsto (fun u : ℝ => (1 + u / beta) ^ 2 * Real.exp (-u)) atTop (nhds 0) := by
    have hsum := (h0.add (h1.const_mul (2 / beta))).add (h2.const_mul (1 / beta ^ 2))
    simp only [mul_zero, add_zero] at hsum
    apply hsum.congr
    intro u
    field_simp
    ring
  have hscale : Tendsto (fun x : ℝ => beta * x) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop hbeta
  have h := hF.comp hscale
  apply h.congr
  intro x
  simp only [Function.comp]
  field_simp

end Tail

/-! ### The closing width contradiction -/

section Width

variable {Cw Csh W H0 : ℝ}

/-- **The width gap holds for all large separations.**  If the shadowing defect
`r(H_0)` tends to `0`, then eventually the circle width `(2H_0 - C_sh r)/π`
exceeds the bound `C_W + 2C_sh r` on the width of the orbit. -/
theorem eventually_width_gap {r : ℝ → ℝ} (hr : Tendsto r atTop (nhds 0)) :
    ∀ᶠ x in atTop, Cw + 2 * Csh * r x < (2 * x - Csh * r x) / Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlin : Tendsto (fun x : ℝ => 2 / Real.pi * x) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop (by positivity)
  have hbdd : Tendsto (fun x : ℝ => -(Csh / Real.pi) * r x - 2 * Csh * r x - Cw)
      atTop (nhds (-Cw)) := by
    have := ((hr.const_mul (-(Csh / Real.pi))).sub (hr.const_mul (2 * Csh))).sub_const Cw
    simpa using this
  have hdiff : Tendsto
      (fun x : ℝ => (2 * x - Csh * r x) / Real.pi - (Cw + 2 * Csh * r x)) atTop atTop := by
    have hsum := hlin.atTop_add hbdd
    apply hsum.congr
    intro x
    field_simp
    ring
  filter_upwards [hdiff.eventually_gt_atTop 0] with x hx
  linarith

/-- **The final contradiction.**  A curve whose width is at most
`C_W + 2C_sh r_0`, in the regime where this is below the circle width
`(2H_0 - C_sh r_0)/π`, is not a circle of that perimeter. -/
theorem width_lt_circle_width {r0 : ℝ} (hw : W ≤ Cw + 2 * Csh * r0)
    (hgap : Cw + 2 * Csh * r0 < (2 * H0 - Csh * r0) / Real.pi) :
    W < (2 * H0 - Csh * r0) / Real.pi := lt_of_le_of_lt hw hgap

end Width

end MainThresholds
