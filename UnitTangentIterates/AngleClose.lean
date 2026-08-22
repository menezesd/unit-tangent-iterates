import Mathlib
import UnitTangentIterates.FrontPeriodizationIntegral
import UnitTangentIterates.MatchingTheorem

/-!
# Closeness of the tangent angles of the periodized and the isolated front

The lemma *Uniform transverse width* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* compares the tangent angle `Θ_H` of the periodized front
with the tangent angle `Θ_*` of the isolated translated hairpin, and consumes
the estimate

```
  ‖Θ_H − Θ_*‖_{L^∞(I_H)} ≤ C e^{−βH} ,       I_H = [−H/2, H/2].
```

This file produces that estimate.  Since `Θ_H' = K_H` and `Θ_*' = K_*`, with a
common origin `Θ_H(0) = Θ_*(0)` the sup distance is at most the `L¹` distance
of the two curvatures over the cell, and that distance is bounded by the two
errors already available:

* the **front periodization error** `∫_{I_H}|K_H − K̄_H|`
  (`FrontPeriodizationIntegral.front_periodization_error_cell_le`), and
* the **omitted mass** `∫_{I_H}|K̄_H − K_*| = ∫_{I_H}∑_{j≠0}K_*(· − jH)`
  (`PeriodizedTail.integral_tsum_translates_le`).

Main results:

* `abs_sub_le_intervalIntegral_abs_deriv` : the elementary sup-from-`L¹` step;
* `curvature_L1_close` : the `L¹` distance of the two curvatures over the cell
  is at most `(Lip(a)·D·8C²/(α−β) + 2C_K/α) e^{−βH}`;
* `angle_sup_close` : hence `|Θ_H(s) − Θ_*(s)| ≤ C e^{−βH}` on the cell.
-/

noncomputable section

open MeasureTheory Set Real

namespace AngleClose

open FrontPeriodization FrontPeriodizationIntegral

variable {f g f' g' y yp Kstar KH ThH Ths : ℝ → ℝ} {C CK D a alpha beta H : ℝ}

/-! ### From an `L¹` bound on the derivatives to a sup bound -/

/-- **Sup distance from `L¹` distance of the derivatives.**  Two primitives
agreeing at the origin differ, at any point of the centred cell, by at most the
`L¹` distance of their derivatives over that cell. -/
theorem abs_sub_le_intervalIntegral_abs_deriv (hH : 0 < H)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (h0 : f 0 = g 0)
    (hint : IntervalIntegrable (fun t => f' t - g' t) volume (-(H / 2)) (H / 2))
    {s : ℝ} (hs : s ∈ Icc (-(H / 2)) (H / 2)) :
    |f s - g s| ≤ ∫ t in (-(H / 2))..(H / 2), |f' t - g' t| := by
  obtain ⟨hs1, hs2⟩ := hs
  have hsub : uIcc (0 : ℝ) s ⊆ Icc (-(H / 2)) (H / 2) := by
    rcases le_total 0 s with hs0 | hs0
    · rw [uIcc_of_le hs0]
      exact Icc_subset_Icc (by linarith) hs2
    · rw [uIcc_of_ge hs0]
      exact Icc_subset_Icc hs1 (by linarith)
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) s, HasDerivAt (fun t => f t - g t) (f' x - g' x) x :=
    fun x _ => (hf x).sub (hg x)
  have hint' : IntervalIntegrable (fun t => f' t - g' t) volume 0 s := by
    refine hint.mono_set ?_
    rw [uIcc_of_le (by linarith : -(H / 2) ≤ H / 2)]
    exact hsub
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint'
  have hval : f s - g s = ∫ t in (0:ℝ)..s, (f' t - g' t) := by
    rw [hfund, h0]
    ring
  rw [hval]
  -- bound the integral over `[0,s]` by the integral of the absolute value over the cell
  have habs : |∫ t in (0:ℝ)..s, (f' t - g' t)| ≤ ∫ t in uIoc (0:ℝ) s, |f' t - g' t| := by
    rcases le_total 0 s with hs0 | hs0
    · rw [uIoc_of_le hs0]
      calc |∫ t in (0:ℝ)..s, (f' t - g' t)| ≤ ∫ t in (0:ℝ)..s, |f' t - g' t| :=
            intervalIntegral.abs_integral_le_integral_abs hs0
        _ = ∫ t in Ioc (0:ℝ) s, |f' t - g' t| := intervalIntegral.integral_of_le hs0
    · rw [uIoc_of_ge hs0]
      have h1 : |∫ t in (0:ℝ)..s, (f' t - g' t)| = |∫ t in s..(0:ℝ), (f' t - g' t)| := by
        rw [intervalIntegral.integral_symm, abs_neg]
      rw [h1]
      calc |∫ t in s..(0:ℝ), (f' t - g' t)| ≤ ∫ t in s..(0:ℝ), |f' t - g' t| :=
            intervalIntegral.abs_integral_le_integral_abs hs0
        _ = ∫ t in Ioc s (0:ℝ), |f' t - g' t| := intervalIntegral.integral_of_le hs0
  refine habs.trans ?_
  rw [intervalIntegral.integral_of_le (by linarith : -(H / 2) ≤ H / 2)]
  refine setIntegral_mono_set ?_ ?_ ?_
  · exact (hint.abs).1
  · exact Filter.Eventually.of_forall (fun t => abs_nonneg _)
  · refine Filter.Eventually.of_forall (fun t ht => ?_)
    rcases le_total 0 s with hs0 | hs0
    · rw [uIoc_of_le hs0] at ht
      exact ⟨by linarith [ht.1], le_trans ht.2 hs2⟩
    · rw [uIoc_of_ge hs0] at ht
      exact ⟨lt_of_lt_of_le (lt_of_le_of_lt hs1 ht.1) (le_refl _), by linarith [ht.2]⟩

/-! ### The `L¹` distance of the two curvatures -/

/-- **The curvatures of the periodized and the isolated front are `L¹`-close
over the cell.**  The two contributions are the front periodization error and
the mass of `K_*` omitted by the cell. -/
theorem curvature_L1_close
    (halpha : 0 < alpha) (hH : 0 < H) (hbeta : 0 < beta) (hba : beta < alpha / 2)
    (hhalf : Real.exp (-(beta * H)) ≤ 1 / 2)
    (hy : Continuous y) (hyp : Continuous yp)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hD : 0 ≤ D) (hypb : ∀ s, |yp s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hYa : ∀ u, (∑' m : ℤ, y (u - m * H)) ≤ a)
    (hKstar : ∀ s, Kstar s = y s + G (y s) * yp s)
    (hKH : ∀ t, KH t = (∑' m : ℤ, y (t - m * H))
      + G (∑' m : ℤ, y (t - m * H)) * (∑' m : ℤ, yp (t - m * H)))
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ CK * Real.exp (-alpha * |s|)) :
    (∫ t in (-(H / 2))..(H / 2), |KH t - Kstar t|)
      ≤ (lipConst a * D * (8 * C ^ 2 / (alpha - beta)) + 2 * CK / alpha)
        * Real.exp (-(beta * H)) := by
  have hcell : -(H / 2) + H = H / 2 := by ring
  -- the periodized isolated profile
  set Kbar : ℝ → ℝ := fun t => ∑' m : ℤ, Kstar (t - m * H) with hKbar
  have habs : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]; exact hyb s
  have habsp : ∀ s, |yp s| ≤ (D * C) * Real.exp (-alpha * |s|) := by
    intro s
    refine (hypb s).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hyb s) hD
  have hKcont : Continuous Kstar := by
    have hyY : ∀ u, y u ≤ ∑' j : ℤ, y (u - j * H) := by
      intro u
      have h := le_tsum_translates (y := y) (C := C) (alpha := alpha) (P := H)
        halpha hH hy0 hyb u 0
      simpa using h
    have hya : ∀ s, y s ≤ a := fun s => (hyY s).trans (hYa s)
    have hGy : Continuous fun s => G (y s) := continuous_G_comp ha0 ha1 hy hy0 hya
    have : Continuous fun s => y s + G (y s) * yp s := hy.add (hGy.mul hyp)
    exact this.congr (fun s => (hKstar s).symm)
  have hKHcont : Continuous KH := by
    have hYcont : Continuous fun u : ℝ => ∑' m : ℤ, y (u - m * H) :=
      continuous_tsum_translates halpha hH hy habs
    have hYpcont : Continuous fun u : ℝ => ∑' m : ℤ, yp (u - m * H) :=
      continuous_tsum_translates halpha hH hyp habsp
    have hY0 : ∀ u : ℝ, 0 ≤ ∑' m : ℤ, y (u - m * H) := by
      intro u
      have h := le_tsum_translates (y := y) (C := C) (alpha := alpha) (P := H)
        halpha hH hy0 hyb u 0
      exact le_trans (hy0 _) (by simpa using h)
    have hGY : Continuous fun u : ℝ => G (∑' m : ℤ, y (u - m * H)) :=
      continuous_G_comp ha0 ha1 hYcont hY0 hYa
    exact (hYcont.add (hGY.mul hYpcont)).congr (fun t => (hKH t).symm)
  have hKbarcont : Continuous Kbar :=
    continuous_tsum_translates halpha hH hKcont hKbd
  -- the pointwise split
  have hsplit : ∀ t, |KH t - Kstar t| ≤ |KH t - Kbar t| + |Kbar t - Kstar t| := by
    intro t
    calc |KH t - Kstar t| = |(KH t - Kbar t) + (Kbar t - Kstar t)| := by ring_nf
      _ ≤ |KH t - Kbar t| + |Kbar t - Kstar t| := abs_add_le _ _
  have hi1 : IntervalIntegrable (fun t => |KH t - Kbar t|) volume (-(H / 2)) (H / 2) :=
    ((hKHcont.sub hKbarcont).abs).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t => |Kbar t - Kstar t|) volume (-(H / 2)) (H / 2) :=
    ((hKbarcont.sub hKcont).abs).intervalIntegrable _ _
  have hi0 : IntervalIntegrable (fun t => |KH t - Kstar t|) volume (-(H / 2)) (H / 2) :=
    ((hKHcont.sub hKcont).abs).intervalIntegrable _ _
  have hmono : (∫ t in (-(H / 2))..(H / 2), |KH t - Kstar t|)
      ≤ (∫ t in (-(H / 2))..(H / 2), |KH t - Kbar t|)
        + ∫ t in (-(H / 2))..(H / 2), |Kbar t - Kstar t| := by
    rw [← intervalIntegral.integral_add hi1 hi2]
    exact intervalIntegral.integral_mono_on (by linarith) hi0 (hi1.add hi2)
      (fun t _ => hsplit t)
  refine hmono.trans ?_
  -- the front periodization error
  have hfront : (∫ t in (-(H / 2))..(H / 2), |KH t - Kbar t|)
      ≤ lipConst a * D * (8 * C ^ 2 / (alpha - beta)) * Real.exp (-(beta * H)) := by
    have hIco : (∫ t in (-(H / 2))..(H / 2), |KH t - Kbar t|)
        = ∫ t in Ico (-(H / 2)) (-(H / 2) + H), |KH t - Kbar t| := by
      rw [hcell, intervalIntegral.integral_of_le (by linarith : -(H / 2) ≤ H / 2),
        integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    rw [hIco]
    have hcongr : (∫ t in Ico (-(H / 2)) (-(H / 2) + H), |KH t - Kbar t|)
        = ∫ t in Ico (-(H / 2)) (-(H / 2) + H),
          |((∑' m : ℤ, y (t - m * H))
              + G (∑' m : ℤ, y (t - m * H)) * (∑' m : ℤ, yp (t - m * H)))
            - ∑' m : ℤ, (y (t - m * H) + G (y (t - m * H)) * yp (t - m * H))| := by
      refine setIntegral_congr_fun measurableSet_Ico (fun t _ => ?_)
      rw [hKH t, hKbar]
      simp only
      congr 2
      exact tsum_congr (fun m => hKstar _)
    rw [hcongr]
    exact front_periodization_error_cell_le (y := y) (yp := yp) (C := C) (alpha := alpha)
      (beta := beta) (a := a) (D := D) (P := H) (p := -(H / 2))
      halpha hH hbeta (by linarith) hhalf hy hyp hy0 hyb hD hypb ha0 ha1 hYa
  -- the omitted mass
  have htail : (∫ t in (-(H / 2))..(H / 2), |Kbar t - Kstar t|)
      ≤ 2 * CK / alpha * Real.exp (-(beta * H)) := by
    have hIco : (∫ t in (-(H / 2))..(H / 2), |Kbar t - Kstar t|)
        = ∫ t in Ico (-(H / 2)) (-(H / 2) + H), |Kbar t - Kstar t| := by
      rw [hcell, intervalIntegral.integral_of_le (by linarith : -(H / 2) ≤ H / 2),
        integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    rw [hIco]
    have hcongr : (∫ t in Ico (-(H / 2)) (-(H / 2) + H), |Kbar t - Kstar t|)
        = ∫ t in Ico (-(H / 2)) (-(H / 2) + H),
            ∑' j : {j : ℤ // j ≠ 0}, Kstar (t - (j : ℤ) * H) := by
      refine setIntegral_congr_fun measurableSet_Ico (fun t _ => ?_)
      have hs : Summable (fun m : ℤ => Kstar (t - m * H)) :=
        summable_translates halpha hH hKbd t
      have hsub : Kbar t - Kstar t = ∑' j : {j : ℤ // j ≠ 0}, Kstar (t - (j : ℤ) * H) := by
        rw [hKbar]
        simp only
        rw [tsum_split_zero hs]
        norm_num
      rw [hsub, abs_of_nonneg]
      refine tsum_nonneg (fun j => hK0 _)
    rw [hcongr]
    have hbound := PeriodizedTail.integral_tsum_translates_le (f := Kstar) (p := -(H / 2))
      (P := H) (C := CK) (alpha := alpha) hH halpha hKint hK0 hKbd
      (by linarith) (by rw [hcell]; linarith)
    refine hbound.trans ?_
    have hCK : 0 ≤ CK := by
      have h := hKbd 0
      have h0 := le_abs_self (Kstar 0)
      have h1 := hK0 0
      simp at h
      linarith
    have hexp : Real.exp (-(alpha / 2 * H)) ≤ Real.exp (-(beta * H)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h1 : CK * Real.exp (alpha * -(H / 2)) / alpha
        ≤ CK / alpha * Real.exp (-(beta * H)) := by
      have : Real.exp (alpha * -(H / 2)) = Real.exp (-(alpha / 2 * H)) := by
        congr 1; ring
      rw [this, mul_div_right_comm]
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
    have h2 : CK * Real.exp (-alpha * (-(H / 2) + H)) / alpha
        ≤ CK / alpha * Real.exp (-(beta * H)) := by
      have : Real.exp (-alpha * (-(H / 2) + H)) = Real.exp (-(alpha / 2 * H)) := by
        congr 1; ring
      rw [this, mul_div_right_comm]
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
    have : CK / alpha * Real.exp (-(beta * H)) + CK / alpha * Real.exp (-(beta * H))
        = 2 * CK / alpha * Real.exp (-(beta * H)) := by ring
    linarith
  have : lipConst a * D * (8 * C ^ 2 / (alpha - beta)) * Real.exp (-(beta * H))
      + 2 * CK / alpha * Real.exp (-(beta * H))
      = (lipConst a * D * (8 * C ^ 2 / (alpha - beta)) + 2 * CK / alpha)
        * Real.exp (-(beta * H)) := by ring
  linarith

/-! ### The sup closeness of the tangent angles -/

/-- **Uniform closeness of the tangent angles.**  With a common origin
`Θ_H(0) = Θ_*(0)`, the tangent angle of the periodized front and that of the
isolated one differ, on the centred cell `I_H = [−H/2, H/2]`, by at most

`(Lip(a)·D·8C²/(α−β) + 2C_K/α) e^{−βH}`.

This is the estimate consumed by the lemma *Uniform transverse width*. -/
theorem angle_sup_close
    (halpha : 0 < alpha) (hH : 0 < H) (hbeta : 0 < beta) (hba : beta < alpha / 2)
    (hhalf : Real.exp (-(beta * H)) ≤ 1 / 2)
    (hy : Continuous y) (hyp : Continuous yp)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hD : 0 ≤ D) (hypb : ∀ s, |yp s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hYa : ∀ u, (∑' m : ℤ, y (u - m * H)) ≤ a)
    (hKstar : ∀ s, Kstar s = y s + G (y s) * yp s)
    (hKH : ∀ t, KH t = (∑' m : ℤ, y (t - m * H))
      + G (∑' m : ℤ, y (t - m * H)) * (∑' m : ℤ, yp (t - m * H)))
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ CK * Real.exp (-alpha * |s|))
    (hThH : ∀ t, HasDerivAt ThH (KH t) t) (hThs : ∀ t, HasDerivAt Ths (Kstar t) t)
    (h0 : ThH 0 = Ths 0)
    {s : ℝ} (hs : s ∈ Icc (-(H / 2)) (H / 2)) :
    |ThH s - Ths s|
      ≤ (lipConst a * D * (8 * C ^ 2 / (alpha - beta)) + 2 * CK / alpha)
        * Real.exp (-(beta * H)) := by
  have habs : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]; exact hyb s
  have habsp : ∀ s, |yp s| ≤ (D * C) * Real.exp (-alpha * |s|) := by
    intro s
    refine (hypb s).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hyb s) hD
  have hyY : ∀ u, y u ≤ ∑' j : ℤ, y (u - j * H) := by
    intro u
    have h := le_tsum_translates (y := y) (C := C) (alpha := alpha) (P := H)
      halpha hH hy0 hyb u 0
    simpa using h
  have hya : ∀ s, y s ≤ a := fun s => (hyY s).trans (hYa s)
  have hKcont : Continuous Kstar := by
    have hGy : Continuous fun s => G (y s) := continuous_G_comp ha0 ha1 hy hy0 hya
    exact (hy.add (hGy.mul hyp)).congr (fun s => (hKstar s).symm)
  have hKHcont : Continuous KH := by
    have hYcont : Continuous fun u : ℝ => ∑' m : ℤ, y (u - m * H) :=
      continuous_tsum_translates halpha hH hy habs
    have hYpcont : Continuous fun u : ℝ => ∑' m : ℤ, yp (u - m * H) :=
      continuous_tsum_translates halpha hH hyp habsp
    have hY0 : ∀ u : ℝ, 0 ≤ ∑' m : ℤ, y (u - m * H) := fun u => (hy0 u).trans (hyY u)
    have hGY : Continuous fun u : ℝ => G (∑' m : ℤ, y (u - m * H)) :=
      continuous_G_comp ha0 ha1 hYcont hY0 hYa
    exact (hYcont.add (hGY.mul hYpcont)).congr (fun t => (hKH t).symm)
  have hint : IntervalIntegrable (fun t => KH t - Kstar t) volume (-(H / 2)) (H / 2) :=
    (hKHcont.sub hKcont).intervalIntegrable _ _
  refine (abs_sub_le_intervalIntegral_abs_deriv hH hThH hThs h0 hint hs).trans ?_
  exact curvature_L1_close halpha hH hbeta hba hhalf hy hyp hy0 hyb hD hypb ha0 ha1 hYa
    hKstar hKH hKint hK0 hKbd

end AngleClose
