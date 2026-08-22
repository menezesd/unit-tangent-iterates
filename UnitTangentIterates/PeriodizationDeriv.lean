import Mathlib

/-!
# Differentiating the periodization in the period

This file formalizes the derivative case of the lemma *Exponential
periodization* of the paper *A Noncircular Oval with Convex Unit-Tangent
Iterates*: the periodization

`Z_H(s) = ∑_{m ∈ ℤ} z(s - mH)`

may be differentiated termwise in the period `H` (with `s` held fixed), the
paper's identity `∂_H z(s - mH) = -m z'(s - mH)`, and the resulting series
converges because the exponential tails dominate the polynomial factor `|m|`.

Main results:

* `abs_shift_le` : the uniform geometric majorant
  `|w(s - mH)| ≤ C e^{a|s|} (e^{-aH₀})^{|m|}` valid for every period
  `H ≥ H₀ > 0`;
* `summable_natAbs_geometric` : summability of `∑_{m ∈ ℤ} |m| q^{|m|}` for
  `0 ≤ q < 1`;
* `summable_periodization_of_le` : the periodized series converges for every
  `H ≥ H₀`, at every point `s`;
* `hasDerivAt_periodization_period` : **termwise differentiation in the
  period**,
  `∂_H ∑_m z(s - mH) = ∑_m (-m) z'(s - mH)` for `H > H₀`.
-/

noncomputable section

open Real

namespace PeriodizationDeriv

variable {z z' w : ℝ → ℝ} {C a H₀ H s : ℝ}

/-- The constant in an exponential majorant is nonnegative. -/
lemma const_nonneg (hb : ∀ x, |w x| ≤ C * Real.exp (-a * |x|)) : 0 ≤ C := by
  have h := hb 0
  simp at h
  exact le_trans (abs_nonneg _) h

/-- **A uniform geometric majorant for the translates.**  If `|w| ≤ C e^{-a|·|}`
then, for every period `H ≥ H₀ > 0`, the translate `w(s - mH)` is bounded by
`C e^{a|s|} (e^{-aH₀})^{|m|}`. -/
theorem abs_shift_le (ha : 0 < a) (hb : ∀ x, |w x| ≤ C * Real.exp (-a * |x|))
    (hH₀ : 0 < H₀) (hH : H₀ ≤ H) (m : ℤ) :
    |w (s - m * H)| ≤ (C * Real.exp (a * |s|)) * (Real.exp (-a * H₀)) ^ m.natAbs := by
  have hC : 0 ≤ C := const_nonneg hb
  have hmabs : |(m : ℝ)| = (m.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; norm_num
  have hlow : (m.natAbs : ℝ) * H - |s| ≤ |s - m * H| := by
    have h1 : |(m : ℝ) * H| - |s| ≤ |(m : ℝ) * H - s| := abs_sub_abs_le_abs_sub _ _
    have h2 : |(m : ℝ) * H - s| = |s - (m : ℝ) * H| := abs_sub_comm _ _
    have h3 : |(m : ℝ) * H| = (m.natAbs : ℝ) * H := by
      rw [abs_mul, abs_of_pos (lt_of_lt_of_le hH₀ hH), hmabs]
    rw [h2, h3] at h1
    linarith
  have hlow' : (m.natAbs : ℝ) * H₀ - |s| ≤ |s - m * H| := by
    have : (m.natAbs : ℝ) * H₀ ≤ (m.natAbs : ℝ) * H :=
      mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg _)
    linarith
  calc |w (s - m * H)| ≤ C * Real.exp (-a * |s - m * H|) := hb _
    _ ≤ C * Real.exp (-a * ((m.natAbs : ℝ) * H₀ - |s|)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact Real.exp_le_exp.mpr (by nlinarith)
    _ = (C * Real.exp (a * |s|)) * (Real.exp (-a * H₀)) ^ m.natAbs := by
        rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
        ring_nf

/-! ### Summability of the geometric and polynomially weighted series -/

variable {q : ℝ}

/-- The two-sided geometric series converges. -/
lemma summable_geometric_int {K : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun m : ℤ => K * q ^ m.natAbs) := by
  have hgeo : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq1
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using hgeo.mul_left K
  · have hshape : (fun n : ℕ => K * q ^ (-((n : ℤ) + 1)).natAbs)
        = fun n : ℕ => (K * q) * q ^ n := by
      funext n
      have hn : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
      rw [hn]; ring
    rw [hshape]
    exact hgeo.mul_left _

/-- The polynomially weighted two-sided geometric series converges. -/
lemma summable_natAbs_geometric {K : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun m : ℤ => K * ((m.natAbs : ℝ) * q ^ m.natAbs)) := by
  have hgeo : Summable (fun n : ℕ => (n : ℝ) * q ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (by rwa [Real.norm_eq_abs,
      abs_of_nonneg hq0])
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using hgeo.mul_left K
  · have hshape : (fun n : ℕ => K * (((-((n : ℤ) + 1)).natAbs : ℝ) * q ^ (-((n : ℤ) + 1)).natAbs))
        = fun n : ℕ => K * (((n + 1 : ℕ) : ℝ) * q ^ (n + 1)) := by
      funext n
      have hn : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
      rw [hn]
    rw [hshape]
    have : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * q ^ (n + 1)) := by
      simpa using (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) * q ^ n) 1).2 hgeo
    exact this.mul_left K

/-- **Convergence of the periodized series** at every point and for every
period `H ≥ H₀ > 0`. -/
theorem summable_periodization_of_le (ha : 0 < a)
    (hzb : ∀ x, |z x| ≤ C * Real.exp (-a * |x|)) (hH₀ : 0 < H₀) (hH : H₀ ≤ H) :
    Summable (fun m : ℤ => z (s - m * H)) := by
  have hq0 : (0:ℝ) ≤ Real.exp (-a * H₀) := (Real.exp_pos _).le
  have hq1 : Real.exp (-a * H₀) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  refine Summable.of_norm_bounded (summable_geometric_int (K := C * Real.exp (a * |s|)) hq0 hq1) ?_
  intro m
  simpa [Real.norm_eq_abs] using abs_shift_le ha hzb hH₀ hH m

/-- **Termwise differentiation of the periodization in the period.**  With `s`
held fixed, `∂_H ∑_m z(s - mH) = ∑_m (-m) z'(s - mH)` for every `H > H₀ > 0`,
provided `z` and `z'` decay exponentially. -/
theorem hasDerivAt_periodization_period (ha : 0 < a) (hH₀ : 0 < H₀)
    (hz : ∀ x, HasDerivAt z (z' x) x)
    (hzb : ∀ x, |z x| ≤ C * Real.exp (-a * |x|))
    (hz'b : ∀ x, |z' x| ≤ C * Real.exp (-a * |x|))
    (hH : H₀ < H) :
    HasDerivAt (fun t => ∑' m : ℤ, z (s - m * t))
      (∑' m : ℤ, (-(m : ℝ)) * z' (s - m * H)) H := by
  set q : ℝ := Real.exp (-a * H₀) with hqdef
  have hq0 : (0:ℝ) ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  set K : ℝ := C * Real.exp (a * |s|) with hKdef
  -- the majorant
  have hu : Summable (fun m : ℤ => K * ((m.natAbs : ℝ) * q ^ m.natAbs)) :=
    summable_natAbs_geometric hq0 hq1
  -- termwise derivatives on the open half-line of admissible periods
  have hg : ∀ (m : ℤ) (t : ℝ), t ∈ Set.Ioi H₀ →
      HasDerivAt (fun r : ℝ => z (s - m * r)) ((-(m : ℝ)) * z' (s - m * t)) t := by
    intro m t _
    have hinner : HasDerivAt (fun r : ℝ => s - m * r) (-(m : ℝ)) t := by
      simpa using ((hasDerivAt_id t).const_mul ((m : ℝ))).const_sub s
    simpa [mul_comm] using (hz (s - m * t)).comp t hinner
  have hg' : ∀ (m : ℤ) (t : ℝ), t ∈ Set.Ioi H₀ →
      ‖(-(m : ℝ)) * z' (s - m * t)‖ ≤ K * ((m.natAbs : ℝ) * q ^ m.natAbs) := by
    intro m t ht
    have hle : H₀ ≤ t := le_of_lt ht
    have hbound := abs_shift_le (w := z') (s := s) ha hz'b hH₀ hle m
    have hmabs : |(-(m : ℝ))| = (m.natAbs : ℝ) := by
      rw [abs_neg, ← Int.cast_abs, Int.abs_eq_natAbs]; norm_num
    calc ‖(-(m : ℝ)) * z' (s - m * t)‖ = (m.natAbs : ℝ) * |z' (s - m * t)| := by
          rw [Real.norm_eq_abs, abs_mul, hmabs]
      _ ≤ (m.natAbs : ℝ) * (K * q ^ m.natAbs) := by
          exact mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
      _ = K * ((m.natAbs : ℝ) * q ^ m.natAbs) := by ring
  have hg0 : Summable (fun m : ℤ => z (s - m * H)) :=
    summable_periodization_of_le ha hzb hH₀ hH.le
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi (isPreconnected_Ioi) hg hg'
    (Set.mem_Ioi.mpr hH) hg0 (Set.mem_Ioi.mpr hH)

end PeriodizationDeriv
