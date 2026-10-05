module

public import Mathlib

/-!
# Periodization of an exponentially decaying pulse (Lemma 4.1, overlap estimate)

For a nonnegative pulse `y` with exponential decay `y(t) ≤ A e^{-a|t|}`, its periodization
`Y_H(s) = ∑_{m ∈ ℤ} y(s - mH)` converges, and the cross terms of the periodization are
exponentially small *relative to* `Y_H` itself:
`∑_{m ≠ n} |u(s - mH)| |v(s - nH)| ≤ C e^{-βH} Y_H(s)` whenever `|u|, |v| ≤ D y`
(this is estimate (4.2) of the paper; the relative bound `|u|, |v| ≤ D y` is how the paper
reduces the derivative cases to `j = k = 0`).
-/

@[expose] public section

namespace Ovals

open Real

/-- The periodization `Y_H(s) = ∑_{m ∈ ℤ} y(s - mH)`. -/
noncomputable def periodize (y : ℝ → ℝ) (H s : ℝ) : ℝ := ∑' m : ℤ, y (s - m * H)

section

variable {y : ℝ → ℝ} {A a : ℝ}

lemma summable_geom_natAbs {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun ℓ : ℤ => r ^ ℓ.natAbs) ∧ ∑' ℓ : ℤ, r ^ ℓ.natAbs ≤ 2 / (1 - r) := by
  have h1 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have hn : ∀ n : ℕ, (-((n : ℤ) + 1)).natAbs = n + 1 := fun n => by omega
  have hn' : ∀ n : ℕ, (-(n : ℤ)).natAbs = n := fun n => by omega
  have h2 : Summable (fun n : ℕ => r ^ (-((n : ℤ) + 1)).natAbs) := by
    refine (h1.mul_left r).congr fun n => ?_
    rw [hn, pow_succ, mul_comm]
  have h0 : Summable (fun n : ℕ => r ^ ((n : ℤ)).natAbs) := by
    simpa only [Int.natAbs_natCast] using h1
  have hs : Summable (fun ℓ : ℤ => r ^ ℓ.natAbs) :=
    Summable.of_nat_of_neg h0 (by simpa only [hn'] using h1)
  refine ⟨hs, ?_⟩
  rw [tsum_of_nat_of_neg_add_one (f := fun ℓ : ℤ => r ^ ℓ.natAbs) h0 h2]
  have e1 : ∑' n : ℕ, r ^ ((n : ℤ)).natAbs = (1 - r)⁻¹ := by
    simp only [Int.natAbs_natCast]; exact tsum_geometric_of_lt_one hr0 hr1
  have e2 : ∑' n : ℕ, r ^ (-((n : ℤ) + 1)).natAbs = r * (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 hr1, ← tsum_mul_left]
    congr 1; ext n
    rw [hn, pow_succ, mul_comm]
  rw [e1, e2]
  have h3 : 0 < 1 - r := by linarith
  have : (1 - r)⁻¹ + r * (1 - r)⁻¹ = (1 + r) / (1 - r) := by field_simp
  rw [this, div_le_div_iff_of_pos_right h3]
  linarith

lemma pulse_shift_le (hyA : ∀ t, y t ≤ A * exp (-(a * |t|))) (hA : 0 ≤ A) (ha : 0 < a)
    {H : ℝ} (hH : 0 < H) (s : ℝ) (m : ℤ) :
    y (s - m * H) ≤ A * exp (a * |s|) * exp (-(a * H)) ^ m.natAbs := by
  refine (hyA _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hA
  rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
  have hm : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hm]
  have : |(m : ℝ)| * H ≤ |s - m * H| + |s| := by
    have := abs_sub_abs_le_abs_sub (m * H : ℝ) s
    rw [abs_mul, abs_of_pos hH, abs_sub_comm] at this
    linarith
  nlinarith

/-- The periodization of an exponentially decaying pulse converges. -/
theorem summable_periodize (hy0 : ∀ t, 0 ≤ y t) (hyA : ∀ t, y t ≤ A * exp (-(a * |t|)))
    (ha : 0 < a) {H : ℝ} (hH : 0 < H) (s : ℝ) :
    Summable (fun m : ℤ => y (s - m * H)) := by
  have hA : 0 ≤ A := by
    have := (hy0 0).trans (hyA 0)
    exact nonneg_of_mul_nonneg_left this (exp_pos _)
  have hr1 : exp (-(a * H)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith
  refine Summable.of_nonneg_of_le (fun m => hy0 _) (fun m => pulse_shift_le hyA hA ha hH s m)
    (((summable_geom_natAbs (exp_pos _).le hr1).1).mul_left _)

/-- The pointwise overlap bound: for `m ≠ n`, one of the two arguments is far from the
origin, so `y(s-mH) y(s-nH) ≤ A e^{-a|m-n|H/2} (y(s-mH) + y(s-nH))`. -/
lemma pulse_pair_le (hy0 : ∀ t, 0 ≤ y t) (hyA : ∀ t, y t ≤ A * exp (-(a * |t|)))
    (ha : 0 < a) {H : ℝ} (hH : 0 < H) (s : ℝ) (m n : ℤ) :
    y (s - m * H) * y (s - n * H) ≤
      A * exp (-(a * H / 2)) ^ (m - n).natAbs * (y (s - m * H) + y (s - n * H)) := by
  have hmn : ((((m - n).natAbs : ℕ) : ℝ)) * H ≤ |s - m * H| + |s - n * H| := by
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
    have : (n - m : ℝ) * H = (s - m * H) - (s - n * H) := by ring
    have h2 := abs_sub (s - m * H) (s - n * H)
    rw [← this, abs_mul, abs_of_pos hH, abs_sub_comm] at h2
    linarith
  have hexp : exp (-(a * H / 2)) ^ (m - n).natAbs =
      exp (-(a * (((m - n).natAbs : ℕ) : ℝ) * H / 2)) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hexp]
  set k : ℝ := (((m - n).natAbs : ℕ) : ℝ)
  have hym := hy0 (s - m * H)
  have hyn := hy0 (s - n * H)
  rcases le_total (k * H / 2) |s - m * H| with h | h
  · have : y (s - m * H) ≤ A * exp (-(a * k * H / 2)) := by
      refine (hyA _).trans ?_
      have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((hy0 0).trans (hyA 0)) (exp_pos _)
      refine mul_le_mul_of_nonneg_left ?_ hA
      rw [Real.exp_le_exp]; nlinarith
    nlinarith
  · have h' : k * H / 2 ≤ |s - n * H| := by linarith
    have : y (s - n * H) ≤ A * exp (-(a * k * H / 2)) := by
      refine (hyA _).trans ?_
      have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((hy0 0).trans (hyA 0)) (exp_pos _)
      refine mul_le_mul_of_nonneg_left ?_ hA
      rw [Real.exp_le_exp]; nlinarith
    nlinarith

/-- **Lemma 4.1, overlap estimate (4.2).**  Let `y ≥ 0` be a pulse with exponential decay
`y(t) ≤ A e^{-a|t|}`, and let `u, v` satisfy the relative bounds `|u|, |v| ≤ D y` (in the
paper, `u = y^{(j)}`, `v = y^{(k)}`, using the relative derivative bounds of Lemma 3.5).
Then there are `C`, `β > 0` and `H₀` such that for every `H ≥ H₀` and every `s`, the cross
terms of the periodization are summable and
`∑_{m ≠ n} |u(s - mH)| |v(s - nH)| ≤ C e^{-βH} Y_H(s)`. -/
theorem overlap_estimate {u v : ℝ → ℝ} {D : ℝ} (hy0 : ∀ t, 0 ≤ y t)
    (hyA : ∀ t, y t ≤ A * exp (-(a * |t|))) (ha : 0 < a)
    (hu : ∀ t, |u t| ≤ D * y t) (hv : ∀ t, |v t| ≤ D * y t) :
    ∃ C β H₀ : ℝ, 0 < β ∧ ∀ H ≥ H₀, ∀ s : ℝ,
      Summable (fun p : ℤ × ℤ =>
        if p.1 ≠ p.2 then |u (s - p.1 * H)| * |v (s - p.2 * H)| else 0) ∧
      ∑' p : ℤ × ℤ, (if p.1 ≠ p.2 then |u (s - p.1 * H)| * |v (s - p.2 * H)| else 0) ≤
        C * exp (-(β * H)) * periodize y H s := by
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((hy0 0).trans (hyA 0)) (exp_pos _)
  refine ⟨16 * D ^ 2 * A, a / 2, 2 / a, by positivity, fun H hH s => ?_⟩
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  set q : ℝ := exp (-(a * H / 2)) with hq
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q ≤ 1 / 2 := by
    have h1 : 1 ≤ a * H / 2 := by
      rw [ge_iff_le, div_le_iff₀ ha] at hH; linarith
    have h2 : (2 : ℝ) ≤ exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have : q ≤ exp (-1) := by rw [hq, Real.exp_le_exp]; linarith
    rw [Real.exp_neg] at this
    refine this.trans ?_
    rw [inv_le_comm₀ (exp_pos _) (by norm_num)]; linarith
  set Y : ℤ → ℝ := fun m => y (s - m * H) with hYdef
  have hY : Summable Y := summable_periodize hy0 hyA ha hH0 s
  have hY0 : ∀ m, 0 ≤ Y m := fun m => hy0 _
  set h : ℤ → ℝ := fun ℓ => if ℓ = 0 then 0 else q ^ ℓ.natAbs with hhdef
  have hh0 : ∀ ℓ, 0 ≤ h ℓ := fun ℓ => by
    simp only [hhdef]; split_ifs <;> positivity
  have hhsymm : ∀ ℓ, h (-ℓ) = h ℓ := fun ℓ => by simp [hhdef, Int.natAbs_neg]
  have hhle : ∀ ℓ, h ℓ ≤ 2 * q * (1 / 2 : ℝ) ^ ℓ.natAbs := fun ℓ => by
    simp only [hhdef]
    split_ifs with hl
    · positivity
    · obtain ⟨k, hk⟩ : ∃ k, ℓ.natAbs = k + 1 := ⟨ℓ.natAbs - 1, by omega⟩
      rw [hk, pow_succ, pow_succ]
      have : q ^ k ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_left₀ hq0 hq1 k
      nlinarith [pow_nonneg hq0 k]
  obtain ⟨hgs, hgle⟩ := summable_geom_natAbs (r := 1 / 2) (by norm_num) (by norm_num)
  have hhs : Summable h :=
    Summable.of_nonneg_of_le hh0 hhle (hgs.mul_left _)
  have hhsum : ∑' ℓ, h ℓ ≤ 8 * q := by
    have := (hhs.tsum_le_tsum hhle (hgs.mul_left _))
    rw [tsum_mul_left] at this
    have h4 : ∑' ℓ : ℤ, (1 / 2 : ℝ) ^ ℓ.natAbs ≤ 4 := by
      refine hgle.trans (le_of_eq ?_); norm_num
    nlinarith
  -- the comparison series
  set S1 : ℤ × ℤ → ℝ := fun p => h (p.1 - p.2) * Y p.1 with hS1
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.1, p.1 - p.2), invFun := fun p => (p.1, p.1 - p.2),
      left_inv := fun p => by simp, right_inv := fun p => by simp }
  have hS1e : ∀ c, S1 (e c) = Y c.1 * h c.2 := fun c => by
    simp [hS1, e, mul_comm]
  have hprod : Summable (fun c : ℤ × ℤ => Y c.1 * h c.2) :=
    Summable.mul_of_nonneg hY hhs (fun m => hY0 m) (fun ℓ => hh0 ℓ)
  have hS1s : Summable S1 := by
    rw [← e.summable_iff]; exact hprod.congr fun c => (hS1e c).symm
  have hS1t : ∑' p, S1 p = (∑' m, Y m) * ∑' ℓ, h ℓ := by
    rw [← e.tsum_eq, tsum_mul_tsum_of_summable_norm (by simpa [Real.norm_eq_abs] using hY.abs)
      (by simpa [Real.norm_eq_abs] using hhs.abs)]
    exact tsum_congr hS1e
  set S2 : ℤ × ℤ → ℝ := fun p => S1 (Equiv.prodComm ℤ ℤ p) with hS2
  have hS2s : Summable S2 := (Equiv.prodComm ℤ ℤ).summable_iff.2 hS1s
  have hS2t : ∑' p, S2 p = ∑' p, S1 p := (Equiv.prodComm ℤ ℤ).tsum_eq S1
  set c : ℝ := D ^ 2 * A with hc
  have hc0 : 0 ≤ c := by positivity
  set R : ℤ × ℤ → ℝ := fun p => c * S1 p + c * S2 p with hR
  have hRs : Summable R := (hS1s.mul_left c).add (hS2s.mul_left c)
  set T : ℤ × ℤ → ℝ := fun p =>
    if p.1 ≠ p.2 then |u (s - p.1 * H)| * |v (s - p.2 * H)| else 0 with hT
  have hT0 : ∀ p, 0 ≤ T p := fun p => by simp only [hT]; split_ifs <;> positivity
  have hTR : ∀ p, T p ≤ R p := fun p => by
    obtain ⟨m, n⟩ := p
    simp only [hT, hR, hS1, hS2, Equiv.prodComm_apply, Prod.swap]
    split_ifs with hmn
    · have hmn' : m - n ≠ 0 := sub_ne_zero.2 hmn
      have hnm' : n - m ≠ 0 := sub_ne_zero.2 (Ne.symm hmn)
      have hsym : h (n - m) = h (m - n) := by
        rw [← hhsymm, neg_sub]
      rw [hsym]
      simp only [hhdef, if_neg hmn']
      have h1 := pulse_pair_le hy0 hyA ha hH0 s m n
      have hu' : |u (s - m * H)| ≤ |D| * Y m := (hu _).trans
        (mul_le_mul_of_nonneg_right (le_abs_self D) (hY0 m))
      have hv' : |v (s - n * H)| ≤ |D| * Y n := (hv _).trans
        (mul_le_mul_of_nonneg_right (le_abs_self D) (hY0 n))
      have h2 : |u (s - m * H)| * |v (s - n * H)| ≤ (|D| * Y m) * (|D| * Y n) :=
        mul_le_mul hu' hv' (abs_nonneg _) (mul_nonneg (abs_nonneg D) (hY0 m))
      have h3 : (|D| * Y m) * (|D| * Y n) = D ^ 2 * (Y m * Y n) := by
        rw [← sq_abs D]; ring
      rw [h3] at h2
      have h4 : D ^ 2 * (Y m * Y n) ≤
          D ^ 2 * (A * q ^ (m - n).natAbs * (Y m + Y n)) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg D)
      simp only [hc]
      nlinarith
    · have hmn' : m - n = 0 := by simp at hmn; omega
      simp only [hmn', hhdef, if_true, show n - m = 0 by omega]
      simp
  have hTs : Summable T := Summable.of_nonneg_of_le hT0 hTR hRs
  refine ⟨hTs, ?_⟩
  calc ∑' p, T p ≤ ∑' p, R p := hTs.tsum_le_tsum hTR hRs
    _ = 2 * c * ((∑' m, Y m) * ∑' ℓ, h ℓ) := by
        rw [hR, (hS1s.mul_left c).tsum_add (hS2s.mul_left c), tsum_mul_left, tsum_mul_left,
          hS2t, hS1t]; ring
    _ ≤ 2 * c * ((∑' m, Y m) * (8 * q)) := by
        gcongr
        exact tsum_nonneg hY0
    _ = 16 * D ^ 2 * A * exp (-(a / 2 * H)) * periodize y H s := by
        simp only [periodize, hc, hq, hYdef]
        rw [show -(a / 2 * H) = -(a * H / 2) by ring]; ring

end

end Ovals

end
