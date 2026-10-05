module

public import UnitTangentIterates.Periodization

/-!
# Periodization estimates (Lemma 4.1, estimate (4.1), with `q = 0`)

For a pulse `y` with `|y(t)| ≤ A e^{-a|t|}`:

* the periodization `Y_H(s) = ∑_m y(s - mH)` converges for every `s`;
* on the centered cell `|s| ≤ H/2`, `|Y_H(s) - y(s)| ≤ C e^{-βH}`;
* if `y` is differentiable with exponentially decaying derivative, then `Y_H` is
  differentiable and may be differentiated termwise; iterating, the same holds for every
  derivative of a smooth pulse all of whose derivatives decay exponentially, which gives
  the `C^r(I_H)` estimate (4.1) (for `q = 0`).
-/

@[expose] public section

namespace Ovals

open Real

section

variable {y : ℝ → ℝ} {A a : ℝ}

/-- The geometric series over `ℤ \ {0}`: for `0 ≤ q ≤ 1/2`,
`∑_{ℓ ≠ 0} q^{|ℓ|} ≤ 8 q`. -/
lemma summable_offzero_geom {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    Summable (fun ℓ : ℤ => if ℓ = 0 then 0 else q ^ ℓ.natAbs) ∧
      ∑' ℓ : ℤ, (if ℓ = 0 then 0 else q ^ ℓ.natAbs) ≤ 8 * q := by
  set h : ℤ → ℝ := fun ℓ => if ℓ = 0 then 0 else q ^ ℓ.natAbs with hhdef
  have hh0 : ∀ ℓ, 0 ≤ h ℓ := fun ℓ => by
    simp only [hhdef]; split_ifs <;> positivity
  have hhle : ∀ ℓ, h ℓ ≤ 2 * q * (1 / 2 : ℝ) ^ ℓ.natAbs := fun ℓ => by
    simp only [hhdef]
    split_ifs with hl
    · positivity
    · obtain ⟨k, hk⟩ : ∃ k, ℓ.natAbs = k + 1 := ⟨ℓ.natAbs - 1, by omega⟩
      rw [hk, pow_succ, pow_succ]
      have : q ^ k ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_left₀ hq0 hq1 k
      nlinarith [pow_nonneg hq0 k]
  obtain ⟨hgs, hgle⟩ := summable_geom_natAbs (r := 1 / 2) (by norm_num) (by norm_num)
  have hhs : Summable h := Summable.of_nonneg_of_le hh0 hhle (hgs.mul_left _)
  refine ⟨hhs, ?_⟩
  have := (hhs.tsum_le_tsum hhle (hgs.mul_left _))
  rw [tsum_mul_left] at this
  have h4 : ∑' ℓ : ℤ, (1 / 2 : ℝ) ^ ℓ.natAbs ≤ 4 := by
    refine hgle.trans (le_of_eq ?_); norm_num
  nlinarith

/-- For `H ≥ 2/a`, `e^{-aH/2} ≤ 1/2`. -/
lemma exp_neg_half_le (ha : 0 < a) {H : ℝ} (hH : 2 / a ≤ H) : exp (-(a * H / 2)) ≤ 1 / 2 := by
  have h1 : 1 ≤ a * H / 2 := by
    rw [div_le_iff₀ ha] at hH; linarith
  have h2 : (2 : ℝ) ≤ exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have : exp (-(a * H / 2)) ≤ exp (-1) := by rw [Real.exp_le_exp]; linarith
  refine this.trans ?_
  rw [Real.exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]; linarith

/-- The periodization of a (signed) exponentially decaying pulse converges absolutely. -/
theorem summable_periodize_abs (hyA : ∀ t, |y t| ≤ A * exp (-(a * |t|))) (ha : 0 < a) {H : ℝ}
    (hH : 0 < H) (s : ℝ) : Summable (fun m : ℤ => y (s - m * H)) := by
  have hs := summable_periodize (y := fun t => |y t|) (fun t => abs_nonneg _) hyA ha hH s
  exact Summable.of_norm (by simpa [Real.norm_eq_abs] using hs)

/-- A shifted copy far from the cell is small: for `|s| ≤ H/2` and `m ≠ 0`,
`|y(s - mH)| ≤ A (e^{-aH/2})^{|m|}`. -/
lemma pulse_shift_cell_le (hyA : ∀ t, |y t| ≤ A * exp (-(a * |t|))) (ha : 0 < a) {H : ℝ}
    (hH : 0 < H) {s : ℝ} (hs : |s| ≤ H / 2) {m : ℤ} (hm : m ≠ 0) :
    |y (s - m * H)| ≤ A * exp (-(a * H / 2)) ^ m.natAbs := by
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hyA 0)) (exp_pos _)
  refine (hyA _).trans (mul_le_mul_of_nonneg_left ?_ hA)
  rw [← Real.exp_nat_mul, Real.exp_le_exp]
  have hmabs : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hmabs]
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm
  have : |(m : ℝ)| * H - |s| ≤ |s - m * H| := by
    have := abs_sub_abs_le_abs_sub (m * H : ℝ) s
    rw [abs_mul, abs_of_pos hH, abs_sub_comm] at this
    linarith
  have h2 : |(m : ℝ)| * H / 2 ≤ |s - m * H| := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 ha.le]

/-- Explicit form of the cell estimate: for `H ≥ 2/a` and `|s| ≤ H/2`,
`|Y_H(s) - y(s)| ≤ 8 A e^{-aH/2}`. -/
theorem periodize_sub_le_explicit (hyA : ∀ t, |y t| ≤ A * exp (-(a * |t|))) (ha : 0 < a)
    {H : ℝ} (hH : 2 / a ≤ H) {s : ℝ} (hs : |s| ≤ H / 2) :
    |periodize y H s - y s| ≤ 8 * A * exp (-(a / 2 * H)) := by
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  set q : ℝ := exp (-(a * H / 2)) with hq
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q ≤ 1 / 2 := exp_neg_half_le ha hH
  have hsum := summable_periodize_abs hyA ha hH0 s
  obtain ⟨hgs, hgle⟩ := summable_offzero_geom hq0 hq1
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hyA 0)) (exp_pos _)
  have key : periodize y H s - y s =
      ∑' m : ℤ, (if m = 0 then 0 else y (s - m * H)) := by
    unfold periodize
    rw [hsum.tsum_eq_add_tsum_ite 0]
    simp
  have hb : ∀ m : ℤ, ‖(if m = 0 then 0 else y (s - m * H))‖ ≤
      A * (if m = 0 then 0 else q ^ m.natAbs) := fun m => by
    split_ifs with hm
    · simp
    · rw [Real.norm_eq_abs]; exact pulse_shift_cell_le hyA ha hH0 hs hm
  rw [key, ← Real.norm_eq_abs]
  refine (tsum_of_norm_bounded (hgs.mul_left A).hasSum hb).trans ?_
  rw [show -(a / 2 * H) = -(a * H / 2) by ring, ← hq, tsum_mul_left]
  nlinarith

/-- **Lemma 4.1, estimate (4.1), `r = q = 0`.**  On the centered cell `I_H = [-H/2, H/2]`,
the periodization is exponentially close to the pulse. -/
theorem periodize_sub_le (hyA : ∀ t, |y t| ≤ A * exp (-(a * |t|))) (ha : 0 < a) :
    ∃ C β H₀ : ℝ, 0 < β ∧ ∀ H ≥ H₀, ∀ s : ℝ, |s| ≤ H / 2 →
      |periodize y H s - y s| ≤ C * exp (-(β * H)) :=
  ⟨8 * A, a / 2, 2 / a, by positivity, fun _ hH _ hs => periodize_sub_le_explicit hyA ha hH hs⟩

/-- The periodization is `H`-periodic (shift by an integer number of periods). -/
theorem periodize_sub_int_mul (y : ℝ → ℝ) (H s : ℝ) (k : ℤ) :
    periodize y H (s - k * H) = periodize y H s := by
  unfold periodize
  rw [← (Equiv.addRight k).tsum_eq (fun n : ℤ => y (s - n * H))]
  congr 1; ext m
  simp only [Equiv.coe_addRight, Int.cast_add]
  ring_nf

/-- Every point is an integer number of periods away from the centered cell. -/
theorem exists_int_cell {H : ℝ} (hH : 0 < H) (s : ℝ) : ∃ k : ℤ, |s - k * H| ≤ H / 2 := by
  refine ⟨round (s / H), ?_⟩
  have h := abs_sub_round (s / H)
  have : s - (round (s / H) : ℝ) * H = (s / H - round (s / H)) * H := by
    field_simp
  rw [this, abs_mul, abs_of_pos hH]
  nlinarith

/-- A uniform upper bound for the periodization: if `y ≤ b` then
`Y_H ≤ b + 8 A e^{-aH/2}` for `H ≥ 2/a`. -/
theorem periodize_le (hyA : ∀ t, |y t| ≤ A * exp (-(a * |t|))) (ha : 0 < a) {b : ℝ}
    (hyb : ∀ t, y t ≤ b) {H : ℝ} (hH : 2 / a ≤ H) (s : ℝ) :
    periodize y H s ≤ b + 8 * A * exp (-(a / 2 * H)) := by
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  obtain ⟨k, hk⟩ := exists_int_cell hH0 s
  rw [← periodize_sub_int_mul y H s k]
  have := periodize_sub_le_explicit hyA ha hH hk
  have := hyb (s - k * H)
  have := le_abs_self (periodize y H (s - k * H) - y (s - k * H))
  linarith

/-- Termwise differentiation of the periodization. -/
theorem hasDerivAt_periodize {y' : ℝ → ℝ} {A' : ℝ} (hy : ∀ t, HasDerivAt y (y' t) t)
    (hyA : ∀ t, |y t| ≤ A * exp (-(a * |t|))) (hyA' : ∀ t, |y' t| ≤ A' * exp (-(a * |t|)))
    (ha : 0 < a) {H : ℝ} (hH : 0 < H) (s : ℝ) :
    HasDerivAt (periodize y H) (periodize y' H s) s := by
  have hA' : 0 ≤ A' := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hyA' 0)) (exp_pos _)
  have hr1 : exp (-(a * H)) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
  have hu := ((summable_geom_natAbs (exp_pos _).le hr1).1).mul_left
    (A' * exp (a * (|s| + 1)))
  have hderiv : ∀ m : ℤ, ∀ z, HasDerivAt (fun x => y (x - m * H)) (y' (z - m * H)) z :=
    fun m z => by simpa using (hy (z - m * H)).comp z ((hasDerivAt_id z).sub_const (m * H))
  have := hasDerivAt_tsum_of_isPreconnected (t := Metric.ball s 1) (y₀ := s) (y := s)
    (g := fun (m : ℤ) x => y (x - m * H)) (g' := fun (m : ℤ) x => y' (x - m * H)) hu
    Metric.isOpen_ball (convex_ball s 1).isPreconnected (fun m z _ => hderiv m z)
    (fun m z hz => ?_) (Metric.mem_ball_self one_pos) (summable_periodize_abs hyA ha hH s)
    (Metric.mem_ball_self one_pos)
  · exact this
  · rw [Real.norm_eq_abs]
    refine (pulse_shift_le (y := fun t => |y' t|) hyA' hA' ha hH z m).trans ?_
    have hz' : |z| ≤ |s| + 1 := by
      have := abs_sub_abs_le_abs_sub z s
      rw [Metric.mem_ball, Real.dist_eq] at hz
      linarith
    gcongr

/-- The derivative of the periodization is the periodization of the derivative. -/
theorem deriv_periodize {y' : ℝ → ℝ} {A' : ℝ} (hy : ∀ t, HasDerivAt y (y' t) t)
    (hyA : ∀ t, |y t| ≤ A * exp (-(a * |t|))) (hyA' : ∀ t, |y' t| ≤ A' * exp (-(a * |t|)))
    (ha : 0 < a) {H : ℝ} (hH : 0 < H) :
    deriv (periodize y H) = periodize y' H :=
  funext fun s => (hasDerivAt_periodize hy hyA hyA' ha hH s).deriv

/-- Iterated termwise differentiation for a smooth pulse all of whose derivatives decay
exponentially at a common rate. -/
theorem iteratedDeriv_periodize (hyC : ContDiff ℝ ⊤ y) {Cj : ℕ → ℝ}
    (hyj : ∀ j t, |iteratedDeriv j y t| ≤ Cj j * exp (-(a * |t|))) (ha : 0 < a) {H : ℝ}
    (hH : 0 < H) (r : ℕ) :
    iteratedDeriv r (periodize y H) = periodize (iteratedDeriv r y) H := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    refine deriv_periodize (A := Cj r) (A' := Cj (r + 1)) (fun t => ?_) (hyj r) ?_ ha hH
    · have hd : Differentiable ℝ (iteratedDeriv r y) :=
        hyC.differentiable_iteratedDeriv r (by exact_mod_cast WithTop.coe_lt_top _)
      exact (hd t).hasDerivAt
    · intro t; rw [← iteratedDeriv_succ]; exact hyj (r + 1) t

/-- **Lemma 4.1, estimate (4.1), `q = 0`, every `r`.**  For a smooth pulse whose
derivatives all decay exponentially, every derivative of `Y_H - y` is exponentially small on
the centered cell `I_H = [-H/2, H/2]`. -/
theorem periodize_iteratedDeriv_sub_le (hyC : ContDiff ℝ ⊤ y) {Cj : ℕ → ℝ}
    (hyj : ∀ j t, |iteratedDeriv j y t| ≤ Cj j * exp (-(a * |t|))) (ha : 0 < a) (r : ℕ) :
    ∃ C β H₀ : ℝ, 0 < β ∧ ∀ H ≥ H₀, ∀ s : ℝ, |s| ≤ H / 2 →
      |iteratedDeriv r (periodize y H) s - iteratedDeriv r y s| ≤ C * exp (-(β * H)) := by
  obtain ⟨C, β, H₀, hβ, hC⟩ := periodize_sub_le (hyj r) ha
  refine ⟨C, β, max H₀ 1, hβ, fun H hH s hs => ?_⟩
  have hH0 : 0 < H := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hH)
  rw [iteratedDeriv_periodize hyC hyj ha hH0 r]
  exact hC H ((le_max_left _ _).trans hH) s hs

end

end Ovals

end
