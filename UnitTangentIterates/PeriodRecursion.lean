module

public import Mathlib

/-!
# The period recursion of Section 7

Section 7 uses the half-perimeter function `P(H)` of the rear `R_H` (Proposition 4.3), which
satisfies, for large `H`, `Δ/2 ≤ H - P(H) ≤ 3Δ/2` and is increasing.  From this it builds the
backward sequence of periods

`P(H_{n+1}) = H_n,   H_n ≥ H_0 + (Δ/2) n`        (7.1)

and shows that the total defect `r_0 ≤ C ∑_n (1 + H_n)² e^{-β H_{n+1}}` is exponentially small
in `H_0` (7.2).  Both facts are elementary and are proved here for an abstract `P`.
-/

@[expose] public section

namespace Ovals

open Real Set

section Recursion

variable {P : ℝ → ℝ} {H₁ Δ : ℝ}

/-- Every value `h ≥ H₁` is attained by `P` at some point `≥ H₁`. -/
lemma exists_preimage_of_shift (hPc : ContinuousOn P (Ici H₁)) (hΔ : 0 < Δ)
    (hP : ∀ H ≥ H₁, Δ / 2 ≤ H - P H ∧ H - P H ≤ 3 * Δ / 2) {h : ℝ} (hh : H₁ ≤ h) :
    ∃ H ≥ H₁, P H = h := by
  have hle : H₁ ≤ h + 3 * Δ / 2 := by linarith
  have h1 : P H₁ ≤ h := by linarith [(hP H₁ le_rfl).1]
  have h2 : h ≤ P (h + 3 * Δ / 2) := by linarith [(hP (h + 3 * Δ / 2) hle).2]
  obtain ⟨H, hH, hPH⟩ := intermediate_value_Icc hle (hPc.mono Icc_subset_Ici_self) ⟨h1, h2⟩
  exact ⟨H, hH.1, hPH⟩

/-- **The period recursion (7.1).**  Let `P` be continuous and strictly increasing on
`[H₁, ∞)`, with `Δ/2 ≤ H - P(H) ≤ 3Δ/2` there (`Δ > 0`).  Then every `H₀ ≥ H₁` determines a
unique sequence `H_n ≥ H₁` with `H_0 = H₀` and `P(H_{n+1}) = H_n`; it satisfies
`H_n ≥ H₀ + (Δ/2) n`. -/
theorem period_recursion (hPc : ContinuousOn P (Ici H₁)) (hPm : StrictMonoOn P (Ici H₁))
    (hΔ : 0 < Δ) (hP : ∀ H ≥ H₁, Δ / 2 ≤ H - P H ∧ H - P H ≤ 3 * Δ / 2) {H₀ : ℝ}
    (hH₀ : H₁ ≤ H₀) :
    ∃! Hs : ℕ → ℝ, Hs 0 = H₀ ∧ (∀ n, H₁ ≤ Hs n) ∧ ∀ n, P (Hs (n + 1)) = Hs n ∧
      H₀ + Δ / 2 * n ≤ Hs n := by
  classical
  -- a right inverse of `P` on `[H₁, ∞)`
  let f : ℝ → ℝ := fun h =>
    if hh : H₁ ≤ h then Classical.choose (exists_preimage_of_shift hPc hΔ hP hh) else h
  have hf : ∀ h, H₁ ≤ h → H₁ ≤ f h ∧ P (f h) = h := fun h hh => by
    simp only [f, dif_pos hh]
    exact Classical.choose_spec (exists_preimage_of_shift hPc hΔ hP hh)
  let Hs : ℕ → ℝ := fun n => f^[n] H₀
  have hge : ∀ n, H₁ ≤ Hs n := by
    intro n; induction n with
    | zero => simpa [Hs] using hH₀
    | succ n ih =>
      simp only [Hs, Function.iterate_succ_apply']
      exact (hf _ ih).1
  have hrec : ∀ n, P (Hs (n + 1)) = Hs n := fun n => by
    simp only [Hs, Function.iterate_succ_apply']
    exact (hf _ (hge n)).2
  refine ⟨Hs, ⟨rfl, hge, fun n => ⟨hrec n, ?_⟩⟩, ?_⟩
  · induction n with
    | zero => simp [Hs]
    | succ n ih =>
      have := (hP _ (hge (n + 1))).1
      rw [hrec n] at this
      push_cast
      linarith
  · rintro G ⟨hG0, hGge, hG⟩
    funext n
    induction n with
    | zero => rw [hG0]; rfl
    | succ n ih =>
      apply hPm.injOn (hGge (n + 1)) (hge (n + 1))
      rw [(hG n).1, hrec n, ih]

end Recursion

/-- `(1 + x)² e^{-c x} ≤ 4 e^c / c²` for `x ≥ 0` and `c > 0`. -/
lemma one_add_sq_mul_exp_le {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    (1 + x) ^ 2 * exp (-(c * x)) ≤ 4 * exp c / c ^ 2 := by
  have h1 : c * (1 + x) / 2 ≤ exp (c * (1 + x) / 2) := by
    linarith [Real.add_one_le_exp (c * (1 + x) / 2)]
  have h2 : (c * (1 + x) / 2) ^ 2 ≤ exp (c * (1 + x)) := by
    have := pow_le_pow_left₀ (by positivity) h1 2
    rw [← Real.exp_nat_mul] at this
    calc _ ≤ _ := this
      _ = exp (c * (1 + x)) := by congr 1; push_cast; ring
  rw [le_div_iff₀ (by positivity)]
  have h3 : exp (c * (1 + x)) * exp (-(c * x)) = exp c := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : 0 < exp (-(c * x)) := exp_pos _
  nlinarith

/-- **The tail estimate (7.2).**  If `H_n ≥ H₀ + (Δ/2) n` with `H₀ ≥ 0` and the sequence is
nondecreasing, then the defect series `∑_n C (1 + H_n)² e^{-β H_{n+1}}` converges and is
bounded by `C' e^{-β' H₀}` with `C'`, `β' > 0` depending only on `C`, `β`, `Δ`. -/
theorem defect_tail_le {β Δ C : ℝ} (hβ : 0 < β) (hΔ : 0 < Δ) (hC : 0 ≤ C) :
    ∃ C' β' : ℝ, 0 < β' ∧ ∀ (H₀ : ℝ) (Hs : ℕ → ℝ), 0 ≤ H₀ →
      (∀ n, H₀ + Δ / 2 * n ≤ Hs n) → (∀ n, Hs n ≤ Hs (n + 1)) →
      Summable (fun n => C * (1 + Hs n) ^ 2 * exp (-(β * Hs (n + 1)))) ∧
      ∑' n, C * (1 + Hs n) ^ 2 * exp (-(β * Hs (n + 1))) ≤ C' * exp (-(β' * H₀)) := by
  set c : ℝ := β / 2 with hcdef
  have hc : 0 < c := by positivity
  set M : ℝ := 4 * exp c / c ^ 2 with hM
  set r : ℝ := exp (-(c * (Δ / 2))) with hr
  have hr0 : 0 ≤ r := (exp_pos _).le
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; nlinarith
  refine ⟨C * M / (1 - r), c, hc, fun H₀ Hs hH₀ hlow hmono => ?_⟩
  have hHs0 : ∀ n, 0 ≤ Hs n := fun n => by
    have := hlow n; have : (0 : ℝ) ≤ Δ / 2 * n := by positivity
    linarith
  have hterm : ∀ n, C * (1 + Hs n) ^ 2 * exp (-(β * Hs (n + 1))) ≤
      (C * M * exp (-(c * H₀))) * r ^ n := fun n => by
    have h1 : exp (-(β * Hs (n + 1))) ≤ exp (-(c * Hs n)) * exp (-(c * Hs n)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have := hmono n
      rw [hcdef]; nlinarith
    have h2 : (1 + Hs n) ^ 2 * exp (-(c * Hs n)) ≤ M := one_add_sq_mul_exp_le hc (hHs0 n)
    have h3 : exp (-(c * Hs n)) ≤ exp (-(c * H₀)) * r ^ n := by
      rw [hr, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
      have := hlow n
      nlinarith
    calc C * (1 + Hs n) ^ 2 * exp (-(β * Hs (n + 1)))
        ≤ C * (1 + Hs n) ^ 2 * (exp (-(c * Hs n)) * exp (-(c * Hs n))) := by gcongr
      _ = C * ((1 + Hs n) ^ 2 * exp (-(c * Hs n))) * exp (-(c * Hs n)) := by ring
      _ ≤ C * M * (exp (-(c * H₀)) * r ^ n) := by
          gcongr
      _ = _ := by ring
  have hgs : Summable (fun n : ℕ => (C * M * exp (-(c * H₀))) * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hnn : ∀ n, 0 ≤ C * (1 + Hs n) ^ 2 * exp (-(β * Hs (n + 1))) := fun n => by positivity
  have hs := Summable.of_nonneg_of_le hnn hterm hgs
  refine ⟨hs, ?_⟩
  calc ∑' n, C * (1 + Hs n) ^ 2 * exp (-(β * Hs (n + 1)))
      ≤ ∑' n : ℕ, (C * M * exp (-(c * H₀))) * r ^ n := hs.tsum_le_tsum hterm hgs
    _ = C * M / (1 - r) * exp (-(c * H₀)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]; ring

end Ovals

end
