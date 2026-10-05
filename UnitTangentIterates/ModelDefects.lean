module

public import UnitTangentIterates.Matching
public import UnitTangentIterates.PeriodSequence

/-!
# The total model defect is exponentially small (estimate (7.2))

Along the period sequence `P(H_{n+1}) = H_n` of Section 7, the defects of Theorem 6.4,

`e_n = (1 + H_n)² ‖k_{H_{n+1}} - K_{H_n}‖_{L¹(ℝ/H_nℤ)}`,

(comparing the curvature of the closed rear `R_{H_{n+1}}` with that of the closed front
`F_{H_n}`, which have the same half-perimeter `H_n`) form a convergent series with
`r₀ = ∑ e_n ≤ C e^{-β H₀}`.
-/

@[expose] public section

namespace Ovals

open Real MeasureTheory

variable {y y' y'' : ℝ → ℝ} {A a D b : ℝ}

/-- **Estimate (7.2) for the closed models.**  For all sufficiently large `H₀` there is a
period sequence `H_n` (`P(H_{n+1}) = H_n`, `H_n ≥ H₀ + (Δ/2) n`) such that, for every choice of
rear curvature functions `k_n` of `R_{H_{n+1}}` (in rear arclength), the defects
`e_n = (1 + H_n)² ∫_{J_n} |k_n - K_{H_n}|` are summable with `∑ e_n ≤ C e^{-β H₀}`. -/
theorem model_defects_small (hy : ∀ t, HasDerivAt y (y' t) t)
    (hy' : ∀ t, HasDerivAt y' (y'' t) t) (hy0 : ∀ t, 0 ≤ y t)
    (hyA : ∀ t, y t ≤ A * exp (-(a * |t|))) (ha : 0 < a)
    (hyD : ∀ t, |y' t| ≤ D * y t) (hyD2 : ∀ t, |y'' t| ≤ D * y t)
    (hyb : ∀ t, y t ≤ b) (hb : b < 1) (x₀ : ℝ)
    (hKx : ∀ s, frontCurv y (x₀ + ∫ r in (0 : ℝ)..s, √(1 - y r ^ 2)) =
      y s / √(1 - y s ^ 2)) {t₀ : ℝ} (ht₀ : 0 < y t₀) :
    ∃ C β H₁ : ℝ, 0 < β ∧ ∀ H₀ ≥ H₁, ∃ Hs : ℕ → ℝ, Hs 0 = H₀ ∧
      (∀ n, halfPerimeter y (Hs (n + 1)) = Hs n ∧ H₀ + steeringDefect y / 2 * n ≤ Hs n) ∧
      ∀ k : ℕ → ℝ → ℝ, (∀ n, Continuous (k n) ∧
          ∀ s, k n (x₀ + ∫ r in (0 : ℝ)..s, √(1 - periodize y (Hs (n + 1)) r ^ 2)) =
            periodize y (Hs (n + 1)) s / √(1 - periodize y (Hs (n + 1)) s ^ 2)) →
        Summable (fun n => (1 + Hs n) ^ 2 *
          ∫ u in (x₀ + ∫ r in (0 : ℝ)..(-Hs (n + 1) / 2),
              √(1 - periodize y (Hs (n + 1)) r ^ 2))..
            (x₀ + ∫ r in (0 : ℝ)..(Hs (n + 1) / 2), √(1 - periodize y (Hs (n + 1)) r ^ 2)),
            |k n u - frontCurv (periodize y (Hs n)) u|) ∧
        ∑' n, (1 + Hs n) ^ 2 *
          ∫ u in (x₀ + ∫ r in (0 : ℝ)..(-Hs (n + 1) / 2),
              √(1 - periodize y (Hs (n + 1)) r ^ 2))..
            (x₀ + ∫ r in (0 : ℝ)..(Hs (n + 1) / 2), √(1 - periodize y (Hs (n + 1)) r ^ 2)),
            |k n u - frontCurv (periodize y (Hs n)) u| ≤ C * exp (-(β * H₀)) := by
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy t).continuousAt
  obtain ⟨C, β, H₂, hβ, hmatch⟩ :=
    curvature_matching hy hy' hy0 hyA ha hyD hyD2 hyb hb x₀ hKx
  obtain ⟨hΔ, H₃, hH₃, hseq⟩ := period_sequence_exists hyc hy0 hyA ha hyb hb ht₀
  obtain ⟨C', β', hβ', htail⟩ := defect_tail_le hβ hΔ (abs_nonneg C)
  refine ⟨C', β', max H₂ H₃, hβ', fun H₀ hH₀ => ?_⟩
  obtain ⟨Hs, h0, hHs⟩ := hseq H₀ ((le_max_right _ _).trans hH₀)
  have hH₀0 : 0 ≤ H₀ := hH₃.le.trans ((le_max_right _ _).trans hH₀)
  have hlow : ∀ n, H₀ + steeringDefect y / 2 * n ≤ Hs n := fun n => (hHs n).2.2.1
  have hmono : ∀ n, Hs n ≤ Hs (n + 1) := fun n => by linarith [(hHs n).2.2.2]
  have hge : ∀ n, H₂ ≤ Hs n := fun n => by
    have : (0 : ℝ) ≤ steeringDefect y / 2 * n := by positivity
    linarith [hlow n, le_max_left H₂ H₃]
  refine ⟨Hs, h0, fun n => ⟨(hHs n).2.1, hlow n⟩, fun k hk => ?_⟩
  obtain ⟨hsum, hle⟩ := htail H₀ Hs hH₀0 hlow hmono
  have hterm : ∀ n, 0 ≤ (1 + Hs n) ^ 2 *
      ∫ u in (x₀ + ∫ r in (0 : ℝ)..(-Hs (n + 1) / 2),
          √(1 - periodize y (Hs (n + 1)) r ^ 2))..
        (x₀ + ∫ r in (0 : ℝ)..(Hs (n + 1) / 2), √(1 - periodize y (Hs (n + 1)) r ^ 2)),
        |k n u - frontCurv (periodize y (Hs n)) u| ∧
      (1 + Hs n) ^ 2 *
      ∫ u in (x₀ + ∫ r in (0 : ℝ)..(-Hs (n + 1) / 2),
          √(1 - periodize y (Hs (n + 1)) r ^ 2))..
        (x₀ + ∫ r in (0 : ℝ)..(Hs (n + 1) / 2), √(1 - periodize y (Hs (n + 1)) r ^ 2)),
        |k n u - frontCurv (periodize y (Hs n)) u| ≤
        |C| * (1 + Hs n) ^ 2 * exp (-(β * Hs (n + 1))) := fun n => by
    obtain ⟨hlen, hbd⟩ := hmatch (Hs (n + 1)) (hge (n + 1))
    have hP := (hHs n).2.1
    rw [hP] at hlen hbd
    have hb' := hbd (k n) (hk n).1 (hk n).2
    have hpos : 0 ≤ Hs n := le_trans (by positivity) (hlow n)
    have hint0 : 0 ≤ ∫ u in (x₀ + ∫ r in (0 : ℝ)..(-Hs (n + 1) / 2),
          √(1 - periodize y (Hs (n + 1)) r ^ 2))..
        (x₀ + ∫ r in (0 : ℝ)..(Hs (n + 1) / 2), √(1 - periodize y (Hs (n + 1)) r ^ 2)),
        |k n u - frontCurv (periodize y (Hs n)) u| :=
      intervalIntegral.integral_nonneg (by linarith) fun _ _ => abs_nonneg _
    refine ⟨by positivity, ?_⟩
    calc _ ≤ (1 + Hs n) ^ 2 * (C * exp (-(β * Hs (n + 1)))) :=
          mul_le_mul_of_nonneg_left hb' (by positivity)
      _ ≤ (1 + Hs n) ^ 2 * (|C| * exp (-(β * Hs (n + 1)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self C)
            (exp_pos _).le) (by positivity)
      _ = _ := by ring
  have hs := Summable.of_nonneg_of_le (fun n => (hterm n).1) (fun n => (hterm n).2) hsum
  exact ⟨hs, (hs.tsum_le_tsum (fun n => (hterm n).2) hsum).trans hle⟩

end Ovals

end
