import Mathlib

/-!
# Tails, propagated bounds and the Cauchy step of the shadowing theorem

This file formalizes the remaining bookkeeping of the proof of the theorem
*Regularizing backward shadowing* of the paper *A Noncircular Oval with Convex
Unit-Tangent Iterates*: the tail sequence `rₙ = ∑_{m ≥ n} eₘ`, the propagation
of the tube bounds through arbitrarily many inverse steps, and the Cauchy
argument that produces the terminal limits `Xₙ` together with the estimate
`d(Xₙ, Zₙ) ≤ C rₙ`.

Main results:

* `tail_succ`, `tail_tendsto_zero`, `tail_antitone` : the elementary properties
  of `rₙ = ∑_{m ≥ n} eₘ` used throughout the proof (in particular
  `aₙ = dₙ + a_{n+1}`);
* `propagated_bounds` : after any number of inverse steps the increment path
  still satisfies `W ≤ d`, `S₀ ≤ M₀d`, `S₁ ≤ M₁d`, with
  `M₀ = max{1, C₀}` and `M₁ = max{1, C₁(1+M₀)}`;
* `S2_propagated_bound` : the accompanying second-order bound
  `S₂ ≤ C₂(1 + M₀ + M₁)d`;
* `exists_limit_of_summable_increments` : summable increments give a limit and
  the tail estimate `d(Z_N, X) ≤ C r_N`, the abstract form of the Cauchy step
  of the shadowing proof.
-/

noncomputable section

open Filter Topology

namespace ShadowingTails

/-! ### The tail sequence -/

/-- The tail `rₙ = ∑_{m ≥ n} eₘ` of a summable sequence. -/
def tail (e : ℕ → ℝ) (n : ℕ) : ℝ := ∑' m, e (n + m)

variable {e : ℕ → ℝ}

lemma summable_shift (hs : Summable e) (n : ℕ) : Summable fun m => e (n + m) := by
  simpa [Nat.add_comm] using (summable_nat_add_iff (f := e) n).mpr hs

theorem tail_nonneg (he : ∀ n, 0 ≤ e n) (n : ℕ) : 0 ≤ tail e n :=
  tsum_nonneg (fun _ => he _)

/-- **`rₙ = eₙ + r_{n+1}`**, the recursion used as `aₙ = dₙ + a_{n+1}`. -/
theorem tail_succ (hs : Summable e) (n : ℕ) : tail e n = e n + tail e (n + 1) := by
  have h := (summable_shift hs n).tsum_eq_zero_add
  simp only [tail]
  rw [h]
  congr 1
  refine tsum_congr (fun m => ?_)
  congr 1
  omega

/-- The tail is nonincreasing. -/
theorem tail_antitone (hs : Summable e) (he : ∀ n, 0 ≤ e n) : Antitone (tail e) := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  have := tail_succ hs n
  have h1 := he n
  linarith

/-- Each term is dominated by its tail. -/
theorem le_tail (hs : Summable e) (he : ∀ n, 0 ≤ e n) (n : ℕ) : e n ≤ tail e n := by
  have h := tail_succ hs n
  have := tail_nonneg he (n + 1)
  linarith

/-- **The tails tend to zero.**  (No summability hypothesis is needed: for a
non-summable sequence every tail is `0` by convention.) -/
theorem tail_tendsto_zero : Tendsto (tail e) atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add (f := e)
  have hcongr : (fun n => ∑' m, e (m + n)) = tail e := by
    funext n
    exact tsum_congr (fun m => by rw [Nat.add_comm])
  rwa [hcongr] at h

/-! ### Propagation of the tube bounds -/

/-- **The propagated increment bounds.**  If one inverse step does not increase
`W`, turns `W` into `S₀` with constant `C₀`, and turns `W + S₀` into `S₁` with
constant `C₁`, then the bounds `W ≤ d`, `S₀ ≤ M₀d`, `S₁ ≤ M₁d` reproduce
themselves at every depth, with `M₀ = max{1, C₀}`,
`M₁ = max{1, C₁(1 + M₀)}`. -/
theorem propagated_bounds {W S0 S1 : ℕ → ℝ} {C0 C1 M0 M1 d : ℝ}
    (hM0 : M0 = max 1 C0) (hM1 : M1 = max 1 (C1 * (1 + M0)))
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hd : 0 ≤ d)
    (hW0 : W 0 ≤ d) (hS00 : S0 0 ≤ d) (hS10 : S1 0 ≤ d)
    (hWs : ∀ k, W (k + 1) ≤ W k)
    (hS0s : ∀ k, S0 (k + 1) ≤ C0 * W k)
    (hS1s : ∀ k, S1 (k + 1) ≤ C1 * (W k + S0 k)) :
    ∀ k, W k ≤ d ∧ S0 k ≤ M0 * d ∧ S1 k ≤ M1 * d := by
  have hM0one : 1 ≤ M0 := by rw [hM0]; exact le_max_left _ _
  have hM0C0 : C0 ≤ M0 := by rw [hM0]; exact le_max_right _ _
  have hM1one : 1 ≤ M1 := by rw [hM1]; exact le_max_left _ _
  have hM1C1 : C1 * (1 + M0) ≤ M1 := by rw [hM1]; exact le_max_right _ _
  intro k
  induction k with
  | zero => exact ⟨hW0, by nlinarith, by nlinarith⟩
  | succ k ih =>
      obtain ⟨hW, hS0, hS1⟩ := ih
      refine ⟨(hWs k).trans hW, ?_, ?_⟩
      · have := hS0s k
        nlinarith
      · have := hS1s k
        nlinarith

/-- **The propagated second-order bound** `S₂ ≤ C₂(1 + M₀ + M₁)d`. -/
theorem S2_propagated_bound {C2 W S0 S1 S2 M0 M1 d : ℝ} (hC2 : 0 ≤ C2)
    (hS2 : S2 ≤ C2 * (W + S0 + S1))
    (hW : W ≤ d) (hS0 : S0 ≤ M0 * d) (hS1 : S1 ≤ M1 * d) :
    S2 ≤ C2 * (1 + M0 + M1) * d := by nlinarith

/-! ### The Cauchy step -/

variable {α : Type*} [MetricSpace α] [CompleteSpace α]

/-- **The Cauchy step of the shadowing theorem.**  If consecutive terminal
pullbacks differ by at most `C dₙ` with `∑ dₙ < ∞`, then they converge, and the
limit is within `C rₙ` of the `n`-th one, where `rₙ` is the tail of `d`. -/
theorem exists_limit_of_summable_increments {Z : ℕ → α} {d : ℕ → ℝ} {C : ℝ}
    (hsum : Summable d)
    (hincr : ∀ N, dist (Z N) (Z (N + 1)) ≤ C * d N) :
    ∃ X : α, Tendsto Z atTop (𝓝 X) ∧ ∀ N, dist (Z N) X ≤ C * tail d N := by
  have hsumC : Summable fun n => C * d n := hsum.mul_left C
  have hcauchy : CauchySeq Z := by
    refine cauchySeq_of_summable_dist (Summable.of_nonneg_of_le (fun n => dist_nonneg)
      (fun n => hincr n) hsumC)
  obtain ⟨X, hX⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨X, hX, fun N => ?_⟩
  have h := dist_le_tsum_of_dist_le_of_tendsto (fun n => C * d n) (fun n => hincr n) hsumC hX N
  have hrw : (∑' m, C * d (N + m)) = C * tail d N := by
    rw [tail, ← tsum_mul_left]
  rwa [hrw] at h

end ShadowingTails
