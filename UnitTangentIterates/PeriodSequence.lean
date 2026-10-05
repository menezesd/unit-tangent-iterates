module

public import UnitTangentIterates.PeriodRecursion
public import UnitTangentIterates.FrontMatching

/-!
# The period sequence of Section 7 for the actual half-perimeter

The half-perimeter `P(H) = ∫₀ᴴ √(1 - Y_H²)` of the closed rear is continuous in `H`, and by
Proposition 4.3 it satisfies `Δ/2 ≤ H - P(H) ≤ 3Δ/2` for large `H`, where `Δ > 0` is the
steering defect.  Hence (7.1): every sufficiently large `H₀` starts a sequence with
`P(H_{n+1}) = H_n` and `H_n ≥ H₀ + (Δ/2) n`.
-/

@[expose] public section

namespace Ovals

open Real Set Filter Topology

variable {y : ℝ → ℝ} {A a : ℝ}

/-- The periodization is jointly continuous in `(H, s)` once `H` is kept away from `0`. -/
theorem continuous_periodize_max (hyc : Continuous y)
    (hyA : ∀ t, |y t| ≤ A * exp (-(a * |t|))) (ha : 0 < a) {c : ℝ} (hc : 0 < c) :
    Continuous (fun p : ℝ × ℝ => periodize y (max p.1 c) p.2) := by
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hyA 0)) (exp_pos _)
  rw [continuous_iff_continuousAt]
  rintro ⟨H₀, s₀⟩
  set R := |s₀| + 1 with hR
  set U : Set (ℝ × ℝ) := univ ×ˢ Metric.ball s₀ 1 with hUdef
  have hU : IsOpen U := isOpen_univ.prod Metric.isOpen_ball
  have hmem : (H₀, s₀) ∈ U := ⟨trivial, Metric.mem_ball_self one_pos⟩
  set q := exp (-(a * c)) with hq
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := by rw [hq, Real.exp_lt_one_iff]; nlinarith
  obtain ⟨hgs, -⟩ := summable_geom_natAbs hq0 hq1
  refine (continuousOn_tsum (u := fun m : ℤ => A * exp (a * R) * q ^ m.natAbs)
    (fun m => ?_) (hgs.mul_left _) (fun m p hp => ?_)).continuousAt (hU.mem_nhds hmem)
  · exact (hyc.comp (continuous_snd.sub (continuous_const.mul
      (continuous_fst.max continuous_const)))).continuousOn
  · obtain ⟨-, hs⟩ := hp
    have hsR : |p.2| < R := by
      rw [Metric.mem_ball, Real.dist_eq] at hs
      have := abs_sub_abs_le_abs_sub p.2 s₀
      rw [hR]; linarith
    rw [Real.norm_eq_abs]
    refine (hyA _).trans ?_
    show A * exp (-(a * |p.2 - m * max p.1 c|)) ≤ A * exp (a * R) * q ^ m.natAbs
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hA
    rw [hq, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
    have hmabs : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [hmabs]
    set H' := max p.1 c
    have hH' : c ≤ H' := le_max_right _ _
    have h1 : |(m : ℝ)| * H' - |p.2| ≤ |p.2 - m * H'| := by
      have := abs_sub_abs_le_abs_sub (m * H' : ℝ) p.2
      rw [abs_mul, abs_of_pos (lt_of_lt_of_le hc hH'), abs_sub_comm] at this
      linarith
    have h2 : |(m : ℝ)| * c ≤ |(m : ℝ)| * H' := mul_le_mul_of_nonneg_left hH' (abs_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left h1 ha.le, mul_le_mul_of_nonneg_left h2 ha.le]

/-- **Continuity of the half-perimeter.** -/
theorem continuousOn_halfPerimeter (hyc : Continuous y)
    (hyA : ∀ t, |y t| ≤ A * exp (-(a * |t|))) (ha : 0 < a) {c : ℝ} (hc : 0 < c) :
    ContinuousOn (halfPerimeter y) (Ici c) := by
  have hcont := continuous_periodize_max hyc hyA ha hc
  have hF : Continuous (fun H => ∫ s in (0 : ℝ)..H, √(1 - periodize y (max H c) s ^ 2)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun H s => √(1 - periodize y (max H c) s ^ 2))
      (Real.continuous_sqrt.comp (continuous_const.sub (hcont.pow 2))) continuous_id
  refine hF.continuousOn.congr fun H hH => ?_
  simp only [halfPerimeter, max_eq_left (show c ≤ H from hH)]

/-- Existence part of the period recursion (no monotonicity needed). -/
theorem exists_period_sequence {P : ℝ → ℝ} {H₁ Δ : ℝ} (hPc : ContinuousOn P (Ici H₁))
    (hΔ : 0 < Δ) (hP : ∀ H ≥ H₁, Δ / 2 ≤ H - P H ∧ H - P H ≤ 3 * Δ / 2) {H₀ : ℝ}
    (hH₀ : H₁ ≤ H₀) :
    ∃ Hs : ℕ → ℝ, Hs 0 = H₀ ∧ (∀ n, H₁ ≤ Hs n) ∧ ∀ n, P (Hs (n + 1)) = Hs n ∧
      H₀ + Δ / 2 * n ≤ Hs n ∧ Hs n + Δ / 2 ≤ Hs (n + 1) := by
  classical
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
  refine ⟨Hs, rfl, hge, fun n => ⟨hrec n, ?_, ?_⟩⟩
  rotate_left
  · have := (hP _ (hge (n + 1))).1
    rw [hrec n] at this
    linarith
  induction n with
  | zero => simp [Hs]
  | succ n ih =>
    have := (hP _ (hge (n + 1))).1
    rw [hrec n] at this
    push_cast
    linarith

/-- **The period recursion (7.1) for the actual half-perimeter.**  For a continuous pulse with
`0 ≤ y ≤ b < 1`, exponential decay and `y(t₀) > 0` somewhere, every sufficiently large `H₀`
starts a sequence with `P(H_{n+1}) = H_n` and `H_n ≥ H₀ + (Δ/2) n`, where `Δ > 0` is the
steering defect. -/
theorem period_sequence_exists (hyc : Continuous y) (hy0 : ∀ t, 0 ≤ y t)
    (hyA : ∀ t, y t ≤ A * exp (-(a * |t|))) (ha : 0 < a) {b : ℝ} (hyb : ∀ t, y t ≤ b)
    (hb : b < 1) {t₀ : ℝ} (ht₀ : 0 < y t₀) :
    0 < steeringDefect y ∧ ∃ H₁ : ℝ, 0 < H₁ ∧ ∀ H₀ ≥ H₁, ∃ Hs : ℕ → ℝ, Hs 0 = H₀ ∧
      ∀ n, H₁ ≤ Hs n ∧ halfPerimeter y (Hs (n + 1)) = Hs n ∧
        H₀ + steeringDefect y / 2 * n ≤ Hs n ∧ Hs n + steeringDefect y / 2 ≤ Hs (n + 1) := by
  have hyA' : ∀ t, |y t| ≤ A * exp (-(a * |t|)) := fun t => by
    rw [abs_of_nonneg (hy0 t)]; exact hyA t
  have hΔ := steeringDefect_pos hyc hy0 hyA ha hyb hb ht₀
  refine ⟨hΔ, ?_⟩
  obtain ⟨C, β, H₂, hβ, hasym⟩ := halfPerimeter_asymptotics hyc hy0 hyA ha hyb hb
  have t : Tendsto (fun H : ℝ => C * exp (-(β * H))) atTop (𝓝 (C * 0)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hβ)).const_mul _
  rw [mul_zero] at t
  obtain ⟨H₃, hH₃⟩ := eventually_atTop.1 (t.eventually (gt_mem_nhds (half_pos hΔ)))
  set H₁ := max (max H₂ H₃) 1 with hH₁
  have hP : ∀ H ≥ H₁, steeringDefect y / 2 ≤ H - halfPerimeter y H ∧
      H - halfPerimeter y H ≤ 3 * steeringDefect y / 2 := fun H hH => by
    have h1 := hasym H ((le_max_left _ _).trans ((le_max_left _ _).trans hH))
    have h2 := hH₃ H ((le_max_right _ _).trans ((le_max_left _ _).trans hH))
    have h3 := abs_le.1 (h1.trans h2.le)
    constructor <;> linarith [h3.1, h3.2]
  refine ⟨H₁, lt_of_lt_of_le one_pos (le_max_right _ _), fun H₀ hH₀ => ?_⟩
  obtain ⟨Hs, h0, hge, hrec⟩ := exists_period_sequence
    ((continuousOn_halfPerimeter hyc hyA' ha one_pos).mono
      (Ici_subset_Ici.2 (le_max_right _ _))) hΔ hP hH₀
  exact ⟨Hs, h0, fun n => ⟨hge n, (hrec n).1, (hrec n).2.1, (hrec n).2.2⟩⟩

end Ovals

end
