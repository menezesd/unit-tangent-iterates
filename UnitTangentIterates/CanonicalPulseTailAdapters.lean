import UnitTangentIterates.CanonicalConsecutivePaperWitness
import UnitTangentIterates.PeriodizedStripThreshold

/-! # Fixed-profile tail adapters for canonical sequence assembly -/

noncomputable section

namespace PaperHairpinConfig

/-- Exact positive mass, continuity, nonnegativity, and a uniform bound give
the integrable, strictly positive square mass used by the strict recurrence. -/
theorem PulseMassData.integrable_sq_and_integral_sq_pos
    {y : ℝ → ℝ} {b : ℝ}
    (d : PulseMassData y) (hyc : Continuous y)
    (hy0 : ∀ s, 0 ≤ y s) (hb0 : 0 ≤ b) (hyb : ∀ s, y s ≤ b) :
    MeasureTheory.Integrable (fun s => y s ^ 2) ∧ 0 < ∫ s, y s ^ 2 := by
  have hsq : MeasureTheory.Integrable (fun s => y s ^ 2) := by
    have hmaj := d.integrable.const_mul b
    refine MeasureTheory.Integrable.mono' hmaj (hyc.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hy0 s, hyb s]
  have hex : ∃ s, y s ≠ 0 := by
    by_contra h
    push_neg at h
    have hyzero : y = fun _ => 0 := funext h
    have hmass := d.mass_eq_pi
    rw [hyzero] at hmass
    simp at hmass
    exact Real.pi_ne_zero hmass.symm
  obtain ⟨s0, hs0⟩ := hex
  have hopen : IsOpen (Function.support fun s => y s ^ 2) :=
    (hyc.pow 2).isOpen_support
  have hsupp : s0 ∈ Function.support fun s => y s ^ 2 := by
    simpa [Function.mem_support] using hs0
  have hpos : 0 < ∫ s, y s ^ 2 := by
    rw [MeasureTheory.integral_pos_iff_support_of_nonneg
      (fun s => sq_nonneg (y s)) hsq]
    exact hopen.measure_pos MeasureTheory.volume ⟨s0, hsupp⟩
  exact ⟨hsq, hpos⟩

/-- One threshold makes the overlap tail fit both the current and preceding
strip budgets. -/
theorem exists_simultaneous_strip_budget_threshold
    {alpha C b a au : ℝ} (halpha : 0 < alpha)
    (hb : b < min a au) :
    ∃ H0 : ℝ, 0 < H0 ∧ ∀ H ≥ H0,
      b + 4 * C * Real.exp (-(alpha / 2) * H) ≤ a ∧
      b + 4 * C * Real.exp (-(alpha / 2) * H) ≤ au := by
  have hrate : 0 < alpha / 2 := by linarith
  have htarget : 0 < min a au - b := by linarith
  have hev : ∀ᶠ H : ℝ in Filter.atTop,
      4 * C * Real.exp (-(alpha / 2) * H) ≤ min a au - b :=
    FrontPeriodizationPositivity.eventually_const_mul_exp_neg_le
      (A := 4 * C) hrate htarget
  have hall : ∀ᶠ H : ℝ in Filter.atTop,
      0 < H ∧ 4 * C * Real.exp (-(alpha / 2) * H) ≤ min a au - b := by
    filter_upwards [Filter.Ioi_mem_atTop (0 : ℝ), hev] with H hH he
    exact ⟨hH, he⟩
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.1 hall
  refine ⟨max Q 1, by positivity, ?_⟩
  intro H hH
  obtain ⟨-, he⟩ := hQ H (le_trans (le_max_left Q 1) hH)
  constructor <;> linarith [min_le_left a au, min_le_right a au]

end PaperHairpinConfig

