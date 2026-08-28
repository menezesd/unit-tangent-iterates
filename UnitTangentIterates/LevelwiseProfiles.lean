import UnitTangentIterates.ConstructedProfileInterior
import UnitTangentIterates.LevelwiseEps

/-!
# The levelwise family of hairpin profiles, with decaying curvature ceilings
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Real HairpinRelative
open scoped ContDiff

namespace LevelwiseEps

/-- **A family of hairpin profiles, one per level, whose curvature ceilings
decay at the rate the backward orbit requires.**

`exists_interiorPhaseData_of_eps` is applied at
`ε = levelEps n` for each `n`, which is legitimate because its only hypotheses
on `ε` are `0 < ε` and `ε ≤ 1/10`, both supplied by `levelEps_pos` and
`levelEps_le_ten`.  Each level therefore carries the full `InteriorPhaseData`
record together with the extra conclusion

  `∀ t ∈ Ioo 0 π, curvField (f n) t < 1 / √(n+1)`

which is exactly the threshold `OrbitCeiling.ceiling_lt_of_steps` shows to be
necessary for a model that must admit `n` backward steps. -/
theorem exists_levelwise_interiorPhaseData :
    ∃ (f g gp theta x : ℕ → ℝ → ℝ) (m Am : ℕ → ℝ), ∀ n : ℕ,
      0 < m n ∧ m n ≤ Am n ∧
      (∀ t ∈ Ioo (0:ℝ) π, m n ≤ f n t) ∧ (∀ t ∈ Ioo (0:ℝ) π, f n t ≤ Am n) ∧
      ContDiffOn ℝ ∞ (f n) (Ioo 0 π) ∧
      StrictMono (theta n) ∧
      (∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta n u = z) ∧
      (∀ u, curvField (f n) (theta n u) ≤ (2 / m n) * Real.exp (-|u| / Am n)) ∧
      CanonicalTranslatorLocalPhase.InteriorPhaseData (f n) (theta n) (x n)
        (g n) (gp n) ∧
      -- the levelwise curvature ceiling
      (∀ t ∈ Ioo (0:ℝ) π, curvField (f n) t < 1 / Real.sqrt ((n : ℝ) + 1)) := by
  have hlevel : ∀ n : ℕ, ∃ (fn gn gpn thetan xn : ℝ → ℝ) (mn Amn : ℝ),
      0 < mn ∧ mn ≤ Amn ∧
      (∀ t ∈ Ioo (0:ℝ) π, mn ≤ fn t) ∧ (∀ t ∈ Ioo (0:ℝ) π, fn t ≤ Amn) ∧
      ContDiffOn ℝ ∞ fn (Ioo 0 π) ∧ StrictMono thetan ∧
      (∀ z ∈ Ioo (0:ℝ) π, ∃ u, thetan u = z) ∧
      (∀ u, curvField fn (thetan u) ≤ (2 / mn) * Real.exp (-|u| / Amn)) ∧
      CanonicalTranslatorLocalPhase.InteriorPhaseData fn thetan xn gn gpn ∧
      (∀ t ∈ Ioo (0:ℝ) π, curvField fn t < 1 / Real.sqrt ((n : ℝ) + 1)) := by
    intro n
    obtain ⟨fn, gn, gpn, thetan, xn, mn, Amn, hbarrier, hm0, hmA, hlow, hupp,
      hsm, hmono, hsurj, hdecay, d⟩ :=
      exists_interiorPhaseData_of_eps
        (levelEps_pos n) (levelEps_le_ten n)
    refine ⟨fn, gn, gpn, thetan, xn, mn, Amn, hm0, hmA, hlow, hupp, hsm, hmono,
      hsurj, hdecay, d, ?_⟩
    -- the construction's barrier is `ε⁻¹ − ε`, whose reciprocal is the ceiling
    intro t ht
    refine lt_of_le_of_lt (curvField_le_of_barrier hm0 (hlow t ht)) ?_
    have hbar : 1 / (1 / levelEps n - levelEps n) < 1 / Real.sqrt ((n : ℝ) + 1) :=
      levelEps_ceiling_lt n
    have hmbar : 1 / levelEps n - levelEps n ≤ mn := by
      rw [one_div (levelEps n)]; exact hbarrier
    have hposbar : (0:ℝ) < 1 / levelEps n - levelEps n := by
      have he : 0 < levelEps n := levelEps_pos n
      have he10 : levelEps n ≤ 1 / 10 := levelEps_le_ten n
      have h1 : (10:ℝ) ≤ 1 / levelEps n := by
        rw [le_div_iff₀ he]; linarith
      linarith
    exact lt_of_le_of_lt (one_div_le_one_div_of_le hposbar hmbar) hbar
  choose f g gp theta x m Am hspec using hlevel
  exact ⟨f, g, gp, theta, x, m, Am, hspec⟩

end LevelwiseEps
