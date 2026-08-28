import Mathlib

/-!
# Uniform bounds for stopped periodic fields

A continuous field which is periodic in its spatial variable and vanishes
outside a compact time interval has a finite global bound.  This is the
compactness step used to retain fresh first-time-derivative bounds on an exact
successor source.
-/

noncomputable section

open Function Set

namespace StoppedPeriodicUniformBound

/-- A continuous, unit-periodic scalar field stopped outside `[0,T]` has a
finite global absolute-value bound. -/
theorem exists_bound {f : ℝ → ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T)
    (hf : Continuous (uncurry f))
    (hper : ∀ t, Periodic (f t) 1)
    (hstop : ∀ t ∉ Icc (0 : ℝ) T, f t = fun _ ↦ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t u, |f t u| ≤ M := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty :=
    ⟨(0, 0), ⟨⟨le_rfl, hT⟩, ⟨le_rfl, zero_le_one⟩⟩⟩
  have hg : Continuous (fun z : ℝ × ℝ ↦ |f z.1 z.2|) :=
    (hf.abs : Continuous fun z : ℝ × ℝ ↦ |uncurry f z|)
  obtain ⟨z, hz, hzmax⟩ := hK.exists_isMaxOn hKne hg.continuousOn
  refine ⟨|f z.1 z.2|, abs_nonneg _, ?_⟩
  intro t u
  by_cases ht : t ∈ Icc (0 : ℝ) T
  · let v : ℝ := Int.fract u
    have hv : v ∈ Icc (0 : ℝ) 1 :=
      ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩
    have huv : f t u = f t v := by
      have hp := (hper t).int_mul ⌊u⌋
      have heq : v + (⌊u⌋ : ℝ) * 1 = u := by
        dsimp [v]
        rw [mul_one, add_comm, Int.floor_add_fract]
      rw [← heq, hp v]
    rw [huv]
    exact @hzmax (t, v) ⟨ht, hv⟩
  · rw [hstop t ht]
    simp

/-- The one-variable version used for stopped period derivatives. -/
theorem exists_bound_time {f : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T)
    (hf : Continuous f)
    (hstop : ∀ t ∉ Icc (0 : ℝ) T, f t = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |f t| ≤ M := by
  have hK : IsCompact (Icc (0 : ℝ) T) := isCompact_Icc
  have hKne : (Icc (0 : ℝ) T).Nonempty := ⟨0, ⟨le_rfl, hT⟩⟩
  obtain ⟨s, hs, hsmax⟩ := hK.exists_isMaxOn hKne hf.abs.continuousOn
  refine ⟨|f s|, abs_nonneg _, ?_⟩
  intro t
  by_cases ht : t ∈ Icc (0 : ℝ) T
  · exact hsmax ht
  · rw [hstop t ht]
    simpa using (abs_nonneg (f s))

end StoppedPeriodicUniformBound
