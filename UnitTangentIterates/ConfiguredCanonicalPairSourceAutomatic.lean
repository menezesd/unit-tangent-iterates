import UnitTangentIterates.ConfiguredCanonicalPairSource

/-!
# Callback-free canonical configured pair source

The exact configured model pair carries no shadowing error.  Consequently its
legacy inductive-tube budget can be instantiated with zero conversion, zero
amplification, and the zero defect sequence.  This keeps that auxiliary budget
out of the final paper-facing assembly.
-/

noncomputable section

open Set Function
open MarkedSpace

namespace ConfiguredCanonicalPairSourceAutomatic

/-- Callback-free canonical pair source for any selected-inverse cap containing
the configured steering strip. -/
theorem exists_output_of_cap
    (D : ConstructedConfiguredSequenceWeighted.Data) {kh : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (ha : D.model.a ≤ kh) :
    ∃ Q : ℕ → Data,
      (∀ n, perim (Q n) = 2 * D.Hs n ∧
        ev (Q n) = TwoCapPairsAssembly.front
          (D.kappas n) D.model.thetaBase (D.Hs n)) ∧
      Nonempty (ConfiguredCanonicalPairSource.Output
        D Q kh 0 0 (fun _ ↦ 0)) := by
  have hspeed : ∀ n,
      PullbackTubeTailBudget.radius 0 0 (fun _ ↦ 0) n ≤ D.Hs 0 := by
    intro n
    simp [PullbackTubeTailBudget.radius, ShadowingTails.tail]
    exact (D.model.separation_pos 0).le
  have hchord : ∀ n,
      2 * PullbackTubeTailBudget.radius 0 0 (fun _ ↦ 0) n ≤
        ConfiguredInductiveTubeBudget.chordBase D.model / 2 *
          ConfiguredInductiveTubeBudget.rowRho D.model 0 0 (fun _ ↦ 0) n := by
    intro n
    have hkpos :=
      ConstructedConfiguredInductiveTubeBudget.configured_kstar_pos D.model
    have hcb0 : 0 ≤ ConfiguredInductiveTubeBudget.chordBase D.model := by
      rw [ConstructedConfiguredInductiveTubeBudget.chordBase_eq_min D.model hkpos]
      exact (lt_min (D.model.separation_pos 0)
        (div_pos Real.pi_pos (mul_pos (by norm_num) hkpos))).le
    have hrho0 : 0 ≤
        ConfiguredInductiveTubeBudget.rowRho D.model 0 0 (fun _ ↦ 0) n := by
      simp only [ConfiguredInductiveTubeBudget.rowRho,
        PullbackTubeTailBudget.radius, ShadowingTails.tail, zero_mul,
        tsum_zero, add_zero]
      exact le_min (by norm_num) (div_nonneg (D.model.separation_pos 0).le
        (mul_nonneg (by norm_num)
          (mul_nonneg (sq_nonneg (2 * D.Hs n)) hkpos.le)))
    simpa [PullbackTubeTailBudget.radius, ShadowingTails.tail] using
      mul_nonneg (div_nonneg hcb0 (by norm_num)) hrho0
  obtain ⟨Q, hQ, R⟩ :=
    ConfiguredInductiveTubeBudget.exists_budget_of_strict_configuredModelSequence
      D.model hkh0 hkh1 (by norm_num) (by norm_num) (fun _ ↦ by norm_num)
      hspeed hchord
  exact ⟨Q, hQ,
    ConfiguredCanonicalPairSource.exists_output D hQ R hkh0 hkh1 ha⟩

/-- The canonical aligned pair source exists without an externally supplied
legacy tube budget.  Nonzero diagonal errors enter only after this exact base
pair has been constructed. -/
theorem exists_output_modelA (D : ConstructedConfiguredSequenceWeighted.Data) :
    ∃ Q : ℕ → Data,
      (∀ n, perim (Q n) = 2 * D.Hs n ∧
        ev (Q n) = TwoCapPairsAssembly.front
          (D.kappas n) D.model.thetaBase (D.Hs n)) ∧
      Nonempty (ConfiguredCanonicalPairSource.Output
        D Q D.model.a 0 0 (fun _ ↦ 0)) := by
  exact exists_output_of_cap D (D.model.configs 0).ha0
    (D.model.configs 0).ha1 (le_refl _)

/-- The strengthened construction's retained steering cap permits the fixed
actual selected-inverse cap `1 / 2`. -/
theorem exists_output_half
    (E : ConstructedConfiguredSequenceWeighted.DataWithActualHalf) :
    ∃ Q : ℕ → Data,
      (∀ n, perim (Q n) = 2 * E.data.Hs n ∧
        ev (Q n) = TwoCapPairsAssembly.front
          (E.data.kappas n) E.data.model.thetaBase (E.data.Hs n)) ∧
      Nonempty (ConfiguredCanonicalPairSource.Output
        E.data Q (1 / 2) 0 0 (fun _ ↦ 0)) := by
  exact exists_output_of_cap E.data (by norm_num) (by norm_num)
    E.steering_le_half

end ConfiguredCanonicalPairSourceAutomatic
