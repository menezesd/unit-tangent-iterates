import UnitTangentIterates.VariableSpeedIteration

/-!
# Certifying the rear-family output against the fixed variable-speed class
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2Increment NormalPathC2IncrementVariableSpeed GaugeFlowDerivCost

namespace PathMetric

/-- **The rear-family output, certified against the fixed class.**

`GaugeRearFamilyFromFront.exists_variableSpeed_normalPath_of_rearFamily_from_front`
returns a path in the class

    IsVariableSpeedNormalPath P0 (costP1 ell khat M) khat
      (costG1 ell khat kappa2 M) (…)

whose ceilings are computed from *that step's* rear period `ell` and cost `M`.
The iteration of §108 runs in a single fixed class `(G1, Cg)`.  This lemma is the
bridge: by §97's `ceilings_uniform` the step ceilings are dominated by their
values at uniform `Q` and `Mtot`, so `IsVariableSpeedNormalPath.mono` places the
output in the fixed class, and `pathDistVS_le_cost` converts it to the bound the
iteration consumes.

Together with §107's `pathDistVS_le_cost` this is what makes the Jacobi estimate
usable: the estimate bounds a cost, the iteration wants a distance bound in a
fixed class, and the two are separated exactly by this monotonicity step. -/
theorem pathDistVS_le_of_step_ceilings {a b : Data}
    {P0 P1 P1' khat G1 Cg ell Q kappa2 M Mtot : ℝ}
    (hkhat : 0 ≤ khat) (hell : 0 ≤ ell) (hellQ : ell ≤ Q) (hk2 : 0 ≤ kappa2)
    (hM : 0 ≤ M) (hMM : M ≤ Mtot) (hP1 : P1' ≤ P1)
    (hG1 : costP1 Q khat Mtot ≤ G1) (hCg : costG1 Q khat kappa2 Mtot ≤ Cg)
    (Γ : NormalPath a b)
    (hvs : IsVariableSpeedNormalPath P0 P1' khat
      (costP1 ell khat M) (costG1 ell khat kappa2 M) Γ) :
    pathDistVS P0 P1 khat G1 Cg a b ≤ cost Γ := by
  obtain ⟨hP, hG⟩ := ceilings_uniform hell hellQ hkhat hk2 hM hMM
  exact pathDistVS_le_cost Γ
    (hvs.mono Γ hkhat hP1 (le_trans hP hG1) (le_trans hG hCg))

/-- The same statement for the defect side, where the path joins the model to the
rear of the next model.  Identical mechanism; stated separately because the
endpoints are the ones `hdefect` names. -/
theorem pathDistVS_defect_le_of_step_ceilings {B : Data → Data} {Q' : ℕ → Data} {n : ℕ}
    {P0 P1 P1' khat G1 Cg ell Q kappa2 M Mtot : ℝ}
    (hkhat : 0 ≤ khat) (hell : 0 ≤ ell) (hellQ : ell ≤ Q) (hk2 : 0 ≤ kappa2)
    (hM : 0 ≤ M) (hMM : M ≤ Mtot) (hP1 : P1' ≤ P1)
    (hG1 : costP1 Q khat Mtot ≤ G1) (hCg : costG1 Q khat kappa2 Mtot ≤ Cg)
    (Λ : NormalPath (Q' n) (B (Q' (n + 1))))
    (hvs : IsVariableSpeedNormalPath P0 P1' khat
      (costP1 ell khat M) (costG1 ell khat kappa2 M) Λ) :
    pathDistVS P0 P1 khat G1 Cg (Q' n) (B (Q' (n + 1))) ≤ cost Λ :=
  pathDistVS_le_of_step_ceilings hkhat hell hellQ hk2 hM hMM hP1 hG1 hCg Λ hvs

/-- **The approximate hypothesis from the certified bound.**  Combining with
§107's near-minimizer property, a `pathDistVS` bound yields the hypothesis the
iteration of §108 consumes. -/
theorem hmap_vs_approx_of_pathDistVS_le {B : Data → Data} {K P0 P1 khat G1 Cg : ℝ}
    (hne : ∀ p q : Data, ∃ Γ : NormalPath (B p) (B q),
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ)
    (hbound : ∀ (p q : Data) (Γ : NormalPath p q),
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ →
      pathDistVS P0 P1 khat G1 Cg (B p) (B q) ≤ K * cost Γ) :
    ∀ (p q : Data) (Γ : NormalPath p q),
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ →
      ∀ ε : ℝ, 0 < ε → ∃ Δ : NormalPath (B p) (B q),
        cost Δ ≤ K * cost Γ + ε ∧ IsVariableSpeedNormalPath P0 P1 khat G1 Cg Δ := by
  intro p q Γ hΓ ε hε
  obtain ⟨Δ, hΔvs, hΔ⟩ := exists_variableSpeed_near_minimizer (hne p q) hε
  exact ⟨Δ, le_trans hΔ (by linarith [hbound p q Γ hΓ]), hΔvs⟩


/-- **End to end.**  A `pathDistVS` bound on the image of `B`, together with
non-emptiness of the image class, runs the whole pullback iteration: `k` steps
cost at most `K^k` times the original, up to any prescribed `ε`, and the result
is still in the class.

This is the `hmap` half of the closing chain, reduced to a single hypothesis
about a distance — no attained minimizer, no constant-speed requirement, no
accumulation of ceilings. -/
theorem exists_path_iterate_of_pathDistVS_le {B : Data → Data} {K P0 P1 khat G1 Cg : ℝ}
    (hK : 0 ≤ K)
    (hne : ∀ p q : Data, ∃ Γ : NormalPath (B p) (B q),
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ)
    (hbound : ∀ (p q : Data) (Γ : NormalPath p q),
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ →
      pathDistVS P0 P1 khat G1 Cg (B p) (B q) ≤ K * cost Γ)
    (k : ℕ) {p q : Data} (Γ : NormalPath p q)
    (hΓ : IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Δ : NormalPath (B^[k] p) (B^[k] q),
      cost Δ ≤ K ^ k * cost Γ + ε ∧ IsVariableSpeedNormalPath P0 P1 khat G1 Cg Δ :=
  TubePullbackLimit.exists_path_iterate_approx_vs hK
    (hmap_vs_approx_of_pathDistVS_le hne hbound) k Γ hΓ ε hε

end PathMetric
