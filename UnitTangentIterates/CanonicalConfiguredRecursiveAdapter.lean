import UnitTangentIterates.CanonicalConfiguredModelCapstone
import UnitTangentIterates.ConfiguredModelGaugeFamily

/-! # Canonical configured model to recursive-output adapter -/

noncomputable section

open MarkedSpace

namespace PathMetric

/-- The exact output of the model-construction half needed by recursive
interpolation: a configured model together with one nonnegative summable
majorant. -/
structure CanonicalConfiguredDefectPackage
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps) where
  defect : ℕ → ℝ
  defect_nonneg : ∀ n, 0 ≤ defect n
  defect_summable : Summable defect

/-- Attach concrete recursive interpolation and reparameterization outputs to
the canonical model/defect package.  The only cross-boundary obligation is
that each chosen stage error be dominated by the packaged marked defect. -/
def CanonicalConfiguredDefectPackage.toRecursiveOutputs
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    {model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps}
    (D : CanonicalConfiguredDefectPackage model)
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg M N C0 : ℝ}
    (stages : ModelRecursiveControlledStages Q P0 P1 khat G1 Cg)
    (junction : ∀ n k, ReparamJunctionCertificate
      (p' := Q n k) (q' := Q n (k + 1)) (stages.stage n k).path)
    (junctionC2 : ∀ n k, ReparamC2Certificate (stages.stage n k).path
      (stages.stage n k).c2 (junction n k))
    (junction_M : ∀ n k, (junction n k).M = M)
    (junction_N : ∀ n k, (junction n k).N = N)
    (reparam_cost : ∀ n k,
      reparamCostConst (junction n k).m (junction n k).M (junction n k).N ≤ C0)
    (stage_nonneg : ∀ n k, 0 ≤
      (if stages.useInterpolation n k then stages.interpolationError n k
        else stages.gaugeError n k))
    (stage_le_defect : ∀ n k,
      (if stages.useInterpolation n k then stages.interpolationError n k
        else stages.gaugeError n k) ≤ D.defect (n + k)) :
    ConfiguredModelRecursiveOutputs model Q P0 P1 khat G1 Cg M N C0 :=
  { stages := stages
    junction := junction
    junctionC2 := junctionC2
    junction_M := junction_M
    junction_N := junction_N
    reparam_cost := reparam_cost
    defect := D.defect
    defect_nonneg := D.defect_nonneg
    defect_summable := D.defect_summable
    stage_nonneg := stage_nonneg
    stage_le_modelDefect := stage_le_defect }

/-- Existence wrapper in the exact type consumed by the paper-facing recursive
main theorem. -/
theorem exists_recursiveOutputs_of_canonicalDefect
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    {model : UnconditionalAssembly.ConfiguredModelSequence kappas Hs eps}
    (D : CanonicalConfiguredDefectPackage model)
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg M N C0 : ℝ}
    (stages : ModelRecursiveControlledStages Q P0 P1 khat G1 Cg)
    (junction : ∀ n k, ReparamJunctionCertificate
      (p' := Q n k) (q' := Q n (k + 1)) (stages.stage n k).path)
    (junctionC2 : ∀ n k, ReparamC2Certificate (stages.stage n k).path
      (stages.stage n k).c2 (junction n k))
    (junction_M : ∀ n k, (junction n k).M = M)
    (junction_N : ∀ n k, (junction n k).N = N)
    (reparam_cost : ∀ n k,
      reparamCostConst (junction n k).m (junction n k).M (junction n k).N ≤ C0)
    (stage_nonneg : ∀ n k, 0 ≤
      (if stages.useInterpolation n k then stages.interpolationError n k
        else stages.gaugeError n k))
    (stage_le_defect : ∀ n k,
      (if stages.useInterpolation n k then stages.interpolationError n k
        else stages.gaugeError n k) ≤ D.defect (n + k)) :
    ∃ O : ConfiguredModelRecursiveOutputs model Q P0 P1 khat G1 Cg M N C0,
      O.defect = D.defect := by
  exact ⟨D.toRecursiveOutputs stages junction junctionC2 junction_M junction_N
    reparam_cost stage_nonneg stage_le_defect, rfl⟩

end PathMetric

