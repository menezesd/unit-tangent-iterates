import Mathlib
import UnitTangentIterates.TubePullbackLimit
import UnitTangentIterates.SummableNormalPathLimitCircle

/-!
# The shadowing scheme is not vacuous: the dilating circles

`TubePullbackLimit.exists_shadowing_limit` runs the scheme of the theorem
*Regularizing backward shadowing* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* in the space of marked curves.  Its hypothesis block —
a map taking constant-speed normal paths to constant-speed normal paths of cost
at most `K ≤ 1` times as large, a model pseudo-orbit whose defect paths have
summable cost, tube membership of the pullbacks, continuity of the map — is
checked here on a genuinely moving pseudo-orbit: the circles of radii
`rₙ = 1 + 2^{-n}` of `SummableNormalPathLimitCircle.lean`, joined by the
dilations, with the identity as the map.

The pseudo-orbit really moves (its defects are the nonzero costs of the
dilations), the tubes really shrink, and the conclusion is the expected one:
the terminal pullbacks converge to the circle of radius one, which is an exact
orbit of the identity and shadows the model within `rₙ = ∑_{m ≥ n} d_m`.

* `exists_shadowing_limit_circles` — the conclusion of the scheme for this
  configuration;
* `shadowing_limit_circles_eq` — the limits are the circle of radius one.
-/

noncomputable section

open Set Filter Topology MarkedSpace PathMetric PathMetric.NormalPath
open SummableNormalPathLimitCircle

namespace TubePullbackLimitCircle

/-- The model pseudo-orbit: the circles of radii `1 + 2^{-n}`. -/
def model (n : ℕ) : Data := circleData (rad n)

/-- The defects: the costs of the dilations joining consecutive circles. -/
def defect (n : ℕ) : ℝ := cost (circlePath n)

/-- With the identity as the map, the pullbacks are the models themselves. -/
theorem pullback_id (n k : ℕ) : TubePullbackLimit.pullback id model n k = model (n + k) := by
  simp [TubePullbackLimit.pullback, Function.iterate_id]

/-- **The scheme applied to the dilating circles.**  Every hypothesis of
`TubePullbackLimit.exists_shadowing_limit` holds for the identity map and the
model pseudo-orbit of circles of radii `1 + 2^{-n}`, so the scheme produces
limits in the tube which form an exact orbit and shadow the model. -/
theorem exists_shadowing_limit_circles :
    ∃ X : ℕ → Data,
      (∀ n, IsTubeMember (2 * Real.pi) (1 / 2) 4 (X n)) ∧
      (∀ n, Tendsto (TubePullbackLimit.pullback id model n) atTop (𝓝 (X n))) ∧
      (∀ n, X n = id (X (n + 1))) ∧
      (∀ n k, TubePullbackLimit.pullback id model n k ∈
        TubeInvariance.tube (model n) (ShadowingTails.tail defect n)) ∧
      (∀ n u, ‖(X n).1 u - (model n).1 u‖ ≤ ShadowingTails.tail defect n) ∧
      (∀ n, dist (model n) (X n) ≤
        NormalPathC2Increment.c2Const (2 * Real.pi) (4 * Real.pi) 1 *
          ShadowingTails.tail defect n) ∧
      (∀ n, |perim (X n) - perim (model n)| ≤
        NormalPathC2Increment.c2Const (2 * Real.pi) (4 * Real.pi) 1 *
          ShadowingTails.tail defect n) := by
  refine TubePullbackLimit.exists_shadowing_limit (B := id) (Q := model) (d := defect)
    (K := 1) (c := 2 * Real.pi) (kmin := 1 / 2) (dlt := 4)
    (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (khat := 1)
    zero_le_one le_rfl (fun n => cost_nonneg _) summable_cost_circlePath
    (fun p q Γ hΓ => ⟨Γ, by simp, hΓ⟩)
    (fun n => ⟨circlePath n, le_rfl, isConstantSpeedNormalPath_circlePath n⟩)
    (fun n k => ?_) continuous_id
  rw [pullback_id]
  exact circleData_rad_mem (n + k)

/-- **The limits are the circle of radius one.**  Along this configuration the
shadowing limits of `exists_shadowing_limit_circles` are the unit circle, for
every level. -/
theorem shadowing_limit_circles_eq {X : ℕ → Data}
    (hX : ∀ n, Tendsto (TubePullbackLimit.pullback id model n) atTop (𝓝 (X n))) (n : ℕ) :
    X n = circleData 1 := by
  have hshift : Tendsto (fun k => model (n + k)) atTop (𝓝 (circleData 1)) := by
    have := tendsto_circleData_rad.comp (tendsto_add_atTop_nat n)
    simpa [model, Nat.add_comm] using this
  have hpull : Tendsto (TubePullbackLimit.pullback id model n) atTop (𝓝 (circleData 1)) := by
    have heq : TubePullbackLimit.pullback id model n = fun k => model (n + k) :=
      funext fun k => pullback_id n k
    rw [heq]
    exact hshift
  exact tendsto_nhds_unique (hX n) hpull

end TubePullbackLimitCircle
