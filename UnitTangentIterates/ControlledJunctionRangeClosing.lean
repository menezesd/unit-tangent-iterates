import Mathlib
import UnitTangentIterates.ControlledJunctionSequenceLimit
import UnitTangentIterates.RangeClosingAdapters
import UnitTangentIterates.CurveDistance

/-!
# Closing controlled-junction range orbits

This is the constructor-independent last step of the paper's closing argument.
One controlled-junction limit is selected at every orbit level.  Explicit
constructor certificates identify those limits with geometric representatives;
the range adapters transfer the unit-tangent orbit, and the width gap rules out
the circular alternative at level zero.
-/

open Filter Function Set Topology MainTheoremConditional

namespace PathMetric

open NormalPath

/-- Controlled-junction limits, representative range closing, and the width
contradiction assembled with the paper's quantifier order.  Certificates which
depend on the concrete interpolation/pullback constructor remain hypotheses. -/
theorem exists_noncircular_rangeOrbit_of_controlledJunction_limits
    {Q : ℕ → ℕ → MarkedSpace.Data}
    (S : ∀ n, ControlledJunctionSequence (Q n))
    {e : ℕ → ℕ → ℝ} {c kmin dlt Cmetric : ℝ}
    (he0 : ∀ n k, 0 ≤ e n k)
    (hesum : ∀ n, Summable (e n))
    (hcost : ∀ n k, NormalPath.cost ((S n).path k) ≤ e n k)
    (hCmetric : 0 ≤ Cmetric)
    (hdist : ∀ n k,
      dist (Q n k) (Q n (k + 1)) ≤ Cmetric * NormalPath.cost ((S n).path k))
    (htube : ∀ n k, MarkedSpace.IsTubeMember c kmin dlt (Q n k))
    (htube_closed : ∀ n X,
      Tendsto (Q n) atTop (𝓝 X) → MarkedSpace.IsTubeMember c kmin dlt X)
    (R : ℕ → ℝ → ℂ)
    (hrepresentative : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      ∀ n, range (MarkedSpace.ev (X n)) = range (R n))
    (htangentRepresentative : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      ∀ n,
        range (UnitTangent.unitTangentMap (MarkedSpace.ev (X n))) =
          range (UnitTangent.unitTangentMap (R n)))
    (hRorbit : ∀ n,
      range (R (n + 1)) = range (UnitTangent.unitTangentMap (R n)))
    (hoval : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      ∀ n, IsOval (MarkedSpace.ev (X n)))
    {M : ℝ → ℂ} {LM d Cw H : ℝ} {u : ℂ}
    (hM : Continuous M) (hMper : Periodic M LM) (hLM : 0 < LM)
    (hu : ‖u‖ = 1) (_hd0 : 0 ≤ d)
    (hMw : Width.width (range M) u ≤ Cw)
    (hinitial : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      Continuous (MarkedSpace.ev (X 0)) ∧
      0 < MarkedSpace.perim (X 0) ∧
      Periodic (MarkedSpace.ev (X 0)) (MarkedSpace.perim (X 0)))
    (hclose : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      Metric.hausdorffDist (range (MarkedSpace.ev (X 0))) (range M) ≤ d)
    (hperimeter : ∀ (X : ℕ → MarkedSpace.Data),
      (∀ n, Tendsto (Q n) atTop (𝓝 (X n))) →
      2 * H - d ≤ MarkedSpace.perim (X 0))
    (hgap : Cw + 2 * d < (2 * H - d) / Real.pi) :
    ∃ (Y : ℕ → ℝ → ℂ) (L : ℝ),
      (∀ n, IsOval (Y n)) ∧
      (∀ n,
        range (Y (n + 1)) = range (UnitTangent.unitTangentMap (Y n))) ∧
      0 < L ∧ Periodic (Y 0) L ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Y 0)) L := by
  have hlimits : ∀ n, ∃ X : MarkedSpace.Data,
      Tendsto (Q n) atTop (𝓝 X) ∧ MarkedSpace.IsTubeMember c kmin dlt X := by
    intro n
    obtain ⟨X, hX, hXtube, _⟩ :=
      exists_limit_of_summable_controlledJunctions
        (S n) (he0 n) (hesum n) (hcost n) hCmetric (hdist n)
          (htube n) (htube_closed n)
    exact ⟨X, hX, hXtube⟩
  choose X hXlim hXtube using hlimits
  let Y : ℕ → ℝ → ℂ := fun n => MarkedSpace.ev (X n)
  let L : ℝ := MarkedSpace.perim (X 0)
  have hYoval : ∀ n, IsOval (Y n) := hoval X hXlim
  have hYorbit : ∀ n,
      range (Y (n + 1)) = range (UnitTangent.unitTangentMap (Y n)) := by
    intro n
    exact RangeClosingAdapters.unitTangent_range_orbit_of_representatives
      (hrepresentative X hXlim n)
      (hrepresentative X hXlim (n + 1))
      (hRorbit n)
      (htangentRepresentative X hXlim n)
  obtain ⟨hYcontinuous, hL, hYperiodic⟩ := hinitial X hXlim
  have hnoncircle :
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Y 0)) L := by
    exact CurveDistance.not_isCircleOfPerimeter_of_hausdorffDist_range_le
      hYcontinuous hYperiodic hL hM hMper hLM hu
      (hclose X hXlim) hMw (hperimeter X hXlim) hgap
  exact ⟨Y, L, hYoval, hYorbit, hL, hYperiodic, hnoncircle⟩

end PathMetric
