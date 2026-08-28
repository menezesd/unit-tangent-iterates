import UnitTangentIterates.MarkedUnitTangentRangeClosure
import UnitTangentIterates.SelectedInverseMap
import UnitTangentIterates.TubePullbackLimit

/-!
# Unit-tangent range orbits from finite pullback edges

The physical reconstruction package is unnecessary for the range-orbit part
of the limiting argument.  The finite recurrence relates row `n + 1` at
stage `k` to row `n` at stage `k + 1`.  An exact unit-tangent range identity
on those finite edges therefore passes directly to the two marked row limits.
-/

noncomputable section

open Filter Function Set Topology MarkedSpace

namespace PullbackUnitTangentRangeOrbit

/-- Exact unit-tangent range identities on the finite pullback recurrence
pass to the marked row limits.  Notice the `k + 1` on the rear row: this is
the alignment furnished by `TubePullbackLimit.pullback_succ`. -/
theorem orbitRange_of_finite_pullbackEdges
    {B : Data → Data} {Q : ℕ → Data} {X : ℕ → Data}
    {c kmin dlt : ℝ}
    (hc : 0 < c)
    (hmem : ∀ n k, IsTubeMember c kmin dlt
      (TubePullbackLimit.pullback B Q n k))
    (hXmem : ∀ n, IsTubeMember c kmin dlt (X n))
    (hXlim : ∀ n, Tendsto (TubePullbackLimit.pullback B Q n) atTop
      (nhds (X n)))
    (hfinite : ∀ n k,
      range (ev (TubePullbackLimit.pullback B Q (n + 1) k)) =
        range (UnitTangent.unitTangentMap
          (ev (TubePullbackLimit.pullback B Q n (k + 1))))) :
    ∀ n, range (ev (X (n + 1))) =
      range (UnitTangent.unitTangentMap (ev (X n))) := by
  intro n
  exact range_unitTangentMap_closed_under_marked_limits hc
    (fun k => hmem (n + 1) k) (fun k => hmem n (k + 1))
    (hXmem (n + 1)) (hXmem n) (hXlim (n + 1))
    ((hXlim n).comp (tendsto_add_atTop_nat 1)) (hfinite n)

/-- Selected-inverse specialization.  The sole finite geometric input is the
range identity for the selected inverse at the front members actually used by
the pullback recurrence; no limiting steering or inverse-arclength data is
retained. -/
theorem selectedInverse_orbitRange_of_finiteRange
    {kh : ℝ} {Q : ℕ → Data} {X : ℕ → Data}
    {c kmin dlt : ℝ}
    (hc : 0 < c)
    (hmem : ∀ n k, IsTubeMember c kmin dlt
      (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n k))
    (hXmem : ∀ n, IsTubeMember c kmin dlt (X n))
    (hXlim : ∀ n,
      Tendsto (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n)
        atTop (nhds (X n)))
    (hfinite : ∀ n k,
      range (ev (TubePullbackLimit.pullback
        (SelectedInverseMap.selInv kh) Q (n + 1) k)) =
      range (UnitTangent.unitTangentMap
        (ev (SelectedInverseMap.selInv kh
          (TubePullbackLimit.pullback
            (SelectedInverseMap.selInv kh) Q (n + 1) k))))) :
    ∀ n, range (ev (X (n + 1))) =
      range (UnitTangent.unitTangentMap (ev (X n))) := by
  apply orbitRange_of_finite_pullbackEdges hc hmem hXmem hXlim
  intro n k
  rw [TubePullbackLimit.pullback_succ]
  exact hfinite n k

end PullbackUnitTangentRangeOrbit
