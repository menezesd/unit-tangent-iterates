import UnitTangentIterates.SelectedInverseApproximateMapPath
import UnitTangentIterates.SelInvRearFamilySupFundamentalC2
import UnitTangentIterates.MarkingDeviationC2

/-!
# Canonical endpoint completion of a selected-rear gauge path

The terminal object produced by the selected-rear gauge family is the
canonical selected inverse read in the terminal gauge marking.  The
`markingC2Bound` chain proves that this marked datum is close to the canonical
marking in the ambient metric; it does not construct a `NormalPath` between
the two markings.

This file gives the exact constructive adapter needed by approximate
pullback.  It concatenates the gauge path with an explicitly supplied terminal
re-marking path.  The only seam datum retained is the variable-speed
certificate of the concatenation itself.  This is necessary because the
current variable-speed API has no concatenation theorem.
-/

noncomputable section

open MarkedSpace PathMetric PathMetric.NormalPath
  NormalPathC2IncrementVariableSpeed

namespace SelectedInverseCanonicalPathCompletion

open SelectedInverseApproximateMapPath

/-- A genuine normal-gauge realization of the terminal change of marking.
The number `E` may be instantiated by the appropriate `markingC2Bound` once
such a realization theorem is proved. -/
structure TerminalRemarkingPath
    (qGauge qCanonical : Data)
    (P0 P1 khat G1 Cg E : ℝ) : Type where
  path : NormalPath qGauge qCanonical
  variableSpeed : IsVariableSpeedNormalPath P0 P1 khat G1 Cg path
  cost_le : cost path ≤ E

/-- The smallest output bundle which turns the gauge-marked rear family into
an endpoint-correct recursive map path.

`joined_variableSpeed` is seam regularity, not another endpoint callback.  The
underlying `NormalPath` is definitionally the concatenation of the two supplied
pieces and its cost is therefore their sum. -/
structure CanonicalRearPathCompletion
    {p q : Data} (Gamma : NormalPath p q)
    (P0 kh khat Qmax Mtotal Ktotal : ℝ) : Type where
  qGauge : Data
  gaugePath : NormalPath (SelectedInverseMap.selInv kh p) qGauge
  gaugeBudget : ℝ
  markingBudget : ℝ
  gauge_cost_le : cost gaugePath ≤ gaugeBudget
  terminal : TerminalRemarkingPath qGauge (SelectedInverseMap.selInv kh q)
    P0 (mapRearP1 kh Qmax khat Mtotal) khat
      (mapRearG1 kh Qmax khat Mtotal) (mapRearCg kh Qmax khat Mtotal)
      markingBudget
  total_control : gaugeBudget + markingBudget ≤ Ktotal * cost Gamma
  joined_variableSpeed : IsVariableSpeedNormalPath
    P0 (mapRearP1 kh Qmax khat Mtotal) khat
      (mapRearG1 kh Qmax khat Mtotal) (mapRearCg kh Qmax khat Mtotal)
      (gaugePath.concat terminal.path)

/-- The endpoint-correct path obtained by the constructive concatenation. -/
def CanonicalRearPathCompletion.path
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax Mtotal Ktotal : ℝ}
    (C : CanonicalRearPathCompletion
      Gamma P0 kh khat Qmax Mtotal Ktotal) :
    NormalPath (SelectedInverseMap.selInv kh p)
      (SelectedInverseMap.selInv kh q) :=
  C.gaugePath.concat C.terminal.path

/-- Cost and fixed-class certificate of the canonical concatenated path. -/
theorem CanonicalRearPathCompletion.cost_le
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax Mtotal Ktotal : ℝ}
    (C : CanonicalRearPathCompletion
      Gamma P0 kh khat Qmax Mtotal Ktotal) :
    cost C.path ≤ Ktotal * cost Gamma ∧
    IsVariableSpeedNormalPath
      P0 (mapRearP1 kh Qmax khat Mtotal) khat
        (mapRearG1 kh Qmax khat Mtotal) (mapRearCg kh Qmax khat Mtotal)
        C.path := by
  constructor
  · rw [CanonicalRearPathCompletion.path, cost_concat]
    exact (add_le_add C.gauge_cost_le C.terminal.cost_le).trans C.total_control
  · exact C.joined_variableSpeed

/-- Family form matching the local approximate-map hypothesis, with an honest
total map factor.  No ambient-distance-to-path realization is assumed. -/
theorem hmap_local
    {P0 kh khat Qmax Mtotal Ktotal c dlt : ℝ}
    (family : ∀ (p q : Data) (Gamma : NormalPath p q),
      IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
      IsVariableSpeedNormalPath
        P0 (mapRearP1 kh Qmax khat Mtotal) khat
          (mapRearG1 kh Qmax khat Mtotal) (mapRearCg kh Qmax khat Mtotal) Gamma →
      cost Gamma ≤ Mtotal →
      Nonempty (CanonicalRearPathCompletion
        Gamma P0 kh khat Qmax Mtotal Ktotal)) :
    ∀ (p q : Data) (Gamma : NormalPath p q),
      IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
      IsVariableSpeedNormalPath
        P0 (mapRearP1 kh Qmax khat Mtotal) khat
          (mapRearG1 kh Qmax khat Mtotal) (mapRearCg kh Qmax khat Mtotal) Gamma →
      cost Gamma ≤ Mtotal →
      ∀ eta : ℝ, 0 < eta →
        ∃ Delta : NormalPath (SelectedInverseMap.selInv kh p)
            (SelectedInverseMap.selInv kh q),
          cost Delta ≤ Ktotal * cost Gamma + eta ∧
          IsVariableSpeedNormalPath
            P0 (mapRearP1 kh Qmax khat Mtotal) khat
              (mapRearG1 kh Qmax khat Mtotal) (mapRearCg kh Qmax khat Mtotal)
              Delta := by
  intro p q Gamma hp hq hGamma hcost eta heta
  let C := Classical.choice (family p q Gamma hp hq hGamma hcost)
  refine ⟨C.path, (C.cost_le.1).trans ?_, C.cost_le.2⟩
  exact le_add_of_nonneg_right heta.le

end SelectedInverseCanonicalPathCompletion
