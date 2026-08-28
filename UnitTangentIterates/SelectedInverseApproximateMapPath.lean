import UnitTangentIterates.ApproximatePaperAssemblySelectedInverse
import UnitTangentIterates.GaugeMarkedDataOfRearFamily
import UnitTangentIterates.LocalVariableSpeedApproximatePullback
import UnitTangentIterates.VariableSpeedCertification

/-!
# Approximate map paths for the selected inverse

This module isolates the exact interface between the selected-rear gauge
construction and the `hmap` hypothesis used by the approximate pullback
assembly.  The gauge construction produces edge-dependent period and cost
ceilings.  Once those are bounded by fixed `Qmax` and `Mtotal`, its existing
uniformization theorem returns a path in one fixed variable-speed class.

The explicit cost factor is the sharp maximum-principle loss
`1 / sqrt (1 - kh^2)`.  The residual below deliberately asks for raw gauge
output rather than an already uniformized `hmap`.

There is an unavoidable quantifier boundary here: the assembly asks for
transport for every pair of marked data and every path, whereas tube and
pinching certificates apply only to paths whose slices lie in the selected
tube.  Moreover the raw gauge ceilings depend on the total path cost, while
the assembly fixes finite ceilings globally.  Thus tube/pinching alone cannot
produce this unrestricted residual without an additional domain restriction
or a global cost bound.
-/

noncomputable section

open MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2IncrementVariableSpeed GaugeFlowDerivCost

namespace SelectedInverseApproximateMapPath

open GaugeMarkedDataOfRearFamily

/-- The explicit selected-rear cost multiplier coming from the strip maximum
principle. -/
def mapK (kh : ℝ) : ℝ := 1 / Real.sqrt (1 - kh ^ 2)

/-- Fixed period-derivative ceiling obtained by uniformizing the raw gauge
output over `ell ≤ Qmax` and `M ≤ Mtotal`. -/
def mapP1 (Qmax khat Mtotal : ℝ) : ℝ :=
  costP1 Qmax khat Mtotal

/-- Fixed first spatial gauge ceiling. -/
def mapG1 (kh Qmax khat Mtotal : ℝ) : ℝ :=
  costG1 Qmax khat (rearKappa2 kh) Mtotal

/-- Fixed mixed second-derivative gauge ceiling. -/
def mapCg (kh Qmax khat Mtotal : ℝ) : ℝ :=
  khat * mapG1 kh Qmax khat Mtotal +
    rearKappa2 kh * mapP1 Qmax khat Mtotal ^ 2

/-- The rear gauge cost cap corresponding to a front path of cost at most
`Mtotal`.  The selected-rear maximum principle loses the factor `mapK kh`, so
using `Mtotal` itself as both caps is not stable when `kh > 0`. -/
def mapRearCostCap (kh Mtotal : ℝ) : ℝ := mapK kh * Mtotal

/-- Fixed output ceilings evaluated at the honest rear cost cap. -/
def mapRearP1 (kh Qmax khat Mtotal : ℝ) : ℝ :=
  mapP1 Qmax khat (mapRearCostCap kh Mtotal)

def mapRearG1 (kh Qmax khat Mtotal : ℝ) : ℝ :=
  mapG1 kh Qmax khat (mapRearCostCap kh Mtotal)

def mapRearCg (kh Qmax khat Mtotal : ℝ) : ℝ :=
  mapCg kh Qmax khat (mapRearCostCap kh Mtotal)

theorem mapK_nonneg {kh : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    0 ≤ mapK kh := by
  exact (one_div_pos.mpr (Real.sqrt_pos.2 (by nlinarith))).le

theorem one_le_mapK {kh : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    1 ≤ mapK kh := by
  have hspos : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hsle : Real.sqrt (1 - kh ^ 2) ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
  rw [mapK, le_div_iff₀ hspos]
  simpa using hsle

/-- The genuinely upstream part of selected-rear path transport.

For every path in the fixed input class it supplies the raw gauge path, its
edge period `ell`, and accumulated cost parameter `M`.  The output is still in
the edge-dependent class produced by `GaugeMarkedDataOfRearFamily`; no
uniformization and no approximate `eta` bookkeeping is assumed here.

The exact canonical endpoints encode the marking-fixed conclusion.  Producing
this field from geometric data requires the appropriate tube, positive
pinching, selected-rear embeddedness, and a domain/cost restriction strong
enough to make the two uniform bounds possible. -/
structure Residual
    (P0 kh khat Qmax Mtotal c dlt : ℝ) : Prop where
  rawGauge : ∀ (p q : Data) (Gamma : NormalPath p q),
    IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
    IsVariableSpeedNormalPath P0 (mapRearP1 kh Qmax khat Mtotal) khat
      (mapRearG1 kh Qmax khat Mtotal) (mapRearCg kh Qmax khat Mtotal) Gamma →
    cost Gamma ≤ Mtotal →
    ∃ ell M : ℝ,
      0 ≤ ell ∧ ell ≤ Qmax ∧ 0 ≤ M ∧
      M ≤ mapRearCostCap kh Mtotal ∧
      ∃ Delta : NormalPath (SelectedInverseMap.selInv kh p)
          (SelectedInverseMap.selInv kh q),
        cost Delta ≤ mapK kh * cost Gamma ∧
        IsVariableSpeedNormalPath P0 (costP1 ell khat M) khat
          (costG1 ell khat (rearKappa2 kh) M)
          (khat * costG1 ell khat (rearKappa2 kh) M +
            rearKappa2 kh * costP1 ell khat M ^ 2) Delta

/-- Uniformize one raw selected-rear gauge output into exactly the same fixed
variable-speed class as its input. -/
theorem exists_map_path
    {P0 kh khat Qmax Mtotal c dlt : ℝ}
    (R : Residual P0 kh khat Qmax Mtotal c dlt)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hkhat : 0 ≤ khat)
    {p q : Data} (Gamma : NormalPath p q)
    (hpmem : IsTubeMember c 0 dlt p) (hqmem : IsTubeMember c 0 dlt q)
    (hGamma : IsVariableSpeedNormalPath P0 (mapRearP1 kh Qmax khat Mtotal) khat
      (mapRearG1 kh Qmax khat Mtotal) (mapRearCg kh Qmax khat Mtotal) Gamma)
    (hcostCap : cost Gamma ≤ Mtotal) :
    ∃ Delta : NormalPath (SelectedInverseMap.selInv kh p)
        (SelectedInverseMap.selInv kh q),
      cost Delta ≤ mapK kh * cost Gamma ∧
      IsVariableSpeedNormalPath P0 (mapRearP1 kh Qmax khat Mtotal) khat
        (mapRearG1 kh Qmax khat Mtotal) (mapRearCg kh Qmax khat Mtotal) Delta := by
  obtain ⟨ell, M, hell, hellQ, hM, hMM, hraw⟩ :=
    R.rawGauge p q Gamma hpmem hqmem hGamma hcostCap
  simpa only [mapRearP1, mapRearG1, mapRearCg] using
    (uniform_transport_of_raw_gauge Gamma hkh0 hkh1 hkhat
      hell hellQ hM hMM hraw)

/-- Family-free form matching the selected-inverse `hmap` hypothesis of
`ApproximatePaperAssemblyResidual`: the exact raw cost bound immediately
implies the requested bound with any positive slack. -/
theorem hmap_local
    {P0 kh khat Qmax Mtotal c dlt : ℝ}
    (R : Residual P0 kh khat Qmax Mtotal c dlt)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hkhat : 0 ≤ khat) :
    ∀ (p q : Data) (Gamma : NormalPath p q),
      IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
      IsVariableSpeedNormalPath P0 (mapRearP1 kh Qmax khat Mtotal) khat
        (mapRearG1 kh Qmax khat Mtotal) (mapRearCg kh Qmax khat Mtotal) Gamma →
      cost Gamma ≤ Mtotal →
      ∀ eta : ℝ, 0 < eta →
        ∃ Delta : NormalPath (SelectedInverseMap.selInv kh p)
            (SelectedInverseMap.selInv kh q),
          cost Delta ≤ mapK kh * cost Gamma + eta ∧
          IsVariableSpeedNormalPath P0 (mapRearP1 kh Qmax khat Mtotal) khat
            (mapRearG1 kh Qmax khat Mtotal) (mapRearCg kh Qmax khat Mtotal) Delta := by
  intro p q Gamma hpmem hqmem hGamma hcostCap eta heta
  obtain ⟨Delta, hcost, hDelta⟩ :=
    exists_map_path R hkh0 hkh1 hkhat Gamma hpmem hqmem hGamma hcostCap
  exact ⟨Delta, hcost.trans (le_add_of_nonneg_right heta.le), hDelta⟩

/-- A direct marked-distance route to the approximate map hypothesis.

The selected-rear comparison theorems bound `dist`, whereas the recursive
transport requires a path in one fixed variable-speed class.  The explicit
`hrealize` premise is the exact missing bridge: marked distance alone does not
upper-bound `pathDistVS`.  Once such a realization is available, no exact
terminal gauge marking is needed. -/
theorem hmap_local_of_dist_bound
    {P0 P1 kh G1 Cg c dlt : ℝ}
    (hne : ∀ p q : Data,
      ∃ Delta : NormalPath (SelectedInverseMap.selInv kh p)
          (SelectedInverseMap.selInv kh q),
        IsVariableSpeedNormalPath P0 P1 kh G1 Cg Delta)
    (hrealize : ∀ p q : Data,
      PathMetric.pathDistVS P0 P1 kh G1 Cg
          (SelectedInverseMap.selInv kh p) (SelectedInverseMap.selInv kh q) ≤
        dist (SelectedInverseMap.selInv kh p) (SelectedInverseMap.selInv kh q))
    (hdist : ∀ (p q : Data) (Gamma : NormalPath p q),
      IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
      IsVariableSpeedNormalPath P0 P1 kh G1 Cg Gamma →
      dist (SelectedInverseMap.selInv kh p) (SelectedInverseMap.selInv kh q) ≤
        mapK kh * cost Gamma) :
    ∀ (p q : Data) (Gamma : NormalPath p q),
      IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
      IsVariableSpeedNormalPath P0 P1 kh G1 Cg Gamma →
      ∀ eta : ℝ, 0 < eta →
        ∃ Delta : NormalPath (SelectedInverseMap.selInv kh p)
            (SelectedInverseMap.selInv kh q),
          cost Delta ≤ mapK kh * cost Gamma + eta ∧
          IsVariableSpeedNormalPath P0 P1 kh G1 Cg Delta := by
  intro p q Gamma hp hq hGamma eta heta
  obtain ⟨Delta, hDelta, hcost⟩ :=
    PathMetric.exists_variableSpeed_near_minimizer (hne p q) heta
  refine ⟨Delta, hcost.trans ?_, hDelta⟩
  simpa [add_comm] using add_le_add_right
    ((hrealize p q).trans (hdist p q Gamma hp hq hGamma)) eta

end SelectedInverseApproximateMapPath
