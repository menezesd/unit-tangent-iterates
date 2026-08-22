import Mathlib
import UnitTangentIterates.PinchedPathConcat

/-!
# The pinched path pseudometric, and the local Lipschitz bound

`PinchedPathBasic.lean` and `PinchedPathConcat.lean` prove the three
pseudometric axioms for the infimum `pinchedDist` of the costs of the paths
admissible for the `C²` estimate: it vanishes at an admissible curve, it is
symmetric, and it satisfies the triangle inequality.  This file records that
and feeds it back into the estimate.

The truncated infimum `SelInvTubePathDist.pinchedPathDist` carries the two
smallness conditions of the estimate inside the set over which it is taken,
which is what breaks the triangle inequality; here they are conditions on the
*distance* instead.  When `pinchedDist p q` is below both thresholds, the
near-minimizing admissible paths are themselves small enough for the estimate,
and one gets

`dist (selInv κ̂ q) (selInv κ̂ p) ≤ selInvLipUniversal … · pinchedDist κ̂ p q`,

a Lipschitz bound for a genuine pseudometric (`dist_selInv_le_pinchedDist`).

Main results: `pinchedDist_self`, `pinchedDist_comm`, `pinchedDist_triangle`
(restated as `IsPinchedPseudoMetric`), `dist_selInv_le_pinchedDist`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath

namespace PinchedPath

open RearOwnHigherRegularity FrontFromPath SelInvPathRegularityC2
  SelInvPathCurvatureC2 SelInvPathPerimC2 SelInvTubePathDist
  RearJacobiSourceCost SelInvLipUniversal GaugeMarkedDataOfRearFamily

variable {kminP kh : ℝ} {p q r : Data}

/-! ### The pseudometric axioms -/

/-- **The pinched pseudodistance is a pseudometric on the admissible curves**:
it vanishes at an admissible curve, it is symmetric, and it satisfies the
triangle inequality whenever the two sets of admissible costs are nonempty. -/
theorem isPinchedPseudoMetric (kminP kh : ℝ) :
    (∀ p : Data, IsPinchedCurve kminP kh p → pinchedDist kminP kh p p = 0) ∧
    (∀ p q : Data, pinchedDist kminP kh p q = pinchedDist kminP kh q p) ∧
    (∀ p q r : Data, (pinchedSet kminP kh p q).Nonempty →
      (pinchedSet kminP kh q r).Nonempty →
      pinchedDist kminP kh p r
        ≤ pinchedDist kminP kh p q + pinchedDist kminP kh q r) :=
  ⟨fun _ hc => pinchedDist_self hc, fun p q => pinchedDist_comm kminP kh p q,
    fun _ _ _ hpq hqr => pinchedDist_triangle hpq hqr⟩

/-! ### The Lipschitz bound -/

/-- An admissible path of cost as close as one likes to the pinched
pseudodistance, and small enough for the two smallness conditions of the `C²`
estimate. -/
theorem exists_small_pinchedPath {khat : ℝ}
    (hne : (pinchedSet kminP kh p q).Nonempty)
    (hlt1 : pinchedDist kminP kh p q < 1)
    (hltC : selInvCostConstUniversal kminP kh khat * pinchedDist kminP kh p q < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Γ : NormalPath p q, IsPinchedPath kminP kh Γ ∧
      cost Γ ≤ pinchedDist kminP kh p q + ε ∧ cost Γ ≤ 1 ∧
      selInvCostConstUniversal kminP kh khat * cost Γ ≤ 1 := by
  set d : ℝ := pinchedDist kminP kh p q with hdef
  set C : ℝ := selInvCostConstUniversal kminP kh khat with hCdef
  have hd0 : 0 ≤ d := pinchedDist_nonneg _ _ _ _
  have hCabs : 0 < |C| + 1 := by positivity
  set e : ℝ := min ε (min (1 - d) ((1 - C * d) / (|C| + 1))) with hedef
  have he1 : e ≤ ε := min_le_left _ _
  have he2 : e ≤ 1 - d := le_trans (min_le_right _ _) (min_le_left _ _)
  have he3 : e ≤ (1 - C * d) / (|C| + 1) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hepos : 0 < e := by
    refine lt_min hε (lt_min (by linarith) ?_)
    have : 0 < 1 - C * d := by linarith
    positivity
  obtain ⟨c, ⟨Γ, hc, hΓ⟩, hlt⟩ := exists_lt_of_csInf_lt hne
    (show d < d + e by linarith)
  refine ⟨Γ, hΓ, ?_, ?_, ?_⟩
  · rw [hc]; linarith
  · rw [hc]; linarith
  · have hcost : cost Γ ≤ d + e := by rw [hc]; linarith
    have hcnn : 0 ≤ cost Γ := Γ.cost_nonneg
    rcases le_or_gt C 0 with hC | hC
    · nlinarith
    · have hCle : C ≤ |C| := le_abs_self C
      have hnum : 0 ≤ 1 - C * d := by linarith
      have he3' : (|C| + 1) * e ≤ 1 - C * d := by
        rw [← le_div_iff₀' hCabs]
        exact he3
      nlinarith

/-- **Below the two thresholds the truncated and the untruncated infima
agree.**  The paths carrying the truncated infimum of `SelInvTubePathDist.lean`
are admissible, so it dominates `pinchedDist`; conversely the near-minimizing
admissible paths are then small enough to be counted in it. -/
theorem pinchedPathDist_eq_pinchedDist {khat : ℝ}
    (hne : (pinchedSet kminP kh p q).Nonempty)
    (hlt1 : pinchedDist kminP kh p q < 1)
    (hltC : selInvCostConstUniversal kminP kh khat * pinchedDist kminP kh p q < 1) :
    pinchedPathDist kminP kh khat p q = pinchedDist kminP kh p q := by
  have hne' : (pinchedCostSet kminP kh khat p q).Nonempty := by
    obtain ⟨Γ, hΓ, -, hcost, hsmall⟩ := exists_small_pinchedPath hne hlt1 hltC one_pos
    exact ⟨cost Γ, Γ, rfl, hΓ, hcost, hsmall⟩
  refine le_antisymm (le_of_forall_pos_le_add (fun ε hε => ?_))
    (pinchedDist_le_pinchedPathDist hne')
  obtain ⟨Γ, hΓ, hnear, hcost, hsmall⟩ := exists_small_pinchedPath hne hlt1 hltC hε
  exact le_trans (pinchedPathDist_le_cost Γ hΓ hcost hsmall) hnear

/-- **The selected inverse is Lipschitz for the pinched pseudometric**, with the
universal constant, on the range of distances for which the estimate applies. -/
theorem dist_selInv_le_pinchedDist {khat : ℝ}
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hpd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u)
    (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u)
    (hqd2 : ∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u)
    (hkh1 : kh < 1) (hkminP : 0 < kminP) (hkhat : rearKappa1 kh ≤ khat)
    (hne : (pinchedSet kminP kh p q).Nonempty)
    (hlt1 : pinchedDist kminP kh p q < 1)
    (hltC : selInvCostConstUniversal kminP kh khat * pinchedDist kminP kh p q < 1) :
    dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
      ≤ selInvLipUniversal kminP kh khat (perim (SelectedInverseMap.selInv kh p))
          (perim (SelectedInverseMap.selInv kh q)) * pinchedDist kminP kh p q := by
  have hkh0 : 0 ≤ kh := by
    obtain ⟨c, Γ, -, hΓ⟩ := hne
    exact le_trans hkminP.le (le_trans (hΓ.kmin 0 0) (hΓ.kmax 0 0))
  refine le_mul_of_near (selInvLipUniversal_nonneg hkminP hkh0 hkh1) (fun ε hε => ?_)
  obtain ⟨Γ, hΓ, hnear, hcost, hsmall⟩ := exists_small_pinchedPath hne hlt1 hltC hε
  refine ⟨cost Γ, hnear, ?_⟩
  exact dist_selInv_le_lipUniversal_cost Γ hpd hpd2 hqd hqd2 hkh1 hΓ.smooth hΓ.speed
    hΓ.per hΓ.normal hkminP hΓ.kmin hΓ.kmax hΓ.short hΓ.slit hΓ.rest hcost hkhat hsmall

end PinchedPath
