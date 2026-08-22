import Mathlib
import UnitTangentIterates.SelInvLipUniversal

/-!
# The selected inverse is Lipschitz for the pinched path pseudodistance

`SelInvLipUniversal.dist_selInv_le_lipUniversal_pathDist` is stated with a
hypothesis quantified over `ε`: it asks for normal paths of cost arbitrarily
close to `pathDist p q` satisfying the geometric hypotheses of the `C²`
estimate.  That hypothesis is exactly the statement that the *constrained*
infimum — the infimum of the costs of the paths whose slices are pinched — is
the pseudodistance itself.

Here the constrained infimum is made into a pseudodistance of its own.
`IsPinchedPath kminP κ̂ Γ` collects the geometric hypotheses of the estimate,
`pinchedCostSet` is the set of costs of the admissible paths and
`pinchedPathDist` its infimum.  It dominates the path pseudodistance
(`pathDist_le_pinchedPathDist`), and the selected inverse is Lipschitz for it,
with the universal constant and with no hypothesis beyond the existence of one
admissible path (`dist_selInv_le_lipUniversal_pinchedPathDist`).

What separates this from non-expansiveness of the selected inverse is
unchanged: the constant has to be at most one, and the pinched paths have to be
cost-minimizing among all normal paths.

Main results: `IsPinchedPath`, `pinchedPathDist`, `pathDist_le_pinchedPathDist`,
`dist_selInv_le_lipUniversal_pinchedPathDist`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse

namespace SelInvTubePathDist

open UniformFrameBounds FrontFromPath RearJacobiSourceCost
  SelInvPathRegularityC2 SelInvPathCurvatureC2 SelInvPathPerimC2
  GaugeMarkedDataOfRearFamily SelInvModulusLinear SelInvLipUniversal

variable {kh : ℝ}

/-- **An admissible path for the `C²` estimate**: a normal path whose slices are
closed curves of constant speed with curvature pinched between `kminP` and `κ̂`,
short enough for the selected rear to be defined, moving along their own normal
and with their marked point at rest. -/
structure IsPinchedPath {p q : Data} (kminP kh : ℝ) (Γ : NormalPath p q) : Prop where
  /-- the family of slices is `C⁶` -/
  smooth : ContDiff ℝ (6 : ℕ) (uncurry Γ.X)
  /-- each slice has constant speed -/
  speed : ∀ t u, ‖(pathVel Γ.X) t u‖ = ‖pathVel Γ.X t 0‖
  /-- each slice is a closed curve -/
  per : ∀ t, Periodic (Γ.X t) 1
  /-- the path moves along the unit normal of its slices -/
  normal : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / ((pathPerim Γ.X) t : ℂ))
  /-- the curvature of the slices is at least `kminP` -/
  kmin : ∀ t σ, kminP ≤ pathKn Γ.X (pathPerim Γ.X) t σ
  /-- the curvature of the slices is at most `κ̂` -/
  kmax : ∀ t σ, pathKn Γ.X (pathPerim Γ.X) t σ ≤ kh
  /-- the slices are short -/
  short : ∀ t, kh * pathPerim Γ.X t < 4 * Real.pi
  /-- the velocity at the marked point avoids the slit -/
  slit : ∀ t, pathVel Γ.X t 0 ∈ Complex.slitPlane
  /-- the marked point of the path is at rest -/
  rest : ∀ t, Γ.eta t 0 = 0

/-- The set of costs of the admissible paths of cost small enough for the
estimate. -/
def pinchedCostSet (kminP kh khat : ℝ) (p q : Data) : Set ℝ :=
  {c | ∃ Γ : NormalPath p q, cost Γ = c ∧ IsPinchedPath kminP kh Γ ∧ cost Γ ≤ 1 ∧
    selInvCostConstUniversal kminP kh khat * cost Γ ≤ 1}

theorem bddBelow_pinchedCostSet (kminP kh khat : ℝ) (p q : Data) :
    BddBelow (pinchedCostSet kminP kh khat p q) := by
  refine ⟨0, ?_⟩
  rintro c ⟨Γ, rfl, -, -, -⟩
  exact Γ.cost_nonneg

/-- **The pinched path pseudodistance**: the infimum of the costs of the
admissible paths joining two marked curves. -/
def pinchedPathDist (kminP kh khat : ℝ) (p q : Data) : ℝ :=
  sInf (pinchedCostSet kminP kh khat p q)

theorem pinchedPathDist_nonneg (kminP kh khat : ℝ) (p q : Data) :
    0 ≤ pinchedPathDist kminP kh khat p q := by
  refine Real.sInf_nonneg ?_
  rintro c ⟨Γ, rfl, -, -, -⟩
  exact Γ.cost_nonneg

theorem pinchedPathDist_le_cost {p q : Data} {kminP khat : ℝ} (Γ : NormalPath p q)
    (hΓ : IsPinchedPath kminP kh Γ) (hcost : cost Γ ≤ 1)
    (hsmall : selInvCostConstUniversal kminP kh khat * cost Γ ≤ 1) :
    pinchedPathDist kminP kh khat p q ≤ cost Γ :=
  csInf_le (bddBelow_pinchedCostSet kminP kh khat p q) ⟨Γ, rfl, hΓ, hcost, hsmall⟩

/-- **The pinched pseudodistance dominates the path pseudodistance**: the
admissible paths are normal paths. -/
theorem pathDist_le_pinchedPathDist {p q : Data} {kminP khat : ℝ}
    (hne : (pinchedCostSet kminP kh khat p q).Nonempty) :
    pathDist p q ≤ pinchedPathDist kminP kh khat p q := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨c, ⟨Γ, hc, -, -, -⟩, hlt⟩ := exists_lt_of_csInf_lt hne
    (show pinchedPathDist kminP kh khat p q < pinchedPathDist kminP kh khat p q + ε by
      linarith)
  have := pathDist_le_cost Γ
  rw [hc] at this
  linarith

/-- A quantity bounded by `C` times numbers arbitrarily close to `D` from above
is bounded by `C · D`. -/
theorem le_mul_of_near {d C D : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε > 0, ∃ c : ℝ, c ≤ D + ε ∧ d ≤ C * c) : d ≤ C * D := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hCpos : 0 < C + 1 := by linarith
  have hεpos : 0 < ε / (C + 1) := by positivity
  obtain ⟨c, hcle, hd⟩ := h (ε / (C + 1)) hεpos
  have h1 : C * c ≤ C * (D + ε / (C + 1)) := mul_le_mul_of_nonneg_left hcle hC
  have h2 : C * (ε / (C + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hCpos]
    nlinarith
  nlinarith [hd, h1, h2]

/-- **The selected inverse is Lipschitz for the pinched path pseudodistance**,
with the universal constant of `SelInvLipUniversal`.  The only hypothesis is
that the two fronts are joined by at least one admissible path. -/
theorem dist_selInv_le_lipUniversal_pinchedPathDist {p q : Data} {kminP khat : ℝ}
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hpd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u)
    (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u)
    (hqd2 : ∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u)
    (hkh1 : kh < 1) (hkminP : 0 < kminP) (hkhat : rearKappa1 kh ≤ khat)
    (hne : (pinchedCostSet kminP kh khat p q).Nonempty) :
    dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
      ≤ selInvLipUniversal kminP kh khat (perim (SelectedInverseMap.selInv kh p))
          (perim (SelectedInverseMap.selInv kh q)) * pinchedPathDist kminP kh khat p q := by
  have hkh0 : 0 ≤ kh := by
    obtain ⟨c, Γ, -, hΓ, -, -⟩ := hne
    exact le_trans hkminP.le (le_trans (hΓ.kmin 0 0) (hΓ.kmax 0 0))
  refine le_mul_of_near (selInvLipUniversal_nonneg hkminP hkh0 hkh1) (fun ε hε => ?_)
  obtain ⟨c, ⟨Γ, hc, hΓ, hcost, hsmall⟩, hlt⟩ := exists_lt_of_csInf_lt hne
    (show pinchedPathDist kminP kh khat p q < pinchedPathDist kminP kh khat p q + ε by
      linarith)
  refine ⟨c, hlt.le, ?_⟩
  rw [← hc]
  exact dist_selInv_le_lipUniversal_cost Γ hpd hpd2 hqd hqd2 hkh1 hΓ.smooth hΓ.speed
    hΓ.per hΓ.normal hkminP hΓ.kmin hΓ.kmax hΓ.short hΓ.slit hΓ.rest hcost hkhat hsmall

end SelInvTubePathDist
