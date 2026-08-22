import Mathlib
import UnitTangentIterates.SelInvPathTubeBasePerimC2
import UnitTangentIterates.SelInvLipschitzPathDist

/-!
# A Lipschitz bound for the selected inverse with a universal constant

`SelInvPathTubeBasePerimC2.dist_selInv_le_lip_cost_perim` writes the `C²`
estimate with a Lipschitz constant built from the two universal perimeter
bounds `2π/κ̂` and `2π/kminP`.  One trace of the path is left in it: the
smallness condition on the cost is written with the rear arclength
`rearArclength (δ 0) L(0)` of the selected rear of the initial slice, a quantity
produced by the estimate itself.

That trace is removed here.  The steering angle takes its values in
`[0, arcsin κ̂] ⊂ [0, π/2]`, so the rear arclength of one period is between `0`
and the perimeter of the slice, hence at most `2π/kminP`; and `rearCostConst` is
monotone in that argument.  So the smallness condition written with `2π/kminP`
— a condition on the curvature pinching, the gauge and the cost alone — implies
the one the estimate asks for.

The estimate then reads: for a normal path of cost at most one whose slices are
pinched, `dist (selInv κ̂ q) (selInv κ̂ p) ≤ selInvLipUniversal … · cost Γ` with a
constant depending only on `kminP`, `κ̂`, `κ̂'` and the perimeters of the two
selected inverses (`dist_selInv_le_lipUniversal_cost`).  Since the constant does
not depend on the path, the passage of `SelInvLipschitzPathDist` applies
verbatim, and along a cost-minimizing sequence of such paths one gets the
Lipschitz bound in the path pseudodistance,
`dist (selInv κ̂ q) (selInv κ̂ p) ≤ selInvLipUniversal … · pathDist p q`
(`dist_selInv_le_lipUniversal_pathDist`).

What is *not* proved here — the last step to non-expansiveness of the selected
inverse — is that the constant `selInvLipUniversal` is at most one; the constant
produced by the chain of estimates is explicit but large.

Main results: `selInvLipUniversal`, `selInvCostConstUniversal`,
`dist_selInv_le_lipUniversal_cost`, `dist_selInv_le_lipUniversal_pathDist`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse

namespace SelInvLipUniversal

open UniformFrameBounds RearOwnHigherRegularity FrontFromPath
  SelInvFrontCostC2 RearJacobiSourceCost GaugeFlowDerivCost
  SelInvPathRegularityC2 SelInvPathCurvatureC2 SelInvPathPerimC2 SelInvPathGaugeC2
  GaugeMarkedDataOfRearFamily SelInvModulusLinear SelInvPathTubeBasePerimC2
  SelInvLipschitzPathDist RearCostDensity

variable {kh : ℝ}

/-! ### The rear arclength of one period is between zero and the perimeter -/

/-- The rear arclength of a steering angle with values in `[0, π/2]` is
nonnegative. -/
theorem rearArclength_nonneg {dl : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hmem : ∀ s, dl s ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ rearArclength dl L := by
  refine intervalIntegral.integral_nonneg hL (fun u _ => ?_)
  refine Real.cos_nonneg_of_mem_Icc ⟨?_, (hmem u).2⟩
  linarith [(hmem u).1, Real.pi_pos]

/-- The rear arclength of one period is at most the perimeter of the slice. -/
theorem rearArclength_le {dl : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hc : Continuous dl) :
    rearArclength dl L ≤ L := by
  have hint : IntervalIntegrable (fun u => Real.cos (dl u)) volume 0 L :=
    (Real.continuous_cos.comp hc).intervalIntegrable 0 L
  have hle : (∫ u in (0 : ℝ)..L, Real.cos (dl u)) ≤ ∫ _u in (0 : ℝ)..L, (1 : ℝ) :=
    intervalIntegral.integral_mono_on hL hint _root_.intervalIntegrable_const
      (fun u _ => Real.cos_le_one _)
  simpa [rearArclength] using hle

/-! ### The cost constant is monotone in the rear arclength -/

theorem costP1_mono_ell {ell ell' khat M : ℝ} (h : ell ≤ ell') :
    costP1 ell khat M ≤ costP1 ell' khat M :=
  mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

theorem costG1_mono_ell {ell ell' khat kappa2 M : ℝ} (hell : 0 ≤ ell) (hk2 : 0 ≤ kappa2)
    (hM : 0 ≤ M) (h : ell ≤ ell') :
    costG1 ell khat kappa2 M ≤ costG1 ell' khat kappa2 M := by
  have h1 : costP1 ell khat M ≤ costP1 ell' khat M := costP1_mono_ell h
  have h0 : 0 ≤ costP1 ell khat M := SelInvModulusLinear.costP1_nonneg hell
  have hsq : costP1 ell khat M ^ 2 ≤ costP1 ell' khat M ^ 2 := by nlinarith
  unfold costG1
  exact mul_le_mul_of_nonneg_right hsq (mul_nonneg hk2 hM)

/-- **The constant of the rear cost is monotone in the rear arclength.** -/
theorem rearCostConst_mono_ell {khat kappa2 ell ell' dd : ℝ} (hell : 0 ≤ ell)
    (hk2 : 0 ≤ kappa2) (hdd : 0 ≤ dd) (h : ell ≤ ell') :
    rearCostConst kh khat kappa2 ell dd ≤ rearCostConst kh khat kappa2 ell' dd := by
  have hA : (0 : ℝ) ≤ 1 / Real.sqrt (1 - kh ^ 2) := by positivity
  have hp1 : costP1 ell khat 1 ≤ costP1 ell' khat 1 := costP1_mono_ell h
  have hp10 : 0 ≤ costP1 ell khat 1 := SelInvModulusLinear.costP1_nonneg hell
  have hg1 : costG1 ell khat kappa2 1 ≤ costG1 ell' khat kappa2 1 :=
    costG1_mono_ell hell hk2 zero_le_one h
  have h2 : 2 * costP1 ell khat 1 * (1 / Real.sqrt (1 - kh ^ 2))
      ≤ 2 * costP1 ell' khat 1 * (1 / Real.sqrt (1 - kh ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hp1 (by norm_num : (0:ℝ) ≤ 2)
    exact mul_le_mul_of_nonneg_right this hA
  have hsq : costP1 ell khat 1 ^ 2 ≤ costP1 ell' khat 1 ^ 2 := by nlinarith
  have h3 : (dd + 2 * (1 / Real.sqrt (1 - kh ^ 2))) * costP1 ell khat 1 ^ 2
        + 2 * costG1 ell khat kappa2 1 * (1 / Real.sqrt (1 - kh ^ 2))
      ≤ (dd + 2 * (1 / Real.sqrt (1 - kh ^ 2))) * costP1 ell' khat 1 ^ 2
        + 2 * costG1 ell' khat kappa2 1 * (1 / Real.sqrt (1 - kh ^ 2)) := by
    have hfac : (0 : ℝ) ≤ dd + 2 * (1 / Real.sqrt (1 - kh ^ 2)) := by linarith
    have ha := mul_le_mul_of_nonneg_left hsq hfac
    have hb : 2 * costG1 ell khat kappa2 1 * (1 / Real.sqrt (1 - kh ^ 2))
        ≤ 2 * costG1 ell' khat kappa2 1 * (1 / Real.sqrt (1 - kh ^ 2)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hg1 (by norm_num : (0:ℝ) ≤ 2)) hA
    linarith
  unfold rearCostConst
  exact max_le_max le_rfl (max_le_max h2 h3)

/-! ### The universal constants -/

/-- **The universal Lipschitz constant of the selected inverse**: the constant
of `SelInvModulusLinear.selInvFrontLip` evaluated at the two universal perimeter
bounds `2π/kminP` and `2π/κ̂` of a slice of curvature pinched between `kminP`
and `κ̂`.  It depends on the curvature pinching, on the gauge `κ̂'` and on the
perimeters `ell`, `L` of the two selected inverses only. -/
def selInvLipUniversal (kminP kh khat ell L : ℝ) : ℝ :=
  selInvFrontLip (2 * Real.pi / kminP) kh ell L (kh / Real.sqrt (1 - kh ^ 2))
    (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)
    (pathPv0 kh (2 * Real.pi / kh) khat (2 * Real.pi / kminP * (kh / (1 - kh ^ 2)))) khat
    (jacobiSourceConst kh (2 * Real.pi / kh))

/-- **The universal constant of the smallness condition on the cost.** -/
def selInvCostConstUniversal (kminP kh khat : ℝ) : ℝ :=
  rearCostConst kh khat (rearKappa2 kh) (2 * Real.pi / kminP)
    (jacobiSourceConst kh (2 * Real.pi / kh))

theorem selInvLipUniversal_nonneg {kminP khat ell L : ℝ} (hkminP : 0 < kminP)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    0 ≤ selInvLipUniversal kminP kh khat ell L :=
  selInvFrontLip_nonneg (by positivity) hkh0 hkh1

/-! ### The estimate with the universal constant -/

/-- **The `C²` estimate with a Lipschitz constant that depends only on the
geometry.**  For a normal path of cost at most one whose slices are closed
curves of constant speed with curvature pinched between `kminP` and `κ̂`, and
whose marked point is at rest, the marked distance of the two selected inverses
is at most `selInvLipUniversal` times the cost of the path. -/
theorem dist_selInv_le_lipUniversal_cost {p q : Data} (Γ : NormalPath p q) {kminP khat : ℝ}
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hpd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u)
    (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u)
    (hqd2 : ∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u)
    (hkh1 : kh < 1)
    (hXC6 : ContDiff ℝ (6 : ℕ) (uncurry Γ.X))
    (hconst : ∀ t u, ‖(pathVel Γ.X) t u‖ = ‖pathVel Γ.X t 0‖)
    (hXper : ∀ t, Periodic (Γ.X t) 1)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / ((pathPerim Γ.X) t : ℂ)))
    (hkminP : 0 < kminP)
    (hKnmin : ∀ t σ, kminP ≤ pathKn Γ.X (pathPerim Γ.X) t σ)
    (hKnk : ∀ t σ, pathKn Γ.X (pathPerim Γ.X) t σ ≤ kh)
    (hshort : ∀ t, kh * pathPerim Γ.X t < 4 * Real.pi)
    (hslit : ∀ t, pathVel Γ.X t 0 ∈ Complex.slitPlane)
    (hmark : ∀ t, Γ.eta t 0 = 0)
    (hcost : cost Γ ≤ 1)
    (hkhat : rearKappa1 kh ≤ khat)
    (hsmall : selInvCostConstUniversal kminP kh khat * cost Γ ≤ 1) :
    dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
      ≤ selInvLipUniversal kminP kh khat (perim (SelectedInverseMap.selInv kh p))
          (perim (SelectedInverseMap.selInv kh q)) * cost Γ := by
  have hkh0 : 0 < kh := lt_of_lt_of_le hkminP (le_trans (hKnmin 0 0) (hKnk 0 0))
  obtain ⟨-, hPu⟩ :=
    perim_pinch_of_path Γ hXC6 hconst hXper hkminP hKnmin hKnk hshort hslit
  have hPpos : ∀ t, 0 < pathPerim Γ.X t :=
    fun t => norm_pos_iff.2 (Complex.slitPlane_ne_zero (hslit t))
  obtain ⟨dn, δ, -, hstrip, hsol, hδ, hbound⟩ :=
    dist_selInv_le_lip_cost_perim Γ hpd hpd2 hqd hqd2 hkh1 hXC6 hconst hXper hnu
      hkminP hKnmin hKnk hshort hslit hmark hcost
  -- the steering angle of the initial slice is continuous with values in `[0, π/2]`
  have hdndiff : Differentiable ℝ (dn 0) := fun σ => (hsol 0 σ).differentiableAt
  have hdncont : Continuous (dn 0) := hdndiff.continuous
  have hδcont : Continuous (δ 0) := by
    have h : δ 0 = fun s => dn 0 (s / pathPerim Γ.X 0) := funext (fun s => hδ 0 s)
    rw [h]
    exact hdncont.comp (continuous_id.div_const _)
  have hδmem : ∀ s, δ 0 s ∈ Icc (0 : ℝ) (Real.pi / 2) := by
    intro s
    rw [hδ 0 s]
    refine ⟨(hstrip 0 _).1, le_trans (hstrip 0 _).2 ?_⟩
    exact Real.arcsin_le_pi_div_two _
  -- so the rear arclength of one period is between zero and `2π/kminP`
  have hL0 : (0 : ℝ) ≤ pathPerim Γ.X 0 := (hPpos 0).le
  have hell0 : 0 ≤ rearArclength (δ 0) (pathPerim Γ.X 0) :=
    rearArclength_nonneg hL0 hδmem
  have hellle : rearArclength (δ 0) (pathPerim Γ.X 0) ≤ 2 * Real.pi / kminP :=
    le_trans (rearArclength_le hL0 hδcont) (hPu 0)
  -- hence the smallness condition of the estimate follows from the universal one
  have hdd : 0 ≤ jacobiSourceConst kh (2 * Real.pi / kh) :=
    jacobiSourceConst_nonneg (by positivity)
  have hk2 : 0 ≤ rearKappa2 kh := rearKappa2_nonneg hkh0.le hkh1
  have hmono : rearCostConst kh khat (rearKappa2 kh)
        (rearArclength (δ 0) (pathPerim Γ.X 0)) (jacobiSourceConst kh (2 * Real.pi / kh))
      ≤ selInvCostConstUniversal kminP kh khat :=
    rearCostConst_mono_ell hell0 hk2 hdd hellle
  have hsmall' : rearCostConst kh khat (rearKappa2 kh)
      (rearArclength (δ 0) (pathPerim Γ.X 0))
      (jacobiSourceConst kh (2 * Real.pi / kh)) * cost Γ ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right hmono Γ.cost_nonneg) hsmall
  exact hbound khat hkhat hsmall'

/-- **The Lipschitz bound for the selected inverse in the path
pseudodistance.**  If `p` and `q` are joined by normal paths of cost arbitrarily
close to `pathDist p q`, each of cost at most one, satisfying the geometric
hypotheses of the `C²` estimate with one and the same curvature pinching, then

`dist (selInv κ̂ q) (selInv κ̂ p) ≤ selInvLipUniversal … · pathDist p q` .

The constant is the universal one: it does not depend on the paths. -/
theorem dist_selInv_le_lipUniversal_pathDist {p q : Data} {kminP khat : ℝ}
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u)
    (hpd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u)
    (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u)
    (hqd2 : ∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u)
    (hkh1 : kh < 1) (hkminP : 0 < kminP)
    (hkhat : rearKappa1 kh ≤ khat)
    (h : ∀ ε > 0, ∃ Γ : NormalPath p q,
      cost Γ ≤ pathDist p q + ε ∧ cost Γ ≤ 1 ∧
      ContDiff ℝ (6 : ℕ) (uncurry Γ.X) ∧
      (∀ t u, ‖(pathVel Γ.X) t u‖ = ‖pathVel Γ.X t 0‖) ∧
      (∀ t, Periodic (Γ.X t) 1) ∧
      (∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / ((pathPerim Γ.X) t : ℂ))) ∧
      (∀ t σ, kminP ≤ pathKn Γ.X (pathPerim Γ.X) t σ) ∧
      (∀ t σ, pathKn Γ.X (pathPerim Γ.X) t σ ≤ kh) ∧
      (∀ t, kh * pathPerim Γ.X t < 4 * Real.pi) ∧
      (∀ t, pathVel Γ.X t 0 ∈ Complex.slitPlane) ∧
      (∀ t, Γ.eta t 0 = 0) ∧
      selInvCostConstUniversal kminP kh khat * cost Γ ≤ 1) :
    dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
      ≤ selInvLipUniversal kminP kh khat (perim (SelectedInverseMap.selInv kh p))
          (perim (SelectedInverseMap.selInv kh q)) * pathDist p q := by
  have hkh0 : 0 ≤ kh := by
    obtain ⟨Γ, -, -, -, -, -, -, hKnmin, hKnk, -, -, -, -⟩ := h 1 one_pos
    exact le_trans hkminP.le (le_trans (hKnmin 0 0) (hKnk 0 0))
  refine dist_selInv_le_mul_pathDist (selInvLipUniversal_nonneg hkminP hkh0 hkh1)
    (fun ε hε => ?_)
  obtain ⟨Γ, hnear, hcost, hXC6, hconst, hXper, hnu, hKnmin, hKnk, hshort, hslit,
    hmark, hsmall⟩ := h ε hε
  exact ⟨Γ, hnear, dist_selInv_le_lipUniversal_cost Γ hpd hpd2 hqd hqd2 hkh1 hXC6 hconst
    hXper hnu hkminP hKnmin hKnk hshort hslit hmark hcost hkhat hsmall⟩

end SelInvLipUniversal
