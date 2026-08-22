import Mathlib
import UnitTangentIterates.SelInvPathTubeBaseUniformC2
import UnitTangentIterates.SelInvModulusLinear
import UnitTangentIterates.PerimeterFromTurning

/-!
# The `C²` estimate with a constant that does not depend on the path

`SelInvPathTubeBaseC2.dist_selInv_le_modulus_of_path_tube_base_C2` produces the
two constants `P₀ ≤ L(t) ≤ P₁` pinching the perimeter of the slices from the
path itself — they are the minimum and the maximum of the perimeter along the
path — so the modulus it produces depends on the path and not only on the
geometry.  That is exactly what stands between the estimate and a bound with one
and the same constant along a family of paths.

It is not necessary.  The slices are closed curves of constant speed and turning
number one whose curvature is pinched by the hypotheses, so
`PerimeterFromTurning` pins their perimeter between the two *universal*
constants `2π/κ̂` and `2π/kminP`, and the uniform form of the estimate,
`SelInvPathTubeBaseUniformC2.dist_selInv_le_modulus_of_path_tube_base_uniform_C2`,
can be run with those.  The resulting modulus — and, in the linear form of
`SelInvModulusLinear`, the resulting Lipschitz constant — depends only on the
curvature pinching `kminP ≤ K̂ ≤ κ̂`, on the gauge `κ̂'` and on the perimeters of
the two selected inverses.

Main results: `dist_selInv_le_modulus_of_path_tube_base_perim_C2`,
`dist_selInv_le_lip_cost_perim`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathTubeBasePerimC2

open UniformFrameBounds RearOwnHigherRegularity FrontFromPath
  SelInvFrontCostC2 RearJacobiSourceCost SelInvFrontStripC2
  SelInvPathRegularityC2 SelInvPathCurvatureC2 SelInvPathCurvBoundC2
  SelInvPathPerimC2 SelInvPathGaugeC2 SelInvPathBoundsC2 SelInvPathTurningC2
  SelInvPathTubeC2 SelInvPathTubeBaseUniformC2 GaugeMarkedDataOfRearFamily
  SelInvFrontChangeVarC2 SelInvFrontVelocityC2 TurningNumberTube
  PerimeterFromTurning SelInvModulusLinear

variable {kh : ℝ}

/-- **The perimeter of the slices of a path with pinched slices is pinched by
universal constants.**  The slices are closed curves of constant speed whose
curvature lies between `kminP` and `κ̂`, and their turning number is one, so
their perimeter lies between `2π/κ̂` and `2π/kminP`. -/
theorem perim_pinch_of_path {p q : Data} (Γ : NormalPath p q) {kminP : ℝ}
    (hXC6 : ContDiff ℝ (6 : ℕ) (uncurry Γ.X))
    (hconst : ∀ t u, ‖(pathVel Γ.X) t u‖ = ‖pathVel Γ.X t 0‖)
    (hXper : ∀ t, Periodic (Γ.X t) 1)
    (hkminP : 0 < kminP)
    (hKnmin : ∀ t σ, kminP ≤ pathKn Γ.X (pathPerim Γ.X) t σ)
    (hKnk : ∀ t σ, pathKn Γ.X (pathPerim Γ.X) t σ ≤ kh)
    (hshort : ∀ t, kh * pathPerim Γ.X t < 4 * Real.pi)
    (hslit : ∀ t, pathVel Γ.X t 0 ∈ Complex.slitPlane) :
    (∀ t, 2 * Real.pi / kh ≤ pathPerim Γ.X t) ∧
      (∀ t, pathPerim Γ.X t ≤ 2 * Real.pi / kminP) := by
  have hkh0 : 0 < kh := lt_of_lt_of_le hkminP (le_trans (hKnmin 0 0) (hKnk 0 0))
  have hX2 : ContDiff ℝ (2 : ℕ) (uncurry Γ.X) := hXC6.of_le (by norm_num)
  have hXdiff : Differentiable ℝ (uncurry Γ.X) := hXC6.differentiable (by norm_num)
  have hVC : ContDiff ℝ ((1 : ℕ)) (uncurry (pathVel Γ.X)) :=
    contDiff_partialArc_self (n := 1) hX2
  have hVdiff : Differentiable ℝ (uncurry (pathVel Γ.X)) := hVC.differentiable (by norm_num)
  have hPpos : ∀ t, 0 < pathPerim Γ.X t :=
    fun t => norm_pos_iff.2 (Complex.slitPlane_ne_zero (hslit t))
  have hPne : ∀ t, pathPerim Γ.X t ≠ 0 := fun t => (hPpos t).ne'
  have hVper : ∀ t, Periodic (pathVel Γ.X t) 1 := periodic_partialArc hXdiff hXper
  have hAper : ∀ t, Periodic (pathAcc Γ.X t) 1 := periodic_partialArc hVdiff hVper
  have hslicec : ∀ t : ℝ, Continuous fun u : ℝ => ((t, u) : ℝ × ℝ) :=
    fun t => continuous_const.prodMk continuous_id
  have hVcont : ∀ t, Continuous (pathVel Γ.X t) := fun t => hVC.continuous.comp (hslicec t)
  have hAcont : ∀ t, Continuous (pathAcc Γ.X t) := fun t =>
    (contDiff_partialArc_self (n := 0) hVC).continuous.comp (hslicec t)
  have hAderiv : ∀ t u, HasDerivAt (pathVel Γ.X t) (pathAcc Γ.X t u) u :=
    fun t u => hasDerivAt_partialArc hVdiff t u
  have hlowc : ∀ t s, kminP ≤ curvOfPath (pathVel Γ.X) (pathAcc Γ.X) (pathPerim Γ.X) t s :=
    fun t s => by rw [curvOfPath_eq_pathKn hPne t s]; exact hKnmin t _
  have hhighc : ∀ t s, curvOfPath (pathVel Γ.X) (pathAcc Γ.X) (pathPerim Γ.X) t s ≤ kh :=
    fun t s => by rw [curvOfPath_eq_pathKn hPne t s]; exact hKnk t _
  have hturn : ∀ t, (∫ u in (0 : ℝ)..1,
      ((starRingEnd ℂ) ((pathVel Γ.X) t u) * (pathAcc Γ.X) t u).im / pathPerim Γ.X t ^ 2)
      = 2 * Real.pi :=
    fun t => turning_of_slice (hAderiv t) (hVper t) (hAper t) (hVcont t) (hAcont t)
      (fun u => hconst t u) (hPpos t) hkminP (hlowc t) (hhighc t) (hshort t)
  have hPcont : ContDiff ℝ ((0 : ℕ)) (pathPerim Γ.X) := by
    rw [Nat.cast_zero, contDiff_zero]
    have h : Continuous (uncurry (partialArc Γ.X)) :=
      (contDiff_partialArc_self (n := 1) hX2).continuous
    exact (h.comp (continuous_id.prodMk continuous_const)).norm
  have hKncont : ∀ t, Continuous (pathKn Γ.X (pathPerim Γ.X) t) := by
    intro t
    have h : ContDiff ℝ ((0 : ℕ)) (uncurry (pathKn Γ.X (pathPerim Γ.X))) :=
      contDiff_pathKn hPne (hVC.of_le (by norm_num))
        ((contDiff_partialArc_self (n := 0) hVC)) hPcont
    exact h.continuous.comp (hslicec t)
  exact ⟨fun t => perim_lower_of_pinch hkh0 (hPpos t) (hKncont t) (hturn t) (hKnk t),
    fun t => perim_upper_of_pinch hkminP (hPpos t) (hKncont t) (hturn t) (hKnmin t)⟩

/-- **The `C²` comparison of the two marked selected inverses at universal
perimeter bounds.**  The hypotheses are those of
`SelInvPathTubeBaseC2.dist_selInv_le_modulus_of_path_tube_base_C2`, but the
modulus is written with the two constants `2π/κ̂` and `2π/kminP`, which depend
only on the curvature pinching of the slices and not on the path. -/
theorem dist_selInv_le_modulus_of_path_tube_base_perim_C2 {p q : Data} (Γ : NormalPath p q)
    {kminP : ℝ}
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
    (hmark : ∀ t, Γ.eta t 0 = 0) :
    ∃ dn δ : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t)
        ((pathPerim Γ.X) t * (pathKn Γ.X (pathPerim Γ.X) t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / (pathPerim Γ.X) t)) ∧
      ∀ (khat : ℝ),
        rearKappa1 kh ≤ khat →
        RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
            (rearArclength (δ 0) ((pathPerim Γ.X) 0))
            (jacobiSourceConst kh (2 * Real.pi / kh)) * cost Γ ≤ 1 →
      dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
        ≤ selInvFrontModulus (2 * Real.pi / kminP) kh
            (perim (SelectedInverseMap.selInv kh p))
            (perim (SelectedInverseMap.selInv kh q)) (kh / Real.sqrt (1 - kh ^ 2))
            (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)
            (pathPv0 kh (2 * Real.pi / kh) khat
              (2 * Real.pi / kminP * (kh / (1 - kh ^ 2)))) khat
            (jacobiSourceConst kh (2 * Real.pi / kh)) (cost Γ) := by
  have hkh0 : 0 < kh := lt_of_lt_of_le hkminP (le_trans (hKnmin 0 0) (hKnk 0 0))
  obtain ⟨hPl, hPu⟩ := perim_pinch_of_path Γ hXC6 hconst hXper hkminP hKnmin hKnk hshort hslit
  have hP0 : 0 < 2 * Real.pi / kh := by positivity
  exact dist_selInv_le_modulus_of_path_tube_base_uniform_C2 Γ hpd hpd2 hqd hqd2 hkh1
    hP0 hPl hPu hXC6 hconst hXper hnu hkminP hKnmin hKnk hshort hslit hmark

/-- **The `C²` estimate as a Lipschitz bound with a constant that does not
depend on the path.**  For a normal path of cost at most one satisfying the
purely geometric hypotheses above, the marked distance of the two selected
inverses is at most `selInvFrontLip …` times the cost of the path, and the
constant depends only on the curvature pinching `kminP ≤ K̂ ≤ κ̂`, on the gauge
`κ̂'` and on the perimeters of the two selected inverses — not on the path. -/
theorem dist_selInv_le_lip_cost_perim {p q : Data} (Γ : NormalPath p q) {kminP : ℝ}
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
    (hcost : cost Γ ≤ 1) :
    ∃ dn δ : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t)
        ((pathPerim Γ.X) t * (pathKn Γ.X (pathPerim Γ.X) t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / (pathPerim Γ.X) t)) ∧
      ∀ (khat : ℝ),
        rearKappa1 kh ≤ khat →
        RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
            (rearArclength (δ 0) ((pathPerim Γ.X) 0))
            (jacobiSourceConst kh (2 * Real.pi / kh)) * cost Γ ≤ 1 →
      dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
        ≤ selInvFrontLip (2 * Real.pi / kminP) kh
            (perim (SelectedInverseMap.selInv kh p))
            (perim (SelectedInverseMap.selInv kh q)) (kh / Real.sqrt (1 - kh ^ 2))
            (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)
            (pathPv0 kh (2 * Real.pi / kh) khat
              (2 * Real.pi / kminP * (kh / (1 - kh ^ 2)))) khat
            (jacobiSourceConst kh (2 * Real.pi / kh)) * cost Γ := by
  have hkh0 : 0 < kh := lt_of_lt_of_le hkminP (le_trans (hKnmin 0 0) (hKnk 0 0))
  obtain ⟨dn, δ, hdnper, hstrip, hsol, hδ, hbound⟩ :=
    dist_selInv_le_modulus_of_path_tube_base_perim_C2 Γ hpd hpd2 hqd hqd2 hkh1 hXC6
      hconst hXper hnu hkminP hKnmin hKnk hshort hslit hmark
  refine ⟨dn, δ, hdnper, hstrip, hsol, hδ, ?_⟩
  intro khat hkhat hsmall
  have hP1nn : (0 : ℝ) ≤ 2 * Real.pi / kminP := by positivity
  have hP0pos : (0 : ℝ) < 2 * Real.pi / kh := by positivity
  have hkap1 : 0 ≤ rearKappa1 kh := by
    unfold rearKappa1
    exact kappa1_nonneg hkh0.le hkh1
  have hkhat0 : 0 ≤ khat := le_trans hkap1 hkhat
  have hrr : 0 ≤ 2 * Real.pi / kminP * (kh / (1 - kh ^ 2)) :=
    mul_nonneg hP1nn (kappa1_nonneg hkh0.le hkh1)
  have hPv0 : 0 ≤ pathPv0 kh (2 * Real.pi / kh) khat
      (2 * Real.pi / kminP * (kh / (1 - kh ^ 2))) :=
    (pathPv0_pos hP0pos hkh0.le hkhat0 hrr).le
  have hellnn : 0 ≤ perim (SelectedInverseMap.selInv kh p) := norm_nonneg _
  have hLnn : 0 ≤ perim (SelectedInverseMap.selInv kh q) := norm_nonneg _
  have hkbnn : 0 ≤ kh / Real.sqrt (1 - kh ^ 2) := by positivity
  have hkLnn : 0 ≤ 2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3 := by positivity
  exact le_trans (hbound khat hkhat hsmall)
    (selInvFrontModulus_le_lip hP1nn hkh0.le hkh1 hellnn hLnn hkbnn hkLnn hPv0 hkhat0
      Γ.cost_nonneg hcost)

end SelInvPathTubeBasePerimC2
