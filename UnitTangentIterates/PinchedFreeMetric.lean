import Mathlib
import UnitTangentIterates.PinchedPathConcat
import UnitTangentIterates.PinchedPathMoving

/-!
# The corrected admissible class and its pseudometric

`PinchedPathRigidity.lean` shows that the class `SelInvTubePathDist.IsPinchedPath`
of paths admissible for the `C²` selected-inverse estimate is *rigid*: such a
path is stationary, so the pseudodistance `PinchedPath.pinchedDist` built from it
is identically zero and the Lipschitz statements proved against it are empty.
`PinchedPathMoving.lean` isolates the responsible hypothesis: it is the
conjunction of the constant speed of the slices with the resting marked point
that is empty, neither condition being restrictive on its own.

This file starts the repair on the side of the metric.  It drops the resting
marked point from the admissible class — the remaining conditions are those of
`PinchedPathMoving.IsPinchedPathFree` — and rebuilds the pseudometric for that
larger class:

* the reversal, the flattening and the concatenation of free-admissible paths
  are free-admissible (`isPinchedPathFree_reverse`, `isPinchedPathFree_slow`,
  `isPinchedPathFree_concatSlow`), so `freeDist` is symmetric and satisfies the
  triangle inequality, and it vanishes at an admissible curve;
* `freeDist` is dominated by `PinchedPath.pinchedDist` and dominates
  `PathMetric.pathDist`, and it dominates the pointwise displacement of the two
  curves (`norm_sub_le_freeDist`);
* it is **not** identically zero: the dilating circle joins the marked circles
  of radii `r` and `r + a` (`0 < a < r`) at cost `a`, and the displacement bound
  is exactly `a`, so `freeDist (1/(r+a)) (1/r) (circleData r) (circleData (r+a)) = a`
  (`freeDist_circleData`).

So the class dropped one hypothesis and became a genuine — non-degenerate —
pseudometric, in contrast with `PinchedPath.pinchedDist`, which
`PinchedPathRigidity.pinchedDist_eq_zero` shows to be identically zero.

Main results: `freeDist`, `freeDist_comm`, `freeDist_self`, `freeDist_triangle`,
`norm_sub_le_freeDist`, `freeDist_circleData`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath

namespace PinchedFree

open PinchedPath PinchedPathMoving SelInvTubePathDist SelInvPathRegularityC2
  SelInvPathCurvatureC2 SelInvPathPerimC2 FrontFromPath

variable {kminP kh : ℝ} {p q r : Data}

/-! ### The three structural operations preserve the class -/

/-- **The reversal of a free-admissible path is free-admissible.** -/
theorem isPinchedPathFree_reverse (Γ : NormalPath p q) (hΓ : IsPinchedPathFree kminP kh Γ) :
    IsPinchedPathFree kminP kh (PathMetric.NormalPath.reverse Γ) := by
  have hX6 : ContDiff ℝ (6 : ℕ) (uncurry Γ.X) := hΓ.smooth
  have hX2 : ContDiff ℝ (2 : ℕ) (uncurry Γ.X) := hX6.of_le (by norm_num)
  have hd : Differentiable ℝ (uncurry Γ.X) := hX2.differentiable (by norm_num)
  refine
    { smooth := contDiff_uncurry_timeSub hX6 Γ.T
      speed := fun t u => ?_
      per := fun t => hΓ.per (Γ.T - t)
      normal := fun t u => ?_
      kmin := fun t σ => ?_
      kmax := fun t σ => ?_
      short := fun t => ?_
      slit := fun t => ?_ }
  · rw [pathVel_reverse Γ hd, pathVel_reverse Γ hd]; exact hΓ.speed (Γ.T - t) u
  · show Γ.nu (Γ.T - t) u = _
    rw [pathVel_reverse Γ hd, pathPerim_reverse Γ hd]
    exact hΓ.normal (Γ.T - t) u
  · rw [pathKn_reverse Γ hX2]; exact hΓ.kmin (Γ.T - t) σ
  · rw [pathKn_reverse Γ hX2]; exact hΓ.kmax (Γ.T - t) σ
  · rw [pathPerim_reverse Γ hd]; exact hΓ.short (Γ.T - t)
  · rw [pathVel_reverse Γ hd]; exact hΓ.slit (Γ.T - t)

/-- **A free-admissible path run on the flat time profile is free-admissible.** -/
theorem isPinchedPathFree_slow (Γ : NormalPath p q) (hΓ : IsPinchedPathFree kminP kh Γ) :
    IsPinchedPathFree kminP kh (slow Γ) := by
  have hX6 : ContDiff ℝ (6 : ℕ) (uncurry Γ.X) := hΓ.smooth
  have hX2 : ContDiff ℝ (2 : ℕ) (uncurry Γ.X) := hX6.of_le (by norm_num)
  have hd : Differentiable ℝ (uncurry Γ.X) := hX2.differentiable (by norm_num)
  have hphi : Differentiable ℝ (flatTime Γ.T) := differentiable_flatTime Γ.T
  refine
    { smooth := by
        show ContDiff ℝ (6 : ℕ) (uncurry fun t u => Γ.X (flatTime Γ.T t) u)
        exact contDiff_uncurry_timeComp hX6 (contDiff_flatTime (n := 6) Γ.T)
      speed := fun t u => ?_
      per := fun t => hΓ.per (flatTime Γ.T t)
      normal := fun t u => ?_
      kmin := fun t σ => ?_
      kmax := fun t σ => ?_
      short := fun t => ?_
      slit := fun t => ?_ }
  · show ‖pathVel (fun t u => Γ.X (flatTime Γ.T t) u) t u‖
      = ‖pathVel (fun t u => Γ.X (flatTime Γ.T t) u) t 0‖
    rw [pathVel_timeComp hd hphi, pathVel_timeComp hd hphi]
    exact hΓ.speed (flatTime Γ.T t) u
  · show Γ.nu (flatTime Γ.T t) u
      = Complex.I * (pathVel (fun t u => Γ.X (flatTime Γ.T t) u) t u
          / ((pathPerim (fun t u => Γ.X (flatTime Γ.T t) u) t : ℝ) : ℂ))
    rw [pathVel_timeComp hd hphi, pathPerim_timeComp hd hphi]
    exact hΓ.normal (flatTime Γ.T t) u
  · show kminP ≤ pathKn (fun t u => Γ.X (flatTime Γ.T t) u)
      (pathPerim fun t u => Γ.X (flatTime Γ.T t) u) t σ
    rw [pathKn_timeComp hX2 hphi]
    exact hΓ.kmin (flatTime Γ.T t) σ
  · show pathKn (fun t u => Γ.X (flatTime Γ.T t) u)
      (pathPerim fun t u => Γ.X (flatTime Γ.T t) u) t σ ≤ kh
    rw [pathKn_timeComp hX2 hphi]
    exact hΓ.kmax (flatTime Γ.T t) σ
  · show kh * pathPerim (fun t u => Γ.X (flatTime Γ.T t) u) t < 4 * Real.pi
    rw [pathPerim_timeComp hd hphi]
    exact hΓ.short (flatTime Γ.T t)
  · show pathVel (fun t u => Γ.X (flatTime Γ.T t) u) t 0 ∈ Complex.slitPlane
    rw [pathVel_timeComp hd hphi]
    exact hΓ.slit (flatTime Γ.T t)

/-- **The concatenation of two free-admissible paths is free-admissible**, as
soon as the glued family of slices is jointly `C⁶`. -/
theorem isPinchedPathFree_concat_of_smooth {A : NormalPath p q} {B : NormalPath q r}
    (hA : IsPinchedPathFree kminP kh A) (hB : IsPinchedPathFree kminP kh B)
    (hsm : ContDiff ℝ (6 : ℕ) (uncurry (concat A B).X)) :
    IsPinchedPathFree kminP kh (concat A B) := by
  have hC2 : ContDiff ℝ (2 : ℕ) (uncurry (concat A B).X) := hsm.of_le (by norm_num)
  have hA2 : ContDiff ℝ (2 : ℕ) (uncurry A.X) := hA.smooth.of_le (by norm_num)
  have hB2 : ContDiff ℝ (2 : ℕ) (uncurry B.X) := hB.smooth.of_le (by norm_num)
  have hCd : Differentiable ℝ (uncurry (concat A B).X) := hC2.differentiable (by norm_num)
  have hAd : Differentiable ℝ (uncurry A.X) := hA2.differentiable (by norm_num)
  have hBd : Differentiable ℝ (uncurry B.X) := hB2.differentiable (by norm_num)
  refine
    { smooth := hsm
      speed := fun t u => ?_
      per := fun t => ?_
      normal := fun t u => ?_
      kmin := fun t σ => ?_
      kmax := fun t σ => ?_
      short := fun t => ?_
      slit := fun t => ?_ }
  · by_cases ht : t ≤ A.T
    · rw [pathVel_concat_of_le hCd hAd ht, pathVel_concat_of_le hCd hAd ht]
      exact hA.speed t u
    · rw [pathVel_concat_of_not_le hCd hBd ht, pathVel_concat_of_not_le hCd hBd ht]
      exact hB.speed (t - A.T) u
  · by_cases ht : t ≤ A.T
    · rw [slice_concat_of_le A B ht]; exact hA.per t
    · rw [slice_concat_of_not_le A B ht]; exact hB.per (t - A.T)
  · by_cases ht : t ≤ A.T
    · show (if t ≤ A.T then A.nu t u else B.nu (t - A.T) u) = _
      rw [if_pos ht, pathVel_concat_of_le hCd hAd ht, pathPerim_concat_of_le hCd hAd ht]
      exact hA.normal t u
    · show (if t ≤ A.T then A.nu t u else B.nu (t - A.T) u) = _
      rw [if_neg ht, pathVel_concat_of_not_le hCd hBd ht,
        pathPerim_concat_of_not_le hCd hBd ht]
      exact hB.normal (t - A.T) u
  · by_cases ht : t ≤ A.T
    · rw [pathKn_concat_of_le hC2 hA2 ht]; exact hA.kmin t σ
    · rw [pathKn_concat_of_not_le hC2 hB2 ht]; exact hB.kmin (t - A.T) σ
  · by_cases ht : t ≤ A.T
    · rw [pathKn_concat_of_le hC2 hA2 ht]; exact hA.kmax t σ
    · rw [pathKn_concat_of_not_le hC2 hB2 ht]; exact hB.kmax (t - A.T) σ
  · by_cases ht : t ≤ A.T
    · rw [pathPerim_concat_of_le hCd hAd ht]; exact hA.short t
    · rw [pathPerim_concat_of_not_le hCd hBd ht]; exact hB.short (t - A.T)
  · by_cases ht : t ≤ A.T
    · rw [pathVel_concat_of_le hCd hAd ht]; exact hA.slit t
    · rw [pathVel_concat_of_not_le hCd hBd ht]; exact hB.slit (t - A.T)

/-- **The flattened concatenation of two free-admissible paths is
free-admissible.** -/
theorem isPinchedPathFree_concatSlow (Γ : NormalPath p q) (Δ : NormalPath q r)
    (hΓ : IsPinchedPathFree kminP kh Γ) (hΔ : IsPinchedPathFree kminP kh Δ) :
    IsPinchedPathFree kminP kh (concatSlow Γ Δ) :=
  isPinchedPathFree_concat_of_smooth (isPinchedPathFree_slow Γ hΓ)
    (isPinchedPathFree_slow Δ hΔ)
    (contDiff_uncurry_concatSlow Γ Δ hΓ.smooth hΔ.smooth)

/-! ### The pseudodistance of the corrected class -/

/-- The set of costs of the free-admissible paths joining two marked curves. -/
def freeSet (kminP kh : ℝ) (p q : Data) : Set ℝ :=
  {c | ∃ Γ : NormalPath p q, cost Γ = c ∧ IsPinchedPathFree kminP kh Γ}

theorem bddBelow_freeSet (kminP kh : ℝ) (p q : Data) : BddBelow (freeSet kminP kh p q) := by
  refine ⟨0, ?_⟩
  rintro c ⟨Γ, rfl, -⟩
  exact Γ.cost_nonneg

/-- **The pseudodistance of the corrected admissible class**: the infimum of the
costs of the paths satisfying every condition of the `C²` estimate but the
resting marked point. -/
def freeDist (kminP kh : ℝ) (p q : Data) : ℝ := sInf (freeSet kminP kh p q)

theorem freeDist_nonneg (kminP kh : ℝ) (p q : Data) : 0 ≤ freeDist kminP kh p q := by
  refine Real.sInf_nonneg ?_
  rintro c ⟨Γ, rfl, -⟩
  exact Γ.cost_nonneg

theorem freeDist_le_cost {Γ : NormalPath p q} (hΓ : IsPinchedPathFree kminP kh Γ) :
    freeDist kminP kh p q ≤ cost Γ :=
  csInf_le (bddBelow_freeSet kminP kh p q) ⟨Γ, rfl, hΓ⟩

/-- An admissible path is free-admissible, so the corrected pseudodistance is at
most the old one. -/
theorem freeSet_subset_pinchedSet (kminP kh : ℝ) (p q : Data) :
    pinchedSet kminP kh p q ⊆ freeSet kminP kh p q := by
  rintro c ⟨Γ, rfl, hΓ⟩
  exact ⟨Γ, rfl, isPinchedPathFree_of_isPinchedPath hΓ⟩

theorem freeDist_le_pinchedDist (hne : (pinchedSet kminP kh p q).Nonempty) :
    freeDist kminP kh p q ≤ pinchedDist kminP kh p q := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨c, hc, hlt⟩ := exists_lt_of_csInf_lt hne
    (show pinchedDist kminP kh p q < pinchedDist kminP kh p q + ε by linarith)
  obtain ⟨Γ, rfl, hΓ⟩ := freeSet_subset_pinchedSet kminP kh p q hc
  have := freeDist_le_cost hΓ
  linarith

/-- **The corrected pseudodistance dominates the path pseudodistance**: the
free-admissible paths are normal paths. -/
theorem pathDist_le_freeDist (hne : (freeSet kminP kh p q).Nonempty) :
    pathDist p q ≤ freeDist kminP kh p q := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨c, ⟨Γ, hc, -⟩, hlt⟩ := exists_lt_of_csInf_lt hne
    (show freeDist kminP kh p q < freeDist kminP kh p q + ε by linarith)
  have := pathDist_le_cost Γ
  rw [hc] at this
  linarith

/-- **The corrected pseudodistance dominates the pointwise displacement of the
two curves.** -/
theorem norm_sub_le_freeDist (hne : (freeSet kminP kh p q).Nonempty) (u : ℝ) :
    ‖q.1 u - p.1 u‖ ≤ freeDist kminP kh p q := by
  refine le_csInf hne ?_
  rintro c ⟨Γ, rfl, -⟩
  exact Γ.norm_sub_le_cost u

/-- **The set of free-admissible costs is symmetric.** -/
theorem freeSet_comm (kminP kh : ℝ) (p q : Data) :
    freeSet kminP kh p q = freeSet kminP kh q p := by
  have key : ∀ a b : Data, freeSet kminP kh a b ⊆ freeSet kminP kh b a := by
    rintro a b c ⟨Γ, rfl, hΓ⟩
    exact ⟨PathMetric.NormalPath.reverse Γ, cost_reverse Γ, isPinchedPathFree_reverse Γ hΓ⟩
  exact subset_antisymm (key p q) (key q p)

/-- **The corrected pseudodistance is symmetric.** -/
theorem freeDist_comm (kminP kh : ℝ) (p q : Data) :
    freeDist kminP kh p q = freeDist kminP kh q p := by
  rw [freeDist, freeDist, freeSet_comm]

/-- **The corrected pseudodistance vanishes at an admissible curve.** -/
theorem freeDist_self (hc : IsPinchedCurve kminP kh p) : freeDist kminP kh p p = 0 := by
  refine le_antisymm ?_ (freeDist_nonneg _ _ _ _)
  have h := freeDist_le_cost
    (isPinchedPathFree_of_isPinchedPath (isPinchedPath_constPinchedPath p hc))
  rwa [cost_constPinchedPath p hc] at h

theorem freeSet_self_nonempty (hc : IsPinchedCurve kminP kh p) :
    (freeSet kminP kh p p).Nonempty :=
  ⟨0, constPinchedPath p hc, cost_constPinchedPath p hc,
    isPinchedPathFree_of_isPinchedPath (isPinchedPath_constPinchedPath p hc)⟩

/-- **The corrected pseudodistance satisfies the triangle inequality.** -/
theorem freeDist_triangle (hpq : (freeSet kminP kh p q).Nonempty)
    (hqr : (freeSet kminP kh q r).Nonempty) :
    freeDist kminP kh p r ≤ freeDist kminP kh p q + freeDist kminP kh q r := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨c₁, ⟨Γ, hc₁, hΓ⟩, hlt₁⟩ := exists_lt_of_csInf_lt hpq
    (show freeDist kminP kh p q < freeDist kminP kh p q + ε / 2 by linarith)
  obtain ⟨c₂, ⟨Δ, hc₂, hΔ⟩, hlt₂⟩ := exists_lt_of_csInf_lt hqr
    (show freeDist kminP kh q r < freeDist kminP kh q r + ε / 2 by linarith)
  have hle := freeDist_le_cost (isPinchedPathFree_concatSlow Γ Δ hΓ hΔ)
  rw [cost_concatSlow, hc₁, hc₂] at hle
  linarith

/-! ### The corrected pseudodistance is not identically zero -/

variable {a : ℝ}

/-- The dilating circle is a free-admissible path between the marked circles of
radii `r` and `r + a`. -/
theorem freeSet_circleData_nonempty {r : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (har : a < r) :
    (freeSet (1 / (r + a)) (1 / r) (circleData r) (circleData (r + a))).Nonempty :=
  ⟨a, dilCirclePath r a ha, cost_dilCirclePath ha,
    dilCirclePath_isPinchedPathFree hr ha har⟩

/-- **The corrected pseudodistance of two circles is the difference of their
radii.**  The upper bound is the dilating circle, of cost `a`; the lower bound is
the displacement of the marked point.  In particular `freeDist` is *not*
identically zero, in contrast with `PinchedPath.pinchedDist`, which
`PinchedPathRigidity.pinchedDist_eq_zero` shows to vanish everywhere. -/
theorem freeDist_circleData {r : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (har : a < r) :
    freeDist (1 / (r + a)) (1 / r) (circleData r) (circleData (r + a)) = a := by
  have hne := freeSet_circleData_nonempty hr ha har
  refine le_antisymm ?_ ?_
  · have h := freeDist_le_cost (dilCirclePath_isPinchedPathFree hr ha har)
    rwa [cost_dilCirclePath ha] at h
  · have h := norm_sub_le_freeDist hne 0
    have h0 : ((circleData (r + a)).1 0 : ℂ) - (circleData r).1 0 = (a : ℂ) := by
      rw [circleData_fst, circleData_fst]
      have hE : normExp 0 = 1 := by simp [normExp]
      rw [hE, mul_one, mul_one]
      push_cast
      ring
    rw [h0] at h
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha] at h

end PinchedFree
