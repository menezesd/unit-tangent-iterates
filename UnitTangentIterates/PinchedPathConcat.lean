import Mathlib
import UnitTangentIterates.PinchedPathSlow

/-!
# The concatenation of two admissible paths, and the triangle inequality

The concatenation of two normal paths is a normal path (`PathMetric`), but the
glued family of slices is in general only continuous in the time, while the
`C²` estimate asks it to be jointly `C⁶`.  `PinchedPathSlow.lean` removes the
obstruction: run each of the two paths on the flat time profile, so that each
stands still on a neighbourhood of the seam.  The glued family is then
identically the common slice near the seam, hence smooth there, and smooth away
from it because each branch is; the cost is unchanged.

Two admissible paths therefore concatenate to an admissible path
(`isPinchedPath_concatSlow`) of the sum of the costs, and the pinched
pseudodistance of `PinchedPathBasic.lean` satisfies the triangle inequality
(`pinchedDist_triangle`).  With the symmetry and the vanishing at an admissible
curve proved there, `pinchedDist` is a pseudometric on the admissible curves.

Main results: `isPinchedPath_concat_of_smooth`, `contDiff_uncurry_concatSlow`,
`isPinchedPath_concatSlow`, `cost_concatSlow`, `pinchedDist_triangle`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath

namespace PinchedPath

open RearOwnHigherRegularity FrontFromPath SelInvPathRegularityC2
  SelInvPathCurvatureC2 SelInvPathPerimC2 SelInvTubePathDist

variable {kminP kh : ℝ} {p q r : Data}

/-! ### Slices -/

/-- A slice of a jointly smooth family is smooth. -/
theorem contDiff_slice {X : ℝ → ℝ → ℂ} {n : ℕ} (hX : ContDiff ℝ (n : ℕ) (uncurry X))
    (t : ℝ) : ContDiff ℝ (n : ℕ) (X t) :=
  hX.comp (contDiff_const.prodMk contDiff_id)

/-- The initial curve of a smooth normal path is a smooth curve. -/
theorem contDiff_start {n : ℕ} (Γ : NormalPath p q)
    (hX : ContDiff ℝ (n : ℕ) (uncurry Γ.X)) : ContDiff ℝ (n : ℕ) (⇑p.1) := by
  have h : (⇑p.1) = Γ.X 0 := by funext u; exact (Γ.start u).symm
  rw [h]; exact contDiff_slice hX 0

/-- The terminal curve of a smooth normal path is a smooth curve. -/
theorem contDiff_finish {n : ℕ} (Γ : NormalPath p q)
    (hX : ContDiff ℝ (n : ℕ) (uncurry Γ.X)) : ContDiff ℝ (n : ℕ) (⇑q.1) := by
  have h : (⇑q.1) = Γ.X Γ.T := by funext u; exact (Γ.finish u).symm
  rw [h]; exact contDiff_slice hX Γ.T

/-- Two families with the same slice at a time have the same parameter
derivative there. -/
theorem partialArc_congr_slice {f g : ℝ → ℝ → ℂ} (hf : Differentiable ℝ (uncurry f))
    (hg : Differentiable ℝ (uncurry g)) {t s : ℝ} (h : f t = g s) (u : ℝ) :
    partialArc f t u = partialArc g s u := by
  have h1 := hasDerivAt_partialArc hf t u
  have h2 := hasDerivAt_partialArc hg s u
  rw [h] at h1
  exact h1.unique h2

/-! ### Concatenating two admissible paths -/

section Concat

variable (A : NormalPath p q) (B : NormalPath q r)

theorem slice_concat_of_le {t : ℝ} (ht : t ≤ A.T) : (concat A B).X t = A.X t :=
  funext fun _ => if_pos ht

theorem slice_concat_of_not_le {t : ℝ} (ht : ¬ t ≤ A.T) :
    (concat A B).X t = B.X (t - A.T) :=
  funext fun _ => if_neg ht

variable {A B}

theorem pathVel_concat_of_le (hC : Differentiable ℝ (uncurry (concat A B).X))
    (hA : Differentiable ℝ (uncurry A.X)) {t : ℝ} (ht : t ≤ A.T) (u : ℝ) :
    pathVel (concat A B).X t u = pathVel A.X t u :=
  partialArc_congr_slice hC hA (slice_concat_of_le A B ht) u

theorem pathVel_concat_of_not_le (hC : Differentiable ℝ (uncurry (concat A B).X))
    (hB : Differentiable ℝ (uncurry B.X)) {t : ℝ} (ht : ¬ t ≤ A.T) (u : ℝ) :
    pathVel (concat A B).X t u = pathVel B.X (t - A.T) u :=
  partialArc_congr_slice hC hB (slice_concat_of_not_le A B ht) u

theorem pathAcc_concat_of_le (hC : ContDiff ℝ (2 : ℕ) (uncurry (concat A B).X))
    (hA : ContDiff ℝ (2 : ℕ) (uncurry A.X)) {t : ℝ} (ht : t ≤ A.T) (u : ℝ) :
    pathAcc (concat A B).X t u = pathAcc A.X t u := by
  have hCd : Differentiable ℝ (uncurry (concat A B).X) := hC.differentiable (by norm_num)
  have hAd : Differentiable ℝ (uncurry A.X) := hA.differentiable (by norm_num)
  have hCV : Differentiable ℝ (uncurry (pathVel (concat A B).X)) :=
    (contDiff_partialArc_self (n := 1) (by exact_mod_cast hC)).differentiable (by norm_num)
  have hAV : Differentiable ℝ (uncurry (pathVel A.X)) :=
    (contDiff_partialArc_self (n := 1) (by exact_mod_cast hA)).differentiable (by norm_num)
  have hslice : pathVel (concat A B).X t = pathVel A.X t := by
    funext u; exact pathVel_concat_of_le hCd hAd ht u
  exact partialArc_congr_slice hCV hAV hslice u

theorem pathAcc_concat_of_not_le (hC : ContDiff ℝ (2 : ℕ) (uncurry (concat A B).X))
    (hB : ContDiff ℝ (2 : ℕ) (uncurry B.X)) {t : ℝ} (ht : ¬ t ≤ A.T) (u : ℝ) :
    pathAcc (concat A B).X t u = pathAcc B.X (t - A.T) u := by
  have hCd : Differentiable ℝ (uncurry (concat A B).X) := hC.differentiable (by norm_num)
  have hBd : Differentiable ℝ (uncurry B.X) := hB.differentiable (by norm_num)
  have hCV : Differentiable ℝ (uncurry (pathVel (concat A B).X)) :=
    (contDiff_partialArc_self (n := 1) (by exact_mod_cast hC)).differentiable (by norm_num)
  have hBV : Differentiable ℝ (uncurry (pathVel B.X)) :=
    (contDiff_partialArc_self (n := 1) (by exact_mod_cast hB)).differentiable (by norm_num)
  have hslice : pathVel (concat A B).X t = pathVel B.X (t - A.T) := by
    funext u; exact pathVel_concat_of_not_le hCd hBd ht u
  exact partialArc_congr_slice hCV hBV hslice u

theorem pathPerim_concat_of_le (hC : Differentiable ℝ (uncurry (concat A B).X))
    (hA : Differentiable ℝ (uncurry A.X)) {t : ℝ} (ht : t ≤ A.T) :
    pathPerim (concat A B).X t = pathPerim A.X t := by
  simp [pathPerim, pathVel_concat_of_le hC hA ht]

theorem pathPerim_concat_of_not_le (hC : Differentiable ℝ (uncurry (concat A B).X))
    (hB : Differentiable ℝ (uncurry B.X)) {t : ℝ} (ht : ¬ t ≤ A.T) :
    pathPerim (concat A B).X t = pathPerim B.X (t - A.T) := by
  simp [pathPerim, pathVel_concat_of_not_le hC hB ht]

theorem pathKn_concat_of_le (hC : ContDiff ℝ (2 : ℕ) (uncurry (concat A B).X))
    (hA : ContDiff ℝ (2 : ℕ) (uncurry A.X)) {t : ℝ} (ht : t ≤ A.T) (σ : ℝ) :
    pathKn (concat A B).X (pathPerim (concat A B).X) t σ
      = pathKn A.X (pathPerim A.X) t σ := by
  have hCd : Differentiable ℝ (uncurry (concat A B).X) := hC.differentiable (by norm_num)
  have hAd : Differentiable ℝ (uncurry A.X) := hA.differentiable (by norm_num)
  simp [pathKn, curvOfPath, pathVel_concat_of_le hCd hAd ht,
    pathAcc_concat_of_le hC hA ht, pathPerim_concat_of_le hCd hAd ht]

theorem pathKn_concat_of_not_le (hC : ContDiff ℝ (2 : ℕ) (uncurry (concat A B).X))
    (hB : ContDiff ℝ (2 : ℕ) (uncurry B.X)) {t : ℝ} (ht : ¬ t ≤ A.T) (σ : ℝ) :
    pathKn (concat A B).X (pathPerim (concat A B).X) t σ
      = pathKn B.X (pathPerim B.X) (t - A.T) σ := by
  have hCd : Differentiable ℝ (uncurry (concat A B).X) := hC.differentiable (by norm_num)
  have hBd : Differentiable ℝ (uncurry B.X) := hB.differentiable (by norm_num)
  simp [pathKn, curvOfPath, pathVel_concat_of_not_le hCd hBd ht,
    pathAcc_concat_of_not_le hC hB ht, pathPerim_concat_of_not_le hCd hBd ht]

/-- **The concatenation of two admissible paths is admissible**, as soon as the
glued family of slices is jointly `C⁶`. -/
theorem isPinchedPath_concat_of_smooth (hA : IsPinchedPath kminP kh A)
    (hB : IsPinchedPath kminP kh B)
    (hsm : ContDiff ℝ (6 : ℕ) (uncurry (concat A B).X)) :
    IsPinchedPath kminP kh (concat A B) := by
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
      slit := fun t => ?_
      rest := fun t => ?_ }
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
  · show (if t ≤ A.T then A.eta t 0 else B.eta (t - A.T) 0) = 0
    by_cases ht : t ≤ A.T
    · rw [if_pos ht]; exact hA.rest t
    · rw [if_neg ht]; exact hB.rest (t - A.T)

end Concat

/-! ### The concatenation on flat time profiles -/

/-- The concatenation of two paths, each run on its flat time profile. -/
def concatSlow (Γ : NormalPath p q) (Δ : NormalPath q r) : NormalPath p r :=
  concat (slow Γ) (slow Δ)

/-- **The glued family of the two flattened paths is jointly `C⁶`.**  Away from
the seam each branch is smooth; at the seam both branches are identically the
common curve. -/
theorem contDiff_uncurry_concatSlow (Γ : NormalPath p q) (Δ : NormalPath q r)
    (hΓ : ContDiff ℝ (6 : ℕ) (uncurry Γ.X)) (hΔ : ContDiff ℝ (6 : ℕ) (uncurry Δ.X)) :
    ContDiff ℝ (6 : ℕ) (uncurry (concatSlow Γ Δ).X) := by
  have hq : ContDiff ℝ (6 : ℕ) (⇑q.1) := contDiff_finish Γ hΓ
  have hA : ContDiff ℝ (6 : ℕ) (uncurry fun t u => Γ.X (flatTime Γ.T t) u) :=
    contDiff_uncurry_timeComp hΓ (contDiff_flatTime (n := 6) Γ.T)
  have hB : ContDiff ℝ (6 : ℕ)
      (uncurry fun t u => Δ.X (flatTime Δ.T (t - Γ.T)) u) := by
    refine contDiff_uncurry_timeComp hΔ ?_
    exact (contDiff_flatTime (n := 6) Δ.T).comp (contDiff_id.sub contDiff_const)
  have hfun : uncurry (concatSlow Γ Δ).X
      = fun z : ℝ × ℝ => if z.1 ≤ Γ.T then Γ.X (flatTime Γ.T z.1) z.2
          else Δ.X (flatTime Δ.T (z.1 - Γ.T)) z.2 := rfl
  rw [contDiff_iff_contDiffAt]
  rintro ⟨t, u⟩
  rcases lt_trichotomy t Γ.T with hlt | heq | hgt
  · have hnhds : {z : ℝ × ℝ | z.1 < Γ.T} ∈ nhds (t, u) :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds hlt
    refine (hA.contDiffAt (x := (t, u))).congr_of_eventuallyEq ?_
    filter_upwards [hnhds] with z hz
    rw [hfun]
    exact if_pos (le_of_lt hz)
  · set d : ℝ := min (Γ.T / 4) (Δ.T / 4) with hd
    have hdpos : 0 < d := lt_min (by linarith [Γ.T_pos]) (by linarith [Δ.T_pos])
    have hnhds : {z : ℝ × ℝ | t - d < z.1 ∧ z.1 < t + d} ∈ nhds (t, u) := by
      refine IsOpen.mem_nhds ?_ ⟨by linarith, by linarith⟩
      exact (isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt continuous_fst continuous_const)
    refine ((hq.comp contDiff_snd).contDiffAt (x := (t, u))).congr_of_eventuallyEq ?_
    filter_upwards [hnhds] with z hz
    rw [hfun]
    dsimp only [Function.comp_apply]
    by_cases hz1 : z.1 ≤ Γ.T
    · rw [if_pos hz1]
      have h34 : 3 * Γ.T / 4 ≤ z.1 := by
        have hmin : d ≤ Γ.T / 4 := min_le_left _ _
        have hlow := hz.1
        rw [heq] at hlow
        linarith
      rw [flatTime_of_ge Γ.T_pos h34]
      exact Γ.finish z.2
    · rw [if_neg hz1]
      have h4 : z.1 - Γ.T ≤ Δ.T / 4 := by
        have hmin : d ≤ Δ.T / 4 := min_le_right _ _
        have hhigh := hz.2
        rw [heq] at hhigh
        linarith
      rw [flatTime_of_le Δ.T_pos h4]
      exact Δ.start z.2
  · have hnhds : {z : ℝ × ℝ | Γ.T < z.1} ∈ nhds (t, u) :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds hgt
    refine (hB.contDiffAt (x := (t, u))).congr_of_eventuallyEq ?_
    filter_upwards [hnhds] with z hz
    rw [hfun]
    exact if_neg (not_le.2 hz)

/-- The cost of the flattened concatenation is the sum of the two costs. -/
theorem cost_concatSlow (Γ : NormalPath p q) (Δ : NormalPath q r) :
    cost (concatSlow Γ Δ) = cost Γ + cost Δ := by
  rw [concatSlow, cost_concat, cost_slow, cost_slow]

/-- **The flattened concatenation of two admissible paths is admissible.** -/
theorem isPinchedPath_concatSlow (Γ : NormalPath p q) (Δ : NormalPath q r)
    (hΓ : IsPinchedPath kminP kh Γ) (hΔ : IsPinchedPath kminP kh Δ) :
    IsPinchedPath kminP kh (concatSlow Γ Δ) :=
  isPinchedPath_concat_of_smooth (isPinchedPath_slow Γ hΓ) (isPinchedPath_slow Δ hΔ)
    (contDiff_uncurry_concatSlow Γ Δ hΓ.smooth hΔ.smooth)

/-! ### The triangle inequality -/

/-- **The pinched pseudodistance satisfies the triangle inequality.** -/
theorem pinchedDist_triangle (hpq : (pinchedSet kminP kh p q).Nonempty)
    (hqr : (pinchedSet kminP kh q r).Nonempty) :
    pinchedDist kminP kh p r ≤ pinchedDist kminP kh p q + pinchedDist kminP kh q r := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨c₁, ⟨Γ, hc₁, hΓ⟩, hlt₁⟩ := exists_lt_of_csInf_lt hpq
    (show pinchedDist kminP kh p q < pinchedDist kminP kh p q + ε / 2 by linarith)
  obtain ⟨c₂, ⟨Δ, hc₂, hΔ⟩, hlt₂⟩ := exists_lt_of_csInf_lt hqr
    (show pinchedDist kminP kh q r < pinchedDist kminP kh q r + ε / 2 by linarith)
  have hle := pinchedDist_le_cost (concatSlow Γ Δ) (isPinchedPath_concatSlow Γ Δ hΓ hΔ)
  rw [cost_concatSlow, hc₁, hc₂] at hle
  linarith

end PinchedPath
