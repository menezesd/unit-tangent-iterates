import Mathlib
import UnitTangentIterates.PinchedPathMetric

/-!
# The slices of an admissible path are admissible curves

`PinchedPathBasic.lean` proves that the pinched pseudodistance vanishes at an
*admissible curve* (`IsPinchedCurve`) and `PinchedPathConcat.lean` that it
satisfies the triangle inequality whenever the two sets of admissible costs are
nonempty.  Both statements carry a hypothesis that this file discharges: the
admissible curves are exactly the curves reached by admissible paths.

Every slice of an admissible path is an admissible curve
(`isPinchedCurve_of_slice`): the frame data of the constant family at the slice
is the frame data of the path at that time, so each of the eight geometric
conditions of `IsPinchedCurve` is the corresponding condition of
`IsPinchedPath` read at that time.  In particular the two ends of an admissible
path are admissible curves, so `IsPinchedCurve p` holds as soon as `p` is
joined to some curve by an admissible path, and it is *equivalent* to `p` being
joined to itself (`isPinchedCurve_iff_pinchedSet_self`).

Being joined by an admissible path (`PinchedConnected`) is then an equivalence
relation on the admissible curves, and on one of its classes `pinchedDist` is a
pseudometric with no side condition left
(`isPinchedPseudoMetric_of_connected`).

Main results: `isPinchedCurve_of_slice`, `isPinchedCurve_start`, `isPinchedCurve_finish`, `isPinchedCurve_iff_pinchedSet_self`,
`PinchedConnected`, `pinchedConnected_equivalence`,
`isPinchedPseudoMetric_of_connected`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath

namespace PinchedPath

open RearOwnHigherRegularity FrontFromPath SelInvPathRegularityC2
  SelInvPathCurvatureC2 SelInvPathPerimC2 SelInvTubePathDist

variable {kminP kh : ℝ} {p q r : Data}

/-! ### The frame data of a slice -/

section Slice

variable {X : ℝ → ℝ → ℂ} {t₀ : ℝ}

/-- The velocity of the constant family at a slice of a family is the velocity
of the family at that time. -/
theorem pathVel_constFam_eq_slice (hX : ContDiff ℝ (1 : ℕ) (uncurry X))
    (hp : ContDiff ℝ (1 : ℕ) (⇑p.1)) (h : ∀ u, X t₀ u = p.1 u) (t u : ℝ) :
    pathVel (constFam p) t u = pathVel X t₀ u := by
  refine partialArc_congr_slice
    ((contDiff_uncurry_constFam hp).differentiable (by norm_num))
    (hX.differentiable (by norm_num)) ?_ u
  funext v
  exact (h v).symm

/-- The acceleration of the constant family at a slice of a family is the
acceleration of the family at that time. -/
theorem pathAcc_constFam_eq_slice (hX : ContDiff ℝ (2 : ℕ) (uncurry X))
    (hp : ContDiff ℝ (2 : ℕ) (⇑p.1)) (h : ∀ u, X t₀ u = p.1 u) (t u : ℝ) :
    pathAcc (constFam p) t u = pathAcc X t₀ u := by
  have hV : ContDiff ℝ (1 : ℕ) (uncurry (pathVel X)) :=
    contDiff_partialArc_self (n := 1) (by exact_mod_cast hX)
  have hVp : ContDiff ℝ (1 : ℕ) (uncurry (pathVel (constFam p))) :=
    contDiff_partialArc_self (n := 1) (by exact_mod_cast contDiff_uncurry_constFam hp)
  show partialArc (pathVel (constFam p)) t u = partialArc (pathVel X) t₀ u
  refine partialArc_congr_slice (hVp.differentiable (by norm_num))
    (hV.differentiable (by norm_num)) ?_ u
  funext v
  exact pathVel_constFam_eq_slice (hX.of_le (by norm_num)) (hp.of_le (by norm_num)) h t v

/-- The perimeter of the constant family at a slice of a family is the
perimeter of the family at that time. -/
theorem pathPerim_constFam_eq_slice (hX : ContDiff ℝ (1 : ℕ) (uncurry X))
    (hp : ContDiff ℝ (1 : ℕ) (⇑p.1)) (h : ∀ u, X t₀ u = p.1 u) (t : ℝ) :
    pathPerim (constFam p) t = pathPerim X t₀ := by
  simp [pathPerim, pathVel_constFam_eq_slice hX hp h]

/-- The normalized curvature of the constant family at a slice of a family is
the normalized curvature of the family at that time. -/
theorem pathKn_constFam_eq_slice (hX : ContDiff ℝ (2 : ℕ) (uncurry X))
    (hp : ContDiff ℝ (2 : ℕ) (⇑p.1)) (h : ∀ u, X t₀ u = p.1 u) (t σ : ℝ) :
    pathKn (constFam p) (pathPerim (constFam p)) t σ = pathKn X (pathPerim X) t₀ σ := by
  have hX1 : ContDiff ℝ (1 : ℕ) (uncurry X) := hX.of_le (by norm_num)
  have hp1 : ContDiff ℝ (1 : ℕ) (⇑p.1) := hp.of_le (by norm_num)
  simp [pathKn, curvOfPath, pathPerim_constFam_eq_slice hX1 hp1 h,
    pathVel_constFam_eq_slice hX1 hp1 h, pathAcc_constFam_eq_slice hX hp h]

end Slice

/-! ### The slices of an admissible path -/

/-- **Every slice of an admissible path is an admissible curve.** -/
theorem isPinchedCurve_of_slice {Γ : NormalPath p q} (hΓ : IsPinchedPath kminP kh Γ)
    {t₀ : ℝ} {c : Data} (h : ∀ u, Γ.X t₀ u = c.1 u) : IsPinchedCurve kminP kh c := by
  have hX6 : ContDiff ℝ (6 : ℕ) (uncurry Γ.X) := hΓ.smooth
  have hX2 : ContDiff ℝ (2 : ℕ) (uncurry Γ.X) := hX6.of_le (by norm_num)
  have hX1 : ContDiff ℝ (1 : ℕ) (uncurry Γ.X) := hX6.of_le (by norm_num)
  have hslice : (⇑c.1) = Γ.X t₀ := by funext u; exact (h u).symm
  have hc6 : ContDiff ℝ (6 : ℕ) (⇑c.1) := by rw [hslice]; exact contDiff_slice hX6 t₀
  have hc2 : ContDiff ℝ (2 : ℕ) (⇑c.1) := hc6.of_le (by norm_num)
  have hc1 : ContDiff ℝ (1 : ℕ) (⇑c.1) := hc6.of_le (by norm_num)
  -- the derivative of the curve is the velocity of the path at that time
  have hderiv : ∀ u, deriv (⇑c.1) u = pathVel Γ.X t₀ u := fun u => by
    rw [← pathVel_constFam hc1 0 u, pathVel_constFam_eq_slice hX1 hc1 h]
  have hslit : deriv (⇑c.1) 0 ∈ Complex.slitPlane := by
    rw [hderiv]; exact hΓ.slit t₀
  refine
    { smooth := hc6
      per := by rw [hslice]; exact hΓ.per t₀
      speed := fun u => by rw [hderiv, hderiv]; exact hΓ.speed t₀ u
      speed_pos := norm_pos_iff.2 (Complex.slitPlane_ne_zero hslit)
      kmin := fun t σ => by
        rw [pathKn_constFam_eq_slice hX2 hc2 h]; exact hΓ.kmin t₀ σ
      kmax := fun t σ => by
        rw [pathKn_constFam_eq_slice hX2 hc2 h]; exact hΓ.kmax t₀ σ
      short := ?_
      slit := hslit }
  have hperim : ‖deriv (⇑c.1) 0‖ = pathPerim Γ.X t₀ := by
    rw [hderiv]; rfl
  rw [hperim]
  exact hΓ.short t₀

/-- **The initial curve of an admissible path is an admissible curve.** -/
theorem isPinchedCurve_start {Γ : NormalPath p q}
    (hΓ : IsPinchedPath kminP kh Γ) : IsPinchedCurve kminP kh p :=
  isPinchedCurve_of_slice hΓ (t₀ := 0) Γ.start

/-- **The terminal curve of an admissible path is an admissible curve.** -/
theorem isPinchedCurve_finish {Γ : NormalPath p q}
    (hΓ : IsPinchedPath kminP kh Γ) : IsPinchedCurve kminP kh q :=
  isPinchedCurve_of_slice hΓ (t₀ := Γ.T) Γ.finish

theorem isPinchedCurve_of_pinchedSet_left (hne : (pinchedSet kminP kh p q).Nonempty) :
    IsPinchedCurve kminP kh p := by
  obtain ⟨_, Γ, -, hΓ⟩ := hne
  exact isPinchedCurve_start hΓ

theorem isPinchedCurve_of_pinchedSet_right (hne : (pinchedSet kminP kh p q).Nonempty) :
    IsPinchedCurve kminP kh q := by
  obtain ⟨_, Γ, -, hΓ⟩ := hne
  exact isPinchedCurve_finish hΓ

/-- **A curve is admissible exactly when it is joined to itself by an
admissible path.** -/
theorem isPinchedCurve_iff_pinchedSet_self :
    IsPinchedCurve kminP kh p ↔ (pinchedSet kminP kh p p).Nonempty :=
  ⟨fun hc => pinchedSet_self_nonempty hc, fun hne => isPinchedCurve_of_pinchedSet_left hne⟩

/-- The pinched pseudodistance vanishes at either end of an admissible path. -/
theorem pinchedDist_self_of_pinchedSet (hne : (pinchedSet kminP kh p q).Nonempty) :
    pinchedDist kminP kh p p = 0 :=
  pinchedDist_self (isPinchedCurve_of_pinchedSet_left hne)

/-! ### The connectivity relation -/

/-- Two marked curves are **pinched-connected** when some admissible path joins
them. -/
def PinchedConnected (kminP kh : ℝ) (p q : Data) : Prop :=
  (pinchedSet kminP kh p q).Nonempty

theorem PinchedConnected.refl_of_isPinchedCurve (hc : IsPinchedCurve kminP kh p) :
    PinchedConnected kminP kh p p :=
  pinchedSet_self_nonempty hc

theorem PinchedConnected.symm (h : PinchedConnected kminP kh p q) :
    PinchedConnected kminP kh q p := by
  rwa [PinchedConnected, ← pinchedSet_comm]

theorem PinchedConnected.trans (hpq : PinchedConnected kminP kh p q)
    (hqr : PinchedConnected kminP kh q r) : PinchedConnected kminP kh p r := by
  obtain ⟨_, Γ, -, hΓ⟩ := hpq
  obtain ⟨_, Δ, -, hΔ⟩ := hqr
  exact ⟨cost (concatSlow Γ Δ), concatSlow Γ Δ, rfl, isPinchedPath_concatSlow Γ Δ hΓ hΔ⟩

/-- **Pinched connectivity is an equivalence relation on the admissible
curves.** -/
theorem pinchedConnected_equivalence (kminP kh : ℝ) :
    (∀ p : Data, IsPinchedCurve kminP kh p → PinchedConnected kminP kh p p) ∧
    (∀ p q : Data, PinchedConnected kminP kh p q → PinchedConnected kminP kh q p) ∧
    (∀ p q r : Data, PinchedConnected kminP kh p q → PinchedConnected kminP kh q r →
      PinchedConnected kminP kh p r) :=
  ⟨fun _ hc => PinchedConnected.refl_of_isPinchedCurve hc,
    fun _ _ h => h.symm, fun _ _ _ hpq hqr => hpq.trans hqr⟩

/-- **On a class of pinched-connected curves the pinched pseudodistance is a
pseudometric**: it vanishes on the diagonal, it is symmetric, and it satisfies
the triangle inequality, the vanishing at an admissible curve of
`PinchedPathBasic.lean` being now a consequence of connectivity. -/
theorem isPinchedPseudoMetric_of_connected (kminP kh : ℝ) :
    (∀ p q : Data, PinchedConnected kminP kh p q → pinchedDist kminP kh p p = 0) ∧
    (∀ p q : Data, pinchedDist kminP kh p q = pinchedDist kminP kh q p) ∧
    (∀ p q r : Data, PinchedConnected kminP kh p q → PinchedConnected kminP kh q r →
      pinchedDist kminP kh p r
        ≤ pinchedDist kminP kh p q + pinchedDist kminP kh q r) :=
  ⟨fun _ _ h => pinchedDist_self_of_pinchedSet h,
    fun p q => pinchedDist_comm kminP kh p q,
    fun _ _ _ hpq hqr => pinchedDist_triangle hpq hqr⟩

end PinchedPath
