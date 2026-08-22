import Mathlib
import UnitTangentIterates.SelInvTubePathDist

/-!
# The pinched path pseudodistance, without the smallness constraint

`SelInvTubePathDist.pinchedPathDist` is the infimum of the costs of the
admissible paths of `SelInvTubePathDist.IsPinchedPath` whose cost is moreover
small enough for the `C²` estimate.  That truncation is convenient for stating
the Lipschitz bound but destroys the pseudometric axioms, since the
concatenation of two admissible paths of small cost need not have small cost.

This file introduces the untruncated infimum `pinchedDist`: the infimum of the
costs of *all* admissible paths.  It dominates `pathDist`, is dominated by
`pinchedPathDist`, and the first two pseudometric axioms are proved here — it
is symmetric, because the reversal of an admissible path is admissible
(`IsPinchedPath.reverse`), and it vanishes at an admissible *curve*
(`IsPinchedCurve`), the constant path at such a curve being admissible and of
cost zero.  The triangle inequality is proved in `PinchedPathConcat.lean`.

Main results: `pinchedDist`, `IsPinchedPath.reverse`, `pinchedDist_comm`,
`IsPinchedCurve`, `pinchedDist_self`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath

namespace PinchedPath

open RearOwnHigherRegularity FrontFromPath SelInvPathRegularityC2
  SelInvPathCurvatureC2 SelInvPathPerimC2 SelInvTubePathDist

variable {kminP kh : ℝ} {p q : Data}

/-! ### Reparametrizing the time -/

/-- The family `t ↦ f (φ t)` is differentiable when `f` and `φ` are. -/
theorem differentiable_uncurry_timeComp {f : ℝ → ℝ → ℂ} {phi : ℝ → ℝ}
    (hf : Differentiable ℝ (uncurry f)) (hphi : Differentiable ℝ phi) :
    Differentiable ℝ (uncurry fun t x => f (phi t) x) := by
  have hmap : Differentiable ℝ fun z : ℝ × ℝ => ((phi z.1 : ℝ), z.2) :=
    (hphi.comp differentiable_fst).prodMk differentiable_snd
  simpa [Function.comp_def, uncurry] using hf.comp hmap

/-- The family `t ↦ f (φ t)` is as smooth as `f` and `φ`. -/
theorem contDiff_uncurry_timeComp {n : ℕ} {f : ℝ → ℝ → ℂ} {phi : ℝ → ℝ}
    (hf : ContDiff ℝ (n : ℕ) (uncurry f)) (hphi : ContDiff ℝ (n : ℕ) phi) :
    ContDiff ℝ (n : ℕ) (uncurry fun t x => f (phi t) x) := by
  have hmap : ContDiff ℝ (n : ℕ) fun z : ℝ × ℝ => ((phi z.1 : ℝ), z.2) :=
    (hphi.comp contDiff_fst).prodMk contDiff_snd
  simpa [Function.comp_def, uncurry] using hf.comp hmap

/-- The parameter derivative is unchanged by a reparametrization of the time. -/
theorem partialArc_timeComp {f : ℝ → ℝ → ℂ} {phi : ℝ → ℝ}
    (hf : Differentiable ℝ (uncurry f)) (hphi : Differentiable ℝ phi) (t x : ℝ) :
    partialArc (fun t x => f (phi t) x) t x = partialArc f (phi t) x := by
  have h1 : HasDerivAt (fun x => f (phi t) x)
      (partialArc (fun t x => f (phi t) x) t x) x :=
    hasDerivAt_partialArc (differentiable_uncurry_timeComp hf hphi) t x
  have h2 : HasDerivAt (f (phi t)) (partialArc f (phi t) x) x :=
    hasDerivAt_partialArc hf (phi t) x
  exact h1.unique h2

/-- The family `t ↦ f (c − t)` is as smooth as `f`. -/
theorem contDiff_uncurry_timeSub {n : ℕ} {f : ℝ → ℝ → ℂ}
    (hf : ContDiff ℝ (n : ℕ) (uncurry f)) (c : ℝ) :
    ContDiff ℝ (n : ℕ) (uncurry fun t x => f (c - t) x) :=
  contDiff_uncurry_timeComp hf (contDiff_const.sub contDiff_id)

/-- The parameter derivative is unchanged by the reversal of the time. -/
theorem partialArc_timeSub {f : ℝ → ℝ → ℂ} (hf : Differentiable ℝ (uncurry f))
    (c t x : ℝ) :
    partialArc (fun t x => f (c - t) x) t x = partialArc f (c - t) x :=
  partialArc_timeComp hf (by fun_prop : Differentiable ℝ fun t : ℝ => c - t) t x

/-! ### The frame data of a family reparametrized in the time -/

section TimeComp

variable {X : ℝ → ℝ → ℂ} {phi : ℝ → ℝ}

theorem pathVel_timeComp (hX : Differentiable ℝ (uncurry X))
    (hphi : Differentiable ℝ phi) (t u : ℝ) :
    pathVel (fun t u => X (phi t) u) t u = pathVel X (phi t) u :=
  partialArc_timeComp hX hphi t u

theorem pathVel_timeComp_eq (hX : Differentiable ℝ (uncurry X))
    (hphi : Differentiable ℝ phi) :
    pathVel (fun t u => X (phi t) u) = fun t u => pathVel X (phi t) u := by
  funext t u; exact pathVel_timeComp hX hphi t u

theorem pathAcc_timeComp (hX : ContDiff ℝ (2 : ℕ) (uncurry X))
    (hphi : Differentiable ℝ phi) (t u : ℝ) :
    pathAcc (fun t u => X (phi t) u) t u = pathAcc X (phi t) u := by
  have hd : Differentiable ℝ (uncurry X) := hX.differentiable (by norm_num)
  have hV : ContDiff ℝ (1 : ℕ) (uncurry (pathVel X)) :=
    contDiff_partialArc_self (n := 1) (by exact_mod_cast hX)
  have hVd : Differentiable ℝ (uncurry (pathVel X)) := hV.differentiable (by norm_num)
  show partialArc (pathVel fun t u => X (phi t) u) t u = _
  rw [pathVel_timeComp_eq hd hphi]
  exact partialArc_timeComp hVd hphi t u

theorem pathPerim_timeComp (hX : Differentiable ℝ (uncurry X))
    (hphi : Differentiable ℝ phi) (t : ℝ) :
    pathPerim (fun t u => X (phi t) u) t = pathPerim X (phi t) := by
  simp [pathPerim, pathVel_timeComp hX hphi]

theorem pathKn_timeComp (hX : ContDiff ℝ (2 : ℕ) (uncurry X))
    (hphi : Differentiable ℝ phi) (t σ : ℝ) :
    pathKn (fun t u => X (phi t) u) (pathPerim fun t u => X (phi t) u) t σ
      = pathKn X (pathPerim X) (phi t) σ := by
  have hd : Differentiable ℝ (uncurry X) := hX.differentiable (by norm_num)
  simp [pathKn, curvOfPath, pathVel_timeComp hd hphi, pathAcc_timeComp hX hphi,
    pathPerim_timeComp hd hphi]

end TimeComp

/-! ### The reversal of an admissible path -/

variable (Γ : NormalPath p q)

/-- The time reversal, as a reparametrization of the time. -/
theorem differentiable_timeSub (c : ℝ) : Differentiable ℝ fun t : ℝ => c - t := by fun_prop

theorem pathVel_reverse (hX : Differentiable ℝ (uncurry Γ.X)) (t u : ℝ) :
    pathVel (reverse Γ).X t u = pathVel Γ.X (Γ.T - t) u :=
  pathVel_timeComp hX (differentiable_timeSub Γ.T) t u

theorem pathAcc_reverse (hX : ContDiff ℝ (2 : ℕ) (uncurry Γ.X)) (t u : ℝ) :
    pathAcc (reverse Γ).X t u = pathAcc Γ.X (Γ.T - t) u :=
  pathAcc_timeComp hX (differentiable_timeSub Γ.T) t u

theorem pathPerim_reverse (hX : Differentiable ℝ (uncurry Γ.X)) (t : ℝ) :
    pathPerim (reverse Γ).X t = pathPerim Γ.X (Γ.T - t) :=
  pathPerim_timeComp hX (differentiable_timeSub Γ.T) t

theorem pathKn_reverse (hX : ContDiff ℝ (2 : ℕ) (uncurry Γ.X)) (t σ : ℝ) :
    pathKn (reverse Γ).X (pathPerim (reverse Γ).X) t σ
      = pathKn Γ.X (pathPerim Γ.X) (Γ.T - t) σ :=
  pathKn_timeComp hX (differentiable_timeSub Γ.T) t σ

/-- **The reversal of an admissible path is admissible.** -/
theorem isPinchedPath_reverse (hΓ : IsPinchedPath kminP kh Γ) :
    IsPinchedPath kminP kh (PathMetric.NormalPath.reverse Γ) := by
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
      slit := fun t => ?_
      rest := fun t => ?_ }
  · rw [pathVel_reverse Γ hd, pathVel_reverse Γ hd]; exact hΓ.speed (Γ.T - t) u
  · show Γ.nu (Γ.T - t) u = _
    rw [pathVel_reverse Γ hd, pathPerim_reverse Γ hd]
    exact hΓ.normal (Γ.T - t) u
  · rw [pathKn_reverse Γ hX2]; exact hΓ.kmin (Γ.T - t) σ
  · rw [pathKn_reverse Γ hX2]; exact hΓ.kmax (Γ.T - t) σ
  · rw [pathPerim_reverse Γ hd]; exact hΓ.short (Γ.T - t)
  · rw [pathVel_reverse Γ hd]; exact hΓ.slit (Γ.T - t)
  · show -Γ.eta (Γ.T - t) 0 = 0
    rw [hΓ.rest (Γ.T - t)]; ring

/-! ### The untruncated pinched pseudodistance -/

/-- The set of costs of the admissible paths joining two marked curves, with no
smallness condition. -/
def pinchedSet (kminP kh : ℝ) (p q : Data) : Set ℝ :=
  {c | ∃ Γ : NormalPath p q, cost Γ = c ∧ IsPinchedPath kminP kh Γ}

theorem bddBelow_pinchedSet (kminP kh : ℝ) (p q : Data) :
    BddBelow (pinchedSet kminP kh p q) := by
  refine ⟨0, ?_⟩
  rintro c ⟨Γ, rfl, -⟩
  exact Γ.cost_nonneg

/-- **The pinched pseudodistance**: the infimum of the costs of the admissible
paths joining two marked curves. -/
def pinchedDist (kminP kh : ℝ) (p q : Data) : ℝ := sInf (pinchedSet kminP kh p q)

theorem pinchedDist_nonneg (kminP kh : ℝ) (p q : Data) :
    0 ≤ pinchedDist kminP kh p q := by
  refine Real.sInf_nonneg ?_
  rintro c ⟨Γ, rfl, -⟩
  exact Γ.cost_nonneg

theorem pinchedDist_le_cost (hΓ : IsPinchedPath kminP kh Γ) :
    pinchedDist kminP kh p q ≤ cost Γ :=
  csInf_le (bddBelow_pinchedSet kminP kh p q) ⟨Γ, rfl, hΓ⟩

/-- The pinched pseudodistance dominates the path pseudodistance. -/
theorem pathDist_le_pinchedDist (hne : (pinchedSet kminP kh p q).Nonempty) :
    pathDist p q ≤ pinchedDist kminP kh p q := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨c, ⟨Γ, hc, -⟩, hlt⟩ := exists_lt_of_csInf_lt hne
    (show pinchedDist kminP kh p q < pinchedDist kminP kh p q + ε by linarith)
  have := pathDist_le_cost Γ
  rw [hc] at this
  linarith

/-- The truncated infimum of `SelInvTubePathDist` dominates the untruncated one. -/
theorem pinchedDist_le_pinchedPathDist {khat : ℝ}
    (hne : (pinchedCostSet kminP kh khat p q).Nonempty) :
    pinchedDist kminP kh p q ≤ pinchedPathDist kminP kh khat p q := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨c, ⟨Γ, hc, hΓ, -, -⟩, hlt⟩ := exists_lt_of_csInf_lt hne
    (show pinchedPathDist kminP kh khat p q < pinchedPathDist kminP kh khat p q + ε by
      linarith)
  have := pinchedDist_le_cost Γ hΓ
  rw [hc] at this
  linarith

/-- **The set of admissible costs is symmetric.** -/
theorem pinchedSet_comm (kminP kh : ℝ) (p q : Data) :
    pinchedSet kminP kh p q = pinchedSet kminP kh q p := by
  have key : ∀ (a b : Data), pinchedSet kminP kh a b ⊆ pinchedSet kminP kh b a := by
    rintro a b c ⟨Γ, rfl, hΓ⟩
    exact ⟨PathMetric.NormalPath.reverse Γ, cost_reverse Γ, isPinchedPath_reverse Γ hΓ⟩
  exact subset_antisymm (key p q) (key q p)

/-- **The pinched pseudodistance is symmetric.** -/
theorem pinchedDist_comm (kminP kh : ℝ) (p q : Data) :
    pinchedDist kminP kh p q = pinchedDist kminP kh q p := by
  rw [pinchedDist, pinchedDist, pinchedSet_comm]

/-! ### The constant path at an admissible curve -/

/-- The constant family of curves at a marked datum. -/
def constFam (p : Data) : ℝ → ℝ → ℂ := fun _ u => p.1 u

theorem contDiff_uncurry_constFam {n : ℕ} (hp : ContDiff ℝ (n : ℕ) (⇑p.1)) :
    ContDiff ℝ (n : ℕ) (uncurry (constFam p)) := hp.comp contDiff_snd

theorem pathVel_constFam (hp : ContDiff ℝ (1 : ℕ) (⇑p.1)) (t u : ℝ) :
    pathVel (constFam p) t u = deriv (⇑p.1) u := by
  have hd : Differentiable ℝ (uncurry (constFam p)) :=
    (contDiff_uncurry_constFam hp).differentiable (by norm_num)
  have h1 : HasDerivAt (constFam p t) (pathVel (constFam p) t u) u :=
    hasDerivAt_partialArc hd t u
  have h2 : HasDerivAt (⇑p.1) (deriv (⇑p.1) u) u :=
    (hp.differentiable (by norm_num)).differentiableAt.hasDerivAt
  exact h1.unique h2

theorem pathVel_constFam_eq (hp : ContDiff ℝ (1 : ℕ) (⇑p.1)) :
    pathVel (constFam p) = fun _ u => deriv (⇑p.1) u := by
  funext t u; exact pathVel_constFam hp t u

theorem pathPerim_constFam (hp : ContDiff ℝ (1 : ℕ) (⇑p.1)) (t : ℝ) :
    pathPerim (constFam p) t = ‖deriv (⇑p.1) 0‖ := by
  simp [pathPerim, pathVel_constFam hp]

/-- **An admissible curve**: a closed `C⁶` curve of constant speed, whose
curvature in the normalized parameter is pinched between `kminP` and `κ̂`, short
enough for the estimate and with its velocity at the marked point off the
slit. -/
structure IsPinchedCurve (kminP kh : ℝ) (p : Data) : Prop where
  /-- the curve is `C⁶` -/
  smooth : ContDiff ℝ (6 : ℕ) (⇑p.1)
  /-- the curve is closed -/
  per : Periodic (⇑p.1) 1
  /-- the curve has constant speed -/
  speed : ∀ u, ‖deriv (⇑p.1) u‖ = ‖deriv (⇑p.1) 0‖
  /-- the speed is positive -/
  speed_pos : 0 < ‖deriv (⇑p.1) 0‖
  /-- the curvature is at least `kminP` -/
  kmin : ∀ t σ, kminP ≤ pathKn (constFam p) (pathPerim (constFam p)) t σ
  /-- the curvature is at most `κ̂` -/
  kmax : ∀ t σ, pathKn (constFam p) (pathPerim (constFam p)) t σ ≤ kh
  /-- the curve is short -/
  short : kh * ‖deriv (⇑p.1) 0‖ < 4 * Real.pi
  /-- the velocity at the marked point avoids the slit -/
  slit : deriv (⇑p.1) 0 ∈ Complex.slitPlane

/-- The constant normal path at an admissible curve, moving along the standard
unit normal of the curve at zero normal speed. -/
def constPinchedPath (p : Data) (hc : IsPinchedCurve kminP kh p) : NormalPath p p where
  T := 1
  T_pos := one_pos
  X := constFam p
  eta := fun _ _ => 0
  nu := fun _ u => Complex.I * (deriv (⇑p.1) u / ((‖deriv (⇑p.1) 0‖ : ℝ) : ℂ))
  m := fun _ => 0
  start := fun _ => rfl
  finish := fun _ => rfl
  hasDerivAt_time := fun t u => by simpa using hasDerivAt_const t (p.1 u)
  cont_vel := fun _ => by simpa using continuous_const
  norm_nu := fun _ u => by
    have h0 : ‖deriv (⇑p.1) 0‖ ≠ 0 := ne_of_gt hc.speed_pos
    rw [norm_mul, Complex.norm_I, one_mul, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc.speed_pos, hc.speed u]
    field_simp
  cont_m := continuous_const
  m_nonneg := fun _ => le_rfl
  m_stop := fun _ _ => rfl
  abs_eta_le := fun _ _ => by simp
  le_m_L1 := fun _ => by simp
  le_m_sup := fun _ j _ => by
    rw [iteratedDeriv_zero_fun j]
    simp [MarkedTopology.supNorm]

theorem cost_constPinchedPath (p : Data) (hc : IsPinchedCurve kminP kh p) :
    cost (constPinchedPath p hc) = 0 := by
  have h : (constPinchedPath p hc).m = fun _ => (0 : ℝ) := rfl
  simp [cost, h]

/-- **The constant path at an admissible curve is admissible.** -/
theorem isPinchedPath_constPinchedPath (p : Data) (hc : IsPinchedCurve kminP kh p) :
    IsPinchedPath kminP kh (constPinchedPath p hc) := by
  have hp1 : ContDiff ℝ (1 : ℕ) (⇑p.1) := hc.smooth.of_le (by norm_num)
  refine
    { smooth := contDiff_uncurry_constFam hc.smooth
      speed := fun t u => ?_
      per := fun _ => hc.per
      normal := fun t u => ?_
      kmin := hc.kmin
      kmax := hc.kmax
      short := fun t => ?_
      slit := fun t => ?_
      rest := fun _ => rfl }
  · show ‖pathVel (constFam p) t u‖ = ‖pathVel (constFam p) t 0‖
    rw [pathVel_constFam hp1, pathVel_constFam hp1]
    exact hc.speed u
  · show Complex.I * (deriv (⇑p.1) u / ((‖deriv (⇑p.1) 0‖ : ℝ) : ℂ))
      = Complex.I * (pathVel (constFam p) t u / ((pathPerim (constFam p) t : ℝ) : ℂ))
    rw [pathVel_constFam hp1, pathPerim_constFam hp1]
  · show kh * pathPerim (constFam p) t < 4 * Real.pi
    rw [pathPerim_constFam hp1]; exact hc.short
  · show pathVel (constFam p) t 0 ∈ Complex.slitPlane
    rw [pathVel_constFam hp1]; exact hc.slit

/-- **The pinched pseudodistance vanishes at an admissible curve.** -/
theorem pinchedDist_self (hc : IsPinchedCurve kminP kh p) :
    pinchedDist kminP kh p p = 0 := by
  refine le_antisymm ?_ (pinchedDist_nonneg _ _ _ _)
  have h := pinchedDist_le_cost (constPinchedPath p hc)
    (isPinchedPath_constPinchedPath p hc)
  rwa [cost_constPinchedPath p hc] at h

theorem pinchedSet_self_nonempty (hc : IsPinchedCurve kminP kh p) :
    (pinchedSet kminP kh p p).Nonempty :=
  ⟨0, constPinchedPath p hc, cost_constPinchedPath p hc,
    isPinchedPath_constPinchedPath p hc⟩

end PinchedPath
