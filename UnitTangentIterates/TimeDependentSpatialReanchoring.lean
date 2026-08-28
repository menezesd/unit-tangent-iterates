import UnitTangentIterates.RearOwnPathDistIntrinsic

/-!
# Time-dependent spatial reanchoring

This file isolates the calculus used when a moving periodic front is translated
in its arclength variable by a time-dependent phase.  The same phase is
subtracted from a (possibly nonaffine) marking, so the normalized marking fixes
the origin.  No geometric construction is hidden here: the phase and its ODE
remain inputs of the application.
-/

noncomputable section

open Function Set RearOwnHigherRegularity

namespace TimeDependentSpatialReanchoring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translate the spatial variable of a time-dependent family. -/
def shift (f : ℝ → ℝ → E) (q : ℝ → ℝ) : ℝ → ℝ → E :=
  fun t s ↦ f t (s + q t)

/-- Subtract the same phase from a nonaffine marking. -/
def normalize (Phi : ℝ → ℝ → ℝ) (q : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t u ↦ Phi t u - q t

/-- The map of the time-space plane underlying `shift`. -/
def pairMap (q : ℝ → ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun p ↦ (p.1, p.2 + q p.1)

theorem pairMap_contDiff {n : WithTop ℕ∞} {q : ℝ → ℝ}
    (hq : ContDiff ℝ n q) : ContDiff ℝ n (pairMap q) := by
  exact contDiff_fst.prodMk
    (contDiff_snd.add (hq.comp contDiff_fst))

theorem shift_contDiff {n : WithTop ℕ∞} {f : ℝ → ℝ → E} {q : ℝ → ℝ}
    (hf : ContDiff ℝ n (uncurry f)) (hq : ContDiff ℝ n q) :
    ContDiff ℝ n (uncurry (shift f q)) := by
  simpa [shift, pairMap, Function.comp_def, uncurry] using
    hf.comp (pairMap_contDiff hq)

theorem shift_spatial_deriv {f fd : ℝ → ℝ → E} {q : ℝ → ℝ}
    (hf : ∀ t s, HasDerivAt (f t) (fd t s) s) (t s : ℝ) :
    HasDerivAt (shift f q t) (fd t (s + q t)) s := by
  have hinner : HasDerivAt (fun x : ℝ ↦ x + q t) 1 s :=
    (hasDerivAt_id s).add_const (q t)
  simpa [shift] using
    (hf t (s + q t)).hasFDerivAt.comp_hasDerivAt s hinner

theorem shift_periodic {f : ℝ → ℝ → E} {q P : ℝ → ℝ}
    (hf : ∀ t, Function.Periodic (f t) (P t)) (t : ℝ) :
    Function.Periodic (shift f q t) (P t) := by
  intro s
  simp only [shift]
  rw [show s + P t + q t = (s + q t) + P t by ring]
  exact hf t (s + q t)

theorem shift_additive_periodic {f : ℝ → ℝ → ℝ} {q P turn : ℝ → ℝ}
    (hf : ∀ t s, f t (s + P t) = f t s + turn t) (t s : ℝ) :
    shift f q t (s + P t) = shift f q t s + turn t := by
  simp only [shift]
  rw [show s + P t + q t = (s + q t) + P t by ring]
  exact hf t (s + q t)

theorem range_shift (f : ℝ → ℝ → E) (q : ℝ → ℝ) (t : ℝ) :
    range (shift f q t) = range (f t) := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s + q t, rfl⟩
  · rintro ⟨s, rfl⟩
    refine ⟨s - q t, ?_⟩
    simp [shift]

theorem normalize_zero {Phi : ℝ → ℝ → ℝ} {q : ℝ → ℝ}
    (hPhi0 : ∀ t, Phi t 0 = q t) (t : ℝ) :
    normalize Phi q t 0 = 0 := by
  simp [normalize, hPhi0]

theorem normalize_shift {Phi : ℝ → ℝ → ℝ} {q P : ℝ → ℝ}
    (hPhi : ∀ t u, Phi t (u + 1) = Phi t u + P t) (t u : ℝ) :
    normalize Phi q t (u + 1) = normalize Phi q t u + P t := by
  simp only [normalize, hPhi t u]
  ring

theorem normalize_spatial_deriv {Phi Phi1 : ℝ → ℝ → ℝ} {q : ℝ → ℝ}
    (hPhi : ∀ t u, HasDerivAt (Phi t) (Phi1 t u) u) (t u : ℝ) :
    HasDerivAt (normalize Phi q t) (Phi1 t u) u := by
  convert (hPhi t u).sub_const (q t) using 1

theorem normalize_eta_link {eta etaF Phi : ℝ → ℝ → ℝ} {q : ℝ → ℝ}
    (heta : ∀ t u, eta t u = etaF t (Phi t u)) (t u : ℝ) :
    eta t u = shift etaF q t (normalize Phi q t u) := by
  rw [heta]
  simp [shift, normalize]

/-- A flow which fixes the marked origin forces its generating tangential
field to vanish there.  This is the non-circular way to recover the pinning
condition after a phase has been normalized. -/
theorem tangential_zero_of_fixed_flow {Phi xi : ℝ → ℝ → ℝ}
    (hzero : ∀ t, Phi t 0 = 0)
    (hflow : ∀ t, HasDerivAt (fun r ↦ Phi r 0) (-xi t (Phi t 0)) t)
    (t : ℝ) : xi t 0 = 0 := by
  have hfun : (fun r ↦ Phi r 0) = (fun _ : ℝ ↦ (0 : ℝ)) := funext hzero
  have h := hflow t
  rw [hfun] at h
  have hconst : HasDerivAt (fun _ : ℝ ↦ (0 : ℝ)) 0 t :=
    hasDerivAt_const t 0
  have heq := h.unique hconst
  simpa [hzero t] using neg_eq_zero.mp heq

/-- Chain rule for the time derivative after a moving spatial translation. -/
theorem shift_time_deriv {f : ℝ → ℝ → E} {q : ℝ → ℝ} {q' t s : ℝ}
    (hf : Differentiable ℝ (uncurry f)) (hq : HasDerivAt q q' t) :
    HasDerivAt (fun r ↦ shift f q r s)
      (partialTime f t (s + q t) + q' • partialArc f t (s + q t)) t := by
  simpa [shift] using
    RearOwnPathDistIntrinsic.hasDerivAt_moving_point hf
      ((hasDerivAt_const t s).add hq)

end TimeDependentSpatialReanchoring
