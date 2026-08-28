import UnitTangentIterates.CurvatureMarkedContinuity

/-!
# The arclength tangent-angle lift of a tube member
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Filter Topology Complex MarkedSpace CurvatureFromMarkedDistance

namespace MarkedSpace

/-- The derivative of a periodic function is periodic. -/
theorem periodic_of_hasDerivAt {f g : ℝ → ℂ} {T : ℝ}
    (hd : ∀ x, HasDerivAt f (g x) x) (hf : Periodic f T) : Periodic g T := by
  intro x
  have hinner : HasDerivAt (fun y : ℝ => y + T) 1 x := (hasDerivAt_id x).add_const T
  have hshift : HasDerivAt (fun y : ℝ => f (y + T)) (g (x + T)) x := by
    simpa [Function.comp] using (hd (x + T)).scomp x hinner
  have heq : (fun y : ℝ => f (y + T)) = f := funext fun y => hf y
  rw [heq] at hshift
  exact hshift.unique (hd x)

theorem periodic_vel {c kmin dlt : ℝ} {p : Data} (hp : IsTubeMember c kmin dlt p) :
    Periodic (⇑p.2.1) 1 :=
  periodic_of_hasDerivAt hp.hasDerivAt_curve hp.periodic

theorem periodic_acc {c kmin dlt : ℝ} {p : Data} (hp : IsTubeMember c kmin dlt p) :
    Periodic (⇑p.2.2) 1 :=
  periodic_of_hasDerivAt hp.hasDerivAt_vel (periodic_vel hp)

/-- The normalized-parameter curvature of a tube member is `1`-periodic. -/
theorem periodic_dataCurv {c kmin dlt : ℝ} {p : Data} (hp : IsTubeMember c kmin dlt p) :
    Periodic (dataCurv p) 1 := by
  intro u
  simp only [dataCurv, periodic_vel hp u, periodic_acc hp u]

/-- **The arclength tangent-angle lift of a tube member.**  Reparametrized by
arclength, a marked curve of the tube has unit speed, a differentiable tangent
angle, and curvature `dataCurv p (s / perim p)` — the normalized-parameter
curvature read at the rescaled time.  This is the `C2` half of
`UnconditionalAssembly.LimitStrictnessDataH`, extracted from tube membership
alone; only nonvanishing and the Harnack inequality remain. -/
theorem exists_arclength_angle {c kmin dlt : ℝ} (hc : 0 < c) {p : Data}
    (hp : IsTubeMember c kmin dlt p) :
    ∃ theta : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (theta s : ℂ))) s) ∧
      (∀ s, HasDerivAt theta (dataCurv p (s / perim p)) s) := by
  set L : ℝ := perim p with hL
  have hLpos : 0 < L := perim_pos hc hp
  have hinner : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s / L) (1 / L) s := by
    intro s
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id s).div_const L
  have hev : ∀ s, HasDerivAt (ev p) (p.2.1 (s / L) / L) s := by
    intro s
    have h := (hp.hasDerivAt_curve (s / L)).scomp s (hinner s)
    simpa [ev, hL, Function.comp, div_eq_mul_inv, one_div, smul_eq_mul, mul_comm] using h
  set tau : ℝ → ℂ := fun s => p.2.1 (s / L) / L with htaudef
  set D : ℝ → ℂ := fun s => p.2.2 (s / L) / (L ^ 2) with hDdef
  have hDderiv : ∀ s, HasDerivAt tau (D s) s := by
    intro s
    have h0 := (hp.hasDerivAt_vel (s / L)).scomp s (hinner s)
    have h := h0.div_const L
    simpa [htaudef, hDdef, Function.comp, div_eq_mul_inv, one_div, smul_eq_mul, sq, mul_comm,
      mul_assoc, mul_left_comm] using h
  have hnorm : ∀ s, ‖tau s‖ = 1 := by
    intro s
    rw [htaudef]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos]
    rw [norm_vel_eq_perim hp, ← hL]
    field_simp
  have hDcont : Continuous D := by
    have h : Continuous fun s : ℝ => p.2.2 (s / L) :=
      p.2.2.continuous.comp (continuous_id.div_const L)
    exact h.div_const _
  -- the arclength curvature is the normalized curvature at the rescaled time
  have hkey : ∀ s, ((starRingEnd ℂ) (tau s) * D s).im = dataCurv p (s / L) := by
    intro s
    have h : (starRingEnd ℂ) (tau s) * D s
        = ((starRingEnd ℂ) (p.2.1 (s / L)) * p.2.2 (s / L)) / ((L ^ 3 : ℝ) : ℂ) := by
      rw [htaudef, hDdef]
      simp only [map_div₀, Complex.conj_ofReal]
      push_cast
      field_simp
    rw [h, Complex.div_ofReal_im, dataCurv, norm_vel_eq_perim hp, ← hL]
  obtain ⟨theta, hthetaderiv, hthetaexp⟩ := exists_angle hnorm hDderiv hDcont
  refine ⟨theta, fun s => ?_, fun s => ?_⟩
  · have := hev s
    rwa [show p.2.1 (s / L) / L = tau s from rfl, ← hthetaexp s] at this
  · have := hthetaderiv s
    rwa [hkey s] at this

end MarkedSpace
