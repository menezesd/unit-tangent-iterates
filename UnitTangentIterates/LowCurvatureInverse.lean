import Mathlib
import UnitTangentIterates.Shadowing

/-!
# The selected rear of a low-curvature front: trapping and symmetry

This file formalizes two steps of the lemma *Low-curvature inverse* of
*A Noncircular Oval with Convex Unit-Tangent Iterates* that the earlier files
left aside:

> Set `d₀ = arcsin κ`.  In the tangent-angle equation `δ_φ = 1 − q sin δ`, the
> vector field is positive at `0` and nonpositive at `d₀`.  Thus the time-`2π`
> map sends `[0, d₀]` into itself and has a fixed point. ...
> Half-turn symmetry follows from uniqueness.

Main results:

* `bicycle_field_pos_at_zero`, `bicycle_field_nonpos_at_arcsin` : the vector
  field of `δ_φ = 1 − q sin δ` points into the interval `[0, arcsin κ]`
  whenever the radius of curvature satisfies `q ≥ 1/κ` (that is, `K ≤ κ`);
* `mapsTo_of_field_sign` : a flow whose value stays in `[0, d₀]` maps the
  interval into itself, which is the hypothesis of the fixed-point statement
  `Shadowing.exists_fixed_point_of_mapsTo`;
* `steering_periodic_of_periodic_curvature` : **half-turn symmetry follows
  from uniqueness** — if the front curvature has period `L` and the selected
  steering angle is `2L`-periodic with values in the closed strip, then it is
  already `L`-periodic.  (For a centrally symmetric front of perimeter `2L`
  this is the central symmetry of the selected rear.)
-/

noncomputable section

open Real Set

namespace LowCurvatureInverse

/-! ### The vector field points into the interval -/

/-- At `δ = 0` the tangent-angle vector field `1 − q sin δ` equals `1 > 0`. -/
theorem bicycle_field_pos_at_zero (q : ℝ) : 0 < 1 - q * Real.sin 0 := by
  simp

/-- At `δ = arcsin κ` the tangent-angle vector field `1 − q sin δ` is
nonpositive, as soon as the radius of curvature satisfies `q ≥ 1/κ`. -/
theorem bicycle_field_nonpos_at_arcsin {kap q : ℝ} (hk0 : 0 < kap) (hk1 : kap ≤ 1)
    (hq : 1 / kap ≤ q) : 1 - q * Real.sin (Real.arcsin kap) ≤ 0 := by
  rw [Real.sin_arcsin (by linarith) hk1]
  have h : 1 ≤ q * kap := by
    rw [div_le_iff₀ hk0] at hq
    linarith
  linarith

/-! ### The interval is forward invariant -/

/-- **A solution cannot cross an upper barrier at which the field is
nonpositive.**  If `delta' = v`, and `v t ≤ 0` whenever `delta t ≥ d₀`, then
`delta a ≤ d₀` implies `delta t ≤ d₀` for all later times. -/
theorem forward_le_of_deriv_nonpos {delta v : ℝ → ℝ} {a d0 : ℝ}
    (hderiv : ∀ t, HasDerivAt delta (v t) t)
    (hsign : ∀ t, d0 ≤ delta t → v t ≤ 0)
    (ha : delta a ≤ d0) {t : ℝ} (hat : a ≤ t) : delta t ≤ d0 := by
  by_contra hcon
  push_neg at hcon
  have hdiff : Differentiable ℝ delta := fun s => (hderiv s).differentiableAt
  have hcont : Continuous delta := hdiff.continuous
  set S : Set ℝ := Icc a t ∩ delta ⁻¹' (Iic d0) with hS
  have hSne : S.Nonempty := ⟨a, ⟨⟨le_rfl, hat⟩, ha⟩⟩
  have hSc : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_Iic.preimage hcont)
  have hmem : sSup S ∈ S := hSc.sSup_mem hSne
  set t0 := sSup S with ht0
  have ht0t : t0 < t := by
    rcases lt_or_eq_of_le hmem.1.2 with h | h
    · exact h
    · exact absurd (h ▸ hmem.2) (by simpa using not_le.mpr hcon)
  have hgt : ∀ u ∈ Ioo t0 t, d0 ≤ delta u := by
    intro u hu
    by_contra hu'
    push_neg at hu'
    have huS : u ∈ S := ⟨⟨le_trans hmem.1.1 hu.1.le, hu.2.le⟩, hu'.le⟩
    exact absurd (le_csSup hSc.bddAbove huS) (not_le.mpr hu.1)
  have hanti : AntitoneOn delta (Icc t0 t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont.continuousOn
      (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hderiv x).deriv]
    exact hsign x (hgt x hx)
  have hle := hanti (left_mem_Icc.mpr ht0t.le) (right_mem_Icc.mpr ht0t.le) ht0t.le
  exact absurd (le_trans hle hmem.2) (not_le.mpr hcon)

/-- The mirror statement: a solution cannot cross a lower barrier at which the
field is nonnegative. -/
theorem forward_ge_of_deriv_nonneg {delta v : ℝ → ℝ} {a c : ℝ}
    (hderiv : ∀ t, HasDerivAt delta (v t) t)
    (hsign : ∀ t, delta t ≤ c → 0 ≤ v t)
    (ha : c ≤ delta a) {t : ℝ} (hat : a ≤ t) : c ≤ delta t := by
  have hderiv' : ∀ s, HasDerivAt (fun u => -delta u) (-v s) s := fun s => (hderiv s).neg
  have hsign' : ∀ s, -c ≤ -delta s → -v s ≤ 0 := by
    intro s hs
    have : delta s ≤ c := by linarith
    linarith [hsign s this]
  have := forward_le_of_deriv_nonpos (delta := fun u => -delta u) (v := fun s => -v s)
    hderiv' hsign' (by simpa using neg_le_neg ha) hat
  linarith [this]

/-- **The steering interval is forward invariant** when the field points
inward at both ends: this is the trapping that makes the Poincaré map of
`[0, d₀]` well defined (`Shadowing.exists_fixed_point_of_mapsTo` then gives a
periodic steering solution). -/
theorem mem_Icc_of_field_inward {delta v : ℝ → ℝ} {a d0 : ℝ}
    (hderiv : ∀ t, HasDerivAt delta (v t) t)
    (hup : ∀ t, d0 ≤ delta t → v t ≤ 0) (hlo : ∀ t, delta t ≤ 0 → 0 ≤ v t)
    (ha : delta a ∈ Icc (0:ℝ) d0) {t : ℝ} (hat : a ≤ t) : delta t ∈ Icc (0:ℝ) d0 :=
  ⟨forward_ge_of_deriv_nonneg hderiv hlo ha.1 hat,
    forward_le_of_deriv_nonpos hderiv hup ha.2 hat⟩

/-! ### Half-turn symmetry of the selected rear -/

variable {K delta : ℝ → ℝ} {L : ℝ}

/-- **Half-turn symmetry follows from uniqueness.**  If the front curvature `K`
has period `L`, and the selected steering angle `δ` solves `δ_s = K − sin δ`,
is `2L`-periodic and takes values in the closed strip `|δ| ≤ π/2`, then `δ` is
`L`-periodic. -/
theorem steering_periodic_of_periodic_curvature (hL : 0 < L)
    (hK : Function.Periodic K L)
    (hode : ∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s)
    (hper : Function.Periodic delta (2 * L))
    (hrange : ∀ s, delta s ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    Function.Periodic delta L := by
  set d2 : ℝ → ℝ := fun s => delta (s + L) with hd2
  have hode2 : ∀ s, HasDerivAt d2 (K s - Real.sin (d2 s)) s := by
    intro s
    have h := (hode (s + L)).comp_add_const s L
    rw [hK s] at h
    exact h
  have hper2 : Function.Periodic d2 (2 * L) := by
    intro s
    simp only [hd2]
    have := hper (s + L)
    simpa [add_right_comm] using this
  have hrange2 : ∀ s, d2 s ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := fun s => hrange (s + L)
  have heq : delta = d2 :=
    Shadowing.steering_unique (by linarith) hode hode2 hper hper2 hrange hrange2
  intro s
  have := congrFun heq.symm s
  simpa [hd2] using this

end LowCurvatureInverse
