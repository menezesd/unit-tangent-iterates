import Mathlib
import UnitTangentIterates.SelectedInverseRearOwn

/-!
# The marked selected inverse is well defined

`SelectedInverseRearOwn.exists_marked_rearOwn` **produces** a marked selected
inverse of a member of the tube.  For the shadowing scheme of the paper the
selected inverse has to be a *map*, so what is produced must also be unique.
This file proves that it is.

* `tube_ext` — a member of the tube is determined by its curve: the velocity
  and the acceleration are its derivatives, so two members with the same curve
  are equal;
* `perim_pos_of_rearArclength` — the rear period of an admissible steering
  angle is positive;
* `marked_rearOwn_unique` — **uniqueness of the marked selected inverse**: any
  two marked curves that are the rear track of the same member of the tube
  written in its own arclength, for their own front data, steering angles and
  changes of variable, are equal.  The three auxiliary data are themselves
  determined: the tangent-angle lift only through its exponential (which is
  enough, by `rearTrack_congr_angle`), the steering angle by uniqueness of the
  periodic solution on the selected strip (`Shadowing.steering_unique`), and
  the change of variable because the rear arclength is strictly increasing.

Together with `exists_marked_rearOwn`, this says that the marked selected
inverse of a member of the tube of curvature pinched by `0 < kmin ≤ K ≤ κ̂ < 1`
exists and is unique — so it is a genuine map of marked curves.
-/

noncomputable section

open Set Function MarkedSpace RearTrack ArclengthInverse

namespace SelectedInverseUnique

/-- **A member of the tube is determined by its curve.** -/
theorem tube_ext {c₁ k₁ d₁ c₂ k₂ d₂ : ℝ} {p q : Data}
    (hp : IsTubeMember c₁ k₁ d₁ p) (hq : IsTubeMember c₂ k₂ d₂ q)
    (h : ∀ u, p.1 u = q.1 u) : p = q := by
  have h1 : p.1 = q.1 := by
    ext u
    exact h u
  have h2 : ∀ u, p.2.1 u = q.2.1 u := by
    intro u
    have hpd : HasDerivAt (⇑p.1) (p.2.1 u) u := hp.hasDerivAt_curve u
    have hqd : HasDerivAt (⇑p.1) (q.2.1 u) u := by
      rw [h1]; exact hq.hasDerivAt_curve u
    exact hpd.unique hqd
  have h2' : p.2.1 = q.2.1 := by
    ext u
    exact h2 u
  have h3 : ∀ u, p.2.2 u = q.2.2 u := by
    intro u
    have hpd : HasDerivAt (⇑p.2.1) (p.2.2 u) u := hp.hasDerivAt_vel u
    have hqd : HasDerivAt (⇑p.2.1) (q.2.2 u) u := by
      rw [h2']; exact hq.hasDerivAt_vel u
    exact hpd.unique hqd
  have h3' : p.2.2 = q.2.2 := by
    ext u
    exact h3 u
  exact Prod.ext h1 (Prod.ext h2' h3')

/-- The rear period of an admissible steering angle is positive. -/
theorem rearArclength_pos {dl : ℝ → ℝ} {kap L : ℝ} (hL : 0 < L) (hkap0 : 0 ≤ kap)
    (hkap1 : kap < 1) (hdc : Continuous dl)
    (hdmem : ∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) : 0 < rearArclength dl L := by
  have hcpos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  exact SelectedInverseRearOwn.rearPeriod_pos hL hcpos hdc fun s =>
    Shadowing.cos_ge_of_mem_strip (hdmem s).1 (hdmem s).2

/-- **The marked selected inverse is unique.**  Two marked curves that are both
the rear track of the same member `p` of the tube, written in their own
arclength and marked at `x = 0`, are equal — whatever front data, steering
angle and change of variable they were built from. -/
theorem marked_rearOwn_unique {c kmin dlt kap : ℝ} (hc : 0 < c) (hkap0 : 0 ≤ kap)
    (hkap1 : kap < 1) {p q₁ q₂ : Data} (hp : IsTubeMember c kmin dlt p)
    {c₁ k₁ d₁ c₂ k₂ d₂ : ℝ} (hq₁ : IsTubeMember c₁ k₁ d₁ q₁)
    (hq₂ : IsTubeMember c₂ k₂ d₂ q₂)
    {Θ₁ K₁ dl₁ sf₁ Θ₂ K₂ dl₂ sf₂ : ℝ → ℝ}
    (hX₁ : ∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ₁ s : ℂ))) s)
    (hΘ₁ : ∀ s, HasDerivAt Θ₁ (K₁ s) s)
    (hdper₁ : Function.Periodic dl₁ (perim p))
    (hdmem₁ : ∀ s, dl₁ s ∈ Icc 0 (Real.arcsin kap))
    (hode₁ : ∀ s, HasDerivAt dl₁ (K₁ s - Real.sin (dl₁ s)) s)
    (hsfinv₁ : ∀ x, rearArclength dl₁ (sf₁ x) = x)
    (hperim₁ : perim q₁ = rearArclength dl₁ (perim p))
    (hev₁ : ∀ x, ev q₁ x = rearTrack (ev p) Θ₁ dl₁ (sf₁ x))
    (hX₂ : ∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ₂ s : ℂ))) s)
    (hΘ₂ : ∀ s, HasDerivAt Θ₂ (K₂ s) s)
    (hdper₂ : Function.Periodic dl₂ (perim p))
    (hdmem₂ : ∀ s, dl₂ s ∈ Icc 0 (Real.arcsin kap))
    (hode₂ : ∀ s, HasDerivAt dl₂ (K₂ s - Real.sin (dl₂ s)) s)
    (hsfinv₂ : ∀ x, rearArclength dl₂ (sf₂ x) = x)
    (hperim₂ : perim q₂ = rearArclength dl₂ (perim p))
    (hev₂ : ∀ x, ev q₂ x = rearTrack (ev p) Θ₂ dl₂ (sf₂ x)) :
    q₁ = q₂ := by
  have hLpos : 0 < perim p := perim_pos hc hp
  -- the two lifts of the tangent angle have the same exponential, hence the same curvature
  have hexp : ∀ s, Complex.exp (Complex.I * (Θ₁ s : ℂ))
      = Complex.exp (Complex.I * (Θ₂ s : ℂ)) := fun s => (hX₁ s).unique (hX₂ s)
  have hK : ∀ s, K₁ s = K₂ s :=
    SelectedInverseTube.curvature_unique hX₁ hX₂ hΘ₁ hΘ₂
  -- the steering angles agree
  have harc : Real.arcsin kap ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two kap
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hdl : dl₁ = dl₂ := by
    refine Shadowing.steering_unique (K := K₂) hLpos ?_ hode₂ hdper₁ hdper₂ ?_ ?_
    · intro s
      have h := hode₁ s
      rw [hK s] at h
      exact h
    · exact fun s => ⟨by linarith [(hdmem₁ s).1], le_trans (hdmem₁ s).2 harc⟩
    · exact fun s => ⟨by linarith [(hdmem₂ s).1], le_trans (hdmem₂ s).2 harc⟩
  -- the changes of variable agree
  have hdc₁ : Continuous dl₁ := Differentiable.continuous fun s => (hode₁ s).differentiableAt
  have hcpos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hcos₁ : ∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (dl₁ s) := fun s =>
    Shadowing.cos_ge_of_mem_strip (hdmem₁ s).1 (hdmem₁ s).2
  have hmono : StrictMono (rearArclength dl₁) :=
    strictMono_of_deriv_ge hcpos (fun s => hasDerivAt_rearArclength hdc₁ s) hcos₁
  have hsf : sf₁ = sf₂ := by
    funext x
    refine hmono.injective ?_
    rw [hsfinv₁ x, hdl, hsfinv₂ x]
  -- the perimeters agree, hence the two marked curves do
  have hperimeq : perim q₁ = perim q₂ := by rw [hperim₁, hperim₂, hdl]
  have hQpos : 0 < perim q₁ := by
    rw [hperim₁]
    exact rearArclength_pos hLpos hkap0 hkap1 hdc₁ hdmem₁
  refine tube_ext hq₁ hq₂ fun u => ?_
  have h₁ : q₁.1 u = ev q₁ (perim q₁ * u) := by
    simp only [ev]
    rw [mul_comm, mul_div_assoc, div_self hQpos.ne', mul_one]
  have h₂ : q₂.1 u = ev q₂ (perim q₂ * u) := by
    simp only [ev]
    rw [mul_comm, mul_div_assoc, div_self (hperimeq ▸ hQpos).ne', mul_one]
  rw [h₁, h₂, hev₁, hev₂, ← hperimeq, hdl, hsf]
  exact SelectedInverseRearOwn.rearTrack_congr_angle hexp _

end SelectedInverseUnique
