import Mathlib
import UnitTangentIterates.SelectedInverseMap
import UnitTangentIterates.SelectedInverseRearOwn
import UnitTangentIterates.RearOwnTangential
import UnitTangentIterates.PathDataTaylorBounds

/-!
# The tangent-angle lift of the marked selected inverse

The `C²` comparison of the two marked selected inverses reads the terminal
curve through a tangent-angle lift: a `Θ_b` with
`(selInv κ̂ q)' = e^{iΘ_b}`, differentiable with derivative `k_b'` — the
curvature of the rear track — bounded by `k_b` and `k_L`-Lipschitz.  Those four
data are not independent: the marked selected inverse *is* the rear track of the
front written in its own arclength, so its tangent angle is `Ψ ∘ sf` and its
curvature is `tan δ ∘ sf`, which on the selected strip is bounded by
`κ̂/√(1−κ̂²)` and has arclength derivative `(K − sin δ)/cos³δ`, bounded by
`2κ̂/√(1−κ̂²)³`; the mean value inequality turns the second bound into the
Lipschitz constant.

Main result: `exists_tangent_lift_selInv`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace RearTrack ArclengthInverse

namespace SelInvTerminalLift

open SelectedInverseMap SelectedInverseRearOwn RearOwnTangential PathDataTaylorBounds

/-- **The tangent-angle lift of the marked selected inverse of a tube member.**
Its curvature is bounded by `κ̂/√(1−κ̂²)` and Lipschitz with constant
`2κ̂/√(1−κ̂²)³`. -/
theorem exists_tangent_lift_selInv {c kmin dlt kh : ℝ} (hc : 0 < c) (hkmin : 0 < kmin)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) {p : Data} (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kh * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Function.Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Θ dl) (Ico 0 (perim p))) :
    ∃ Θb kb' : ℝ → ℝ,
      (∀ s, HasDerivAt (ev (selInv kh p)) (Complex.exp (Complex.I * (Θb s : ℂ))) s) ∧
      (∀ s, HasDerivAt Θb (kb' s) s) ∧
      (∀ s, |kb' s| ≤ kh / Real.sqrt (1 - kh ^ 2)) ∧
      (∀ s t, |kb' s - kb' t| ≤ 2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3 * |s - t|) := by
  classical
  -- the marked selected inverse is the rear track in its own arclength
  obtain ⟨-, Θ, K, dl, sf, hX, hΘ, hdper, hdmem, hode, hsfinv, -, hev⟩ :=
    isMarkedSelectedInverse_selInv hc hkmin hkh1 hp hub hinjR
  -- the curvature of the front is the canonical one, hence bounded by `κ̂`
  obtain ⟨Θ₀, K₀, -, -, hX₀, hΘ₀, hK₀low, hK₀high⟩ :=
    SelectedInverseTube.exists_front_data hc hp hub
  have hKK₀ : ∀ s, K s = K₀ s := fun s =>
    SelectedInverseTube.curvature_unique hX hX₀ hΘ hΘ₀ s
  have hKbd : ∀ s, |K s| ≤ kh := by
    intro s
    rw [hKK₀ s, abs_le]
    exact ⟨by linarith [hK₀low s, hkmin.le], hK₀high s⟩
  -- the geometry of the selected strip
  have hcpos : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hcos : ∀ s, Real.sqrt (1 - kh ^ 2) ≤ Real.cos (dl s) := fun s =>
    Shadowing.cos_ge_of_mem_strip (hdmem s).1 (hdmem s).2
  have hcospos : ∀ s, 0 < Real.cos (dl s) := fun s => lt_of_lt_of_le hcpos (hcos s)
  have hdc : Continuous dl := Differentiable.continuous fun s => (hode s).differentiableAt
  have hsf : ∀ x, HasDerivAt sf (1 / Real.cos (dl (sf x))) x := fun x =>
    hasDerivAt_of_rightInverse hcpos (fun s => hasDerivAt_rearArclength hdc s) hcos hsfinv x
  -- the lift and its derivative
  refine ⟨fun x => rearAngle Θ dl (sf x), fun x => Real.tan (dl (sf x)), ?_, ?_, ?_, ?_⟩
  · intro x
    have hfun : ev (selInv kh p) = fun z => rearTrack (ev p) Θ dl (sf z) := funext hev
    rw [hfun]
    exact hasDerivAt_rearOwnCurve hcpos hdc hcos hsfinv hX hΘ hode x
  · intro x
    exact hasDerivAt_rearOwnAngleSf hcpos hdc hcos hsfinv hΘ hode x
  · intro x
    exact abs_tan_le_strip hkh0 hkh1 (hdmem (sf x)).1 (hdmem (sf x)).2
  · -- the derivative of the rear curvature is bounded, hence it is Lipschitz
    have hderiv : ∀ x, HasDerivAt (fun x' => Real.tan (dl (sf x')))
        ((K (sf x) - Real.sin (dl (sf x))) / Real.cos (dl (sf x)) ^ 3) x := by
      intro x
      exact hasDerivAt_rearCurv_space (δ := fun _ => dl) (K := fun _ => K)
        (sf := fun _ => sf) (fun _ s => hode s) (fun _ y => hsf y)
        (fun _ s => (hcospos s).ne') 0 x
    have hbd : ∀ x, |(K (sf x) - Real.sin (dl (sf x))) / Real.cos (dl (sf x)) ^ 3|
        ≤ 2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3 := fun x =>
      abs_curvDeriv_le_strip hkh0 hkh1 (hdmem (sf x)).1 (hdmem (sf x)).2 (hKbd (sf x))
    exact fun s t => abs_sub_le_of_deriv_bound hderiv hbd s t

end SelInvTerminalLift
