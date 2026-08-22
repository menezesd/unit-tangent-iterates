import Mathlib
import UnitTangentIterates.RearOval
import UnitTangentIterates.SteeringExistence
import UnitTangentIterates.LowCurvatureAssembly

/-!
# The selected inverse of an oval front is an oval

This file assembles the *selected inverse* of the paper *A Noncircular Oval
with Convex Unit-Tangent Iterates* at the level of **curves**: given an oval
front whose curvature is pinched between `0 < k_min` and `κ̂ < 1`, the selected
steering solution exists (`SteeringExistence.exists_periodic_steering`), the
rear track it defines is a closed regular curve of positive curvature
(`RearTrack.lean`, `LowCurvatureAssembly.lean`), and reparametrizing it by its
own arclength turns it into an oval whose unit-tangent transform retraces the
front (`RearOval.lean`).

* `exists_oval_rear_of_oval_front` : **every admissible oval is the
  unit-tangent transform, up to reparametrization, of an oval** — if `X` is a
  closed unit-speed curve of curvature `k_min ≤ K ≤ κ̂ < 1` (with `k_min > 0`)
  then there is an oval `Y` with `range (𝒯 Y) = range X`, and the curvature of
  `Y` is pinched between `k_min/√(1-k_min²)` and `κ̂/√(1-κ̂²)`.

As everywhere in this project, the global topological fact that the rear track
is embedded is carried as an explicit hypothesis.
-/

noncomputable section

open Set Function

namespace SelectedInverseOval

/-- The unit tangent of a `p`-periodic curve is `p`-periodic. -/
theorem expTangent_periodic {X : ℝ → ℂ} {Θ : ℝ → ℝ} {p : ℝ}
    (hX : ∀ s, HasDerivAt X (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hXper : Periodic X p) (s : ℝ) :
    Complex.exp (Complex.I * (Θ (s + p) : ℂ)) = Complex.exp (Complex.I * (Θ s : ℂ)) := by
  have hshift := (hX (s + p)).comp_add_const s p
  rw [hXper.funext] at hshift
  exact hshift.unique (hX s)

/-- **Every admissible oval is the unit-tangent transform of an oval, up to
reparametrization.**  Let `X` be a closed unit-speed plane curve with tangent
angle `Θ`, curvature `K = Θ'` pinched by `0 < k_min ≤ K ≤ κ̂ < 1`, and period
`p`.  Then the selected rear of `X`, reparametrized by its own arclength, is an
oval `Y` with `range (𝒯 Y) = range X`, whose curvature `k_Y` obeys the pinch
`k_min/√(1-k_min²) ≤ k_Y ≤ κ̂/√(1-κ̂²)`. -/
theorem exists_oval_rear_of_oval_front {X : ℝ → ℂ} {Θ K : ℝ → ℝ} {p kmin kap : ℝ}
    (hp : 0 < p) (hkmin : 0 < kmin) (hkap1 : kap < 1)
    (hKc : Continuous K) (hKper : Periodic K p)
    (hX : ∀ s, HasDerivAt X (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hXper : Periodic X p)
    (hKlow : ∀ s, kmin ≤ K s) (hKhigh : ∀ s, K s ≤ kap)
    (hinj : ∀ delta : ℝ → ℝ, Periodic delta p →
      (∀ s, delta s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s) →
      InjOn (RearTrack.rearTrack X Θ delta) (Ico 0 p)) :
    ∃ (Y : ℝ → ℂ) (th kY : ℝ → ℝ) (q : ℝ),
      MainTheoremConditional.IsOval Y ∧
      range (UnitTangent.unitTangentMap Y) = range X ∧
      0 < q ∧ Periodic Y q ∧ Continuous kY ∧ Periodic kY q ∧
      (∀ y, HasDerivAt Y (Complex.exp (Complex.I * (th y : ℂ))) y) ∧
      (∀ y, HasDerivAt th (kY y) y) ∧
      (∀ y, kmin / Real.sqrt (1 - kmin ^ 2) ≤ kY y ∧
        kY y ≤ kap / Real.sqrt (1 - kap ^ 2)) ∧ q ≤ p := by
  have hkap0 : 0 ≤ kap := le_trans hkmin.le (le_trans (hKlow 0) (hKhigh 0))
  obtain ⟨delta, hdper, hdmem, hdcos, hode⟩ :=
    SteeringExistence.exists_periodic_steering hp hKc hKper hkap0 hkap1.le
      (fun s => le_trans hkmin.le (hKlow s)) hKhigh
  have hΘc : Continuous Θ := Differentiable.continuous fun s => (hΘ s).differentiableAt
  have hdc : Continuous delta :=
    Differentiable.continuous fun s => (hode s).differentiableAt
  -- the speed of the rear is bounded below
  have hcpos : 0 < Real.sqrt (1 - kap ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  -- the rear curvature is positive
  have hdpos : ∀ s, 0 < delta s :=
    LowCurvatureAssembly.steering_pos_of_curvature_pos hode (fun s => (hdmem s).1)
      (fun s => lt_of_lt_of_le hkmin (hKlow s))
  have hdlt : ∀ s, delta s < Real.pi / 2 := by
    intro s
    refine lt_of_le_of_lt (hdmem s).2 ?_
    have := Real.arcsin_lt_pi_div_two (x := kap)
    exact this.mpr (by linarith)
  have htan : ∀ s, 0 < Real.tan (delta s) := fun s =>
    Real.tan_pos_of_pos_of_lt_pi_div_two (hdpos s) (hdlt s)
  -- periodicity of the front's unit tangent
  have hexpper : ∀ s, Complex.exp (Complex.I * (Θ (s + p) : ℂ))
      = Complex.exp (Complex.I * (Θ s : ℂ)) := expTangent_periodic hX hXper
  have htanper : ∀ s, Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta (s + p) : ℂ))
      = Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta s : ℂ)) := by
    intro s
    have hsplit : ∀ t : ℝ, Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta t : ℂ))
        = Complex.exp (Complex.I * (Θ t : ℂ)) * Complex.exp (-(Complex.I * (delta t : ℂ))) := by
      intro t
      rw [← Complex.exp_add]
      congr 1
      simp [RearTrack.rearAngle]
      ring
    rw [hsplit (s + p), hsplit s, hexpper s, hdper s]
  have hRper : Periodic (RearTrack.rearTrack X Θ delta) p := by
    intro s
    simp only [RearTrack.rearTrack]
    rw [hXper s, htanper s]
  obtain ⟨Y, phi, L, hoval, -, hrange, hLpos, hYper, -, hphic, hphiper, hth, hthderiv, hLeq⟩ :=
    RearOval.exists_isOval_rear_unitTangent_range_eq (K := K) hp hcpos hdcos hdc hΘc hX hΘ
      hode htan hRper hdper htanper (hinj delta hdper hdmem hode)
  have hpinch := LowCurvatureAssembly.selected_rear_curvature_pinched hp hkmin.le hkap1
    hdper hode hdmem hKlow
  refine ⟨Y, fun y => RearTrack.rearAngle Θ delta (phi y),
    fun y => Real.tan (delta (phi y)), L, hoval, hrange, hLpos, hYper, ?_, ?_,
    hth, hthderiv, fun y => hpinch (phi y), ?_⟩
  · have hcomp : Continuous fun y => delta (phi y) := hdc.comp hphic
    have heq : (fun y => Real.tan (delta (phi y)))
        = fun y => Real.sin (delta (phi y)) / Real.cos (delta (phi y)) :=
      funext fun y => Real.tan_eq_sin_div_cos _
    rw [heq]
    exact (Real.continuous_sin.comp hcomp).div (Real.continuous_cos.comp hcomp)
      (fun y => ne_of_gt (lt_of_lt_of_le hcpos (hdcos (phi y))))
  · intro y
    show Real.tan (delta (phi (y + L))) = Real.tan (delta (phi y))
    rw [hphiper y, hdper (phi y)]
  · -- the rear is not longer than the front: `L = ∫₀^p cos δ ≤ p`
    rw [hLeq]
    have hint : IntervalIntegrable (fun s => Real.cos (delta s)) MeasureTheory.volume 0 p :=
      (Real.continuous_cos.comp hdc).intervalIntegrable _ _
    have hmono : (∫ s in (0:ℝ)..p, Real.cos (delta s)) ≤ ∫ _s in (0:ℝ)..p, (1:ℝ) :=
      intervalIntegral.integral_mono_on hp.le hint intervalIntegrable_const
        (fun s _ => Real.cos_le_one _)
    simpa using hmono

end SelectedInverseOval
