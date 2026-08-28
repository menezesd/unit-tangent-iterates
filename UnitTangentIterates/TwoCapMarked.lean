import Mathlib
import UnitTangentIterates.TwoCapPairsExistence
import UnitTangentIterates.SelectedInverseTube
import UnitTangentIterates.ConvexEmbedded

/-!
# The exact two-cap pair as a pair of marked curves

`TwoCapPairsExistence.lean` produces, for an `H`-periodic front curvature
`K` with `0 ≤ K ≤ κ̂ < 1` and total turning `π` over one period, the exact
two-cap pair of the paper *A Noncircular Oval with Convex Unit-Tangent
Iterates*: a unit-speed front `F_H` of perimeter `2H`, and a rear track `R_H`
with `𝒯R_H = F_H`.  Those are curves; the shadowing scheme of the last section
of the paper, however, runs in the **space of marked curves** of
`MarkedSpace.lean`, whose members carry a normalized parameter.

This file puts the two-cap pair into that space.  For a front curvature pinched
by `0 < kmin ≤ K ≤ κ̂ < 1`, and with the embeddedness of the front carried as a
hypothesis (as global topological facts are throughout this project):

* `exists_marked_front` : the front is a member of the tube, with perimeter
  `2H`, with the given curve as its arclength parametrization and with its
  curvature bounded above by `κ̂`;
* `exists_marked_two_cap_pair` : both members of the pair are members of the
  tube — the rear with curvature at least `kmin/√(1−kmin²)`, perimeter at most
  that of the front, and unit-tangent transform retracing the front — so the
  model curve of the paper *is* an object of the space of marked curves, and
  the marked selected inverse of the front is its two-cap partner.

The hypotheses are not vacuous: `marked_two_cap_front_circle` checks them for
the constant curvature `1/2` and the half-period `2π`, whose front is the
circle of radius `2`.
-/

noncomputable section

open Set Function MarkedSpace

namespace TwoCapMarked

open TwoCapPairsAssembly CurvatureInterpolation

/-! ### The front is a marked curve -/

/-- **The front of a two-cap pair is a member of the tube of marked curves.**
For a continuous `H`-periodic front curvature pinched by `kmin ≤ K ≤ κ̂` and of
total turning `π` over one period, whose front is embedded, the front is the
arclength parametrization of a marked curve of perimeter `2H` and curvature
at most `κ̂`. -/
theorem exists_marked_front {kappa : ℝ → ℝ} {H kmin kap theta0 : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (hkmin : ∀ s, kmin ≤ kappa s) (hkap : ∀ s, kappa s ≤ kap)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = Real.pi)
    (hinj : InjOn (front kappa theta0 H) (Ico 0 (2 * H))) :
    ∃ (q : Data) (d : ℝ), 0 < d ∧ IsTubeMember (2 * H) kmin d q ∧ perim q = 2 * H ∧
      ev q = front kappa theta0 H ∧
      ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kap * ‖q.2.1 u‖ ^ 3 := by
  have hper2 : Periodic kappa (2 * H) := by
    simpa using hper.nat_mul 2
  exact SelectedInverseTube.exists_tube_member_of_oval (by linarith)
    (front_periodic hk hper htotal) hinj
    (fun s => front_hasDerivAt (theta0 := theta0) (H := H) hk s)
    (fun s => hasDerivAt_tangentAngle (θ₀ := theta0) hk s) hk hper2 hkmin hkap

/-! ### The pair is a pair of marked curves -/

/-- **The exact two-cap pair, as a pair of marked curves.**  For a front
curvature pinched by `0 < kmin ≤ K ≤ κ̂ < 1`, with total turning `π` over one
period, whose front and whose rear track are embedded, both members of the
two-cap pair are members of the tube of marked curves: the front with perimeter
`2H` and curvature at most `κ̂`, the rear with curvature at least
`kmin/√(1−kmin²)`, perimeter at most `2H`, and unit-tangent transform retracing
the front. -/
theorem exists_marked_two_cap_pair {kappa : ℝ → ℝ} {H kmin kap theta0 : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (hkminpos : 0 < kmin) (hkap1 : kap < 1)
    (hkmin : ∀ s, kmin ≤ kappa s) (hkap : ∀ s, kappa s ≤ kap)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = Real.pi)
    (hinj : InjOn (front kappa theta0 H) (Ico 0 (2 * H)))
    (hinjR : ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (front kappa theta0 H) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Periodic dl (2 * H) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (RearTrack.rearTrack (front kappa theta0 H) Θ dl) (Ico 0 (2 * H))) :
    ∃ (qF qR : Data) (dF dR LR : ℝ),
      0 < dF ∧ IsTubeMember (2 * H) kmin dF qF ∧ perim qF = 2 * H ∧
        ev qF = front kappa theta0 H ∧
      0 < LR ∧ 0 < dR ∧ IsTubeMember LR (kmin / Real.sqrt (1 - kmin ^ 2)) dR qR ∧
        perim qR = LR ∧ LR ≤ 2 * H ∧
        MainTheoremConditional.IsOval (ev qR) ∧
        range (UnitTangent.unitTangentMap (ev qR)) = range (front kappa theta0 H) := by
  obtain ⟨qF, dF, hdF, hmemF, hperimF, hevF, hubF⟩ :=
    exists_marked_front hH hk hper hkmin hkap htotal hinj
  have hcF : (0:ℝ) < 2 * H := by linarith
  have hinjR' : ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev qF) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Periodic dl (perim qF) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (RearTrack.rearTrack (ev qF) Θ dl) (Ico 0 (perim qF)) := by
    intro Θ K dl h1 h2 h3 h4 h5
    rw [hevF] at h1 ⊢
    rw [hperimF] at h3 ⊢
    exact hinjR Θ K dl h1 h2 h3 h4 h5
  obtain ⟨qR, LR, dR, hLR, hdR, hmemR, hperimR, hle, hovalR, -, hrange⟩ :=
    SelectedInverseTube.exists_tube_member_rear hcF hkminpos hkap1 hmemF hubF hinjR'
  refine ⟨qF, qR, dF, dR, LR, hdF, hmemF, hperimF, hevF, hLR, hdR, hmemR, hperimR, ?_, hovalR, ?_⟩
  · rw [← hperimF, ← hperimR]; exact hle
  · rw [hrange, hevF]

/-! ### The front is embedded, unconditionally -/

/-- **The two-cap front tangent angle turns by `2π` over its full period.**  The
prescribed curvature has total turning `π` over a half period, so two
applications of `TwoCapPairsAssembly.frontAngle_add_halfPeriod` give the full
turning identity.  This is the turning number of the front, and for the paper's
model curves it is exact by construction rather than a topological input. -/
theorem frontAngle_add_period {kappa : ℝ → ℝ} {theta0 H : ℝ}
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = Real.pi) (s : ℝ) :
    frontAngle kappa theta0 (s + 2 * H) = frontAngle kappa theta0 s + 2 * Real.pi := by
  have h1 := frontAngle_add_halfPeriod (theta0 := theta0) hk hper htotal s
  have h2 := frontAngle_add_halfPeriod (theta0 := theta0) hk hper htotal (s + H)
  have hs : s + 2 * H = s + H + H := by ring
  rw [hs, h2, h1]
  ring

/-- The front tangent angle is strictly increasing when the prescribed curvature
is strictly positive. -/
theorem strictMono_frontAngle {kappa : ℝ → ℝ} {theta0 kmin : ℝ}
    (hk : Continuous kappa) (hkminpos : 0 < kmin) (hkmin : ∀ s, kmin ≤ kappa s) :
    StrictMono (frontAngle kappa theta0) := by
  have hd : ∀ s, HasDerivAt (frontAngle kappa theta0) (kappa s) s :=
    fun s => hasDerivAt_tangentAngle (θ₀ := theta0) hk s
  refine strictMono_of_deriv_pos fun s => ?_
  rw [(hd s).deriv]
  exact lt_of_lt_of_le hkminpos (hkmin s)

/-- **The two-cap front is embedded.**  Strict positivity of the prescribed
curvature makes the tangent angle strictly increasing, and the total turning is
exactly `2π` by construction, so `ConvexEmbedded.injOn_Ico_of_turning_one`
applies.  Front embeddedness is therefore *not* an extra topological hypothesis
for the curves of the paper's model orbit. -/
theorem injOn_front {kappa : ℝ → ℝ} {theta0 H kmin : ℝ}
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (hkminpos : 0 < kmin) (hkmin : ∀ s, kmin ≤ kappa s)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = Real.pi) :
    InjOn (front kappa theta0 H) (Ico 0 (2 * H)) := by
  have hd : ∀ s, HasDerivAt (frontAngle kappa theta0) (kappa s) s :=
    fun s => hasDerivAt_tangentAngle (θ₀ := theta0) hk s
  have hcont : Continuous (frontAngle kappa theta0) :=
    continuous_iff_continuousAt.2 fun s => (hd s).differentiableAt.continuousAt
  have hX : ∀ s, HasDerivAt (front kappa theta0 H)
      ((((1 : ℝ)) : ℂ) *
        Complex.exp (Complex.I * (frontAngle kappa theta0 s : ℂ))) s := by
    intro s
    simpa using front_hasDerivAt (theta0 := theta0) (H := H) hk s
  have hres := ConvexEmbedded.injOn_Ico_of_turning_one (v := fun _ => (1 : ℝ)) hX
    (fun _ => one_pos) hcont (strictMono_frontAngle hk hkminpos hkmin)
    (frontAngle_add_period (theta0 := theta0) hk hper htotal)
    (front_periodic hk hper htotal) 0
  simpa using hres

/-! ### The hypotheses are not vacuous -/

/-- The constant curvature `1/2`. -/
def kcirc : ℝ → ℝ := fun _ => 1 / 2

theorem continuous_kcirc : Continuous kcirc := continuous_const

theorem kcirc_periodic : Periodic kcirc (2 * Real.pi) := fun _ => rfl

theorem kcirc_total : (∫ r in (0:ℝ)..(2 * Real.pi), kcirc r) = Real.pi := by
  simp [kcirc]; ring

/-- The tangent angle of the constant-curvature front is `s/2`. -/
theorem tangentAngle_kcirc (s : ℝ) : tangentAngle kcirc 0 s = s / 2 := by
  simp [tangentAngle, kcirc]; ring

/-- The constant-curvature front is a circle of radius `2`: it differs from
`−2i e^{is/2}` by a constant. -/
theorem front_kcirc_sub (s t : ℝ) :
    front kcirc 0 (2 * Real.pi) s - front kcirc 0 (2 * Real.pi) t
      = -(2 * Complex.I) * (tau (s / 2) - tau (t / 2)) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun r : ℝ =>
      front kcirc 0 (2 * Real.pi) r + (2 * Complex.I) * tau (r / 2)) 0 x := by
    intro x
    have h1 : HasDerivAt (front kcirc 0 (2 * Real.pi)) (tau (x / 2)) x := by
      have h := front_hasDerivAt (kappa := kcirc) (theta0 := 0) (H := 2 * Real.pi)
        continuous_kcirc x
      rw [← tau_eq_exp] at h
      simpa [frontAngle, tangentAngle_kcirc] using h
    have h2 : HasDerivAt (fun r : ℝ => (2 * Complex.I) * tau (r / 2))
        (-(tau (x / 2))) x := by
      have hhalf : HasDerivAt (fun r : ℝ => r / 2) (1 / 2 : ℝ) x :=
        (hasDerivAt_id x).div_const 2
      have h := ((hasDerivAt_tau (x / 2)).scomp x hhalf).const_mul (2 * Complex.I)
      have heq : (2 * Complex.I) * ((1 / 2 : ℝ) • (Complex.I * tau (x / 2)))
          = -(tau (x / 2)) := by
        rw [Complex.real_smul]
        push_cast
        rw [show (2 * Complex.I) * ((1 / 2 : ℂ) * (Complex.I * tau (x / 2)))
            = Complex.I ^ 2 * tau (x / 2) by ring, Complex.I_sq]
        ring
      exact h.congr_deriv heq
    simpa using h1.add h2
  have hconst : ∀ x y : ℝ,
      front kcirc 0 (2 * Real.pi) x + (2 * Complex.I) * tau (x / 2)
        = front kcirc 0 (2 * Real.pi) y + (2 * Complex.I) * tau (y / 2) := by
    intro x y
    have := is_const_of_deriv_eq_zero
      (f := fun r : ℝ => front kcirc 0 (2 * Real.pi) r + (2 * Complex.I) * tau (r / 2))
      (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) x y
    exact this
  have h := hconst s t
  have : front kcirc 0 (2 * Real.pi) s - front kcirc 0 (2 * Real.pi) t
      = (2 * Complex.I) * tau (t / 2) - (2 * Complex.I) * tau (s / 2) := by
    linear_combination h
  rw [this]; ring

/-- **The constant-curvature front is embedded.**  A special case of the
general `injOn_front`; no separate argument for the circle is needed. -/
theorem injOn_front_kcirc :
    InjOn (front kcirc 0 (2 * Real.pi)) (Ico 0 (2 * (2 * Real.pi))) :=
  injOn_front (kmin := 1 / 2) continuous_kcirc kcirc_periodic (by norm_num)
    (fun _ => le_rfl) kcirc_total

/-- **The hypotheses of `exists_marked_front` are not vacuous.**  The constant
curvature `1/2` with half-period `2π` — whose front is the circle of radius `2`
and perimeter `4π` — satisfies them, so it is a marked curve of the tube. -/
theorem marked_two_cap_front_circle :
    ∃ (q : Data) (d : ℝ), 0 < d ∧ IsTubeMember (2 * (2 * Real.pi)) (1 / 2) d q ∧
      perim q = 2 * (2 * Real.pi) ∧ ev q = front kcirc 0 (2 * Real.pi) ∧
      ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ (1 / 2) * ‖q.2.1 u‖ ^ 3 :=
  exists_marked_front (kmin := 1/2) (kap := 1/2) (by positivity) continuous_kcirc
    kcirc_periodic (fun _ => le_rfl) (fun _ => le_rfl) kcirc_total injOn_front_kcirc

end TwoCapMarked
