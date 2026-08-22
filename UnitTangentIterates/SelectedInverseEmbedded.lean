import Mathlib
import UnitTangentIterates.ConvexChordArcSpeed
import UnitTangentIterates.TwoCapMarked
import UnitTangentIterates.ModelChordArc
import UnitTangentIterates.SelectedInverseMap

/-!
# The rear track of a pinched front is embedded

Putting the two-cap pair of *A Noncircular Oval with Convex Unit-Tangent
Iterates* into the space of marked curves
(`TwoCapMarked.exists_marked_two_cap_pair`) carries two global hypotheses:
embeddedness of the front, and embeddedness of **every** rear track built from
an admissible steering angle of that front.  The second one was so far only
checked for the circle (`TwoCapMarkedCircle.lean`).

This file discharges it in general, from the curvature pinching of the front.
Let `F` be a closed front of period `L`, unit tangent `e^{iΘ}`, curvature
`Θ_s = κ` pinched by `0 < kmin ≤ κ`, turning by `2π` over one period, and let
`δ` be an `L`-periodic solution of the steering equation `δ_s = κ − sin δ` in
the selected strip `0 ≤ δ ≤ arcsin κ̂`, `κ̂ < 1`.  Then the rear track
`R = F − e^{i(Θ−δ)}` satisfies

`R_s = cos δ · e^{iΨ}`,  `Ψ_s = sin δ`,  `Ψ = Θ − δ`,

so `R` is a closed curve of speed at least `√(1−κ̂²) > 0` whose tangent turns at
the rate `sin δ ∈ [kmin, κ̂]` and by `2π` over one period.  The variable-speed
chord-arc bound of `ConvexChordArcSpeed.lean` then makes it embedded.

The lower bound `sin δ ≥ kmin` is `sin_steering_ge`: at a parameter where the
periodic `δ` is smallest one has `δ_s = 0`, hence `sin δ = κ ≥ kmin` there, and
`δ` stays in `[0, π/2]` where `sin` is nondecreasing.

* `sin_steering_ge` — the turning rate of the rear is at least `kmin`;
* `injOn_rearTrack_of_pinched` — the rear track is embedded;
* `injOn_rearTrack_front` — the same for the two-cap front;
* `TwoCapMarked.exists_marked_two_cap_pair_pinched` — the two-cap pair is a
  pair of marked curves, with the rear embeddedness hypothesis removed.
-/

noncomputable section

open Real Set Function RearTrack

namespace SelectedInverseEmbedded

/-- **The rear turning rate is bounded below by the front curvature bound.**
A periodic steering angle attains a minimum, where `δ_s = 0` forces
`sin δ = K ≥ kmin`; on the selected strip `sin` is nondecreasing, so the bound
propagates to every parameter. -/
theorem sin_steering_ge {dl K : ℝ → ℝ} {L kmin kap : ℝ} (hL : 0 < L)
    (hdper : Periodic dl L)
    (hode : ∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s)
    (hkmin : ∀ s, kmin ≤ K s)
    (hdmem : ∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) (s : ℝ) :
    kmin ≤ Real.sin (dl s) := by
  have hcont : Continuous dl := by
    have hdiff : Differentiable ℝ dl := fun u => (hode u).differentiableAt
    exact hdiff.continuous
  obtain ⟨s0, hs0mem, hs0⟩ := (isCompact_Icc (a := (0:ℝ)) (b := L)).exists_isMinOn
    (Set.nonempty_Icc.2 hL.le) hcont.continuousOn
  have hglobal : ∀ t, dl s0 ≤ dl t := by
    intro t
    obtain ⟨y, hy, hyeq⟩ := hdper.exists_mem_Ico₀ hL t
    rw [hyeq]
    exact isMinOn_iff.1 hs0 y ⟨hy.1, hy.2.le⟩
  have hloc : IsLocalMin dl s0 := Filter.Eventually.of_forall hglobal
  have hzero : K s0 - Real.sin (dl s0) = 0 := hloc.hasDerivAt_eq_zero (hode s0)
  have hs0sin : kmin ≤ Real.sin (dl s0) := by linarith [hkmin s0]
  have harc : Real.arcsin kap ≤ π / 2 := Real.arcsin_le_pi_div_two kap
  have h1 : Real.sin (dl s0) ≤ Real.sin (dl s) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [(hdmem s0).1, pi_pos])
      (le_trans (hdmem s).2 harc) (hglobal s)
  linarith

/-- The turning rate of the rear is at most `κ̂` on the selected strip. -/
theorem sin_steering_le {dl : ℝ → ℝ} {kap : ℝ} (hkap0 : 0 ≤ kap) (hkap1 : kap ≤ 1)
    (hdmem : ∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) (s : ℝ) :
    Real.sin (dl s) ≤ kap := by
  have harc : Real.arcsin kap ≤ π / 2 := Real.arcsin_le_pi_div_two kap
  have h := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [(hdmem s).1, pi_pos]) harc (hdmem s).2
  rwa [Real.sin_arcsin (by linarith) hkap1] at h

/-- **Every rear track of a pinched closed front is embedded.**  The front `F`
of period `L` has unit tangent `e^{iΘ}`, curvature `κ ≥ kmin > 0` and total
turning `2π`; the steering angle `δ` is `L`-periodic and lies in the selected
strip `0 ≤ δ ≤ arcsin κ̂` with `κ̂ < 1`.  Then `R = F − e^{i(Θ−δ)}` is injective
on one period. -/
theorem injOn_rearTrack_of_pinched {F : ℝ → ℂ} {thF kappa Θ K dl : ℝ → ℝ} {L kmin kap : ℝ}
    (hL : 0 < L) (hkminpos : 0 < kmin) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hFder : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (thF s : ℂ))) s)
    (hthF : ∀ s, HasDerivAt thF (kappa s) s)
    (hkmin : ∀ s, kmin ≤ kappa s)
    (hFper : Periodic F L)
    (hturn : ∀ s, thF (s + L) = thF s + 2 * π)
    (hX : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hdper : Periodic dl L)
    (hdmem : ∀ s, dl s ∈ Icc 0 (Real.arcsin kap))
    (hode : ∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) :
    InjOn (rearTrack F Θ dl) (Ico 0 L) := by
  -- the two tangent angles of `F` have the same derivative
  have hKeq : ∀ s, K s = kappa s := fun s =>
    SelectedInverseTube.curvature_unique hX hFder hΘ hthF s
  have hkminK : ∀ s, kmin ≤ K s := fun s => by rw [hKeq s]; exact hkmin s
  -- hence they differ by a constant, and `Θ` turns by `2π` as well
  have hgd : ∀ s, HasDerivAt (fun t => Θ t - thF t) 0 s := by
    intro s
    have h := (hΘ s).sub (hthF s)
    rw [hKeq s, sub_self] at h
    exact h
  have hgconst : ∀ a b : ℝ, Θ a - thF a = Θ b - thF b := by
    have hdiff : Differentiable ℝ (fun t => Θ t - thF t) := fun u => (hgd u).differentiableAt
    exact fun a b => is_const_of_deriv_eq_zero hdiff (fun x => (hgd x).deriv) a b
  have hturnΘ : ∀ s, Θ (s + L) = Θ s + 2 * π := by
    intro s
    have h := hgconst (s + L) s
    rw [hturn s] at h
    linarith
  -- the rear data
  set Psi : ℝ → ℝ := rearAngle Θ dl with hPsi
  have hRder : ∀ s, HasDerivAt (rearTrack F Θ dl)
      (((Real.cos (dl s) : ℝ) : ℂ) * Complex.exp ((Psi s : ℂ) * Complex.I)) s := by
    intro s
    have h := hasDerivAt_rearTrack (hX s) (hΘ s) (hode s)
    rwa [mul_comm Complex.I ((rearAngle Θ dl s : ℂ))] at h
  have hPsider : ∀ s, HasDerivAt Psi (Real.sin (dl s)) s := fun s =>
    hasDerivAt_rearAngle (hΘ s) (hode s)
  have hwmin : ∀ s, kmin ≤ Real.sin (dl s) := fun s =>
    sin_steering_ge hL hdper hode hkminK hdmem s
  have hwmax : ∀ s, Real.sin (dl s) ≤ kap := fun s =>
    sin_steering_le hkap0 hkap1.le hdmem s
  have hv : ∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (dl s) := fun s =>
    Shadowing.cos_ge_of_mem_strip (hdmem s).1 (hdmem s).2
  have hvpos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hturnPsi : ∀ s, Psi (s + L) = Psi s + 2 * π := by
    intro s
    simp only [hPsi, rearAngle, hturnΘ s, hdper s]
    ring
  have hRper : Periodic (rearTrack F Θ dl) L := by
    intro s
    simp only [rearTrack]
    rw [hFper s, rearTangent_periodic hdper hturnΘ s]
  exact ConvexChordArcSpeed.injOn_of_convex_speed (w := fun s => Real.sin (dl s))
    (v := fun s => Real.cos (dl s)) hL hRder hPsider hwmin hwmax hkminpos hv hvpos
    hRper hturnPsi

open CurvatureInterpolation TwoCapPairsAssembly in
/-- **Every rear track of the two-cap front is embedded**, as soon as the front
curvature is bounded below by `kmin > 0` and the steering strip has
`κ̂ < 1`. -/
theorem injOn_rearTrack_front {kappa : ℝ → ℝ} {H kmin kap theta0 : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (hkminpos : 0 < kmin) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hkmin : ∀ s, kmin ≤ kappa s)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = π)
    (Θ K dl : ℝ → ℝ)
    (hX : ∀ s, HasDerivAt (front kappa theta0 H) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hdper : Periodic dl (2 * H))
    (hdmem : ∀ s, dl s ∈ Icc 0 (Real.arcsin kap))
    (hode : ∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) :
    InjOn (rearTrack (front kappa theta0 H) Θ dl) (Ico 0 (2 * H)) := by
  have hturn : ∀ s, frontAngle kappa theta0 (s + 2 * H) = frontAngle kappa theta0 s + 2 * π := by
    intro s
    have h1 := frontAngle_add_halfPeriod (theta0 := theta0) hk hper htotal s
    have h2 := frontAngle_add_halfPeriod (theta0 := theta0) hk hper htotal (s + H)
    have hs : s + H + H = s + 2 * H := by ring
    rw [hs] at h2
    rw [h2, h1]
    ring
  exact injOn_rearTrack_of_pinched (thF := frontAngle kappa theta0) (kappa := kappa)
    (by linarith) hkminpos hkap0 hkap1 (fun s => front_hasDerivAt hk s)
    (fun s => hasDerivAt_tangentAngle hk s) hkmin (front_periodic hk hper htotal) hturn
    hX hΘ hdper hdmem hode

open MarkedSpace CurvatureInterpolation TwoCapPairsAssembly in
/-- **The exact two-cap pair is a pair of marked curves**, with the rear
embeddedness hypothesis of `TwoCapMarked.exists_marked_two_cap_pair` discharged:
only embeddedness of the *front* is still assumed. -/
theorem exists_marked_two_cap_pair_pinched {kappa : ℝ → ℝ} {H kmin kap theta0 : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (hkminpos : 0 < kmin) (hkap1 : kap < 1)
    (hkmin : ∀ s, kmin ≤ kappa s) (hkap : ∀ s, kappa s ≤ kap)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = π)
    (hinj : InjOn (front kappa theta0 H) (Ico 0 (2 * H))) :
    ∃ (qF qR : Data) (dF dR LR : ℝ),
      0 < dF ∧ IsTubeMember (2 * H) kmin dF qF ∧ perim qF = 2 * H ∧
        ev qF = front kappa theta0 H ∧
      0 < LR ∧ 0 < dR ∧ IsTubeMember LR (kmin / Real.sqrt (1 - kmin ^ 2)) dR qR ∧
        perim qR = LR ∧ LR ≤ 2 * H ∧
        MainTheoremConditional.IsOval (ev qR) ∧
        range (UnitTangent.unitTangentMap (ev qR)) = range (front kappa theta0 H) := by
  have hkap0 : 0 ≤ kap := le_trans hkminpos.le (le_trans (hkmin 0) (hkap 0))
  exact TwoCapMarked.exists_marked_two_cap_pair hH hk hper hkminpos hkap1 hkmin hkap htotal hinj
    (fun Θ K dl h1 h2 h3 h4 h5 =>
      injOn_rearTrack_front hH hk hper hkminpos hkap0 hkap1 hkmin htotal Θ K dl h1 h2 h3 h4 h5)

open MarkedSpace CurvatureInterpolation TwoCapPairsAssembly in
/-- **The exact two-cap pair of a pinched curvature is a pair of marked
curves**, with *both* embeddedness hypotheses of
`TwoCapMarked.exists_marked_two_cap_pair` discharged.  Nothing is assumed of
the curvature beyond continuity, `H`-periodicity, the pinching
`0 < kmin ≤ κ ≤ κ̂ < 1` and the total turning `π` over one period: the front is
embedded by `ModelChordArc.injOn_front`, and every rear track of it by
`injOn_rearTrack_front`. -/
theorem exists_marked_two_cap_pair_of_pinching {kappa : ℝ → ℝ} {H kmin kap theta0 : ℝ}
    (hH : 0 < H) (hk : Continuous kappa) (hper : Periodic kappa H)
    (hkminpos : 0 < kmin) (hkap1 : kap < 1)
    (hkmin : ∀ s, kmin ≤ kappa s) (hkap : ∀ s, kappa s ≤ kap)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = π) :
    ∃ (qF qR : Data) (dF dR LR : ℝ),
      0 < dF ∧ IsTubeMember (2 * H) kmin dF qF ∧ perim qF = 2 * H ∧
        ev qF = front kappa theta0 H ∧
      0 < LR ∧ 0 < dR ∧ IsTubeMember LR (kmin / Real.sqrt (1 - kmin ^ 2)) dR qR ∧
        perim qR = LR ∧ LR ≤ 2 * H ∧
        MainTheoremConditional.IsOval (ev qR) ∧
        range (UnitTangent.unitTangentMap (ev qR)) = range (front kappa theta0 H) :=
  exists_marked_two_cap_pair_pinched hH hk hper hkminpos hkap1 hkmin hkap htotal
    (ModelChordArc.injOn_front hH hk hper hkminpos hkmin hkap htotal)

open MarkedSpace in
/-- **The rear embeddedness hypothesis of a member of the tube, from the
turning number of its front.**  For a member `p` of the tube whose curvature is
pinched by `0 < kmin ≤ K ≤ κ̂ < 1`, embeddedness of *every* rear track built
from an admissible steering angle — the hypothesis `hinjR` carried by the
selected-inverse files — follows from the single topological normalization that
the tangent angle of `ev p` increases by `2π` over one period. -/
theorem injOn_rearTrack_of_tubeMember {c kmin dlt kap : ℝ} {p : Data}
    (hc : 0 < c) (hkminpos : 0 < kmin) (hkap1 : kap < 1)
    (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hturn : ∀ Θ K : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      ∀ s, Θ (s + perim p) = Θ s + 2 * π) :
    ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Θ dl) (Ico 0 (perim p)) := by
  intro Θ K dl hX hΘ hdper hdmem hode
  obtain ⟨Θ0, K0, -, -, hX0, hΘ0, hKlow, hKhigh⟩ :=
    SelectedInverseTube.exists_front_data hc hp hub
  have hKeq : ∀ s, K s = K0 s := fun s =>
    SelectedInverseTube.curvature_unique hX hX0 hΘ hΘ0 s
  have hkap0 : 0 ≤ kap := le_trans hkminpos.le (le_trans (hKlow 0) (hKhigh 0))
  exact injOn_rearTrack_of_pinched (thF := Θ) (kappa := K) (perim_pos hc hp) hkminpos hkap0
    hkap1 hX hΘ (fun s => by rw [hKeq s]; exact hKlow s) (periodic_ev hc hp)
    (hturn Θ K hX hΘ) hX hΘ hdper hdmem hode

open MarkedSpace SelectedInverseMap in
/-- **The geometry of the selected inverse, from the turning number of the
front.**  `SelectedInverseMap.selInv_spec` with its rear embeddedness
hypothesis discharged by `injOn_rearTrack_of_tubeMember`. -/
theorem selInv_spec_of_turning {c kmin dlt kap : ℝ} {p : Data}
    (hc : 0 < c) (hkminpos : 0 < kmin) (hkap1 : kap < 1)
    (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hturn : ∀ Θ K : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      ∀ s, Θ (s + perim p) = Θ s + 2 * π) :
    ∃ dR : ℝ, 0 < dR ∧
      IsTubeMember (perim (selInv kap p)) (kmin / Real.sqrt (1 - kmin ^ 2)) dR
        (selInv kap p) ∧
      MainTheoremConditional.IsOval (ev (selInv kap p)) ∧
      (∀ u, ((starRingEnd ℂ) ((selInv kap p).2.1 u) * (selInv kap p).2.2 u).im
        ≤ kap / Real.sqrt (1 - kap ^ 2) * ‖(selInv kap p).2.1 u‖ ^ 3) ∧
      range (UnitTangent.unitTangentMap (ev (selInv kap p))) = range (ev p) :=
  selInv_spec hc hkminpos hkap1 hp hub
    (injOn_rearTrack_of_tubeMember hc hkminpos hkap1 hp hub hturn)

/-- **The hypotheses of `exists_marked_two_cap_pair_of_pinching` are
satisfiable**: the constant curvature `1/2` with half-period `2π`, whose front
is the circle of radius `2`, meets all of them. -/
theorem pinching_hypotheses_nonvacuous :
    ∃ (kappa : ℝ → ℝ) (H kmin kap : ℝ), 0 < H ∧ Continuous kappa ∧ Periodic kappa H ∧
      0 < kmin ∧ kap < 1 ∧ (∀ s, kmin ≤ kappa s) ∧ (∀ s, kappa s ≤ kap) ∧
      (∫ r in (0:ℝ)..H, kappa r) = π :=
  ⟨TwoCapMarked.kcirc, 2 * π, 1 / 2, 1 / 2, by positivity, TwoCapMarked.continuous_kcirc,
    TwoCapMarked.kcirc_periodic, by norm_num, by norm_num, fun _ => le_rfl, fun _ => le_rfl,
    TwoCapMarked.kcirc_total⟩

end SelectedInverseEmbedded
