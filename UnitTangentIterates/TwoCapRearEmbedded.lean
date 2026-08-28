import Mathlib
import UnitTangentIterates.RearTrackEmbedded
import UnitTangentIterates.TwoCapPairsAssembly
import UnitTangentIterates.SelectedInverseModelCoupling
import UnitTangentIterates.SelectedInverseMap
import UnitTangentIterates.TwoCapMarked
import UnitTangentIterates.SelectedInverseStrip

/-!
# The rear track of a two-cap model front is embedded

`RearTrackEmbedded.injOn_rearTrack_of_tube` discharges the standing hypothesis
`hinjR` — *every steering solution on the selected strip reconstructs an
embedded rear* — from strict convexity of the front, **provided** the front's
tangent angle turns by exactly `2π` over one period.  That turning number is a
global topological fact (the Umlaufsatz), and it is carried as an explicit
hypothesis there.

For the curves the paper actually runs the shadowing scheme on it is not a
hypothesis at all.  The two-cap fronts of Section 4 are *built* from a
prescribed curvature `κ` of half-period `H` with

  `∫₀^H κ = π`,

so the tangent angle `Θ = θ₀ + ∫₀^· κ` advances by `π` over a half period, hence
by `2π` over the full period `2H`.  This file records that observation and uses
it to remove `hinjR` from the model-orbit selected-inverse constructor.

Note that the general pinching criterion `TurningNumberDischarge.turning_two_pi_of_tube`
does *not* apply here: it needs `κ_max · L < 4π`, while the two-cap fronts have
perimeter `L = 2H → ∞` with curvature of fixed size concentrated on the caps.
The exact turning identity is what makes the model case unconditional.

Main results:

* `injOn_rearTrack_of_two_cap_front` : the hypothesis `hinjR`, discharged for a
  tube member whose arclength parametrization is a two-cap front;
* `exists_marked_two_cap_selected_inverse` : the marked selected inverse of a
  two-cap model front, with no embeddedness hypothesis.
-/

noncomputable section

open Set Function MarkedSpace RearTrack

namespace TwoCapRearEmbedded

variable {kappa : ℝ → ℝ} {theta0 H : ℝ}

/-- The turning identity for the two-cap front, from `TwoCapMarked`. -/
theorem frontAngle_add_period (hk : Continuous kappa)
    (hper : Periodic kappa H) (htotal : (∫ r in (0:ℝ)..H, kappa r) = Real.pi)
    (s : ℝ) :
    TwoCapPairsAssembly.frontAngle kappa theta0 (s + 2 * H)
      = TwoCapPairsAssembly.frontAngle kappa theta0 s + 2 * Real.pi :=
  TwoCapMarked.frontAngle_add_period hk hper htotal s

/-- **The rear track of a two-cap model front is embedded.**  This is exactly
the hypothesis `hinjR` carried by the selected-inverse API, discharged for the
curves of the paper's model orbit. -/
theorem injOn_rearTrack_of_two_cap_front {c kmin dlt kap : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    {p : Data} (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = Real.pi)
    (hev : ev p = TwoCapPairsAssembly.front kappa theta0 H)
    (hperim : perim p = 2 * H) :
    ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Θ dl) (Ico 0 (perim p)) := by
  refine RearTrackEmbedded.injOn_rearTrack_of_tube hc hkmin hkap0 hkap1 hp hub
    ⟨TwoCapPairsAssembly.frontAngle kappa theta0, kappa, ?_, ?_, ?_⟩
  · intro s
    rw [hev]
    exact TwoCapPairsAssembly.front_hasDerivAt (theta0 := theta0) (H := H) hk s
  · intro s
    exact CurvatureInterpolation.hasDerivAt_tangentAngle (θ₀ := theta0) hk s
  · intro s
    rw [hperim]
    exact frontAngle_add_period (theta0 := theta0) hk hper htotal s

/-- **The marked selected inverse of a two-cap model front**, with the
embeddedness of the rear no longer assumed.  Compare
`SelectedInverseModelCoupling.exists_marked_model_selected_inverse`, which
carries `hinjR` as a hypothesis. -/
theorem exists_marked_two_cap_selected_inverse {c dlt kmin kap : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    {p : Data} (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = Real.pi)
    (hev : ev p = TwoCapPairsAssembly.front kappa theta0 H)
    (hperim : perim p = 2 * H) :
    ∃ q : Data,
      (∃ dR > 0, IsTubeMember (perim q) (kmin / Real.sqrt (1 - kmin ^ 2)) dR q) ∧
      MainTheoremConditional.IsOval (ev q) ∧
      range (UnitTangent.unitTangentMap (ev q)) = range (ev p) :=
  SelectedInverseModelCoupling.exists_marked_model_selected_inverse hc hkmin hkap1
    hp hub (injOn_rearTrack_of_two_cap_front (theta0 := theta0) hc hkmin hkap0
      hkap1 hp hub hk hper htotal hev hperim)

/-- **The selected inverse map is realized on a two-cap model front.**  The
canonical single-valued `SelectedInverseMap.selInv` takes the value predicted by
the marked selected-inverse relation, with no embeddedness hypothesis. -/
theorem isMarkedSelectedInverse_selInv_two_cap {c dlt kmin kap : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    {p : Data} (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = Real.pi)
    (hev : ev p = TwoCapPairsAssembly.front kappa theta0 H)
    (hperim : perim p = 2 * H) :
    SelectedInverseMap.IsMarkedSelectedInverse kap p (SelectedInverseMap.selInv kap p) :=
  SelectedInverseMap.isMarkedSelectedInverse_selInv hc hkmin hkap1 hp hub
    (injOn_rearTrack_of_two_cap_front (theta0 := theta0) hc hkmin hkap0 hkap1 hp
      hub hk hper htotal hev hperim)

/-- **The geometry of the selected inverse of a two-cap model front.**  This is
`SelectedInverseMap.selInv_spec` with its embeddedness hypothesis discharged:
for the curves of the paper's model orbit, the image of the selected inverse is
unconditionally a tube member, an oval, of curvature at most
`κ̂/√(1-κ̂²)`, and its unit-tangent transform retraces the front. -/
theorem selInv_spec_two_cap {c dlt kmin kap : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    {p : Data} (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kap * ‖p.2.1 u‖ ^ 3)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = Real.pi)
    (hev : ev p = TwoCapPairsAssembly.front kappa theta0 H)
    (hperim : perim p = 2 * H) :
    ∃ dR : ℝ, 0 < dR ∧
      IsTubeMember (perim (SelectedInverseMap.selInv kap p))
        (kmin / Real.sqrt (1 - kmin ^ 2)) dR (SelectedInverseMap.selInv kap p) ∧
      MainTheoremConditional.IsOval (ev (SelectedInverseMap.selInv kap p)) ∧
      (∀ u, ((starRingEnd ℂ) ((SelectedInverseMap.selInv kap p).2.1 u) *
          (SelectedInverseMap.selInv kap p).2.2 u).im
        ≤ kap / Real.sqrt (1 - kap ^ 2) *
            ‖(SelectedInverseMap.selInv kap p).2.1 u‖ ^ 3) ∧
      range (UnitTangent.unitTangentMap (ev (SelectedInverseMap.selInv kap p)))
        = range (ev p) :=
  SelectedInverseMap.selInv_spec hc hkmin hkap1 hp hub
    (injOn_rearTrack_of_two_cap_front (theta0 := theta0) hc hkmin hkap0 hkap1 hp
      hub hk hper htotal hev hperim)

/-- **The exact two-cap pair is a pair of marked curves — unconditionally.**
This is `TwoCapMarked.exists_marked_two_cap_pair` with *both* of its
embeddedness hypotheses discharged.  The only inputs left are the prescribed
curvature data of Section 4 of the paper: `κ` continuous, `H`-periodic, pinched
by `0 < kmin ≤ κ ≤ κ̂ < 1`, of total turning `π` over one period. -/
theorem exists_marked_two_cap_pair_of_prescribed_curvature
    {kmin kap : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (hkminpos : 0 < kmin) (hkap1 : kap < 1)
    (hkmin : ∀ s, kmin ≤ kappa s) (hkap : ∀ s, kappa s ≤ kap)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = Real.pi) :
    ∃ (qF qR : Data) (dF dR LR : ℝ),
      0 < dF ∧ IsTubeMember (2 * H) kmin dF qF ∧ perim qF = 2 * H ∧
        ev qF = TwoCapPairsAssembly.front kappa theta0 H ∧
      0 < LR ∧ 0 < dR ∧
        IsTubeMember LR (kmin / Real.sqrt (1 - kmin ^ 2)) dR qR ∧
        perim qR = LR ∧ LR ≤ 2 * H ∧
        MainTheoremConditional.IsOval (ev qR) ∧
        range (UnitTangent.unitTangentMap (ev qR))
          = range (TwoCapPairsAssembly.front kappa theta0 H) := by
  have hinj : InjOn (TwoCapPairsAssembly.front kappa theta0 H) (Ico 0 (2 * H)) :=
    TwoCapMarked.injOn_front hk hper hkminpos hkmin htotal
  obtain ⟨qF, dF, hdF, hmemF, hperimF, hevF, hubF⟩ :=
    TwoCapMarked.exists_marked_front (theta0 := theta0) hH hk hper hkmin hkap
      htotal hinj
  have hkap0 : (0 : ℝ) ≤ kap :=
    le_trans (le_trans hkminpos.le (hkmin 0)) (hkap 0)
  have hcF : (0 : ℝ) < 2 * H := by linarith
  have hinjR' := injOn_rearTrack_of_two_cap_front (theta0 := theta0) hcF hkminpos
    hkap0 hkap1 hmemF hubF hk hper htotal hevF hperimF
  have hinjR : ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (TwoCapPairsAssembly.front kappa theta0 H)
        (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Periodic dl (2 * H) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (rearTrack (TwoCapPairsAssembly.front kappa theta0 H) Θ dl)
        (Ico 0 (2 * H)) := by
    intro Θ K dl h1 h2 h3 h4 h5
    have := hinjR' Θ K dl (by rw [hevF]; exact h1) h2
      (by rw [hperimF]; exact h3) h4 h5
    rw [hevF, hperimF] at this
    exact this
  exact TwoCapMarked.exists_marked_two_cap_pair (theta0 := theta0) hH hk hper
    hkminpos hkap1 hkmin hkap htotal hinj hinjR

/-- **The unconditional pair theorem is not vacuous.**  Constant curvature
`1/2` with half-period `2π` — whose front is the circle of radius `2` — is
admissible, so both members of its two-cap pair are marked curves of the tube.
Front embeddedness is derived, not assumed. -/
theorem marked_two_cap_pair_circle :
    ∃ (qF qR : Data) (dF dR LR : ℝ),
      0 < dF ∧ IsTubeMember (2 * (2 * Real.pi)) (1 / 2) dF qF ∧
        perim qF = 2 * (2 * Real.pi) ∧
        ev qF = TwoCapPairsAssembly.front TwoCapMarked.kcirc 0 (2 * Real.pi) ∧
      0 < LR ∧ 0 < dR ∧
        IsTubeMember LR ((1 / 2) / Real.sqrt (1 - (1 / 2) ^ 2)) dR qR ∧
        perim qR = LR ∧ LR ≤ 2 * (2 * Real.pi) ∧
        MainTheoremConditional.IsOval (ev qR) ∧
        range (UnitTangent.unitTangentMap (ev qR))
          = range (TwoCapPairsAssembly.front TwoCapMarked.kcirc 0 (2 * Real.pi)) :=
  exists_marked_two_cap_pair_of_prescribed_curvature (theta0 := 0)
    (kmin := 1 / 2) (kap := 1 / 2) (by positivity)
    TwoCapMarked.continuous_kcirc TwoCapMarked.kcirc_periodic (by norm_num)
    (by norm_num) (fun _ => le_rfl) (fun _ => le_rfl) TwoCapMarked.kcirc_total

/-- **The selected-rear side of the paper's pseudo-orbit, unconditionally.**
Section 7 of the paper builds the pseudo-orbit from `Qₙ = F_{Hₙ}` together with
`Aₙ = 𝔅 Q_{n+1} = R_{H_{n+1}}`.  `TwoCapModelOrbit.exists_model_orbit_tube`
supplies the `Qₙ`; this supplies the `Aₙ`, as marked curves of the tube whose
unit-tangent transform retraces the corresponding front, with no embeddedness
hypothesis anywhere. -/
theorem exists_model_selected_rear_sequence
    {kappas : ℕ → ℝ → ℝ} {Hs theta0s : ℕ → ℝ} {kmin kap : ℝ}
    (hH : ∀ n, 0 < Hs n)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (hkminpos : 0 < kmin) (hkap1 : kap < 1)
    (hkmin : ∀ n s, kmin ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi) :
    ∃ A : ℕ → Data, ∀ n,
      (∃ dR > 0, ∃ LR > 0, LR ≤ 2 * Hs n ∧ perim (A n) = LR ∧
        IsTubeMember LR (kmin / Real.sqrt (1 - kmin ^ 2)) dR (A n)) ∧
      MainTheoremConditional.IsOval (ev (A n)) ∧
      range (UnitTangent.unitTangentMap (ev (A n)))
        = range (TwoCapPairsAssembly.front (kappas n) (theta0s n) (Hs n)) := by
  have hex : ∀ n, ∃ q : Data,
      (∃ dR > 0, ∃ LR > 0, LR ≤ 2 * Hs n ∧ perim q = LR ∧
        IsTubeMember LR (kmin / Real.sqrt (1 - kmin ^ 2)) dR q) ∧
      MainTheoremConditional.IsOval (ev q) ∧
      range (UnitTangent.unitTangentMap (ev q))
        = range (TwoCapPairsAssembly.front (kappas n) (theta0s n) (Hs n)) := by
    intro n
    obtain ⟨qF, qR, dF, dR, LR, -, -, -, -, hLR, hdR, hmemR, hperimR, hle,
      hovalR, hrangeR⟩ :=
      exists_marked_two_cap_pair_of_prescribed_curvature (theta0 := theta0s n)
        (kmin := kmin) (kap := kap) (hH n) (hk n) (hper n) hkminpos hkap1
        (hkmin n) (hkap n) (htotal n)
    exact ⟨qR, ⟨dR, hdR, LR, hLR, hle, hperimR, hmemR⟩, hovalR, hrangeR⟩
  choose A hA using hex
  exact ⟨A, hA⟩

/-- **`lem:closed-strip-inverse` for the paper's model fronts, unconditionally.**
`SelectedInverseStrip.selected_inverse_on_closed_strip` needs the turning
identity `Θ(s + S) = Θ(s) + 2π` as an input.  For a two-cap front that identity
is `TwoCapMarked.frontAngle_add_period`, so the whole conclusion — existence and
uniqueness of the periodic steering solution on `[0, arcsin κ̂]`, the rear track
it defines, its regularity and convexity, and its closing up — holds with no
topological hypothesis. -/
theorem selected_inverse_on_closed_strip_two_cap {kap : ℝ}
    (hH : 0 < H) (hk : Continuous kappa) (hper : Periodic kappa H)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hK0 : ∀ s, 0 ≤ kappa s) (hKk : ∀ s, kappa s ≤ kap)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = Real.pi) :
    ∃ delta : ℝ → ℝ,
      Periodic delta (2 * H) ∧
      (∀ s, delta s ∈ Icc 0 (Real.arcsin kap)) ∧
      (∀ s, HasDerivAt delta (kappa s - Real.sin (delta s)) s) ∧
      (∀ e : ℝ → ℝ, Periodic e (2 * H) →
        (∀ s, e s ∈ Icc 0 (Real.arcsin kap)) →
        (∀ s, HasDerivAt e (kappa s - Real.sin (e s)) s) → e = delta) ∧
      (∀ s, rearTrack (TwoCapPairsAssembly.front kappa theta0 H)
            (TwoCapPairsAssembly.frontAngle kappa theta0) delta s
          + Complex.exp (Complex.I *
              (rearAngle (TwoCapPairsAssembly.frontAngle kappa theta0) delta s : ℂ))
          = TwoCapPairsAssembly.front kappa theta0 H s) ∧
      (∀ s, HasDerivAt (rearTrack (TwoCapPairsAssembly.front kappa theta0 H)
            (TwoCapPairsAssembly.frontAngle kappa theta0) delta)
          ((Real.cos (delta s) : ℂ) *
            Complex.exp (Complex.I *
              (rearAngle (TwoCapPairsAssembly.frontAngle kappa theta0) delta s : ℂ))) s) ∧
      (∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (delta s)) ∧
      StrictMono (rearArclength delta) ∧
      (∀ s, HasDerivAt (rearAngle (TwoCapPairsAssembly.frontAngle kappa theta0) delta)
          (Real.tan (delta s) * Real.cos (delta s)) s) ∧
      (∀ s, 0 ≤ Real.tan (delta s)) ∧
      (∀ s, Complex.exp (Complex.I *
            (rearAngle (TwoCapPairsAssembly.frontAngle kappa theta0) delta (s + 2 * H) : ℂ))
          = Complex.exp (Complex.I *
            (rearAngle (TwoCapPairsAssembly.frontAngle kappa theta0) delta s : ℂ))) := by
  have hper2 : Periodic kappa (2 * H) := by simpa using hper.nat_mul 2
  exact SelectedInverseStrip.selected_inverse_on_closed_strip (by linarith) hk
    hper2 hkap0 hkap1 hK0 hKk
    (fun s => TwoCapPairsAssembly.front_hasDerivAt (theta0 := theta0) (H := H) hk s)
    (fun s => CurvatureInterpolation.hasDerivAt_tangentAngle (θ₀ := theta0) hk s)
    (fun s => TwoCapMarked.frontAngle_add_period (theta0 := theta0) hk hper htotal s)

end TwoCapRearEmbedded
