import Mathlib
import UnitTangentIterates.LowCurvatureInverse
import UnitTangentIterates.SelectedInverseStrip
import UnitTangentIterates.Bicycle

/-!
# The lemma *Low-curvature inverse*, assembled

This file assembles the lemma *Low-curvature inverse* of *A Noncircular Oval
with Convex Unit-Tangent Iterates*:

> Let `F` be a smooth strictly convex closed curve with `0 < K ≤ κ < 1`.  There
> is a unique closed rear track on the branch `0 < δ < π/2`.  It is smooth and
> strictly convex, and `k_R ≤ κ/√(1−κ²)`.  If `F` is centrally symmetric, so is
> the selected rear track.

The steering solution and the rear it defines come from
`SelectedInverseStrip.selected_inverse_on_closed_strip`.  What is added here is

* `steering_pos_of_curvature_pos` : with a *strictly* positive front curvature
  the selected steering angle never vanishes — at a zero it would have a
  minimum, forcing `0 = δ_s = K > 0`.  Hence the rear curvature `tan δ` is
  strictly positive: the rear track is **strictly convex**;
* `low_curvature_inverse` : the assembled statement, with the curvature bound
  `k_R = tan δ ≤ κ/√(1−κ²)` of `Bicycle.rear_curvature_le`;
* `low_curvature_inverse_centrally_symmetric` : the half-turn symmetry clause —
  for a centrally symmetric front (curvature of period `L`, perimeter `2L`) the
  selected steering angle, hence the selected rear, is `L`-periodic.
-/

noncomputable section

open Real Set Complex

namespace LowCurvatureAssembly

/-- **The selected steering angle is strictly positive** when the front
curvature is: at a zero of `δ` the nonnegative function `δ` would have a
minimum, so `0 = δ_s = K − sin 0 = K > 0`, a contradiction. -/
theorem steering_pos_of_curvature_pos {delta K : ℝ → ℝ}
    (hode : ∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s)
    (hnonneg : ∀ s, 0 ≤ delta s) (hK : ∀ s, 0 < K s) (s : ℝ) : 0 < delta s := by
  rcases lt_or_eq_of_le (hnonneg s) with h | h
  · exact h
  · exfalso
    have hmin : IsLocalMin delta s := by
      refine Filter.Eventually.of_forall fun t => ?_
      rw [← h]
      exact hnonneg t
    have hzero := hmin.hasDerivAt_eq_zero (hode s)
    rw [← h] at hzero
    simp at hzero
    linarith [hK s]

/-- **Strong positivity of a nontrivial periodic selected steering.**  A
nonnegative periodic solution of `δ' = K - sin δ` with nonnegative, nonzero
forcing cannot touch zero.  This is the form needed when the front curvature
has flat pieces but positive total turning. -/
theorem steering_pos_of_nonnegative_nonzero {delta K : ℝ → ℝ} {P : ℝ}
    (hP : 0 < P) (hper : Function.Periodic delta P)
    (hode : ∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s)
    (hnonneg : ∀ s, 0 ≤ delta s) (hKnonneg : ∀ s, 0 ≤ K s)
    (hKnonzero : ∃ s, K s ≠ 0) (s : ℝ) : 0 < delta s := by
  rcases lt_or_eq_of_le (hnonneg s) with hs | hs
  · exact hs
  exfalso
  let f : ℝ → ℝ := fun x => Real.exp x * delta x
  have hfd : ∀ x, HasDerivAt f
      (Real.exp x * (delta x + (K x - Real.sin (delta x)))) x := by
    intro x
    simpa [f, add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_exp x).mul (hode x)
  have hfmono : Monotone f := by
    apply monotone_of_deriv_nonneg
    · exact fun x => (hfd x).differentiableAt
    · intro x
      rw [(hfd x).deriv]
      have hsin : Real.sin (delta x) ≤ delta x := Real.sin_le (hnonneg x)
      exact mul_nonneg (Real.exp_pos x).le (by linarith [hKnonneg x])
  obtain ⟨r, hr⟩ := hKnonzero
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt ((r - s) / P)
  have hrpast : r - n * P < s := by
    rw [div_lt_iff₀ hP] at hn
    push_cast
    linarith
  have hfzero : f (r - n * P) = 0 := by
    have hle := hfmono hrpast.le
    have hfnonneg : 0 ≤ f (r - n * P) := mul_nonneg (Real.exp_pos _).le (hnonneg _)
    have hfs : f s = 0 := by
      change Real.exp s * delta s = 0
      rw [← hs, mul_zero]
    rw [hfs] at hle
    linarith
  have hdeltaPast : delta (r - n * P) = 0 := by
    change Real.exp (r - n * P) * delta (r - n * P) = 0 at hfzero
    rw [mul_eq_zero] at hfzero
    exact hfzero.resolve_left (Real.exp_ne_zero _)
  have hdeltar : delta r = 0 := by
    have hp := (hper.nat_mul n) (r - n * P)
    have harg : r - n * P + ↑n * P = r := by ring
    rw [harg] at hp
    exact hp.trans hdeltaPast
  have hmin : IsLocalMin delta r := by
    refine Filter.Eventually.of_forall fun t => ?_
    rw [hdeltar]
    exact hnonneg t
  have hzero := hmin.hasDerivAt_eq_zero (hode r)
  rw [hdeltar] at hzero
  simp only [Real.sin_zero, sub_zero] at hzero
  exact hr hzero

/-- **Low-curvature inverse.**  A unit-speed closed front with continuous
periodic curvature `0 < K ≤ κ < 1` has a unique closed rear track on the branch
`0 < δ < π/2`; it is regular, strictly convex, and its curvature is at most
`κ/√(1−κ²)`. -/
theorem low_curvature_inverse {F : ℝ → ℂ} {Θ K : ℝ → ℝ} {S kap : ℝ}
    (hS : 0 < S) (hK : Continuous K) (hKper : Function.Periodic K S)
    (hkap1 : kap < 1) (hK0 : ∀ s, 0 < K s) (hKk : ∀ s, K s ≤ kap)
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hturn : ∀ s, Θ (s + S) = Θ s + 2 * π) :
    ∃ delta : ℝ → ℝ,
      -- the selected steering angle, on the open branch `0 < δ < π/2`
      Function.Periodic delta S ∧
      (∀ s, 0 < delta s ∧ delta s < π / 2) ∧
      (∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s) ∧
      (∀ e : ℝ → ℝ, Function.Periodic e S → (∀ s, e s ∈ Icc 0 (Real.arcsin kap)) →
        (∀ s, HasDerivAt e (K s - Real.sin (e s)) s) → e = delta) ∧
      -- the rear track: it is a rear track of `F`, regular and strictly convex
      (∀ s, RearTrack.rearTrack F Θ delta s
          + Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta s : ℂ)) = F s) ∧
      (∀ s, HasDerivAt (RearTrack.rearTrack F Θ delta)
          ((Real.cos (delta s) : ℂ)
            * Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta s : ℂ))) s) ∧
      StrictMono (RearTrack.rearArclength delta) ∧
      (∀ s, HasDerivAt (RearTrack.rearAngle Θ delta)
          (Real.tan (delta s) * Real.cos (delta s)) s) ∧
      (∀ s, 0 < Real.tan (delta s)) ∧
      -- the rear curvature bound
      (∀ s, Real.tan (delta s) ≤ kap / Real.sqrt (1 - kap ^ 2)) ∧
      -- the rear closes up
      (∀ s, Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta (s + S) : ℂ))
          = Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta s : ℂ))) := by
  have hkap0 : 0 ≤ kap := le_trans (hK0 0).le (hKk 0)
  obtain ⟨delta, hper, hrange, hode, huniq, hrear, hderivR, hcos, hmono, hangle, htan, hclose⟩ :=
    SelectedInverseStrip.selected_inverse_on_closed_strip hS hK hKper hkap0 hkap1
      (fun s => (hK0 s).le) hKk hF hΘ hturn
  have hpos : ∀ s, 0 < delta s :=
    steering_pos_of_curvature_pos hode (fun s => (hrange s).1) hK0
  have hhalf : ∀ s, delta s < π / 2 := by
    intro s
    have h1 : delta s ≤ Real.arcsin kap := (hrange s).2
    have h2 : Real.arcsin kap < π / 2 := by
      rw [show π / 2 = Real.arcsin 1 by simp [Real.arcsin_one]]
      exact Real.arcsin_lt_arcsin (by linarith) hkap1 (le_refl 1)
    linarith
  refine ⟨delta, hper, fun s => ⟨hpos s, hhalf s⟩, hode, huniq, hrear, hderivR, hmono, hangle,
    ?_, ?_, hclose⟩
  · intro s
    have hcospos : 0 < Real.cos (delta s) := by
      have h := hcos s
      have hpos' : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
      linarith
    have hsinpos : 0 < Real.sin (delta s) :=
      Real.sin_pos_of_pos_of_lt_pi (hpos s) (by linarith [hhalf s, Real.pi_pos])
    rw [Real.tan_eq_sin_div_cos]
    positivity
  · intro s
    exact Bicycle.rear_curvature_le hkap1 (hrange s).1 (hrange s).2

/-- **Half-turn symmetry of the selected rear.**  If the front is centrally
symmetric — its curvature has period `L` and its perimeter is `2L` — then the
selected steering angle is `L`-periodic, hence so is the rear it defines. -/
theorem low_curvature_inverse_centrally_symmetric {delta K : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hKper : Function.Periodic K L)
    (hode : ∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s)
    (hper : Function.Periodic delta (2 * L))
    (hrange : ∀ s, delta s ∈ Icc (0:ℝ) (π / 2)) :
    Function.Periodic delta L := by
  refine LowCurvatureInverse.steering_periodic_of_periodic_curvature hL hKper hode hper ?_
  intro s
  exact ⟨by linarith [(hrange s).1, Real.pi_pos], (hrange s).2⟩

/-! ### A lower bound for the rear curvature -/

/-- **At its minimum the steering angle satisfies `sin δ = K`.**  Hence a front
curvature bounded below by `k_min` forces `δ ≥ arcsin k_min` everywhere. -/
theorem steering_ge_arcsin_of_curvature_ge {delta K : ℝ → ℝ} {S kmin : ℝ} (hS : 0 < S)
    (hper : Function.Periodic delta S)
    (hode : ∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s)
    (hrange : ∀ s, delta s ∈ Icc 0 (π / 2))
    (hK : ∀ s, kmin ≤ K s) :
    ∀ s, Real.arcsin kmin ≤ delta s := by
  have hcont : Continuous delta := Differentiable.continuous fun s => (hode s).differentiableAt
  obtain ⟨t0, _, ht0⟩ := isCompact_Icc.exists_isMinOn (s := Icc (0:ℝ) S)
    (Set.nonempty_Icc.mpr hS.le) hcont.continuousOn
  have hglobal : ∀ s, delta t0 ≤ delta s := by
    intro s
    obtain ⟨y, hy, hys⟩ := hper.exists_mem_Ico₀ hS s
    rw [hys]
    exact ht0 ⟨hy.1, hy.2.le⟩
  have hmin : IsLocalMin delta t0 := Filter.Eventually.of_forall hglobal
  have hzero := hmin.hasDerivAt_eq_zero (hode t0)
  have hsin : Real.sin (delta t0) = K t0 := by linarith
  have hle : Real.arcsin kmin ≤ delta t0 := by
    have h1 : Real.arcsin kmin ≤ Real.arcsin (Real.sin (delta t0)) := by
      rw [hsin]; exact Real.arcsin_le_arcsin (hK t0)
    rwa [Real.arcsin_sin (by linarith [(hrange t0).1, Real.pi_pos]) (hrange t0).2] at h1
  exact fun s => le_trans hle (hglobal s)

/-- Monotonicity of `tan` on the branch: `δ ≥ arcsin k_min` gives the rear
curvature bound `tan δ ≥ k_min/√(1 − k_min²)`. -/
theorem tan_ge_of_arcsin_le {delta kmin : ℝ} (hkmin0 : 0 ≤ kmin)
    (hle : Real.arcsin kmin ≤ delta) (hd : delta < π / 2) :
    kmin / Real.sqrt (1 - kmin ^ 2) ≤ Real.tan delta := by
  have harc0 : 0 ≤ Real.arcsin kmin := Real.arcsin_nonneg.mpr hkmin0
  have hmono : Real.tan (Real.arcsin kmin) ≤ Real.tan delta := by
    rcases eq_or_lt_of_le hle with h | h
    · rw [h]
    · exact le_of_lt (Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [Real.pi_pos]) hd h)
  rwa [Real.tan_arcsin] at hmono

/-- **The rear curvature is pinched.**  For a front curvature with
`0 < k_min ≤ K ≤ κ < 1`, the selected rear curvature satisfies
`k_min/√(1 − k_min²) ≤ tan δ ≤ κ/√(1 − κ²)`; in particular it is bounded away
from `0`, as the tube of marked curves requires. -/
theorem selected_rear_curvature_pinched {delta K : ℝ → ℝ} {S kmin kap : ℝ} (hS : 0 < S)
    (hkmin0 : 0 ≤ kmin) (hkap1 : kap < 1)
    (hper : Function.Periodic delta S)
    (hode : ∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s)
    (hrange : ∀ s, delta s ∈ Icc 0 (Real.arcsin kap))
    (hK : ∀ s, kmin ≤ K s) :
    ∀ s, kmin / Real.sqrt (1 - kmin ^ 2) ≤ Real.tan (delta s) ∧
      Real.tan (delta s) ≤ kap / Real.sqrt (1 - kap ^ 2) := by
  have harc : Real.arcsin kap < π / 2 := Real.arcsin_lt_pi_div_two.mpr hkap1
  have hstrip : ∀ s, delta s ∈ Icc (0:ℝ) (π / 2) :=
    fun s => ⟨(hrange s).1, le_trans (hrange s).2 harc.le⟩
  have hge := steering_ge_arcsin_of_curvature_ge hS hper hode hstrip hK
  intro s
  exact ⟨tan_ge_of_arcsin_le hkmin0 (hge s) (lt_of_le_of_lt (hrange s).2 harc),
    Bicycle.rear_curvature_le hkap1 (hrange s).1 (hrange s).2⟩

end LowCurvatureAssembly
