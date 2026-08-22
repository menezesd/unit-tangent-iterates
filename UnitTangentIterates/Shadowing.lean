import Mathlib

/-!
# Cores of the shadowing section

This file formalizes the self-contained computational cores of three lemmas of
the shadowing section of the paper *A Noncircular Oval with Convex Unit-Tangent
Iterates*.

* From the lemma *Inverse Jacobi estimates*: the identity
  `(1 + ∂_x) η_R = sec δ · η_F ∘ s`, obtained by expanding the front normal
  velocity in the rear frame; the tangential terms cancel precisely because
  the rear curvature is `k = tan δ`.
* From the lemma *Selected inverse on the closed strip*: the uniqueness of the
  periodic steering solution of `δ_s = K - sin δ` inside the closed strip
  `|δ| ≤ π/2`, by the maximum principle, and the lower bound
  `x_s = cos δ ≥ √(1 - κ̂²)` on the strip `0 ≤ δ ≤ arcsin κ̂`, which also gives
  the lower bound `κ̂^{-1}√(1-κ̂²)` for the zeroth-order coefficient
  `q cos δ` of the linearized steering equation appearing in the lemma
  *Smooth dependence of the selected rear*.
* From the lemma *Stopped curvature estimate*: the exit-time argument, in the
  form that a continuous curvature bound which can only move by less than
  `κ_e - κ_b` while it stays below `κ_e` never reaches `κ_e`.

Main results:

* `inverse_jacobi_identity`, `rear_normal_deriv` : the Jacobi identity;
* `steering_unique` : uniqueness of the periodic steering solution;
* `cos_ge_of_mem_strip`, `zeroth_order_coeff_ge` : the uniform lower bounds on
  the strip;
* `stopped_curvature` : the exit-time argument.
-/

noncomputable section

open Real Set

namespace Shadowing

/-! ### The inverse Jacobi identity -/

/-- **The inverse Jacobi identity.**  Writing the rear velocity as
`ξ τ + η_R ν`, the front velocity has normal component
`η_F = -ξ sin δ + (η_R + η_{R,x} + k ξ) cos δ`.  When the rear curvature is
`k = tan δ`, the tangential contributions cancel and
`η_R + η_{R,x} = sec δ · η_F`. -/
theorem inverse_jacobi_identity {xi etaR etaRx k delta etaF : ℝ}
    (hk : k = Real.tan delta) (hcos : Real.cos delta ≠ 0)
    (hF : etaF = -xi * Real.sin delta + (etaR + etaRx + k * xi) * Real.cos delta) :
    etaR + etaRx = etaF / Real.cos delta := by
  rw [hF, hk, Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- The differentiated form: `η_{R,x} = sec δ η_F - η_R`. -/
theorem rear_normal_deriv {xi etaR etaRx k delta etaF : ℝ}
    (hk : k = Real.tan delta) (hcos : Real.cos delta ≠ 0)
    (hF : etaF = -xi * Real.sin delta + (etaR + etaRx + k * xi) * Real.cos delta) :
    etaRx = etaF / Real.cos delta - etaR := by
  have h := inverse_jacobi_identity hk hcos hF
  linarith

/-! ### Uniqueness of the periodic steering solution -/

section Uniqueness

variable {d1 d2 K : ℝ → ℝ} {P : ℝ}

/-- One half of the maximum-principle argument: a periodic solution of the
steering equation cannot exceed another one. -/
theorem steering_le_of_periodic (hP : 0 < P)
    (h1 : ∀ s, HasDerivAt d1 (K s - Real.sin (d1 s)) s)
    (h2 : ∀ s, HasDerivAt d2 (K s - Real.sin (d2 s)) s)
    (hp1 : Function.Periodic d1 P) (hp2 : Function.Periodic d2 P)
    (hr1 : ∀ s, d1 s ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hr2 : ∀ s, d2 s ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    ∀ s, d1 s ≤ d2 s := by
  set w : ℝ → ℝ := fun s => d1 s - d2 s with hw
  have hwd : ∀ s, HasDerivAt w (Real.sin (d2 s) - Real.sin (d1 s)) s := by
    intro s
    have := (h1 s).sub (h2 s)
    simpa [hw] using this.congr_deriv (by ring)
  have hwcont : Continuous w := by
    have : Differentiable ℝ w := fun s => (hwd s).differentiableAt
    exact this.continuous
  have hwper : Function.Periodic w P := fun s => by
    simp only [hw, hp1 s, hp2 s]
  -- the maximum over one period is a global maximum
  obtain ⟨t0, ht0mem, ht0⟩ := isCompact_Icc.exists_isMaxOn (s := Icc (0:ℝ) P)
    (Set.nonempty_Icc.mpr hP.le) hwcont.continuousOn
  have hglobal : ∀ s, w s ≤ w t0 := by
    intro s
    obtain ⟨y, hy, hys⟩ := hwper.exists_mem_Ico₀ hP s
    rw [hys]
    exact ht0 ⟨hy.1, hy.2.le⟩
  have hmax : IsLocalMax w t0 := Filter.Eventually.of_forall hglobal
  have hzero : Real.sin (d2 t0) - Real.sin (d1 t0) = 0 := hmax.hasDerivAt_eq_zero (hwd t0)
  have heq : d1 t0 = d2 t0 :=
    Real.injOn_sin (hr1 t0) (hr2 t0) (by linarith)
  have hwt0 : w t0 = 0 := by simp [hw, heq]
  intro s
  have := hglobal s
  rw [hwt0] at this
  simpa [hw, sub_nonpos] using this

/-- **Uniqueness of the periodic steering solution.**  On the closed strip
`|δ| ≤ π/2`, the periodic solution of `δ_s = K - sin δ` is unique. -/
theorem steering_unique (hP : 0 < P)
    (h1 : ∀ s, HasDerivAt d1 (K s - Real.sin (d1 s)) s)
    (h2 : ∀ s, HasDerivAt d2 (K s - Real.sin (d2 s)) s)
    (hp1 : Function.Periodic d1 P) (hp2 : Function.Periodic d2 P)
    (hr1 : ∀ s, d1 s ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hr2 : ∀ s, d2 s ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    d1 = d2 := by
  funext s
  exact le_antisymm (steering_le_of_periodic hP h1 h2 hp1 hp2 hr1 hr2 s)
    (steering_le_of_periodic hP h2 h1 hp2 hp1 hr2 hr1 s)

end Uniqueness

/-! ### Uniform bounds on the selected strip -/

/-- On the selected strip `0 ≤ δ ≤ arcsin κ̂`, the rear speed
`x_s = cos δ` is bounded below by `√(1 - κ̂²)`. -/
theorem cos_ge_of_mem_strip {kap delta : ℝ}
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ Real.arcsin kap) :
    Real.sqrt (1 - kap ^ 2) ≤ Real.cos delta := by
  have harc : Real.arcsin kap ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two kap
  have hmono : Real.cos (Real.arcsin kap) ≤ Real.cos delta := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi hd0 (harc.trans (by linarith [Real.pi_pos])) hd1
  rwa [Real.cos_arcsin] at hmono

/-- The zeroth-order coefficient `q cos δ = cos δ / K` of the linearized
steering equation is bounded below by `κ̂^{-1}√(1-κ̂²)` on the selected
strip. -/
theorem zeroth_order_coeff_ge {kap delta Kv : ℝ}
    (hK0 : 0 < Kv) (hK : Kv ≤ kap)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ Real.arcsin kap) :
    Real.sqrt (1 - kap ^ 2) / kap ≤ Real.cos delta / Kv := by
  have hcos : Real.sqrt (1 - kap ^ 2) ≤ Real.cos delta := cos_ge_of_mem_strip hd0 hd1
  have hs : 0 ≤ Real.sqrt (1 - kap ^ 2) := Real.sqrt_nonneg _
  exact div_le_div₀ (le_trans hs hcos) hcos hK0 hK

/-! ### The stopped curvature estimate -/

/-- **The exit-time argument of the stopped curvature estimate.**  Let `f` be
continuous with `f 0 ≤ κ_b < κ_e`, and suppose that whenever `f` has stayed
below `κ_e` strictly before time `t`, it can have moved by at most
`S < κ_e - κ_b`.  Then `f` stays below `κ_e` for all time. -/
theorem stopped_curvature {f : ℝ → ℝ} {kb ke S : ℝ} (hcont : Continuous f)
    (hf0 : f 0 ≤ kb) (hS : S < ke - kb)
    (hmove : ∀ t, 0 ≤ t → (∀ r ∈ Ico (0:ℝ) t, f r ≤ ke) → |f t - f 0| ≤ S) :
    ∀ t, 0 ≤ t → f t < ke := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨t, ht0, htge⟩ := hcon
  -- the first time at which `f` reaches `ke`
  set A : Set ℝ := {r ∈ Icc (0:ℝ) t | ke ≤ f r} with hA
  have hAne : A.Nonempty := ⟨t, ⟨⟨ht0, le_refl t⟩, htge⟩⟩
  have hAclosed : IsClosed A := by
    have hAeq : A = Icc (0:ℝ) t ∩ f ⁻¹' (Ici ke) := by
      ext r; simp [hA, Set.mem_inter_iff, Set.mem_preimage]
    rw [hAeq]
    exact isClosed_Icc.inter (isClosed_Ici.preimage hcont)
  have hAbdd : BddBelow A := ⟨0, fun r hr => hr.1.1⟩
  set T : ℝ := sInf A with hT
  have hTA : T ∈ A := hAclosed.csInf_mem hAne hAbdd
  have hT0 : 0 ≤ T := hTA.1.1
  have hTt : T ≤ t := hTA.1.2
  have hTge : ke ≤ f T := hTA.2
  have hbefore : ∀ r ∈ Ico (0:ℝ) T, f r ≤ ke := by
    intro r hr
    by_contra hlt
    push_neg at hlt
    have hrA : r ∈ A := ⟨⟨hr.1, le_trans hr.2.le hTt⟩, hlt.le⟩
    have := csInf_le hAbdd hrA
    linarith [hr.2]
  have hmoveT := hmove T hT0 hbefore
  have h1 : f T - f 0 ≤ S := (abs_le.mp hmoveT).2
  linarith

/-! ### Existence of the periodic steering solution -/

/-- **The Poincaré map has a fixed point.**  In the lemmas *Low-curvature
inverse* and *Selected inverse on the closed strip*, the steering vector field
points into the interval `[0, arcsin κ̂]`, so the time-`P` map of the steering
equation sends that interval into itself; being continuous, it then has a fixed
point, which is exactly a periodic steering solution inside the closed
strip. -/
theorem exists_fixed_point_of_mapsTo {P : ℝ → ℝ} {d0 : ℝ} (hd0 : 0 ≤ d0)
    (hcont : ContinuousOn P (Icc 0 d0)) (hmaps : Set.MapsTo P (Icc 0 d0) (Icc 0 d0)) :
    ∃ x ∈ Icc 0 d0, P x = x := by
  set f : ℝ → ℝ := fun x => P x - x with hf
  have hfcont : ContinuousOn f (Icc 0 d0) := hcont.sub continuousOn_id
  have h0 : 0 ≤ f 0 := by
    have := (hmaps ⟨le_rfl, hd0⟩).1
    simp [hf]
    linarith
  have h1 : f d0 ≤ 0 := by
    have := (hmaps ⟨hd0, le_rfl⟩).2
    simp [hf]
    linarith
  have hsub : Icc (f d0) (f 0) ⊆ f '' Icc 0 d0 := intermediate_value_Icc' hd0 hfcont
  obtain ⟨x, hx, hfx⟩ := hsub ⟨h1, h0⟩
  exact ⟨x, hx, by simpa [hf, sub_eq_zero] using hfx⟩

end Shadowing
