module

public import UnitTangentIterates.ShadowMax
public import UnitTangentIterates.Jacobi
public import UnitTangentIterates.JacobiEstimates

/-!
# Paths of curves in intrinsic data form, and their selected rears

A path of closed convex curves is described, in a fixed periodic material parameter `u`
(period `p`), by

* `a t u = ∂ᵤΘ` (the derivative of the tangent angle) and `g t u = |∂ᵤX|` (the speed), so that
  the curvature is `a / g`;
* the tangential and inward normal velocities `ξ, η`, with `∂ₜX = ξ τ + η ν`;
* `ω = ∂ₜΘ` and `gd = ∂ₜ g`.

Equality of mixed partial derivatives of `X` amounts to `g ω = ∂ᵤη + ξ a` and
`gd = ∂ᵤξ - η a`; equality of the mixed partials of `Θ` and `g` is encoded by asking that `a`
and `g` are differentiable in `t`, uniformly in `u`, with derivatives `∂ᵤω` and `gd`.

`PathData.rear` applies the selected inverse at every time: the steering angle `δ(t, ·)` is the
periodic solution of `∂ᵤδ = a - g sin δ`, and the rear path has data
`(g sin δ, g cos δ, ξ cos δ - η sin δ, ξ sin δ + η cos δ - (ω - D), ω - D, …)` where
`D = ∂ₜδ` solves the linearized equation.  `PathData.Valid.rear` shows that the rears of a valid
path form a valid path, provided their curvature `tan δ` is bounded by some `κ' < 1`.
-/

@[expose] public section

namespace Ovals

open Real Filter Topology

/-! ### Selected solutions, chosen once and for all -/

/-- The selected periodic solution of `δ' = a - b sin δ` (with values in `[0, π/2)`). -/
noncomputable def steerAngle (p : ℝ) (a b : ℝ → ℝ) : ℝ → ℝ :=
  open Classical in
  if h : ∃ δ : ℝ → ℝ, Function.Periodic δ p ∧
      (∀ u, HasDerivAt δ (a u - b u * Real.sin (δ u)) u) ∧ ∀ u, δ u ∈ Set.Ico 0 (π / 2)
  then h.choose else 0

/-- A continuous periodic function with values in `[0, π/2)` stays below some `A < π/2`. -/
lemma exists_lt_pi_div_two_of_periodic {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p) (hf : Continuous f)
    (hfp : Function.Periodic f p) (hf2 : ∀ u, f u < π / 2) : ∃ A < π / 2, ∀ u, f u ≤ A := by
  obtain ⟨u₀, hu₀⟩ := exists_max_of_periodic hp hf hfp
  exact ⟨f u₀, hf2 u₀, hu₀⟩

/-- The derivative of a periodic function is periodic. -/
lemma periodic_deriv {f : ℝ → ℝ} {p : ℝ} (h : Function.Periodic f p) :
    Function.Periodic (deriv f) p := fun u => by
  rw [← deriv_comp_add_const]
  congr 1
  funext x
  exact h x

section steer

variable {p κ : ℝ} {a b : ℝ → ℝ}

/-- **Specification of `steerAngle`.** -/
theorem steerAngle_spec (hp : 0 < p) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (ha : Continuous a)
    (hb : Continuous b) (hap : Function.Periodic a p) (hbp : Function.Periodic b p)
    (hb0 : ∀ u, 0 < b u) (ha0 : ∀ u, 0 ≤ a u) (hab : ∀ u, a u ≤ κ * b u) :
    Function.Periodic (steerAngle p a b) p ∧
      (∀ u, HasDerivAt (steerAngle p a b) (a u - b u * Real.sin (steerAngle p a b u)) u) ∧
      ∀ u, steerAngle p a b u ∈ Set.Icc 0 (Real.arcsin κ) := by
  obtain ⟨δ₀, h0p, h0d, h0b⟩ := weightedSteering_exists hp hκ0 hκ1 ha hb hap hbp hb0 ha0 hab
  have hA : Real.arcsin κ < π / 2 := arcsin_lt_pi_div_two hκ1
  have hex : ∃ δ : ℝ → ℝ, Function.Periodic δ p ∧
      (∀ u, HasDerivAt δ (a u - b u * Real.sin (δ u)) u) ∧ ∀ u, δ u ∈ Set.Ico 0 (π / 2) :=
    ⟨δ₀, h0p, h0d, fun u => ⟨(h0b u).1, (h0b u).2.trans_lt hA⟩⟩
  have e : steerAngle p a b = hex.choose := by simp only [steerAngle, dif_pos hex]
  obtain ⟨h1p, h1d, h1b⟩ := hex.choose_spec
  have hc : Continuous hex.choose :=
    continuous_iff_continuousAt.2 fun x => (h1d x).continuousAt
  obtain ⟨A', hA', hA'b⟩ := exists_lt_pi_div_two_of_periodic hp hc h1p fun u => (h1b u).2
  obtain ⟨m, hm, hbm⟩ := exists_pos_lower_bound_of_periodic hp hb hbp hb0
  have heq : hex.choose = δ₀ := weightedSteering_unique hp (A := max A' (Real.arcsin κ))
    (max_lt hA' hA) hm h1d h0d h1p h0p (fun u => ⟨(h1b u).1, (hA'b u).trans (le_max_left _ _)⟩)
    (fun u => ⟨(h0b u).1, (h0b u).2.trans (le_max_right _ _)⟩) hbm
  rw [e, heq]
  exact ⟨h0p, h0d, h0b⟩

/-- **Uniqueness**: any periodic solution with values in `[0, A]`, `A < π/2`, is the selected
one. -/
theorem steerAngle_eq (hp : 0 < p) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (ha : Continuous a)
    (hb : Continuous b) (hap : Function.Periodic a p) (hbp : Function.Periodic b p)
    (hb0 : ∀ u, 0 < b u) (ha0 : ∀ u, 0 ≤ a u) (hab : ∀ u, a u ≤ κ * b u)
    {δ : ℝ → ℝ} {A : ℝ} (hA : A < π / 2) (hδp : Function.Periodic δ p)
    (hδ : ∀ u, HasDerivAt δ (a u - b u * Real.sin (δ u)) u) (hδb : ∀ u, δ u ∈ Set.Icc 0 A) :
    steerAngle p a b = δ := by
  obtain ⟨h1p, h1d, h1b⟩ := steerAngle_spec hp hκ0 hκ1 ha hb hap hbp hb0 ha0 hab
  obtain ⟨m, hm, hbm⟩ := exists_pos_lower_bound_of_periodic hp hb hbp hb0
  exact weightedSteering_unique hp (A := max A (Real.arcsin κ))
    (max_lt hA (arcsin_lt_pi_div_two hκ1)) hm h1d hδ h1p hδp
    (fun u => ⟨(h1b u).1, (h1b u).2.trans (le_max_right _ _)⟩)
    (fun u => ⟨(hδb u).1, (hδb u).2.trans (le_max_left _ _)⟩) hbm

end steer

/-- The periodic solution of the linear equation `D' = f - β D`. -/
noncomputable def linSol (p : ℝ) (f β : ℝ → ℝ) : ℝ → ℝ :=
  open Classical in
  if h : ∃ D : ℝ → ℝ, Function.Periodic D p ∧ ∀ u, HasDerivAt D (f u - β u * D u) u
  then h.choose else 0

theorem linSol_spec {p : ℝ} {f β : ℝ → ℝ} (hp : 0 < p) (hf : Continuous f) (hβ : Continuous β)
    (hfp : Function.Periodic f p) (hβp : Function.Periodic β p) (hβ0 : ∀ u, 0 < β u) :
    Function.Periodic (linSol p f β) p ∧
      ∀ u, HasDerivAt (linSol p f β) (f u - β u * linSol p f β u) u := by
  have hex := linear_periodic_exists hp hf hβ hfp hβp hβ0
  simp only [linSol, dif_pos hex]
  exact hex.choose_spec

/-! ### Paths in data form -/

/-- A path of curves in data form (see the module docstring). -/
structure PathData where
  p : ℝ
  a : ℝ → ℝ → ℝ
  g : ℝ → ℝ → ℝ
  ξ : ℝ → ℝ → ℝ
  η : ℝ → ℝ → ℝ
  ω : ℝ → ℝ → ℝ
  gd : ℝ → ℝ → ℝ

/-- Validity of a path in data form, with curvature `a / g ∈ [0, κ]` and speed `g ≥ m > 0`. -/
structure PathData.Valid (P : PathData) (κ m : ℝ) : Prop where
  p_pos : 0 < P.p
  a_per : ∀ t, Function.Periodic (P.a t) P.p
  g_per : ∀ t, Function.Periodic (P.g t) P.p
  ξ_per : ∀ t, Function.Periodic (P.ξ t) P.p
  η_per : ∀ t, Function.Periodic (P.η t) P.p
  ω_per : ∀ t, Function.Periodic (P.ω t) P.p
  gd_per : ∀ t, Function.Periodic (P.gd t) P.p
  a_cont : ∀ t, Continuous (P.a t)
  g_cont : ∀ t, Continuous (P.g t)
  gd_cont : ∀ t, Continuous (P.gd t)
  ξ_diff : ∀ t, Differentiable ℝ (P.ξ t)
  η_diff : ∀ t, Differentiable ℝ (P.η t)
  η_deriv_cont : ∀ t, Continuous (deriv (P.η t))
  ω_diff : ∀ t, Differentiable ℝ (P.ω t)
  ω_deriv_cont : ∀ t, Continuous (deriv (P.ω t))
  m_pos : 0 < m
  g_ge : ∀ t u, m ≤ P.g t u
  a_nonneg : ∀ t u, 0 ≤ P.a t u
  a_le : ∀ t u, P.a t u ≤ κ * P.g t u
  turn : ∀ t, ∫ u in (0 : ℝ)..P.p, P.a t u = π
  rot : ∀ t u, P.g t u * P.ω t u = deriv (P.η t) u + P.ξ t u * P.a t u
  stretch : ∀ t u, P.gd t u = deriv (P.ξ t) u - P.η t u * P.a t u
  a_udiff : ∀ t₀, UDiffAt P.a (deriv (P.ω t₀)) t₀
  g_udiff : ∀ t₀, UDiffAt P.g (P.gd t₀) t₀

namespace PathData

/-- The steering angle of the path at time `t`. -/
noncomputable def δ (P : PathData) (t : ℝ) : ℝ → ℝ := steerAngle P.p (P.a t) (P.g t)

/-- Its time derivative: the periodic solution of the linearized steering equation. -/
noncomputable def D (P : PathData) (t : ℝ) : ℝ → ℝ :=
  linSol P.p (fun u => deriv (P.ω t) u - P.gd t u * Real.sin (P.δ t u))
    (fun u => P.g t u * Real.cos (P.δ t u))

/-- The path of selected rears. -/
noncomputable def rear (P : PathData) : PathData where
  p := P.p
  a t u := P.g t u * Real.sin (P.δ t u)
  g t u := P.g t u * Real.cos (P.δ t u)
  ξ t u := P.ξ t u * Real.cos (P.δ t u) - P.η t u * Real.sin (P.δ t u)
  η t u := P.ξ t u * Real.sin (P.δ t u) + P.η t u * Real.cos (P.δ t u) - (P.ω t u - P.D t u)
  ω t u := P.ω t u - P.D t u
  gd t u := P.gd t u * Real.cos (P.δ t u) - P.g t u * Real.sin (P.δ t u) * P.D t u

variable {P : PathData} {κ m : ℝ}

lemma Valid.g_pos (hP : P.Valid κ m) (t u : ℝ) : 0 < P.g t u := hP.m_pos.trans_le (hP.g_ge t u)

lemma Valid.δ_spec (hP : P.Valid κ m) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (t : ℝ) :
    Function.Periodic (P.δ t) P.p ∧
      (∀ u, HasDerivAt (P.δ t) (P.a t u - P.g t u * Real.sin (P.δ t u)) u) ∧
      ∀ u, P.δ t u ∈ Set.Icc 0 (Real.arcsin κ) :=
  steerAngle_spec hP.p_pos hκ0 hκ1 (hP.a_cont t) (hP.g_cont t) (hP.a_per t) (hP.g_per t)
    (hP.g_pos t) (hP.a_nonneg t) (hP.a_le t)

lemma Valid.δ_cont (hP : P.Valid κ m) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (t : ℝ) :
    Continuous (P.δ t) :=
  continuous_iff_continuousAt.2 fun u => ((hP.δ_spec hκ0 hκ1 t).2.1 u).continuousAt

lemma Valid.cos_δ_pos (hP : P.Valid κ m) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (t u : ℝ) :
    0 < Real.cos (P.δ t u) := by
  have hb := (hP.δ_spec hκ0 hκ1 t).2.2 u
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hb.1, Real.pi_pos],
    hb.2.trans_lt (arcsin_lt_pi_div_two hκ1)⟩

lemma Valid.cos_arcsin_le (hP : P.Valid κ m) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (t u : ℝ) :
    Real.cos (Real.arcsin κ) ≤ Real.cos (P.δ t u) := by
  have hb := (hP.δ_spec hκ0 hκ1 t).2.2 u
  exact Real.cos_le_cos_of_nonneg_of_le_pi hb.1
    (by linarith [arcsin_lt_pi_div_two hκ1, Real.pi_pos]) hb.2

lemma Valid.D_spec (hP : P.Valid κ m) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (t : ℝ) :
    Function.Periodic (P.D t) P.p ∧
      ∀ u, HasDerivAt (P.D t) (deriv (P.ω t) u - P.gd t u * Real.sin (P.δ t u) -
        P.g t u * Real.cos (P.δ t u) * P.D t u) u := by
  have hδc := hP.δ_cont hκ0 hκ1 t
  have hδp := (hP.δ_spec hκ0 hκ1 t).1
  exact linSol_spec hP.p_pos ((hP.ω_deriv_cont t).sub ((hP.gd_cont t).mul
      (Real.continuous_sin.comp hδc)))
    ((hP.g_cont t).mul (Real.continuous_cos.comp hδc))
    (fun u => by
      show deriv (P.ω t) (u + P.p) - P.gd t (u + P.p) * Real.sin (P.δ t (u + P.p)) = _
      rw [periodic_deriv (hP.ω_per t) u, hP.gd_per t u, hδp u])
    (fun u => by simp only [hP.g_per t u, hδp u])
    (fun u => mul_pos (hP.g_pos t u) (hP.cos_δ_pos hκ0 hκ1 t u))

lemma Valid.D_cont (hP : P.Valid κ m) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (t : ℝ) :
    Continuous (P.D t) :=
  continuous_iff_continuousAt.2 fun u => ((hP.D_spec hκ0 hκ1 t).2 u).continuousAt

/-- **The steering angle is differentiable in `t`, uniformly in `u`, with derivative `D`.** -/
lemma Valid.δ_udiff (hP : P.Valid κ m) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (t₀ : ℝ) :
    UDiffAt P.δ (P.D t₀) t₀ := by
  obtain ⟨M, hM⟩ := exists_abs_le_of_periodic hP.p_pos (hP.g_cont t₀) (hP.g_per t₀)
  obtain ⟨M₁, hM₁⟩ := exists_abs_le_of_periodic hP.p_pos (hP.ω_deriv_cont t₀)
    (periodic_deriv (hP.ω_per t₀))
  obtain ⟨M₂, hM₂⟩ := exists_abs_le_of_periodic hP.p_pos (hP.gd_cont t₀) (hP.gd_per t₀)
  exact steering_param_deriv (M := M) (M' := max M₁ M₂) hP.p_pos
    (arcsin_lt_pi_div_two hκ1) hP.m_pos (fun t => (hP.δ_spec hκ0 hκ1 t).2.1)
    (fun t => (hP.δ_spec hκ0 hκ1 t).1) (fun t => (hP.δ_spec hκ0 hκ1 t).2.2) hP.g_ge
    (fun u => (le_abs_self _).trans (hM u)) (fun u => (hM₁ u).trans (le_max_left _ _))
    (fun u => (hM₂ u).trans (le_max_right _ _)) (hP.a_udiff t₀) (hP.g_udiff t₀)
    (hP.D_spec hκ0 hκ1 t₀).2 (hP.D_spec hκ0 hκ1 t₀).1

/-- The derivative of the rear normal velocity: the **Jacobi equation**. -/
lemma Valid.rear_η_hasDerivAt (hP : P.Valid κ m) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (t u : ℝ) :
    HasDerivAt (P.rear.η t) (P.g t u * P.η t u - P.g t u * Real.cos (P.δ t u) *
      P.rear.η t u) u := by
  have := jacobi_equation (ξ := P.ξ t) (η := P.η t) (g := P.g t) (δ := P.δ t)
    (Θdot := P.ω t) (gdot := P.gd t) (D := P.D t) (ξ' := deriv (P.ξ t))
    (η' := deriv (P.η t)) (Θ' := P.a t) (Θdot' := deriv (P.ω t)) u
    ((hP.ξ_diff t u).hasDerivAt) ((hP.η_diff t u).hasDerivAt)
    ((hP.δ_spec hκ0 hκ1 t).2.1 u) ((hP.ω_diff t u).hasDerivAt)
    ((hP.D_spec hκ0 hκ1 t).2 u) (hP.rot t u) (hP.stretch t u)
  exact this

lemma Valid.rear_ξ_hasDerivAt (hP : P.Valid κ m) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (t u : ℝ) :
    HasDerivAt (P.rear.ξ t)
      (deriv (P.ξ t) u * Real.cos (P.δ t u) +
        P.ξ t u * (-Real.sin (P.δ t u) * (P.a t u - P.g t u * Real.sin (P.δ t u))) -
        (deriv (P.η t) u * Real.sin (P.δ t u) +
          P.η t u * (Real.cos (P.δ t u) * (P.a t u - P.g t u * Real.sin (P.δ t u))))) u := by
  have hδ := (hP.δ_spec hκ0 hκ1 t).2.1 u
  have h := ((hP.ξ_diff t u).hasDerivAt.mul hδ.cos).sub ((hP.η_diff t u).hasDerivAt.mul hδ.sin)
  convert h using 1

lemma Valid.rear_ω_hasDerivAt (hP : P.Valid κ m) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (t u : ℝ) :
    HasDerivAt (P.rear.ω t) (P.gd t u * Real.sin (P.δ t u) +
      P.g t u * Real.cos (P.δ t u) * P.D t u) u := by
  have h := (hP.ω_diff t u).hasDerivAt.sub ((hP.D_spec hκ0 hκ1 t).2 u)
  convert h using 1; ring

/-- **The rears of a valid path form a valid path**, provided their curvatures `tan δ` are at
most `κ'`. -/
theorem Valid.rear (hP : P.Valid κ m) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {κ' : ℝ}
    (hcurv : ∀ t u, Real.tan (P.δ t u) ≤ κ') :
    P.rear.Valid κ' (m * Real.cos (Real.arcsin κ)) := by
  have hδs := hP.δ_spec hκ0 hκ1
  have hδc := hP.δ_cont hκ0 hκ1
  have hDs := hP.D_spec hκ0 hκ1
  have hDc := hP.D_cont hκ0 hκ1
  have hcos := hP.cos_δ_pos hκ0 hκ1
  have hca : 0 < Real.cos (Real.arcsin κ) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.arcsin_nonneg.2 hκ0, Real.pi_pos], arcsin_lt_pi_div_two hκ1⟩
  have hηR := hP.rear_η_hasDerivAt hκ0 hκ1
  have hξR := hP.rear_ξ_hasDerivAt hκ0 hκ1
  have hωR := hP.rear_ω_hasDerivAt hκ0 hκ1
  -- bounds at a fixed time
  have bnd : ∀ t₀, ∃ B, (∀ u, |P.g t₀ u| ≤ B) ∧ (∀ u, |P.gd t₀ u| ≤ B) ∧
      (∀ u, |P.D t₀ u| ≤ B) ∧ (∀ u, |Real.sin (P.δ t₀ u)| ≤ B) ∧
      (∀ u, |Real.cos (P.δ t₀ u)| ≤ B) := by
    intro t₀
    obtain ⟨B₁, h₁⟩ := exists_abs_le_of_periodic hP.p_pos (hP.g_cont t₀) (hP.g_per t₀)
    obtain ⟨B₂, h₂⟩ := exists_abs_le_of_periodic hP.p_pos (hP.gd_cont t₀) (hP.gd_per t₀)
    obtain ⟨B₃, h₃⟩ := exists_abs_le_of_periodic hP.p_pos (hDc t₀) (hDs t₀).1
    refine ⟨max (max B₁ B₂) (max B₃ 1), fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_,
      fun u => ?_⟩
    · exact (h₁ u).trans (le_max_of_le_left (le_max_left _ _))
    · exact (h₂ u).trans (le_max_of_le_left (le_max_right _ _))
    · exact (h₃ u).trans (le_max_of_le_right (le_max_left _ _))
    · exact (Real.abs_sin_le_one _).trans (le_max_of_le_right (le_max_right _ _))
    · exact (Real.abs_cos_le_one _).trans (le_max_of_le_right (le_max_right _ _))
  refine
  { p_pos := hP.p_pos
    a_per := fun t u => by simp only [PathData.rear, hP.g_per t u, (hδs t).1 u]
    g_per := fun t u => by simp only [PathData.rear, hP.g_per t u, (hδs t).1 u]
    ξ_per := fun t u => by simp only [PathData.rear, hP.ξ_per t u, hP.η_per t u, (hδs t).1 u]
    η_per := fun t u => by
      simp only [PathData.rear, hP.ξ_per t u, hP.η_per t u, hP.ω_per t u, (hδs t).1 u,
        (hDs t).1 u]
    ω_per := fun t u => by simp only [PathData.rear, hP.ω_per t u, (hDs t).1 u]
    gd_per := fun t u => by
      simp only [PathData.rear, hP.gd_per t u, hP.g_per t u, (hδs t).1 u, (hDs t).1 u]
    a_cont := fun t => (hP.g_cont t).mul (Real.continuous_sin.comp (hδc t))
    g_cont := fun t => (hP.g_cont t).mul (Real.continuous_cos.comp (hδc t))
    gd_cont := fun t => ((hP.gd_cont t).mul (Real.continuous_cos.comp (hδc t))).sub
      (((hP.g_cont t).mul (Real.continuous_sin.comp (hδc t))).mul (hDc t))
    ξ_diff := fun t u => (hξR t u).differentiableAt
    η_diff := fun t u => (hηR t u).differentiableAt
    η_deriv_cont := fun t => by
      rw [show deriv (P.rear.η t) = fun u => P.g t u * P.η t u - P.g t u *
        Real.cos (P.δ t u) * P.rear.η t u from funext fun u => (hηR t u).deriv]
      exact ((hP.g_cont t).mul (hP.η_diff t).continuous).sub
        (((hP.g_cont t).mul (Real.continuous_cos.comp (hδc t))).mul
          (continuous_iff_continuousAt.2 fun u => (hηR t u).continuousAt))
    ω_diff := fun t u => (hωR t u).differentiableAt
    ω_deriv_cont := fun t => by
      rw [show deriv (P.rear.ω t) = fun u => P.gd t u * Real.sin (P.δ t u) +
        P.g t u * Real.cos (P.δ t u) * P.D t u from funext fun u => (hωR t u).deriv]
      exact ((hP.gd_cont t).mul (Real.continuous_sin.comp (hδc t))).add
        (((hP.g_cont t).mul (Real.continuous_cos.comp (hδc t))).mul (hDc t))
    m_pos := mul_pos hP.m_pos hca
    g_ge := fun t u => mul_le_mul (hP.g_ge t u) (hP.cos_arcsin_le hκ0 hκ1 t u) hca.le
      (hP.g_pos t u).le
    a_nonneg := fun t u => by
      have hb := (hδs t).2.2 u
      exact mul_nonneg (hP.g_pos t u).le (Real.sin_nonneg_of_nonneg_of_le_pi hb.1
        (by linarith [hb.2, arcsin_lt_pi_div_two hκ1, Real.pi_pos]))
    a_le := fun t u => by
      have h1 := hcurv t u
      rw [Real.tan_eq_sin_div_cos, div_le_iff₀ (hcos t u)] at h1
      show P.g t u * Real.sin (P.δ t u) ≤ κ' * (P.g t u * Real.cos (P.δ t u))
      have := mul_le_mul_of_nonneg_left h1 (hP.g_pos t u).le
      linarith
    turn := fun t => by
      show ∫ u in (0 : ℝ)..P.p, P.g t u * Real.sin (P.δ t u) = π
      have e : (fun u => P.g t u * Real.sin (P.δ t u)) =
          fun u => P.a t u - (P.a t u - P.g t u * Real.sin (P.δ t u)) := by
        funext u; ring
      have hi : IntervalIntegrable (fun u => P.a t u - P.g t u * Real.sin (P.δ t u))
          MeasureTheory.volume 0 P.p := ((hP.a_cont t).sub ((hP.g_cont t).mul
          (Real.continuous_sin.comp (hδc t)))).intervalIntegrable _ _
      rw [e, intervalIntegral.integral_sub ((hP.a_cont t).intervalIntegrable _ _) hi, hP.turn t,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => (hδs t).2.1 u) hi,
        show P.δ t P.p = P.δ t 0 from by simpa using (hδs t).1 0, sub_self, sub_zero]
    rot := fun t u => by
      rw [(hηR t u).deriv]
      simp only [PathData.rear]
      have hsc := Real.sin_sq_add_cos_sq (P.δ t u)
      linear_combination (P.g t u * P.η t u) * hsc
    stretch := fun t u => by
      rw [(hξR t u).deriv]
      simp only [PathData.rear]
      have hr := hP.rot t u
      have hs := hP.stretch t u
      linear_combination Real.cos (P.δ t u) * hs - Real.sin (P.δ t u) * hr
    a_udiff := fun t₀ => by
      obtain ⟨B, hB1, hB2, hB3, hB4, hB5⟩ := bnd t₀
      have h1 := (hP.δ_udiff hκ0 hκ1 t₀).sin hB3
      have hB : ∀ u, |Real.cos (P.δ t₀ u) * P.D t₀ u| ≤ B * B := fun u => by
        rw [abs_mul]; exact mul_le_mul (hB5 u) (hB3 u) (abs_nonneg _)
          ((abs_nonneg _).trans (hB5 u))
      have h2 := (hP.g_udiff t₀).mul (B := max B (B * B)) h1
        (fun u => (hB1 u).trans (le_max_left _ _)) (fun u => (hB4 u).trans (le_max_left _ _))
        (fun u => (hB2 u).trans (le_max_left _ _)) (fun u => (hB u).trans (le_max_right _ _))
      refine h2.congr (fun t u => rfl) (fun u => ?_)
      rw [(hωR t₀ u).deriv]; ring
    g_udiff := fun t₀ => by
      obtain ⟨B, hB1, hB2, hB3, hB4, hB5⟩ := bnd t₀
      have h1 := (hP.δ_udiff hκ0 hκ1 t₀).cos hB3
      have hB : ∀ u, |-(Real.sin (P.δ t₀ u) * P.D t₀ u)| ≤ B * B := fun u => by
        rw [abs_neg, abs_mul]; exact mul_le_mul (hB4 u) (hB3 u) (abs_nonneg _)
          ((abs_nonneg _).trans (hB5 u))
      have h2 := (hP.g_udiff t₀).mul (B := max B (B * B)) h1
        (fun u => (hB1 u).trans (le_max_left _ _)) (fun u => (hB5 u).trans (le_max_left _ _))
        (fun u => (hB2 u).trans (le_max_left _ _)) (fun u => (hB u).trans (le_max_right _ _))
      refine h2.congr (fun t u => rfl) (fun u => ?_)
      simp only [PathData.rear]; ring }

end PathData

end Ovals

end
