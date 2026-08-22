import Mathlib
import UnitTangentIterates.PathMetricRescale
import UnitTangentIterates.ArclengthInverse

/-!
# Normal paths can be run at bounded normal speed

`PathMetricRescale.pathDist_eq_sInf_unitTime` shows that the path
pseudodistance of `PathMetric.lean` is already the infimum of the costs of the
normal paths **of duration one**: a linear change of the time does not change
the cost.  A linear change of the time does not, however, control the *size* of
the normal velocity: a path of small cost may still move very fast for a very
short while, its cost density `m` having a tall thin spike.

Many of the estimates of the paper degrade with the size of the normal velocity
along the path rather than with its cost — the constants of the gauge flow, for
instance, involve a sup bound `E_F` for the normal velocity of the fronts — so a
Lipschitz criterion tested on paths of duration one is not by itself enough.
This file removes that obstruction with a **nonlinear** change of the time.

Given a normal path `Γ` and `ε > 0`, write `M(t) = ∫₀ᵗ (m + ε/T)` for the mass
of its cost density augmented by a positive constant.  `M` is a `C¹`
increasing bijection of the line, so the time may be changed by
`ψ(τ) = M⁻¹(M(T)·A(τ))`, where `A` is the primitive of the fixed profile
`w(τ) = 6 max(0, τ(1−τ))`, which vanishes off `(0,1)` and has total mass one.
Along the reparametrized path the cost density is at most `M(T)·w(τ)`: the
motion is spread evenly over the unit time interval, at the price of the
arbitrarily small extra cost `ε`.

Main results:

* `PathMetric.NormalPath.reparam` : the reparametrized path, with
  `cost_reparam` and `reparam_m_le`;
* `PathMetric.exists_unitTime_bounded_speed` : every normal path is, up to an
  arbitrarily small extra cost, a path of duration one whose cost density —
  hence whose normal speed, together with the sup norms of its first two
  arclength derivatives — is everywhere at most `(3/2)` times its cost;
* `PathMetric.pathDist_le_mul_of_maps_bounded_paths` : consequently, in the
  Lipschitz criterion it is enough to control the image of the normal paths of
  duration one **whose cost density is bounded by `(3/2)b`**, for any `b`
  exceeding the pseudodistance of the two curves.
-/

noncomputable section

open Set MeasureTheory MarkedSpace MarkedTopology

namespace PathMetric

/-! ### The sup norm under a scalar factor -/

/-- The sup norm of a nonnegative multiple. -/
theorem supNorm_const_mul {c : ℝ} (hc : 0 ≤ c) (f : ℝ → ℝ) :
    supNorm (fun u => c * f u) = c * supNorm f := by
  unfold supNorm
  rw [Real.mul_iSup_of_nonneg hc]
  exact iSup_congr fun u => by rw [abs_mul, abs_of_nonneg hc]

/-- Iterated derivatives commute with a scalar factor, with no regularity
hypothesis: where the function fails to be differentiable, so does its
multiple. -/
theorem iteratedDeriv_const_mul' (c : ℝ) (f : ℝ → ℝ) (n : ℕ) :
    iteratedDeriv n (fun u => c * f u) = fun u => c * iteratedDeriv n f u := by
  induction n generalizing f with
  | zero => funext u; simp
  | succ k ih =>
      funext u
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      have hd : deriv (fun u => c * f u) = fun u => c * deriv f u := by
        funext x; exact deriv_const_mul_field c
      rw [hd, ih]

/-! ### The time profile -/

/-- The time profile `w(τ) = 6 max(0, τ(1−τ))`: a continuous nonnegative
function, vanishing off `(0,1)`, of total mass one and sup norm `3/2`. -/
def speedProfile (t : ℝ) : ℝ := 6 * max 0 (t * (1 - t))

theorem speedProfile_nonneg (t : ℝ) : 0 ≤ speedProfile t := by
  have h : (0:ℝ) ≤ max 0 (t * (1 - t)) := le_max_left _ _
  unfold speedProfile; linarith

theorem continuous_speedProfile : Continuous speedProfile := by
  unfold speedProfile; fun_prop

theorem speedProfile_le (t : ℝ) : speedProfile t ≤ 3 / 2 := by
  have h : max 0 (t * (1 - t)) ≤ 1 / 4 := max_le (by norm_num) (by nlinarith [sq_nonneg (t - 1/2)])
  unfold speedProfile; linarith

theorem speedProfile_eq_zero {t : ℝ} (ht : t ∉ Ioo (0:ℝ) 1) : speedProfile t = 0 := by
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at ht
  have h : t * (1 - t) ≤ 0 := by
    rcases ht with ht | ht
    · nlinarith
    · nlinarith
  unfold speedProfile
  rw [max_eq_left h]
  ring

/-- The primitive of the time profile. -/
def profileMass (t : ℝ) : ℝ := ∫ r in (0:ℝ)..t, speedProfile r

theorem hasDerivAt_profileMass (t : ℝ) : HasDerivAt profileMass (speedProfile t) t :=
  (continuous_speedProfile.integral_hasStrictDerivAt 0 t).hasDerivAt

@[simp] theorem profileMass_zero : profileMass 0 = 0 := by
  simp [profileMass]

@[simp] theorem profileMass_one : profileMass 1 = 1 := by
  have hcongr : (∫ r in (0:ℝ)..1, speedProfile r) = ∫ r in (0:ℝ)..1, (6 * r - 6 * r ^ 2) := by
    refine intervalIntegral.integral_congr (fun r hr => ?_)
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hr
    have h : 0 ≤ r * (1 - r) := mul_nonneg hr.1 (by linarith [hr.2])
    unfold speedProfile
    rw [max_eq_right h]
    ring
  have h1 : (∫ r in (0:ℝ)..1, (6 * r - 6 * r ^ 2)) = 1 := by
    have hi1 : IntervalIntegrable (fun r : ℝ => 6 * r) volume 0 1 :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun r : ℝ => 6 * r ^ 2) volume 0 1 :=
      (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_id, integral_pow]
    norm_num
  rw [profileMass, hcongr, h1]

namespace NormalPath

variable {p q : Data}

/-! ### The augmented mass of the cost density -/

/-- The mass of the cost density of a normal path, augmented by a constant. -/
def mass (Γ : NormalPath p q) (e : ℝ) (t : ℝ) : ℝ := ∫ r in (0:ℝ)..t, (Γ.m r + e)

theorem hasDerivAt_mass (Γ : NormalPath p q) (e t : ℝ) :
    HasDerivAt (mass Γ e) (Γ.m t + e) t :=
  ((Γ.cont_m.add continuous_const).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem le_mass_deriv (Γ : NormalPath p q) {e : ℝ} (t : ℝ) : e ≤ Γ.m t + e := by
  linarith [Γ.m_nonneg t]

@[simp] theorem mass_zero (Γ : NormalPath p q) (e : ℝ) : mass Γ e 0 = 0 := by
  simp [mass]

theorem mass_final (Γ : NormalPath p q) (e : ℝ) : mass Γ e Γ.T = cost Γ + e * Γ.T := by
  rw [mass, intervalIntegral.integral_add (Γ.cont_m.intervalIntegrable _ _)
    (intervalIntegrable_const)]
  simp [cost, mul_comm]

theorem mass_nonneg (Γ : NormalPath p q) {e : ℝ} (he : 0 ≤ e) : 0 ≤ mass Γ e Γ.T := by
  rw [mass_final]
  have := Γ.cost_nonneg
  have := Γ.T_pos.le
  positivity

/-! ### The change of time -/

variable (Γ : NormalPath p q) (e : ℝ) (minv : ℝ → ℝ)

/-- The change of time: the profile mass, rescaled to the augmented mass of the
cost density and read through its inverse. -/
def reparamTime (τ : ℝ) : ℝ := minv (mass Γ e Γ.T * profileMass τ)

/-- Its derivative. -/
def reparamSpeed (τ : ℝ) : ℝ :=
  mass Γ e Γ.T * speedProfile τ / (Γ.m (reparamTime Γ e minv τ) + e)

variable {Γ e minv}

theorem hasDerivAt_reparamTime (he : 0 < e) (hminv : ∀ y, mass Γ e (minv y) = y) (τ : ℝ) :
    HasDerivAt (reparamTime Γ e minv) (reparamSpeed Γ e minv τ) τ := by
  have hin : HasDerivAt (fun r => mass Γ e Γ.T * profileMass r)
      (mass Γ e Γ.T * speedProfile τ) τ := (hasDerivAt_profileMass τ).const_mul _
  have hout := ArclengthInverse.hasDerivAt_of_rightInverse he (hasDerivAt_mass Γ e)
    (fun t => le_mass_deriv Γ t) hminv (mass Γ e Γ.T * profileMass τ)
  have h := hout.comp τ hin
  rw [Function.comp_def] at h
  refine h.congr_deriv ?_
  rw [reparamSpeed, reparamTime]
  ring

theorem reparamTime_zero (he : 0 < e) (hminv : ∀ y, mass Γ e (minv y) = y) :
    reparamTime Γ e minv 0 = 0 := by
  have hinj : Function.Injective (mass Γ e) :=
    (ArclengthInverse.strictMono_of_deriv_ge he (hasDerivAt_mass Γ e)
      (fun t => le_mass_deriv Γ t)).injective
  have h : mass Γ e (reparamTime Γ e minv 0) = mass Γ e 0 := by
    rw [reparamTime, hminv, profileMass_zero, mul_zero, mass_zero]
  exact hinj h

theorem reparamTime_one (he : 0 < e) (hminv : ∀ y, mass Γ e (minv y) = y) :
    reparamTime Γ e minv 1 = Γ.T := by
  have hinj : Function.Injective (mass Γ e) :=
    (ArclengthInverse.strictMono_of_deriv_ge he (hasDerivAt_mass Γ e)
      (fun t => le_mass_deriv Γ t)).injective
  have h : mass Γ e (reparamTime Γ e minv 1) = mass Γ e Γ.T := by
    rw [reparamTime, hminv, profileMass_one, mul_one]
  exact hinj h

theorem reparamSpeed_nonneg (he : 0 < e) (τ : ℝ) : 0 ≤ reparamSpeed Γ e minv τ := by
  have hden : 0 < Γ.m (reparamTime Γ e minv τ) + e :=
    lt_of_lt_of_le he (le_mass_deriv Γ _)
  have hnum : 0 ≤ mass Γ e Γ.T * speedProfile τ :=
    mul_nonneg (mass_nonneg Γ he.le) (speedProfile_nonneg τ)
  exact div_nonneg hnum hden.le

/-- **The reparametrized path is slow**: its cost density is at most the total
augmented mass times the profile. -/
theorem m_reparamSpeed_le (he : 0 < e) (τ : ℝ) :
    Γ.m (reparamTime Γ e minv τ) * reparamSpeed Γ e minv τ
      ≤ mass Γ e Γ.T * speedProfile τ := by
  have hden : 0 < Γ.m (reparamTime Γ e minv τ) + e :=
    lt_of_lt_of_le he (le_mass_deriv Γ _)
  have hnum : 0 ≤ mass Γ e Γ.T * speedProfile τ :=
    mul_nonneg (mass_nonneg Γ he.le) (speedProfile_nonneg τ)
  rw [reparamSpeed, mul_div_assoc', div_le_iff₀ hden]
  nlinarith [Γ.m_nonneg (reparamTime Γ e minv τ)]

theorem continuous_reparamTime (he : 0 < e) (hminv : ∀ y, mass Γ e (minv y) = y) :
    Continuous (reparamTime Γ e minv) :=
  continuous_iff_continuousAt.mpr fun τ => (hasDerivAt_reparamTime he hminv τ).continuousAt

theorem continuous_reparamSpeed (he : 0 < e) (hminv : ∀ y, mass Γ e (minv y) = y) :
    Continuous (reparamSpeed Γ e minv) := by
  have hden : Continuous fun τ => Γ.m (reparamTime Γ e minv τ) + e :=
    (Γ.cont_m.comp (continuous_reparamTime he hminv)).add continuous_const
  refine Continuous.div (continuous_const.mul continuous_speedProfile) hden (fun τ => ?_)
  exact ne_of_gt (lt_of_lt_of_le he (le_mass_deriv Γ _))

/-! ### The reparametrized path -/

/-- **The reparametrization of a normal path in the time.**  The motion is
spread over the unit time interval according to the fixed profile
`w(τ) = 6 max(0, τ(1−τ))`, so that the new cost density is at most
`(cost Γ + e·T)·w(τ)`; the extra cost `e·T` can be made as small as one
likes. -/
def reparam (Γ : NormalPath p q) {e : ℝ} (he : 0 < e) {minv : ℝ → ℝ}
    (hminv : ∀ y, mass Γ e (minv y) = y) : NormalPath p q where
  T := 1
  T_pos := one_pos
  X := fun τ u => Γ.X (reparamTime Γ e minv τ) u
  eta := fun τ u => reparamSpeed Γ e minv τ * Γ.eta (reparamTime Γ e minv τ) u
  nu := fun τ u => Γ.nu (reparamTime Γ e minv τ) u
  m := fun τ => mass Γ e Γ.T * speedProfile τ
  start := fun u => by rw [reparamTime_zero he hminv]; exact Γ.start u
  finish := fun u => by rw [reparamTime_one he hminv]; exact Γ.finish u
  hasDerivAt_time := by
    intro τ u
    have h := (Γ.hasDerivAt_time (reparamTime Γ e minv τ) u).scomp τ
      (hasDerivAt_reparamTime he hminv τ)
    refine h.congr_deriv ?_
    simp [Complex.real_smul]
    ring
  cont_vel := by
    intro u
    have hcomp : Continuous fun τ =>
        ((Γ.eta (reparamTime Γ e minv τ) u : ℂ) * Γ.nu (reparamTime Γ e minv τ) u) :=
      (Γ.cont_vel u).comp (continuous_reparamTime he hminv)
    have hfun : (fun τ => ((reparamSpeed Γ e minv τ * Γ.eta (reparamTime Γ e minv τ) u : ℝ) : ℂ)
        * Γ.nu (reparamTime Γ e minv τ) u)
        = fun τ => ((reparamSpeed Γ e minv τ : ℝ) : ℂ) *
          ((Γ.eta (reparamTime Γ e minv τ) u : ℂ) * Γ.nu (reparamTime Γ e minv τ) u) := by
      funext τ; push_cast; ring
    rw [hfun]
    exact (Complex.continuous_ofReal.comp (continuous_reparamSpeed he hminv)).mul hcomp
  norm_nu := fun τ u => Γ.norm_nu _ u
  cont_m := continuous_const.mul continuous_speedProfile
  m_nonneg := fun τ => mul_nonneg (mass_nonneg Γ he.le) (speedProfile_nonneg τ)
  m_stop := fun τ hτ => by rw [speedProfile_eq_zero hτ, mul_zero]
  abs_eta_le := by
    intro τ u
    rw [abs_mul, abs_of_nonneg (reparamSpeed_nonneg he τ)]
    have h1 : reparamSpeed Γ e minv τ * |Γ.eta (reparamTime Γ e minv τ) u|
        ≤ reparamSpeed Γ e minv τ * Γ.m (reparamTime Γ e minv τ) :=
      mul_le_mul_of_nonneg_left (Γ.abs_eta_le _ u) (reparamSpeed_nonneg he τ)
    have h2 := m_reparamSpeed_le (Γ := Γ) (e := e) (minv := minv) he τ
    nlinarith
  le_m_L1 := by
    intro τ
    have hfun : (∫ u in (0:ℝ)..1, |reparamSpeed Γ e minv τ * Γ.eta (reparamTime Γ e minv τ) u|)
        = reparamSpeed Γ e minv τ * ∫ u in (0:ℝ)..1, |Γ.eta (reparamTime Γ e minv τ) u| := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      rw [abs_mul, abs_of_nonneg (reparamSpeed_nonneg he τ)]
    rw [hfun]
    have h1 : reparamSpeed Γ e minv τ * ∫ u in (0:ℝ)..1, |Γ.eta (reparamTime Γ e minv τ) u|
        ≤ reparamSpeed Γ e minv τ * Γ.m (reparamTime Γ e minv τ) :=
      mul_le_mul_of_nonneg_left (Γ.le_m_L1 _) (reparamSpeed_nonneg he τ)
    have h2 := m_reparamSpeed_le (Γ := Γ) (e := e) (minv := minv) he τ
    nlinarith
  le_m_sup := by
    intro τ j hj
    rw [iteratedDeriv_const_mul' _ _ j, supNorm_const_mul (reparamSpeed_nonneg he τ)]
    have h1 : reparamSpeed Γ e minv τ * supNorm (iteratedDeriv j (Γ.eta (reparamTime Γ e minv τ)))
        ≤ reparamSpeed Γ e minv τ * Γ.m (reparamTime Γ e minv τ) :=
      mul_le_mul_of_nonneg_left (Γ.le_m_sup _ j hj) (reparamSpeed_nonneg he τ)
    have h2 := m_reparamSpeed_le (Γ := Γ) (e := e) (minv := minv) he τ
    nlinarith

@[simp] theorem reparam_T (Γ : NormalPath p q) {e : ℝ} (he : 0 < e) {minv : ℝ → ℝ}
    (hminv : ∀ y, mass Γ e (minv y) = y) : (Γ.reparam he hminv).T = 1 := rfl

/-- The cost of the reparametrized path: the cost of the original, plus the
extra `e·T`. -/
theorem cost_reparam (Γ : NormalPath p q) {e : ℝ} (he : 0 < e) {minv : ℝ → ℝ}
    (hminv : ∀ y, mass Γ e (minv y) = y) :
    cost (Γ.reparam he hminv) = cost Γ + e * Γ.T := by
  have h : cost (Γ.reparam he hminv) = ∫ τ in (0:ℝ)..1, mass Γ e Γ.T * speedProfile τ := rfl
  rw [h, intervalIntegral.integral_const_mul]
  rw [show (∫ τ in (0:ℝ)..1, speedProfile τ) = profileMass 1 from rfl, profileMass_one, mul_one,
    mass_final]

/-- **The reparametrized path is slow**: its cost density never exceeds `3/2`
times its cost. -/
theorem reparam_m_le (Γ : NormalPath p q) {e : ℝ} (he : 0 < e) {minv : ℝ → ℝ}
    (hminv : ∀ y, mass Γ e (minv y) = y) (τ : ℝ) :
    (Γ.reparam he hminv).m τ ≤ (3 / 2) * (cost Γ + e * Γ.T) := by
  have h : (Γ.reparam he hminv).m τ = mass Γ e Γ.T * speedProfile τ := rfl
  rw [h, mass_final]
  have hc : 0 ≤ cost Γ + e * Γ.T := by
    have := Γ.cost_nonneg; have := Γ.T_pos.le; positivity
  nlinarith [speedProfile_le τ, speedProfile_nonneg τ]

end NormalPath

/-! ### Slow paths suffice -/

open NormalPath

/-- **Every normal path can be run at bounded normal speed**, over the unit
time interval and at an arbitrarily small extra cost: there is a normal path
between the same two marked curves, of duration one, of cost `cost Γ + ε`,
whose cost density — hence the size of its normal velocity and of the first two
arclength derivatives of that velocity — is everywhere at most `3/2` times its
cost. -/
theorem exists_unitTime_bounded_speed {p q : Data} (Γ : NormalPath p q) {ε : ℝ} (hε : 0 < ε) :
    ∃ Δ : NormalPath p q, Δ.T = 1 ∧ cost Δ = cost Γ + ε ∧
      ∀ t, Δ.m t ≤ (3 / 2) * (cost Γ + ε) := by
  set e : ℝ := ε / Γ.T with he_def
  have he : 0 < e := div_pos hε Γ.T_pos
  have heT : e * Γ.T = ε := by
    rw [he_def, div_mul_cancel₀ _ (ne_of_gt Γ.T_pos)]
  obtain ⟨minv, hminv⟩ := ArclengthInverse.exists_rightInverse he
    (hasDerivAt_mass Γ e) (fun t => le_mass_deriv Γ t)
  refine ⟨Γ.reparam he hminv, rfl, ?_, fun t => ?_⟩
  · rw [cost_reparam, heT]
  · have := reparam_m_le Γ he hminv t
    rwa [heT] at this

/-- **A Lipschitz criterion tested on slow paths.**  If a map of marked curves
takes every normal path of duration one *whose cost density is at most*
`(3/2)b` to a path of cost at most `C` times as large, then it is `C`-Lipschitz
at the pair `p, q`, provided `b` exceeds their pseudodistance.

This is the form the estimates of the paper can meet: their constants degrade
with the size of the normal velocity along the path rather than with its cost,
and `exists_unitTime_bounded_speed` shows that near-optimal paths may always be
taken with the normal velocity bounded in terms of the pseudodistance. -/
theorem pathDist_le_mul_of_maps_bounded_paths {F : Data → Data} {p q : Data} {C b : ℝ}
    (hC : 0 ≤ C) (hb : pathDist p q < b)
    (h : ∀ Γ : NormalPath p q, Γ.T = 1 → (∀ t, Γ.m t ≤ (3 / 2) * b) →
      ∃ Γ' : NormalPath (F p) (F q), cost Γ' ≤ C * cost Γ)
    (hne : Nonempty (NormalPath p q)) :
    pathDist (F p) (F q) ≤ C * pathDist p q := by
  have hS : (costSet p q).Nonempty := ⟨cost hne.some, ⟨hne.some, rfl⟩⟩
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hCpos : 0 < C + 1 := by linarith
  set d : ℝ := pathDist p q with hd_def
  set r : ℝ := min (ε / (C + 1)) (b - d) with hr_def
  have hrpos : 0 < r := lt_min (by positivity) (by linarith)
  -- a path of cost close to the pseudodistance
  obtain ⟨c, ⟨Γ, rfl⟩, hc⟩ := exists_lt_of_csInf_lt hS
    (show d < d + r / 2 by linarith)
  -- run it at bounded speed
  obtain ⟨Δ, hT, hcost, hm⟩ := exists_unitTime_bounded_speed Γ (show (0:ℝ) < r / 2 by linarith)
  have hcostΔ : cost Δ ≤ d + r := by rw [hcost]; linarith
  have hmb : ∀ t, Δ.m t ≤ (3 / 2) * b := by
    intro t
    have h1 : cost Γ + r / 2 ≤ b := by
      have : r ≤ b - d := min_le_right _ _
      linarith
    have := hm t
    nlinarith
  obtain ⟨Γ', hΓ'⟩ := h Δ hT hmb
  have h1 : pathDist (F p) (F q) ≤ C * cost Δ := le_trans (pathDist_le_cost Γ') hΓ'
  have h2 : C * cost Δ ≤ C * (d + r) := mul_le_mul_of_nonneg_left hcostΔ hC
  have h3 : C * r ≤ ε := by
    have hr : r ≤ ε / (C + 1) := min_le_left _ _
    have : C * r ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hr hC
    have h4 : C * (ε / (C + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ hCpos]
      nlinarith
    linarith
  nlinarith

/-- **The same criterion with the hypothesis phrased on the normal speed.**  The
cost density of a normal path dominates its normal speed, so it is enough to
control the image of the paths of duration one along which the curve moves at
speed at most `(3/2)b`.  This is the shape the estimates of the paper ask for:
they are driven by a sup bound for the normal velocity. -/
theorem pathDist_le_mul_of_maps_slow_paths {F : Data → Data} {p q : Data} {C b : ℝ}
    (hC : 0 ≤ C) (hb : pathDist p q < b)
    (h : ∀ Γ : NormalPath p q, Γ.T = 1 → (∀ t u, |Γ.eta t u| ≤ (3 / 2) * b) →
      ∃ Γ' : NormalPath (F p) (F q), cost Γ' ≤ C * cost Γ)
    (hne : Nonempty (NormalPath p q)) :
    pathDist (F p) (F q) ≤ C * pathDist p q :=
  pathDist_le_mul_of_maps_bounded_paths hC hb
    (fun Γ hT hm => h Γ hT (fun t u => le_trans (Γ.abs_eta_le t u) (hm t))) hne

end PathMetric
