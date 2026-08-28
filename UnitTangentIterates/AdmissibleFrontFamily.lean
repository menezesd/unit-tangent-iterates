import Mathlib
import UnitTangentIterates.TwoCapPairsAssembly
import UnitTangentIterates.ConvexChordArc
import UnitTangentIterates.MainTheoremModel

/-!
# An explicit admissible family of model fronts

The closing step of *A Noncircular Oval with Convex Unit-Tangent Iterates*, in
the form `MarkedSpace.main_theorem_of_model_transverse`, asks of the geometry a
block of hypotheses on a family of model curvatures `κₙ` and their fronts:
continuity, `Hₙ`-periodicity, pinching `kmin ≤ κₙ ≤ κ̂`, total turning `π`,
a uniform chord-arc bound, small transverse width of the first model, and a
numerical slack in the width gap.

This file discharges that block **unconditionally**, by an explicit construction:
a constant-height family of thin capsule fronts.  The curvature is

`κ(s) = kmin + A · 2·max 0 (cos(2πs/H) − 1/2)`,

a baseline curvature `kmin > 0` carrying a smooth bump of extra turning
concentrated near `s ≡ 0 mod H`; the amplitude `A` is *defined* by the
normalisation `A·J = π − kmin·H` with `J = ∫₀ᴴ bump`, so the total-turning
axiom holds by construction.  Every other axiom is elementary calculus:
continuity and periodicity are inherited from `cos`; the chord-arc bound is
`ConvexChordArc.chord_arc_of_convex` applied to the front, whose tangent angle
turns exactly `2π` over `2H` by applying `frontAngle_add_halfPeriod` twice;
and the width estimate splits the centred cell into the bump zone (where
`sin Θ ≤ 1`) and two flat zones where the direction stays within
`kmin·H/3 = 1/48` of horizontal.

Outcomes:

* `exists_admissible_geometry` : the geometric block of hypotheses of
  `main_theorem_of_model_transverse` is simultaneously satisfiable;
* `main_theorem_from_dynamics` : feeding the family in, the paper's closing
  argument follows from the *dynamical* input alone (a non-expansive selected
  inverse realizing the unit-tangent transform up to reparametrization, and
  summability of the model defects).

This family is a surrogate for the hairpin-derived models of Sections 4–5;
instantiating it from the translating soliton, and proving the defect estimate
itself, remain open — as everywhere in this project.
-/

noncomputable section

namespace AdmissibleFrontFamily

open Real MeasureTheory intervalIntegral Set Function
open TwoCapPairsAssembly ConvexChordArc CurvatureInterpolation MarkedSpace

/-! ### Constants -/

/-- The separation of the (constant) model family. -/
def H : ℝ := 64

/-- The curvature floor. -/
def kmin : ℝ := 1 / 1024

/-- The curvature ceiling. -/
def kap : ℝ := 3 / 4

theorem hHpos : 0 < H := by norm_num [H]

theorem hkmpos : 0 < kmin := by norm_num [kmin]

theorem hkle : kmin ≤ kap := by norm_num [kmin, kap]

theorem pi_lb : 3 < Real.pi := Real.pi_gt_three

theorem pi_ub : Real.pi < 3.15 := Real.pi_lt_d2

theorem kmin_H : kmin * H = 1 / 16 := by unfold kmin H; norm_num

theorem kap_sub_kmin_pos : 0 < kap - kmin := by unfold kap kmin; norm_num

private theorem uIcc_mem {a b x : ℝ} (hab : a ≤ b) (h : x ∈ uIcc a b) : x ∈ Icc a b := by
  rcases mem_uIcc.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · have hxa : x = a := le_antisymm h2 (hab.trans h1)
    rw [hxa]
    exact ⟨le_rfl, hab⟩

/-! ### Trigonometric estimates -/

/-- `√3 ≥ 5/3`. -/
theorem five_third_le_sqrt_three : 5 / 3 ≤ Real.sqrt 3 :=
  calc (5:ℝ)/3 = Real.sqrt (((5:ℝ)/3)^2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)

/-- On `[0, π/6]` the cosine is at least `5/6`. -/
theorem cos_ge_five_six {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ Real.pi / 6) :
    5 / 6 ≤ Real.cos x := by
  have h : Real.cos (Real.pi / 6) ≤ Real.cos x :=
    Real.cos_le_cos_of_nonneg_of_le_pi h1 (by linarith [Real.pi_pos]) h2
  rw [Real.cos_pi_div_six] at h
  linarith [h, five_third_le_sqrt_three]

/-- On `[-π/6, π/6]` the cosine is at least `5/6`. -/
theorem cos_abs_ge_five_six {x : ℝ} (h : |x| ≤ Real.pi / 6) :
    5 / 6 ≤ Real.cos x := by
  rcases le_or_gt 0 x with hx | hx
  · have h' : x ≤ Real.pi / 6 := by rwa [abs_of_nonneg hx] at h
    exact cos_ge_five_six hx h'
  · have hxpos : 0 ≤ -x := by linarith
    have hbound : -x ≤ Real.pi / 6 := by
      have hb := abs_le.mp h
      linarith
    have hres := cos_ge_five_six hxpos hbound
    rwa [Real.cos_neg] at hres

/-- On `[π/3, π]` the cosine is at most `1/2`. -/
theorem cos_le_half {x : ℝ} (h1 : Real.pi / 3 ≤ x) (h2 : x ≤ Real.pi) :
    Real.cos x ≤ 1 / 2 := by
  have h : Real.cos x ≤ Real.cos (Real.pi / 3) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) h2 h1
  rwa [Real.cos_pi_div_three] at h

/-- `sin x ≤ x` for `0 ≤ x ≤ π/2`. -/
theorem sin_le_self_aux {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ Real.pi / 2) :
    Real.sin x ≤ x := by
  have hint : (∫ t in (0:ℝ)..x, Real.cos t) = Real.sin x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => Real.hasDerivAt_sin t)
      (Real.continuous_cos.intervalIntegrable (0:ℝ) x)]
    simp
  have hm : (∫ t in (0:ℝ)..x, Real.cos t) ≤ (∫ t in (0:ℝ)..x, (1:ℝ)) := by
    refine intervalIntegral.integral_mono_on hx
      (Real.continuous_cos.intervalIntegrable (0:ℝ) x)
      intervalIntegral.intervalIntegrable_const ?_
    intro t ht
    rcases mem_Icc.mp ht with ⟨ht1, ht2⟩
    have hpos : Real.cos (Real.pi / 2) ≤ Real.cos t :=
      Real.cos_le_cos_of_nonneg_of_le_pi ht1 (by linarith [Real.pi_pos])
        (by linarith [ht2, hx2])
    rw [Real.cos_pi_div_two] at hpos
    linarith [hpos, Real.cos_le_one t]
  calc Real.sin x = ∫ t in (0:ℝ)..x, Real.cos t := hint.symm
    _ ≤ ∫ t in (0:ℝ)..x, (1:ℝ) := hm
    _ = x := by simp

/-! ### The bump -/

/-- One period of extra turning: twice the positive part of
`cos(2πs/H) − 1/2`, of height `1` at multiples of `H`. -/
noncomputable def bump (s : ℝ) : ℝ :=
  2 * max 0 (Real.cos (2 * Real.pi * s / H) - 1 / 2)

theorem bump_nonneg (s : ℝ) : 0 ≤ bump s := by
  unfold bump
  have h : 0 ≤ max 0 (Real.cos (2 * Real.pi * s / H) - 1 / 2) := le_max_left 0 _
  linarith

theorem bump_le_one (s : ℝ) : bump s ≤ 1 := by
  have hc : Real.cos (2 * Real.pi * s / H) ≤ 1 := Real.cos_le_one _
  unfold bump
  have h1 : max 0 (Real.cos (2 * Real.pi * s / H) - 1 / 2) ≤ 1 / 2 := by
    refine max_le ?_ ?_ <;> linarith
  have h2 : (2:ℝ) * max 0 (Real.cos (2 * Real.pi * s / H) - 1 / 2)
      ≤ (2:ℝ) * (1/2) := mul_le_mul_of_nonneg_left h1 (by norm_num)
  linarith

theorem continuous_bump : Continuous bump := by
  unfold bump
  refine Continuous.mul continuous_const ?_
  refine Continuous.max continuous_const ?_
  exact (Real.continuous_cos.comp
    ((continuous_const.mul continuous_id).div continuous_const
      (fun _ => by norm_num [H]))).sub continuous_const

theorem periodic_bump : Function.Periodic bump H := by
  intro s
  unfold bump
  have key : 2 * Real.pi * (s + H) / H = 2 * Real.pi * s / H + 2 * Real.pi := by
    have e1 : (2:ℝ)*π*(s+H)/H = (2*π*s/H) + (2*π*H)/H := by
      rw [show (2:ℝ)*π*(s+H) = 2*π*s + 2*π*H from by ring, add_div]
    have e2 : ((2:ℝ)*π*H)/H = 2*π := by
      have hHne := hHpos.ne'
      field_simp
    rw [e1, e2]
  show 2 * max 0 (Real.cos (2 * Real.pi * (s + H) / H) - 1/2)
      = 2 * max 0 (Real.cos (2 * Real.pi * s / H) - 1/2)
  rw [key, Real.cos_add, Real.cos_two_pi, Real.sin_two_pi]
  ring

/-- The bump vanishes on the half-period away from the centre. -/
theorem bump_eq_zero_nonneg {s : ℝ} (h1 : H / 6 ≤ s) (h2 : s ≤ H / 2) : bump s = 0 := by
  have hHne := hHpos.ne'
  have hfacp : (0:ℝ) < 2 * Real.pi / H := div_pos (by linarith [Real.pi_pos]) hHpos
  have hc : Real.cos (2 * Real.pi * s / H) ≤ 1 / 2 := by
    refine cos_le_half ?_ ?_
    · have hEq : (2:ℝ)*π/H*(H/6) = π/3 := by
        have hrw : (2:ℝ)*π/H*(H/6) = (2*π/H*H)/6 := by ring
        rw [hrw, div_mul_cancel₀ _ hHne]
        ring
      calc Real.pi / 3 = (2:ℝ)*π/H*(H/6) := hEq.symm
        _ ≤ (2:ℝ)*π/H*s := mul_le_mul_of_nonneg_left h1 hfacp.le
        _ = 2 * Real.pi * s / H := by ring
    · have hEq : (2:ℝ)*π/H*(H/2) = π := by
        have hrw : (2:ℝ)*π/H*(H/2) = (2*π/H*H)/2 := by ring
        rw [hrw, div_mul_cancel₀ _ hHne]
        ring
      calc 2 * Real.pi * s / H = (2:ℝ)*π/H*s := by ring
        _ ≤ (2:ℝ)*π/H*(H/2) := mul_le_mul_of_nonneg_left h2 hfacp.le
        _ = π := hEq
  unfold bump
  rw [max_eq_left (by linarith)]
  ring

/-- The bump vanishes away from the centre of the period. -/
theorem bump_eq_zero {s : ℝ} (hsL : -(H / 2) ≤ s) (hsR : s ≤ H / 2)
    (hfar : H / 6 ≤ |s|) : bump s = 0 := by
  rcases le_abs.mp hfar with h | h
  · exact bump_eq_zero_nonneg h hsR
  · have hb : bump (-s) = 0 :=
      bump_eq_zero_nonneg (by linarith) (by linarith)
    have heq : bump s = bump (-s) := by
      unfold bump
      have hkey : (2:ℝ) * π * s / H = -((2:ℝ) * π * (-s) / H) := by ring
      rw [hkey, Real.cos_neg]
    rw [heq, hb]

/-! ### Total mass of the bump -/

/-- The total extra turning of the bump over one period. -/
noncomputable def J : ℝ := ∫ s in (0:ℝ)..H, bump s

theorem integral_window {f : ℝ → ℝ} (hp : Function.Periodic f H) :
    (∫ u in (-(H/2))..(H/2), f u) = ∫ u in (0:ℝ)..H, f u := by
  have h := hp.intervalIntegral_add_eq (-(H/2)) 0
  rw [show (-(H/2) + H : ℝ) = H / 2 from by ring, show (0:ℝ) + H = H from by ring] at h
  exact h

theorem J_lower_bound : 64 / 9 ≤ J := by
  have hwin : J = ∫ u in (-(H/2))..(H/2), bump u :=
    (integral_window periodic_bump).symm
  rw [hwin]
  have h12 : (-(H/12) : ℝ) ≤ H / 12 := by linarith [hHpos]
  have hAB : (∫ u in (-(H/2))..(H/2), bump u)
      = (∫ u in (-(H/2))..(-(H/12)), bump u) + ∫ u in (-(H/12))..(H/2), bump u :=
    (intervalIntegral.integral_add_adjacent_intervals
      (continuous_bump.intervalIntegrable (-(H/2)) (-(H/12)))
      (continuous_bump.intervalIntegrable (-(H/12)) (H/2))).symm
  have hBC : (∫ u in (-(H/12))..(H/2), bump u)
      = (∫ u in (-(H/12))..(H/12), bump u) + ∫ u in (H/12)..(H/2), bump u :=
    (intervalIntegral.integral_add_adjacent_intervals
      (continuous_bump.intervalIntegrable (-(H/12)) (H/12))
      (continuous_bump.intervalIntegrable (H/12) (H/2))).symm
  rw [hAB, hBC]
  have h0' : 0 ≤ (∫ u in (-(H/2))..(-(H/12)), bump u) :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _ => bump_nonneg u)
  have h2' : 0 ≤ (∫ u in (H/12)..(H/2), bump u) :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _ => bump_nonneg u)
  have hintconst : (∫ u in (-(H/12))..(H/12), (2:ℝ)/3) = 64 / 9 := by
    rw [intervalIntegral.integral_const]
    unfold H
    norm_num
  have hmid : (∫ u in (-(H/12))..(H/12), (2:ℝ)/3)
      ≤ ∫ u in (-(H/12))..(H/12), bump u := by
    refine intervalIntegral.integral_mono_on h12
      intervalIntegral.intervalIntegrable_const
      (continuous_bump.intervalIntegrable _ _) ?_
    intro t ht
    rcases mem_Icc.mp ht with ⟨ht1, ht2⟩
    have habs : |2 * Real.pi * t / H| ≤ Real.pi / 6 := by
      rw [abs_le]
      constructor
      · have key : ((-1:ℝ)/6) * H ≤ 2 * t := by
          have ht1' := ht1
          unfold H at ht1' ⊢
          linarith
        calc -(Real.pi / 6) = Real.pi * ((-1:ℝ)/6) := by ring
          _ ≤ Real.pi * (2 * t / H) :=
                mul_le_mul_of_nonneg_left
                  (by rw [le_div_iff₀ hHpos]; exact key) (le_of_lt Real.pi_pos)
          _ = 2 * Real.pi * t / H := by ring
      · have hinner : (2:ℝ)*t/H ≤ 1/6 := by
          rw [div_le_iff₀ hHpos]
          have ht2' := ht2
          unfold H at ht2' ⊢
          linarith
        calc 2 * Real.pi * t / H = Real.pi * (2 * t / H) := by ring
          _ ≤ Real.pi * (1/6) :=
                mul_le_mul_of_nonneg_left hinner (le_of_lt Real.pi_pos)
          _ = Real.pi / 6 := by ring
    have hge : 5 / 6 ≤ Real.cos (2 * Real.pi * t / H) :=
      cos_abs_ge_five_six habs
    unfold bump
    have hsub : 0 ≤ Real.cos (2 * π * t / H) - 1/2 := by linarith [hge]
    rw [max_eq_right hsub]
    linarith
  rw [hintconst] at hmid
  linarith

theorem J_pos : 0 < J := lt_of_lt_of_le (by norm_num) J_lower_bound

/-! ### Amplitude and curvature -/

/-- The bump amplitude, normalising the total turn of `κ` to `π`. -/
noncomputable def A : ℝ := (Real.pi - kmin * H) / J

theorem A_mul_J : A * J = Real.pi - kmin * H := by
  unfold A
  have hJ := J_pos.ne'
  field_simp

theorem A_pos : 0 < A := by
  unfold A
  refine div_pos ?_ J_pos
  rw [kmin_H]
  linarith [pi_lb]

theorem A_le_kap_sub_kmin : A ≤ kap - kmin := by
  unfold A
  rw [kmin_H, div_le_iff₀ J_pos]
  have h1 : (kap - kmin) * (64/9) ≤ (kap - kmin) * J :=
    mul_le_mul_of_nonneg_left J_lower_bound kap_sub_kmin_pos.le
  have h2 : Real.pi - 1/16 ≤ (kap - kmin) * (64/9) := by
    unfold kap kmin
    nlinarith [pi_ub]
  linarith

/-- The model curvature: baseline plus bump. -/
noncomputable def K (s : ℝ) : ℝ := kmin + A * bump s

theorem K_continuous : Continuous K := by
  unfold K
  exact continuous_const.add (continuous_const.mul continuous_bump)

theorem K_periodic : Function.Periodic K H := by
  intro s
  unfold K
  rw [periodic_bump s]

theorem K_ge (s : ℝ) : kmin ≤ K s := by
  unfold K
  exact le_add_of_nonneg_right (mul_nonneg A_pos.le (bump_nonneg s))

theorem K_nonneg (s : ℝ) : 0 ≤ K s := le_trans (le_of_lt hkmpos) (K_ge s)

theorem K_le (s : ℝ) : K s ≤ kap := by
  have hb : bump s ≤ 1 := bump_le_one s
  have h1 : A * bump s ≤ A * 1 := mul_le_mul_of_nonneg_left hb A_pos.le
  unfold K
  have hA : A ≤ kap - kmin := A_le_kap_sub_kmin
  linarith

theorem K_integral : (∫ r in (0:ℝ)..H, K r) = Real.pi := by
  have hc1 : (∫ r in (0:ℝ)..H, kmin) = kmin * H := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  have hJdef : (∫ r in (0:ℝ)..H, bump r) = J := rfl
  have hspl : (∫ r in (0:ℝ)..H, K r)
      = (∫ r in (0:ℝ)..H, kmin) + ∫ r in (0:ℝ)..H, A * bump r := by
    simp only [K]
    exact intervalIntegral.integral_add
      (continuous_const.intervalIntegrable 0 H)
      ((continuous_const.mul continuous_bump).intervalIntegrable 0 H)
  rw [hspl, hc1, intervalIntegral.integral_const_mul, hJdef, A_mul_J]
  ring

theorem K_eq_kmin {s : ℝ} (hsL : -(H / 2) ≤ s) (hsR : s ≤ H / 2) (hfar : H / 6 ≤ |s|) :
    K s = kmin := by
  unfold K
  rw [bump_eq_zero hsL hsR hfar]
  ring

/-! ### The tangent angle on the centred cell -/

/-- The origin of the tangent angle, chosen so that `Θ(-H/2) = 0`. -/
noncomputable def theta0 : ℝ := ∫ s in (-(H/2))..(0:ℝ), K s

/-- Constant family of curvatures. -/
noncomputable def kappaFam : ℕ → ℝ → ℝ := fun _ => K

/-- Constant family of separations. -/
def HFam : ℕ → ℝ := fun _ => H

/-- Constant family of base angles. -/
noncomputable def thetaFam : ℕ → ℝ := fun _ => theta0

theorem Theta_eq_integral (s : ℝ) (_hs : -(H/2) ≤ s) :
    frontAngle K theta0 s = ∫ u in (-(H/2))..s, K u := by
  have hdef : frontAngle K theta0 s = theta0 + ∫ r in (0:ℝ)..s, K r := by rfl
  rw [hdef]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (K_continuous.intervalIntegrable (-(H/2)) 0)
    (K_continuous.intervalIntegrable 0 s)]
  rfl

theorem Theta_left_zero : frontAngle K theta0 (-(H/2)) = 0 := by
  rw [Theta_eq_integral (-(H/2)) (le_refl _)]
  exact intervalIntegral.integral_same

theorem Theta_right_pi : frontAngle K theta0 (H / 2) = Real.pi := by
  rw [Theta_eq_integral (H/2) (by linarith [hHpos]), integral_window K_periodic]
  exact K_integral

theorem turn_two_pi (s : ℝ) :
    frontAngle K theta0 (s + 2*H) = frontAngle K theta0 s + 2 * Real.pi := by
  rw [show (s:ℝ) + 2*H = (s + H) + H from by ring,
    frontAngle_add_halfPeriod K_continuous K_periodic K_integral,
    frontAngle_add_halfPeriod K_continuous K_periodic K_integral]
  ring

theorem sin_nonneg_cell (s : ℝ) (hs : s ∈ Icc (-(H/2)) (H/2)) :
    0 ≤ Real.sin (frontAngle K theta0 s) := by
  rcases mem_Icc.mp hs with ⟨hsL, hsR⟩
  have hΘ := Theta_eq_integral s hsL
  have hge : 0 ≤ frontAngle K theta0 s := by
    rw [hΘ]
    exact intervalIntegral.integral_nonneg (by linarith) (fun u _ => K_nonneg u)
  have hle : frontAngle K theta0 s ≤ Real.pi := by
    rw [hΘ]
    have hsplit : (∫ u in (-(H/2))..s, K u) + ∫ u in s..(H/2), K u
        = ∫ u in (-(H/2))..(H/2), K u :=
      intervalIntegral.integral_add_adjacent_intervals
        (K_continuous.intervalIntegrable (-(H/2)) s)
        (K_continuous.intervalIntegrable s (H/2))
    have hpart : 0 ≤ ∫ u in s..(H/2), K u :=
      intervalIntegral.integral_nonneg (by linarith) (fun u _ => K_nonneg u)
    have hw : (∫ u in (-(H/2))..(H/2), K u) = ∫ u in (0:ℝ)..H, K u :=
      integral_window K_periodic
    rw [hw, K_integral] at hsplit
    linarith
  exact Real.sin_nonneg_of_nonneg_of_le_pi hge hle

/-- On the flat left shoulder the angle is the baseline drift. -/
theorem Theta_flat_left {t : ℝ} (h1 : -(H/2) ≤ t) (h2 : t ≤ -(H/6)) :
    frontAngle K theta0 t = kmin * (t + H/2) := by
  rw [Theta_eq_integral t h1]
  have hcongr : (∫ u in (-(H/2))..t, K u) = ∫ u in (-(H/2))..t, kmin := by
    refine intervalIntegral.integral_congr ?_
    intro u hu
    rcases mem_Icc.mp (uIcc_mem (by linarith) hu) with ⟨hu1, hu2⟩
    refine K_eq_kmin hu1 (by linarith) ?_
    rw [abs_of_nonpos (by linarith : (u:ℝ) ≤ 0)]
    linarith
  rw [hcongr, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- On the flat right shoulder the angle misses `π` by the baseline drift. -/
theorem Theta_flat_right {t : ℝ} (h1 : H/6 ≤ t) (h2 : t ≤ H/2) :
    Real.pi - frontAngle K theta0 t = kmin * (H/2 - t) := by
  have hΘt := Theta_eq_integral t (by linarith [hHpos])
  have hΘend := Theta_eq_integral (H/2) (by linarith [hHpos])
  have hb1 : IntervalIntegrable K volume (-(H/2)) t :=
    K_continuous.intervalIntegrable _ _
  have hb2 : IntervalIntegrable K volume t (H/2) :=
    K_continuous.intervalIntegrable _ _
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hb1 hb2
  have hcongr : (∫ u in t..(H/2), K u) = ∫ u in t..(H/2), kmin := by
    refine intervalIntegral.integral_congr ?_
    intro u hu
    rcases mem_Icc.mp (uIcc_mem (by linarith [hHpos]) hu) with ⟨hu1, hu2⟩
    refine K_eq_kmin (by linarith [hHpos]) hu2 ?_
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u)]
    linarith
  have hc : (∫ u in t..(H/2), kmin) = kmin * (H/2 - t) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [hcongr, hc] at hsplit
  rw [← hΘend, Theta_right_pi] at hsplit
  rw [hΘt]
  linarith

/-- Model tangent angle, abstracted so downstream statements never unfold
its construction. -/
noncomputable def modelAngle : ℝ → ℝ := frontAngle K theta0

theorem continuous_modelAngle : Continuous modelAngle :=
  continuous_tangentAngle K_continuous

theorem modelAngle_eq_integral {s : ℝ} (hs : -(H/2) ≤ s) :
    modelAngle s = ∫ u in (-(H/2))..s, K u := Theta_eq_integral s hs

theorem sin_modelAngle_integrable (a b : ℝ) :
    IntervalIntegrable (fun t => Real.sin (modelAngle t)) volume a b :=
  (Real.continuous_sin.comp continuous_modelAngle).intervalIntegrable a b

/-! ### The width estimate -/

/-- Pointwise bound on the left flat shoulder. -/
theorem pt_left (t : ℝ) (h1 : -(H/2) ≤ t) (h2 : t ≤ -(H/6)) :
    Real.sin (modelAngle t) ≤ 1/48 := by
  have hΘeq : modelAngle t = kmin * (t + H/2) := Theta_flat_left h1 h2
  have hΘge : 0 ≤ modelAngle t := by
    rw [hΘeq]; exact mul_nonneg hkmpos.le (by linarith)
  have hΘub : modelAngle t ≤ 1/48 := by
    rw [hΘeq]
    have hbound : kmin * (t + H/2) ≤ kmin * (H/3) :=
      mul_le_mul_of_nonneg_left (by linarith [h2, hHpos]) hkmpos.le
    have hv : kmin * (H/3) = 1/48 := by unfold kmin H; norm_num
    linarith
  exact le_trans (sin_le_self_aux hΘge (by linarith [pi_lb])) hΘub

/-- Pointwise bound on the right flat shoulder. -/
theorem pt_right (t : ℝ) (h1 : H/6 ≤ t) (h2 : t ≤ H/2) :
    Real.sin (modelAngle t) ≤ 1/48 := by
  have hsub : Real.pi - modelAngle t = kmin * (H/2 - t) := Theta_flat_right h1 h2
  have hge : 0 ≤ Real.pi - modelAngle t := by
    rw [hsub]; exact mul_nonneg hkmpos.le (by linarith)
  have hle : Real.pi - modelAngle t ≤ 1/48 := by
    rw [hsub]
    have hbound : kmin * (H/2 - t) ≤ kmin * (H/3) :=
      mul_le_mul_of_nonneg_left (by linarith [h1, hHpos]) hkmpos.le
    have hv : kmin * (H/3) = 1/48 := by unfold kmin H; norm_num
    linarith
  calc Real.sin (modelAngle t)
      = Real.sin (Real.pi - modelAngle t) := (Real.sin_pi_sub (modelAngle t)).symm
    _ ≤ Real.pi - modelAngle t := sin_le_self_aux hge (by linarith [pi_lb])
    _ ≤ 1 / 48 := hle

set_option maxHeartbeats 8000000 in
/-- **The transverse width of the first model is at most `200/9`.** -/
theorem width_le :
    (∫ t in (-(H/2))..(H/2), Real.sin (modelAngle t)) ≤ 200 / 9 := by
  have hab1 : (-(H/2) : ℝ) ≤ -(H/6) := by linarith [hHpos]
  have hab2 : (-(H/6) : ℝ) ≤ H/6 := by linarith
  have hab3 : (H/6 : ℝ) ≤ H/2 := by linarith
  have hIL := sin_modelAngle_integrable (-(H/2)) (-(H/6))
  have hIM := sin_modelAngle_integrable (-(H/6)) (H/6)
  have hIR := sin_modelAngle_integrable (H/6) (H/2)
  have e1 : (∫ t in (-(H/2))..(-(H/6)), Real.sin (modelAngle t))
      + ∫ t in (-(H/6))..(H/2), Real.sin (modelAngle t)
      = ∫ t in (-(H/2))..(H/2), Real.sin (modelAngle t) :=
    intervalIntegral.integral_add_adjacent_intervals hIL (sin_modelAngle_integrable _ _)
  have e2 : (∫ t in (-(H/6))..(H/6), Real.sin (modelAngle t))
      + ∫ t in (H/6)..(H/2), Real.sin (modelAngle t)
      = ∫ t in (-(H/6))..(H/2), Real.sin (modelAngle t) :=
    intervalIntegral.integral_add_adjacent_intervals hIM hIR
  have hL : (∫ t in (-(H/2))..(-(H/6)), Real.sin (modelAngle t)) ≤ 4/9 := by
    have hconst : IntervalIntegrable (fun _ : ℝ => (1/48:ℝ)) volume (-(H/2)) (-(H/6)) :=
      continuous_const.intervalIntegrable _ _
    have hm : (∫ t in (-(H/2))..(-(H/6)), Real.sin (modelAngle t))
        ≤ (∫ t in (-(H/2))..(-(H/6)), (1/48:ℝ)) :=
      intervalIntegral.integral_mono_on hab1 hIL hconst
        (fun t ht => by rcases mem_Icc.mp ht with ⟨ht1, ht2⟩; exact pt_left t ht1 ht2)
    have hv : (∫ t in (-(H/2))..(-(H/6)), (1/48:ℝ)) = 4/9 := by
      rw [intervalIntegral.integral_const]; unfold H; norm_num
    rw [hv] at hm; exact hm
  have hM : (∫ t in (-(H/6))..(H/6), Real.sin (modelAngle t)) ≤ 64/3 := by
    have hconst : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume (-(H/6)) (H/6) :=
      continuous_const.intervalIntegrable _ _
    have hm : (∫ t in (-(H/6))..(H/6), Real.sin (modelAngle t))
        ≤ (∫ t in (-(H/6))..(H/6), (1:ℝ)) :=
      intervalIntegral.integral_mono_on hab2 hIM hconst (fun _ _ => Real.sin_le_one _)
    have hv : (∫ t in (-(H/6))..(H/6), (1:ℝ)) = 64/3 := by
      rw [intervalIntegral.integral_const]; unfold H; norm_num
    rw [hv] at hm; exact hm
  have hR : (∫ t in (H/6)..(H/2), Real.sin (modelAngle t)) ≤ 4/9 := by
    have hconst : IntervalIntegrable (fun _ : ℝ => (1/48:ℝ)) volume (H/6) (H/2) :=
      continuous_const.intervalIntegrable _ _
    have hm : (∫ t in (H/6)..(H/2), Real.sin (modelAngle t))
        ≤ (∫ t in (H/6)..(H/2), (1/48:ℝ)) :=
      intervalIntegral.integral_mono_on hab3 hIR hconst
        (fun t ht => by rcases mem_Icc.mp ht with ⟨ht1, ht2⟩; exact pt_right t ht1 ht2)
    have hv : (∫ t in (H/6)..(H/2), (1/48:ℝ)) = 4/9 := by
      rw [intervalIntegral.integral_const]; unfold H; norm_num
    rw [hv] at hm; exact hm
  linarith

/-! ### The chord-arc bound -/

theorem chordConst_pos' : 0 < ConvexChordArc.chordConst kmin kap (2 * H) :=
  ConvexChordArc.chordConst_pos hkmpos hkle (by norm_num [H])

/-- The uniform chord-arc bound for the front, from `ConvexChordArc`. -/
theorem chord_bound (x y : ℝ) :
    ConvexChordArc.chordConst kmin kap (2 * H) * min |x - y| (2 * H - |x - y|)
      ≤ ‖front K theta0 H x - front K theta0 H y‖ := by
  have hX : ∀ s, HasDerivAt (front K theta0 H)
      (Complex.exp ((frontAngle K theta0 s : ℂ) * Complex.I)) s := by
    intro s
    have h := front_hasDerivAt K_continuous (theta0 := theta0) (H := H) s
    have hz : (Complex.I : ℂ) * (frontAngle K theta0 s : ℂ)
        = (frontAngle K theta0 s : ℂ) * Complex.I := mul_comm _ _
    rw [hz] at h
    exact h
  exact chord_arc_of_convex (by norm_num [H]) hX
    (fun s => hasDerivAt_tangentAngle (θ₀ := theta0) K_continuous s)
    K_ge K_le hkmpos (front_periodic K_continuous K_periodic K_integral)
    turn_two_pi x y

/-! ### Numerical slack and the assembly -/

/-- The uniform chord-arc hypothesis of the closing step for the constant
family: the normalizing ratio cancels, leaving exactly `chord_bound`. -/
theorem chord_hyp {κ : ℝ → ℝ} {θ₀ H₀ Hn : ℝ}
    (hκ : κ = K) (hθ : θ₀ = theta0) (hH₀ : H₀ = H) (hHn : Hn = H) (x y : ℝ) :
    ConvexChordArc.chordConst kmin kap (2 * H) * (2 * H₀) / (2 * Hn)
        * min |x - y| (2 * Hn - |x - y|)
      ≤ ‖front κ θ₀ Hn x - front κ θ₀ Hn y‖ := by
  subst hκ; subst hθ; subst hH₀; subst hHn
  have h2H : (2:ℝ)*H ≠ 0 := by norm_num [H]
  calc ConvexChordArc.chordConst kmin kap (2*H) * (2*H) / (2*H)
        * min |x - y| (2*H - |x - y|)
      = ConvexChordArc.chordConst kmin kap (2*H)
          * ((2*H) / (2*H)) * min |x - y| (2*H - |x - y|) := by
        rw [mul_div_assoc]
  _ = ConvexChordArc.chordConst kmin kap (2*H)
          * min |x - y| (2*H - |x - y|) := by
        rw [div_self h2H, mul_one]
  _ ≤ ‖front K theta0 H x - front K theta0 H y‖ := chord_bound x y

/-- The closing width gap holds whenever the shadowing tail is at most `7`. -/
theorem gap_slack {t : ℝ} (ht : t ≤ 7) :
    (200:ℝ)/9 + 2 * t < (2 * H - t) / Real.pi := by
  rw [lt_div_iff₀ (by positivity)]
  have e : (200/9 + 2*t) * Real.pi = (200/9) * Real.pi + 2 * (t * Real.pi) := by
    ring
  have b1 : (200:ℝ)/9 * Real.pi ≤ (200/9) * 3.15 :=
    mul_le_mul_of_nonneg_left pi_ub.le (by norm_num : (0:ℝ) ≤ 200 / 9)
  have b2 : t * Real.pi ≤ 7 * 3.15 := by
    rcases le_or_gt 0 t with ht0 | ht0
    · calc t * Real.pi ≤ t * 3.15 := mul_le_mul_of_nonneg_left pi_ub.le ht0
        _ ≤ 7 * 3.15 := mul_le_mul_of_nonneg_right ht (by norm_num : (0:ℝ) ≤ 3.15)
    · have htpos : (0:ℝ) < Real.pi := Real.pi_pos
      have h1 : (0:ℝ) < -t := by linarith
      have hneg : t * Real.pi ≤ 0 := by
        nlinarith [h1, htpos]
      linarith
  have hfin : (121:ℝ) ≤ 2 * H - t := by unfold H; linarith
  have hnum : ((200:ℝ)/9)*3.15 + 2*(7*3.15) < 121 := by norm_num
  rw [e]
  nlinarith [b1, b2, hfin, hnum]

/-- **The geometric block of `main_theorem_of_model_transverse` is satisfiable.**
An explicit constant family of capsule fronts satisfies every hypothesis that
the closing argument asks of the geometry; only the dynamical input remains. -/
theorem exists_admissible_geometry :
    ∃ (kappas : ℕ → ℝ → ℝ) (Hs theta0 : ℕ → ℝ) (kmin kap dlt Cw : ℝ),
      0 < kmin ∧ 0 < dlt ∧ (∀ n, 0 < Hs n) ∧ (∀ n, Hs 0 ≤ Hs n) ∧
      (∀ n, Continuous (kappas n)) ∧ (∀ n, Function.Periodic (kappas n) (Hs n)) ∧
      (∀ n s, kmin ≤ kappas n s) ∧ (∀ n s, kappas n s ≤ kap) ∧
      (∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi) ∧
      (∀ n, ∀ x ∈ Icc (0:ℝ) (2 * Hs n), ∀ y ∈ Icc (0:ℝ) (2 * Hs n),
        dlt * (2 * Hs 0) / (2 * Hs n) * min |x - y| (2 * Hs n - |x - y|)
          ≤ ‖front (kappas n) (theta0 n) (Hs n) x
              - front (kappas n) (theta0 n) (Hs n) y‖) ∧
      (∀ s ∈ Icc (-(Hs 0 / 2)) (Hs 0 / 2),
        0 ≤ Real.sin (frontAngle (kappas 0) (theta0 0) s)) ∧
      ((∫ t in (-(Hs 0 / 2))..(Hs 0 / 2),
          Real.sin (frontAngle (kappas 0) (theta0 0) t)) ≤ Cw) ∧
      (Cw + 14 < (2 * Hs 0 - 7) / Real.pi) := by
  refine ⟨kappaFam, HFam, thetaFam, kmin, kap,
    ConvexChordArc.chordConst kmin kap (2 * H), 200 / 9,
    hkmpos, chordConst_pos', fun _ => hHpos, fun _ => le_rfl,
    fun _ => K_continuous, fun _ => K_periodic,
    fun _ s => K_ge s, fun _ s => K_le s, fun _ => K_integral, ?_, ?_, width_le,
    (by
      have hg := gap_slack (t := 7) (le_refl 7)
      rw [show HFam 0 = H from rfl]
      norm_num at hg ⊢
      exact hg)⟩
  · intro n x hx y hy
    exact chord_hyp rfl rfl rfl rfl x y
  · intro s hs
    exact sin_nonneg_cell s hs

/-- **With the geometry made explicit, the paper's closing step needs only
dynamics.**  Feeding the explicit admissible family into
`main_theorem_of_model_transverse`, every remaining hypothesis is dynamical:
a non-expansive selected inverse `B` with a left inverse realizing the
unit-tangent transform up to reparametrization, and a summable defect estimate
of the model fronts against their inverses. -/
theorem main_theorem_from_dynamics
    {Csh : ℝ} (hCsh : 1 ≤ Csh)
    {B T : tube (2*H) kmin (chordConst kmin kap (2*H) * (2*H))
        → tube (2*H) kmin (chordConst kmin kap (2*H) * (2*H))}
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y) (hBcont : Continuous B)
    (hT : ∀ x, T (B x) = x)
    (hTev : ∀ m : tube (2*H) kmin (chordConst kmin kap (2*H) * (2*H)),
      range (ev ((T m : Data))) = range (UnitTangent.unitTangentMap (ev ((m : Data)))))
    {e : ℕ → ℝ} (hsum : Summable e)
    (hdef : ∀ (n : ℕ) (p q : tube (2*H) kmin (chordConst kmin kap (2*H) * (2*H))),
      ev ((p : Data)) = front K theta0 H → ev ((q : Data)) = front K theta0 H →
        dist p (B q) ≤ e n)
    (hgap : 200/9 + 2 * (Csh * ShadowingTails.tail e 0)
      < (2 * H - Csh * ShadowingTails.tail e 0) / Real.pi) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, range (X (n + 1)) = range (UnitTangent.unitTangentMap (X n))) ∧
      0 < LX ∧ Function.Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  refine MarkedSpace.main_theorem_of_model_transverse (kappas := fun _ => K)
    (Hs := fun _ => H) (theta0 := fun _ => theta0) (kmin := kmin) (kap := kap)
    (dlt := ConvexChordArc.chordConst kmin kap (2 * H)) (e := e) (Cw := 200/9)
    (Csh := Csh) (B := B) (T := T)
    hkmpos chordConst_pos' (fun _ => hHpos) (fun _ => le_rfl)
    (fun _ => K_continuous) (fun _ => K_periodic) (fun _ s => K_ge s)
    (fun _ s => K_le s) (fun _ => K_integral) ?_ hB hBcont hT hTev hsum
    (fun n p q hp hq => hdef n p q hp hq) hCsh ?_ width_le hgap
  · intro _ x _ y _
    exact chord_hyp rfl rfl rfl rfl x y
  · intro s hs
    exact sin_nonneg_cell s hs

end AdmissibleFrontFamily
