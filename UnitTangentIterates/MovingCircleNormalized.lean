import Mathlib
import UnitTangentIterates.MovingCircleSlices
import UnitTangentIterates.RearOwnPathDistNormalized

/-!
# The moving circle meets the normalized form of the path-distance assembly

`RearOwnPathDistNormalized.pathDist_le_of_front_normalized` is the path-distance
bound for the selected rears in which the curvature and the steering angle are
given in the normalized parameter `σ = s / P(t)`, so that no hypothesis forces
`P'(t) ∂_sK = 0`.  This file checks that the family of circles of radius
`1 / sin A(t)` — whose front period `P(t) = 2π / sin A(t)` moves and whose rear
arclength period passes from `2π` to `2π√3` — satisfies its hypotheses, so that
form is not vacuous.

The normalized data of that family are the constant slices `δ̂(t, σ) = A(t)`,
`K̂(t, σ) = sin A(t)`, and the two derivatives of the period
`P'(t) = −2π A'(t) cos A(t) / sin²A(t)` are computed and bounded here.

Main result: `movingCircle_instance_normalized`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath RearTrack
  RearFamilyFrame RearOwnArclength RearOwnMotion MovingCircleProfile MovingCircle
  MovingCirclePath MovingCirclePathDist MovingCircleTangential MovingCircleGeometric

namespace MovingCircleNormalized

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistFrontOnly
  RearOwnPathDistIntrinsic RearOwnPathDistSlices RearOwnPathDistNormalized
  RearOwnHigherRegularity MovingCircleFrontOnly MovingCircleCurvature MovingCircleSlices
  SecondOrderBounds

/-! ### The two derivatives of the front period -/

/-- The derivative of the front period `P(t) = 2π / sin A(t)`. -/
def Ppd (t : ℝ) : ℝ := -(2 * Real.pi) * sAd t / sA t ^ 2

/-- Its own derivative. -/
def Ppdd (t : ℝ) : ℝ := -(2 * Real.pi) * (sAdd t * sA t - 2 * sAd t ^ 2) / sA t ^ 3

theorem hasDerivAt_Pp (t : ℝ) : HasDerivAt Pp (Ppd t) t := by
  have h := (hasDerivAt_const t (2 * Real.pi)).div (hasDerivAt_sAd t) (sA_ne t)
  have hfun : Pp = fun x => 2 * Real.pi / sA x := rfl
  have hne : sA t ≠ 0 := sA_ne t
  rw [hfun]
  convert h using 1
  rw [Ppd]
  field_simp
  ring

theorem hasDerivAt_Ppd (t : ℝ) : HasDerivAt Ppd (Ppdd t) t := by
  have hu : HasDerivAt (fun x => -(2 * Real.pi) * sAd x) (-(2 * Real.pi) * sAdd t) t :=
    (hasDerivAt_sAdd t).const_mul _
  have hv : HasDerivAt (fun x => sA x ^ 2) (2 * sA t * sAd t) t := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using (hasDerivAt_sAd t).pow 2
  have hne : sA t ^ 2 ≠ 0 := pow_ne_zero _ (sA_ne t)
  have h := hu.div hv hne
  have hfun : Ppd = fun x => -(2 * Real.pi) * sAd x / sA x ^ 2 := rfl
  rw [hfun]
  convert h using 1
  rw [Ppdd]
  have hsne : sA t ≠ 0 := sA_ne t
  field_simp
  ring

theorem contDiff_Pp (n : ℕ) : ContDiff ℝ n Pp := by
  have h : ContDiff ℝ (n : ℕ) sA := contDiff_sA.of_le (by exact ENat.LEInfty.out)
  have : ContDiff ℝ (n : ℕ) (fun t => 2 * Real.pi / sA t) :=
    contDiff_const.div h (fun t => sA_ne t)
  simpa [Pp] using this

theorem contDiff_Ppd (n : ℕ) : ContDiff ℝ n Ppd := by
  have hA : ContDiff ℝ (n : ℕ) sA := contDiff_sA.of_le (by exact ENat.LEInfty.out)
  have hAd : ContDiff ℝ (n : ℕ) sAd := contDiff_sAd.of_le (by exact ENat.LEInfty.out)
  exact (contDiff_const.mul hAd).div (hA.pow 2) (fun t => pow_ne_zero _ (sA_ne t))

theorem abs_Ppd_le {Md : ℝ} (hMd : ∀ t, |sAd t| ≤ Md) (t : ℝ) :
    |Ppd t| ≤ 8 * Real.pi * Md := by
  have hpi := Real.pi_pos
  have hs := sA_ge t
  have hsq : (1 : ℝ) / 4 ≤ sA t ^ 2 := by nlinarith [sA_pos t]
  have hpos : (0 : ℝ) < sA t ^ 2 := by positivity
  have hMd0 : 0 ≤ Md := le_trans (abs_nonneg _) (hMd t)
  rw [Ppd, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have habs : |-(2 * Real.pi) * sAd t| = 2 * Real.pi * |sAd t| := by
    rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  rw [habs]
  calc 2 * Real.pi * |sAd t| ≤ 2 * Real.pi * Md :=
        mul_le_mul_of_nonneg_left (hMd t) (by positivity)
    _ = 8 * Real.pi * Md * (1 / 4) := by ring
    _ ≤ 8 * Real.pi * Md * sA t ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)

theorem abs_Ppdd_le {Md CKb : ℝ} (hMd : ∀ t, |sAd t| ≤ Md) (hCK : ∀ t, |sAdd t| ≤ CKb)
    (t : ℝ) : |Ppdd t| ≤ 16 * Real.pi * (CKb + 2 * Md ^ 2) := by
  have hpi := Real.pi_pos
  have hs := sA_ge t
  have hsle : sA t ≤ 1 := le_trans (sA_le t) (Real.sin_le_one _)
  have hcube : (1 : ℝ) / 8 ≤ sA t ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 2) hs 3
    norm_num at h
    linarith
  have hpos : (0 : ℝ) < sA t ^ 3 := by positivity
  have hMd0 : 0 ≤ Md := le_trans (abs_nonneg _) (hMd t)
  have hCK0 : 0 ≤ CKb := le_trans (abs_nonneg _) (hCK t)
  rw [Ppdd, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have hnum : |sAdd t * sA t - 2 * sAd t ^ 2| ≤ CKb + 2 * Md ^ 2 := by
    have h1 : |sAdd t * sA t| ≤ CKb := by
      rw [abs_mul, abs_of_pos (sA_pos t)]
      nlinarith [hCK t, abs_nonneg (sAdd t), sA_pos t]
    have h2 : |2 * sAd t ^ 2| ≤ 2 * Md ^ 2 := by
      have : sAd t ^ 2 ≤ Md ^ 2 := by
        nlinarith [hMd t, abs_nonneg (sAd t), sq_abs (sAd t)]
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * sAd t ^ 2)]
      linarith
    have hsplit : |sAdd t * sA t - 2 * sAd t ^ 2| ≤ |sAdd t * sA t| + |2 * sAd t ^ 2| := by
      have h := abs_add_le (sAdd t * sA t) (-(2 * sAd t ^ 2))
      rw [abs_neg] at h
      simpa [sub_eq_add_neg] using h
    calc |sAdd t * sA t - 2 * sAd t ^ 2| ≤ |sAdd t * sA t| + |2 * sAd t ^ 2| := hsplit
      _ ≤ CKb + 2 * Md ^ 2 := add_le_add h1 h2
  have habs : |-(2 * Real.pi) * (sAdd t * sA t - 2 * sAd t ^ 2)|
      = 2 * Real.pi * |sAdd t * sA t - 2 * sAd t ^ 2| := by
    rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  rw [habs]
  calc 2 * Real.pi * |sAdd t * sA t - 2 * sAd t ^ 2|
      ≤ 2 * Real.pi * (CKb + 2 * Md ^ 2) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = 16 * Real.pi * (CKb + 2 * Md ^ 2) * (1 / 8) := by ring
    _ ≤ 16 * Real.pi * (CKb + 2 * Md ^ 2) * sA t ^ 3 :=
        mul_le_mul_of_nonneg_left hcube (by positivity)

/-! ### The instance -/

/-- **The hypotheses of the normalized form of the assembly are met by a family
whose period moves.**  The circles of radius `1 / sin A(t)` have the normalized
data `δ̂(t, σ) = A(t)` and `K̂(t, σ) = sin A(t)`, both `1`-periodic in `σ`, and the
moving front period `P(t) = 2π / sin A(t)`; the sup bound `E` of the front normal
velocity is produced by the statement, together with the path-distance bound it
enters. -/
theorem movingCircle_instance_normalized :
    ∃ E : ℝ, 0 ≤ E ∧
      (∀ t s, |frontNormalVelocityAt (partialTime Ff) Th de t s| ≤ E) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        rearArclength (de 0) (Pp 0) = 2 * Real.pi ∧
        rearArclength (de 1) (Pp 1) = 2 * Real.pi * Real.sqrt 3 ∧
        (∀ u, Phi 0 u = 2 * Real.pi * u) ∧
        (∀ u, rearData0.1 u = rearOwn Ff Th de sff 0 (2 * Real.pi * u)) ∧
        ∀ q' : Data, (∀ u, q'.1 u = rearOwn Ff Th de sff 1 (Phi 1 u)) →
          pathDist rearData0 q' ≤
            gaugeJacobiConst (2 * Real.pi) (4 * Real.pi) (Real.sin (Real.pi / 4))
              (E / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2)
                * (Real.sin (Real.pi / 4) / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2)))
              ((E / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2)
                    + E / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2))
                  * (Real.sin (Real.pi / 4) / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2))
                + E / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2) * (2 * Real.sin (Real.pi / 4)
                  / Real.sqrt (1 - Real.sin (Real.pi / 4) ^ 2) ^ 3)) 1
              (2 * Real.pi) * cost movingPath := by
  have hpi := Real.pi_pos
  have harcsin : Real.arcsin (Real.sin (Real.pi / 4)) = Real.pi / 4 :=
    Real.arcsin_sin (by linarith) (by linarith)
  have hsin4 : Real.sin (Real.pi / 4) < 1 := by
    rw [Real.sin_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hsin4pos : 0 ≤ Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four]; positivity
  obtain ⟨Md, hMd0, hMd⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |sAd t| ≤ M :=
    exists_bound_of_vanishing_outside (a := 0) (b := 1)
      (contDiff_sAd.continuous) (fun x hx => sAd_eq_zero_outside hx)
  obtain ⟨CKb, hCK0, hCK⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |sAdd t| ≤ M :=
    exists_bound_of_vanishing_outside (a := 0) (b := 1)
      (contDiff_sAdd.continuous) (fun x hx => sAdd_eq_zero_outside hx)
  obtain ⟨E, hE0, hEF, Phi, hPhi0, -, hPhi⟩ := pathDist_le_of_front_normalized
    (P0 := 2 * Real.pi) (P1 := 4 * Real.pi) (kh := Real.sin (Real.pi / 4))
    (P := Pp) (Pd := Ppd) (F := Ff) (Θ := Th) (δ := de) (K := Kk)
    (dn := de) (Kn := Kk) (Kdn := fun t _ => sAd t) (sf := sff)
    (Md := Md) (MP := 8 * Real.pi * Md) (Klip := Md) (Plip := 8 * Real.pi * Md)
    (CK := CKb) (CP := 16 * Real.pi * (CKb + 2 * Md ^ 2))
    movingPath rearData0
    (by positivity) hsin4pos hsin4
    (fun t => by
      rw [Pp, le_div_iff₀ (sA_pos t)]
      nlinarith [sA_le t, Real.sin_le_one (prof t), sA_pos t])
    (fun t => by
      rw [Pp, div_le_iff₀ (sA_pos t)]
      nlinarith [sA_ge t])
    (fun t s => rfl) (fun t s => rfl)
    (fun t σ => by
      have hz : Pp t * (Kk t σ - Real.sin (de t σ)) = 0 := by
        simp [Kk, de, sA]
      rw [hz]
      exact hasDerivAt_const σ (prof t))
    (fun t σ => ⟨(prof_pos t).le, by rw [harcsin]; exact prof_le t⟩)
    (fun t s => rfl) (fun t s => rfl) (fun t s => rfl)
    (fun t σ => by
      rw [Kk, abs_of_pos (sA_pos t)]
      exact sA_le t)
    (fun t σ => hMd t)
    (abs_Ppd_le hMd)
    (fun a b σ => by
      simpa [Kk] using abs_sub_le_of_deriv_bound hasDerivAt_sAd hMd a b)
    (fun a b => abs_sub_le_of_deriv_bound hasDerivAt_Pp (abs_Ppd_le hMd) a b)
    (fun a b σ => by
      simpa [Kk] using abs_taylor_quadratic hasDerivAt_sAd hasDerivAt_sAdd hCK a b)
    (fun a b => abs_taylor_quadratic hasDerivAt_Pp hasDerivAt_Ppd (abs_Ppdd_le hMd hCK) a b)
    hCK0 (by positivity)
    (contDiff_Pp 4) (contDiff_Ppd 3)
    (by
      have h : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) sA := contDiff_sA.of_le (by exact ENat.LEInfty.out)
      simpa [Kk, uncurry] using h.comp contDiff_fst)
    (by
      have h : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) sAd :=
        contDiff_sAd.of_le (by exact ENat.LEInfty.out)
      simpa [uncurry] using h.comp contDiff_fst)
    hasDerivAt_Ff_space hasDerivAt_Th_space
    Ff_periodic Th_periodic
    (contDiff_uncurry_Ff.of_le (by exact ENat.LEInfty.out))
    (contDiff_uncurry_Th.of_le (by exact ENat.LEInfty.out))
    sff_inv
    movingPath_X_eq movingPath_nu_eq
    (fun u => rearData0_apply u)
  refine ⟨E, hE0, hEF, Phi, rearPeriod_zero, rearPeriod_one, ?_, fun u => rfl, ?_⟩
  · intro u
    have h := hPhi0 u
    rwa [rearPeriod_zero] at h
  · intro q' hq'
    have h := hPhi q' hq'
    rwa [rearPeriod_zero] at h

end MovingCircleNormalized
