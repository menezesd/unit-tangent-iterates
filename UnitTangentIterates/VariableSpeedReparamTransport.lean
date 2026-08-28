import Mathlib
import UnitTangentIterates.C2NormalPathJunctionAdapter
import UnitTangentIterates.NormalPathC2IncrementVariableSpeed

noncomputable section

open Set Function MarkedSpace

namespace PathMetric

open NormalPathC2IncrementVariableSpeed

/-- Variable-speed geometry transported through a fixed controlled spatial
reparameterization.  No third derivative of `phi` is needed. -/
theorem isVariableSpeedNormalPath_reparamAtJunction
    {p q p' q' : Data} {Gamma : NormalPath p q}
    (hC2 : C2NormalPathData Gamma) (J : ReparamJunctionCertificate
      (p' := p') (q' := q') Gamma)
    {P0 P1 khat G1 Cg : ℝ}
    (hvar : IsVariableSpeedNormalPath P0 P1 khat G1 Cg Gamma)
    (hP0 : 0 < P0) (hP1 : 0 ≤ P1) (hkhat : 0 ≤ khat)
    (hG1 : 0 ≤ G1) (hCg : 0 ≤ Cg) (hM : 0 ≤ J.M) (hN : 0 ≤ J.N) :
    IsVariableSpeedNormalPath P0 (P1 * J.M) khat
      (G1 * J.M ^ 2 + P1 * J.N)
      (Cg * J.M ^ 2 + khat * P1 * J.N)
      (reparamAtJunction Gamma hC2 J) := by
  rcases hvar with
    ⟨g, gu, gt, gut, theta, kappa, etas, kt,
      hg0, hgP, hguB, hkB, hX, hguD, hthetaD,
      hgtD, hgtC, hgtB, hgutD, hgutC, hgutB,
      hetaD, hetaC, hetaB, hktD, hktC, hktB⟩
  let gp : ℝ → ℝ → ℝ := fun t u => g t (J.phi u) * J.phi1 u
  let gup : ℝ → ℝ → ℝ := fun t u =>
    gu t (J.phi u) * J.phi1 u ^ 2 + g t (J.phi u) * J.phi2 u
  let gtp : ℝ → ℝ → ℝ := fun t u => gt t (J.phi u) * J.phi1 u
  let gutp : ℝ → ℝ → ℝ := fun t u =>
    gut t (J.phi u) * J.phi1 u ^ 2 + gt t (J.phi u) * J.phi2 u
  let thetap : ℝ → ℝ → ℝ := fun t u => theta t (J.phi u)
  let kappap : ℝ → ℝ → ℝ := fun t u => kappa t (J.phi u)
  let etap : ℝ → ℝ → ℝ := fun t u => etas t (J.phi u)
  let ktp : ℝ → ℝ → ℝ := fun t u => kt t (J.phi u)
  refine ⟨gp, gup, gtp, gutp, thetap, kappap, etap, ktp, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t u
    exact mul_nonneg (hg0 t (J.phi u)) (le_trans J.m_pos.le (J.jacobian_lower u))
  · intro t u
    exact mul_le_mul (hgP t (J.phi u)) (le_trans (le_abs_self _) (J.jacobian_upper u))
      (le_trans J.m_pos.le (J.jacobian_lower u)) hP1
  · intro t u
    dsimp [gup]
    calc
      |gu t (J.phi u) * J.phi1 u ^ 2 + g t (J.phi u) * J.phi2 u|
          ≤ |gu t (J.phi u)| * |J.phi1 u| ^ 2 +
              |g t (J.phi u)| * |J.phi2 u| := by
                refine (abs_add_le _ _).trans ?_
                rw [abs_mul, abs_mul, abs_pow]
      _ ≤ G1 * J.M ^ 2 + P1 * J.N := by
        gcongr
        · exact hguB t (J.phi u)
        · exact J.jacobian_upper u
        · exact (abs_of_nonneg (hg0 t (J.phi u))).symm ▸ hgP t (J.phi u)
        · exact J.second_upper u
  · exact fun t u => hkB t (J.phi u)
  · intro t u
    dsimp [reparamAtJunction, NormalPath.reparamSpace, gp, thetap]
    convert (hX t (J.phi u)).scomp u (J.phi_deriv u) using 1
    push_cast
    rw [Complex.real_smul]
    ring
  · intro t u
    dsimp [gp, gup]
    convert ((hguD t (J.phi u)).comp u (J.phi_deriv u)).mul
      (J.phi1_deriv u) using 1
    simp only [Function.comp_apply]
    ring
  · intro t u
    dsimp [thetap, gp, kappap]
    convert (hthetaD t (J.phi u)).comp u (J.phi_deriv u) using 1 <;> ring
  · intro t u
    dsimp [gp, gtp]
    exact (hgtD t (J.phi u)).mul_const (J.phi1 u)
  · intro u
    exact (hgtC (J.phi u)).mul continuous_const
  · intro t u
    dsimp [gtp]
    calc
      |gt t (J.phi u) * J.phi1 u| ≤
          (khat * P1 * Gamma.m t) * J.M := by
        rw [abs_mul]
        exact mul_le_mul (hgtB t (J.phi u)) (J.jacobian_upper u)
          (abs_nonneg _) (mul_nonneg (mul_nonneg hkhat hP1) (Gamma.m_nonneg t))
      _ ≤ khat * (P1 * J.M) * (reparamAtJunction Gamma hC2 J).m t := by
        rw [reparamAtJunction_density]
        have hR := one_le_reparamCostConst J.m J.M J.N
        have hm := Gamma.m_nonneg t
        have hbase : (0:ℝ) ≤ khat * P1 * J.M * Gamma.m t :=
          mul_nonneg (mul_nonneg (mul_nonneg hkhat hP1) hM) hm
        nlinarith [mul_le_mul_of_nonneg_left hR hbase]
  · intro t u
    dsimp [gup, gutp]
    exact ((hgutD t (J.phi u)).mul_const (J.phi1 u ^ 2)).add
      ((hgtD t (J.phi u)).mul_const (J.phi2 u))
  · intro u
    exact ((hgutC (J.phi u)).mul continuous_const).add
      ((hgtC (J.phi u)).mul continuous_const)
  · intro t u
    dsimp [gutp]
    have h1 : |gut t (J.phi u) * J.phi1 u ^ 2| ≤
        Cg * Gamma.m t * J.M ^ 2 := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul (hgutB t (J.phi u))
        (pow_le_pow_left₀ (abs_nonneg _) (J.jacobian_upper u) 2)
        (pow_nonneg (abs_nonneg _) 2) (mul_nonneg hCg (Gamma.m_nonneg t))
    have h2 : |gt t (J.phi u) * J.phi2 u| ≤
        khat * P1 * Gamma.m t * J.N := by
      rw [abs_mul]
      exact mul_le_mul (hgtB t (J.phi u)) (J.second_upper u)
        (abs_nonneg _) (mul_nonneg (mul_nonneg hkhat hP1) (Gamma.m_nonneg t))
    rw [reparamAtJunction_density]
    have hR := one_le_reparamCostConst J.m J.M J.N
    calc
      |gut t (J.phi u) * J.phi1 u ^ 2 + gt t (J.phi u) * J.phi2 u|
          ≤ |gut t (J.phi u) * J.phi1 u ^ 2| + |gt t (J.phi u) * J.phi2 u| := abs_add_le _ _
      _ ≤ Cg * Gamma.m t * J.M ^ 2 + khat * P1 * Gamma.m t * J.N := add_le_add h1 h2
      _ ≤ (Cg * J.M ^ 2 + khat * P1 * J.N) *
          (reparamCostConst J.m J.M J.N * Gamma.m t) := by
        have hA : (0:ℝ) ≤ Cg * J.M ^ 2 + khat * P1 * J.N :=
          add_nonneg (mul_nonneg hCg (sq_nonneg _))
            (mul_nonneg (mul_nonneg hkhat hP1) hN)
        have hAm : (0:ℝ) ≤ (Cg * J.M ^ 2 + khat * P1 * J.N) * Gamma.m t :=
          mul_nonneg hA (Gamma.m_nonneg t)
        nlinarith [mul_le_mul_of_nonneg_left hR hAm]
  · intro t u
    dsimp [thetap, etap]
    exact hetaD t (J.phi u)
  · exact fun u => hetaC (J.phi u)
  · intro t u
    dsimp [etap]
    rw [reparamAtJunction_density]
    have hmle : Gamma.m t ≤ reparamCostConst J.m J.M J.N * Gamma.m t := by
      nlinarith [one_le_reparamCostConst J.m J.M J.N, Gamma.m_nonneg t]
    exact (hetaB t (J.phi u)).trans
      (mul_le_mul_of_nonneg_left hmle (le_of_lt (div_pos one_pos hP0)))
  · intro t u
    dsimp [kappap, ktp]
    exact hktD t (J.phi u)
  · exact fun u => hktC (J.phi u)
  · intro t u
    dsimp [ktp]
    rw [reparamAtJunction_density]
    have hmle : Gamma.m t ≤ reparamCostConst J.m J.M J.N * Gamma.m t := by
      nlinarith [one_le_reparamCostConst J.m J.M J.N, Gamma.m_nonneg t]
    have hc : (0:ℝ) ≤ 1 / P0 ^ 2 + khat ^ 2 :=
      add_nonneg (le_of_lt (div_pos one_pos (pow_pos hP0 2))) (sq_nonneg _)
    exact (hktB t (J.phi u)).trans (mul_le_mul_of_nonneg_left hmle hc)

end PathMetric
