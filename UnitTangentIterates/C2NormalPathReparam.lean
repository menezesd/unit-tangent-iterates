import Mathlib
import UnitTangentIterates.PathMetric
import UnitTangentIterates.ArclengthReparamEstimates

/-! Controlled fixed spatial reparameterization of smooth normal paths. -/

noncomputable section

open Set Function MeasureTheory MarkedSpace PathMetric

namespace PathMetric

/-- Spatial C² data missing from the bare `NormalPath` interface. -/
structure C2NormalPathData {p q : Data} (Gamma : NormalPath p q) where
  eta1 : ℝ → ℝ → ℝ
  eta2 : ℝ → ℝ → ℝ
  eta_deriv : ∀ t u, HasDerivAt (Gamma.eta t) (eta1 t u) u
  eta1_deriv : ∀ t u, HasDerivAt (eta1 t) (eta2 t u) u
  eta1_cont : ∀ t, Continuous (eta1 t)
  eta2_cont : ∀ t, Continuous (eta2 t)
  eta1_bdd : ∀ t, BddAbove (Set.range fun u => |eta1 t u|)
  eta2_bdd : ∀ t, BddAbove (Set.range fun u => |eta2 t u|)
  eta_periodic : ∀ t, Periodic (Gamma.eta t) 1
  eta1_periodic : ∀ t, Periodic (eta1 t) 1
  eta2_periodic : ∀ t, Periodic (eta2 t) 1

/-- One coefficient dominating all four path-functional distortions. -/
def reparamCostConst (m M N : ℝ) : ℝ :=
  max (1 / m) (max 1 (max (2 * M) (3 * (M ^ 2 + N))))

theorem one_le_reparamCostConst (m M N : ℝ) :
    1 ≤ reparamCostConst m M N := by
  unfold reparamCostConst
  exact (le_max_left 1 _).trans (le_max_right _ _)

theorem reparamCostConst_nonneg {m M N : ℝ} (hm : 0 < m) :
    0 ≤ reparamCostConst m M N := by
  exact le_trans (by positivity : 0 ≤ 1 / m) (le_max_left _ _)

/-- A fixed orientation-preserving periodic C² change of the normalized
spatial parameter preserves normality and multiplies path cost by an explicit
constant. -/
def NormalPath.reparamSpace
    {p q p' q' : Data} (Gamma : NormalPath p q) (hC2 : C2NormalPathData Gamma)
    {phi phi1 phi2 : ℝ → ℝ} {m M N : ℝ}
    (hm : 0 < m)
    (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi2 : ∀ u, HasDerivAt phi1 (phi2 u) u)
    (hphi1c : Continuous phi1) (hphi2c : Continuous phi2)
    (hlow : ∀ u, m ≤ phi1 u) (hM : ∀ u, |phi1 u| ≤ M)
    (hN : ∀ u, |phi2 u| ≤ N)
    (hphi0 : phi 0 = 0) (hphi1v : phi 1 = 1)
    (hstart : ∀ u, Gamma.X 0 (phi u) = p'.1 u)
    (hfinish : ∀ u, Gamma.X Gamma.T (phi u) = q'.1 u) :
    NormalPath p' q' where
  T := Gamma.T
  T_pos := Gamma.T_pos
  X := fun t u => Gamma.X t (phi u)
  eta := fun t u => Gamma.eta t (phi u)
  nu := fun t u => Gamma.nu t (phi u)
  m := fun t => reparamCostConst m M N * Gamma.m t
  start := hstart
  finish := hfinish
  hasDerivAt_time := fun t u => Gamma.hasDerivAt_time t (phi u)
  cont_vel := fun u => Gamma.cont_vel (phi u)
  norm_nu := fun t u => Gamma.norm_nu t (phi u)
  cont_m := continuous_const.mul Gamma.cont_m
  m_nonneg := fun t => mul_nonneg (reparamCostConst_nonneg hm) (Gamma.m_nonneg t)
  m_stop := fun t ht => by rw [Gamma.m_stop t ht, mul_zero]
  abs_eta_le := fun t u => (Gamma.abs_eta_le t (phi u)).trans
    (by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right
          (one_le_reparamCostConst m M N) (Gamma.m_nonneg t)))
  le_m_L1 := fun t => by
    have h := PathFunctionalsReparam.integral_abs_comp_le
      (m := m) (a := 0) (b := 1) (eta := Gamma.eta t)
      (phi := phi) (phi1 := phi1) hm zero_le_one
      (continuous_iff_continuousAt.2 fun u => (hC2.eta_deriv t u).continuousAt)
      hphi1 hphi1c hlow
    rw [hphi0, hphi1v] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (Gamma.le_m_L1 t) (by positivity)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Gamma.m_nonneg t)))
  le_m_sup := fun t j hj => by
    rcases Nat.le_of_lt_succ (Nat.lt_succ_of_le hj) with hj'
    interval_cases j
    · exact (PathFunctionalsReparam.supNorm_comp_le
        ⟨Gamma.m t, by rintro _ ⟨u, rfl⟩; exact Gamma.abs_eta_le t u⟩ phi).trans
        ((Gamma.le_m_sup t 0 (by norm_num)).trans
          (by
            simpa only [one_mul] using
              (mul_le_mul_of_nonneg_right
                (one_le_reparamCostConst m M N) (Gamma.m_nonneg t))))
    · have hd : deriv (fun u => Gamma.eta t (phi u)) =
          fun u => hC2.eta1 t (phi u) * phi1 u := by
        funext u
        exact ((hC2.eta_deriv t (phi u)).comp u (hphi1 u)).deriv
      rw [iteratedDeriv_one, hd]
      have hsup : MarkedTopology.supNorm
          (fun u => hC2.eta1 t (phi u) * phi1 u) ≤ 2 * M * Gamma.m t := by
        refine ciSup_le fun u => ?_
        rw [abs_mul]
        have hEta : |hC2.eta1 t (phi u)| ≤ Gamma.m t := by
          calc
            |hC2.eta1 t (phi u)| ≤ MarkedTopology.supNorm (hC2.eta1 t) :=
              MarkedTopology.le_supNorm (hC2.eta1_bdd t) _
            _ = MarkedTopology.supNorm (iteratedDeriv 1 (Gamma.eta t)) := by
              congr 1
              funext y
              rw [iteratedDeriv_one]
              exact (hC2.eta_deriv t y).deriv.symm
            _ ≤ Gamma.m t := Gamma.le_m_sup t 1 (by norm_num)
        have hM0 : 0 ≤ M := (abs_nonneg (phi1 u)).trans (hM u)
        have hprod : |hC2.eta1 t (phi u)| * |phi1 u| ≤ Gamma.m t * M :=
          mul_le_mul hEta (hM u) (abs_nonneg _) (Gamma.m_nonneg t)
        nlinarith [mul_nonneg hM0 (Gamma.m_nonneg t)]
      exact hsup.trans (mul_le_mul_of_nonneg_right
          ((le_max_left (2 * M) _).trans
            ((le_max_right 1 _).trans (le_max_right _ _)))
          (Gamma.m_nonneg t))
    · have hd1 : deriv (fun u => Gamma.eta t (phi u)) =
          fun u => hC2.eta1 t (phi u) * phi1 u := by
        funext u
        exact ((hC2.eta_deriv t (phi u)).comp u (hphi1 u)).deriv
      have hd2 : deriv (deriv (fun u => Gamma.eta t (phi u))) = fun u =>
          hC2.eta2 t (phi u) * phi1 u ^ 2 + hC2.eta1 t (phi u) * phi2 u := by
        rw [hd1]
        funext u
        have h := ((hC2.eta1_deriv t (phi u)).comp u (hphi1 u)).mul (hphi2 u)
        simpa only [Function.comp_apply, pow_two, mul_comm, mul_left_comm, mul_assoc]
          using h.deriv
      have hi2 : iteratedDeriv 2 (fun u => Gamma.eta t (phi u)) =
          deriv (deriv (fun u => Gamma.eta t (phi u))) := by
        simp only [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
          iteratedDeriv_zero]
      rw [hi2, hd2]
      have hsup : MarkedTopology.supNorm (fun u =>
          hC2.eta2 t (phi u) * phi1 u ^ 2 + hC2.eta1 t (phi u) * phi2 u) ≤
          3 * (M ^ 2 + N) * Gamma.m t := by
        refine ciSup_le fun u => ?_
        have hη1 : |hC2.eta1 t (phi u)| ≤ Gamma.m t := by
          calc
            |hC2.eta1 t (phi u)| ≤ MarkedTopology.supNorm (hC2.eta1 t) :=
              MarkedTopology.le_supNorm (hC2.eta1_bdd t) _
            _ = MarkedTopology.supNorm (iteratedDeriv 1 (Gamma.eta t)) := by
              congr 1
              funext y
              rw [iteratedDeriv_one]
              exact (hC2.eta_deriv t y).deriv.symm
            _ ≤ Gamma.m t := Gamma.le_m_sup t 1 (by norm_num)
        have hη2 : |hC2.eta2 t (phi u)| ≤ Gamma.m t := by
          calc
            |hC2.eta2 t (phi u)| ≤ MarkedTopology.supNorm (hC2.eta2 t) :=
              MarkedTopology.le_supNorm (hC2.eta2_bdd t) _
            _ = MarkedTopology.supNorm (iteratedDeriv 2 (Gamma.eta t)) := by
              congr 1
              funext y
              simp only [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
                iteratedDeriv_zero]
              rw [show deriv (Gamma.eta t) = hC2.eta1 t from funext fun z =>
                (hC2.eta_deriv t z).deriv]
              exact (hC2.eta1_deriv t y).deriv.symm
            _ ≤ Gamma.m t := Gamma.le_m_sup t 2 (by norm_num)
        have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM u)
        have hN0 : 0 ≤ N := le_trans (abs_nonneg _) (hN u)
        calc
          |hC2.eta2 t (phi u) * phi1 u ^ 2 + hC2.eta1 t (phi u) * phi2 u| ≤
              |hC2.eta2 t (phi u) * phi1 u ^ 2| +
              |hC2.eta1 t (phi u) * phi2 u| := abs_add_le _ _
          _ = |hC2.eta2 t (phi u)| * |phi1 u| ^ 2 +
                |hC2.eta1 t (phi u)| * |phi2 u| := by
              rw [abs_mul, abs_pow, abs_mul]
          _ ≤ 3 * (M ^ 2 + N) * Gamma.m t := by
              have hM2 : |phi1 u| ^ 2 ≤ M ^ 2 :=
                (sq_le_sq₀ (abs_nonneg (phi1 u)) hM0).2 (hM u)
              have hterm1 : |hC2.eta2 t (phi u)| * |phi1 u| ^ 2 ≤
                  Gamma.m t * M ^ 2 :=
                mul_le_mul hη2 hM2 (sq_nonneg _) (Gamma.m_nonneg t)
              have hterm2 : |hC2.eta1 t (phi u)| * |phi2 u| ≤
                  Gamma.m t * N :=
                mul_le_mul hη1 (hN u) (abs_nonneg _) (Gamma.m_nonneg t)
              nlinarith [mul_nonneg (add_nonneg (sq_nonneg M) hN0)
                (Gamma.m_nonneg t)]
      exact hsup.trans (mul_le_mul_of_nonneg_right
          (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _) (le_max_right _ _))) (Gamma.m_nonneg t)
        )

end PathMetric
