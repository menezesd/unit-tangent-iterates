import UnitTangentIterates.PeriodicSupNormFunctionalIntegrable
import UnitTangentIterates.AnchoredJacobiStableTransition

/-!
# Canonical functional recosting of a normal path

The `m` field of a `NormalPath` is only an arbitrary common majorant.  This
module replaces it by the canonical sum of the four paper densities.  The
underlying family, normal velocity, endpoints, and normal gauge are unchanged.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace MarkedTopology PathMetric

namespace CanonicalNormalPathRecost

open PathMetric.NormalPath PeriodicSupNormFunctionalIntegrable
open ControlledJunctionPathFunctionalBounds
open AnchoredJacobiStableTransition

def density {p q : Data} (Gamma : NormalPath p q) (t : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
    supNorm (Gamma.eta t) +
    supNorm (iteratedDeriv 1 (Gamma.eta t)) +
    supNorm (iteratedDeriv 2 (Gamma.eta t))

theorem density_nonnegative {p q : Data} (Gamma : NormalPath p q) (t : ℝ) :
    0 ≤ density Gamma t := by
  unfold density
  have hw : 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
    intervalIntegral.integral_nonneg (by norm_num) (fun u _ => abs_nonneg _)
  exact add_nonneg (add_nonneg (add_nonneg hw (supNorm_nonneg _))
    (supNorm_nonneg _)) (supNorm_nonneg _)

theorem continuous_density {p q : Data} (Gamma : NormalPath p q)
    (hC2 : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2.eta1))
    (heta2 : Continuous (Function.uncurry hC2.eta2)) :
    Continuous (density Gamma) := by
  have hd1 : ∀ t, iteratedDeriv 1 (Gamma.eta t) = hC2.eta1 t := by
    intro t
    funext u
    simp only [iteratedDeriv_one]
    exact (hC2.eta_deriv t u).deriv
  have hd2 : ∀ t, iteratedDeriv 2 (Gamma.eta t) = hC2.eta2 t := by
    intro t
    funext u
    simp only [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_zero]
    rw [show deriv (Gamma.eta t) = hC2.eta1 t by
      funext v; exact (hC2.eta_deriv t v).deriv]
    exact (hC2.eta1_deriv t u).deriv
  unfold density
  apply Continuous.add
  · apply Continuous.add
    · apply Continuous.add
      · exact continuous_L1_density_of_joint_continuous heta
      · exact continuous_supNorm_of_joint_continuous_periodic one_pos heta
          hC2.eta_periodic
    · simpa only [hd1] using
        continuous_supNorm_of_joint_continuous_periodic one_pos heta1
          hC2.eta1_periodic
  · simpa only [hd2] using
      continuous_supNorm_of_joint_continuous_periodic one_pos heta2
        hC2.eta2_periodic

def recost {p q : Data} (Gamma : NormalPath p q)
    (hC2 : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2.eta1))
    (heta2 : Continuous (Function.uncurry hC2.eta2)) : NormalPath p q where
  T := Gamma.T
  T_pos := Gamma.T_pos
  X := Gamma.X
  eta := Gamma.eta
  nu := Gamma.nu
  m := density Gamma
  start := Gamma.start
  finish := Gamma.finish
  hasDerivAt_time := Gamma.hasDerivAt_time
  cont_vel := Gamma.cont_vel
  norm_nu := Gamma.norm_nu
  cont_m := continuous_density Gamma hC2 heta heta1 heta2
  m_nonneg := density_nonnegative Gamma
  m_stop := by
    intro t ht
    have hw0 : (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) = 0 := by
      apply le_antisymm
      · simpa [Gamma.m_stop t ht] using Gamma.le_m_L1 t
      · exact intervalIntegral.integral_nonneg (by norm_num)
          (fun u _ => abs_nonneg _)
    have hs0 : supNorm (Gamma.eta t) = 0 := by
      apply le_antisymm
      · simpa [Gamma.m_stop t ht] using Gamma.le_m_sup t 0 (by norm_num)
      · exact supNorm_nonneg _
    have hs1 : supNorm (iteratedDeriv 1 (Gamma.eta t)) = 0 := by
      apply le_antisymm
      · simpa [Gamma.m_stop t ht] using Gamma.le_m_sup t 1 (by norm_num)
      · exact supNorm_nonneg _
    have hs2 : supNorm (iteratedDeriv 2 (Gamma.eta t)) = 0 := by
      apply le_antisymm
      · simpa [Gamma.m_stop t ht] using Gamma.le_m_sup t 2 (by norm_num)
      · exact supNorm_nonneg _
    unfold density
    rw [hw0, hs0, hs1, hs2]
    ring
  abs_eta_le := by
    intro t u
    have hbdd : BddAbove (Set.range fun v => |Gamma.eta t v|) := by
      refine ⟨Gamma.m t, ?_⟩
      rintro _ ⟨v, rfl⟩
      exact Gamma.abs_eta_le t v
    have hw : 0 ≤ ∫ v in (0 : ℝ)..1, |Gamma.eta t v| :=
      intervalIntegral.integral_nonneg (by norm_num) (fun v _ => abs_nonneg _)
    exact (le_supNorm hbdd u).trans (by
      unfold density
      linarith [supNorm_nonneg (Gamma.eta t),
        supNorm_nonneg (iteratedDeriv 1 (Gamma.eta t)),
        supNorm_nonneg (iteratedDeriv 2 (Gamma.eta t))])
  le_m_L1 := by
    intro t
    unfold density
    linarith [supNorm_nonneg (Gamma.eta t),
      supNorm_nonneg (iteratedDeriv 1 (Gamma.eta t)),
      supNorm_nonneg (iteratedDeriv 2 (Gamma.eta t))]
  le_m_sup := by
    intro t j hj
    have hw : 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      intervalIntegral.integral_nonneg (by norm_num) (fun u _ => abs_nonneg _)
    have hs0 := supNorm_nonneg (Gamma.eta t)
    have hs1 := supNorm_nonneg (iteratedDeriv 1 (Gamma.eta t))
    have hs2 := supNorm_nonneg (iteratedDeriv 2 (Gamma.eta t))
    interval_cases j
    · simpa only [iteratedDeriv_zero] using
        (show supNorm (Gamma.eta t) ≤ density Gamma t by
          unfold density; linarith)
    · unfold density
      linarith
    · unfold density
      linarith

@[simp] theorem recost_eta {p q : Data} (Gamma : NormalPath p q)
    (hC2 : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2.eta1))
    (heta2 : Continuous (Function.uncurry hC2.eta2)) :
    (recost Gamma hC2 heta heta1 heta2).eta = Gamma.eta := by
  simp [recost]

theorem cost_recost_eq_components {p q : Data} (Gamma : NormalPath p q)
    (hT : Gamma.T = 1) (hC2 : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2.eta1))
    (heta2 : Continuous (Function.uncurry hC2.eta2)) :
    cost (recost Gamma hC2 heta heta1 heta2) =
      W Gamma.eta 1 + S 0 Gamma.eta + S 1 Gamma.eta + S 2 Gamma.eta := by
  rw [cost, show (recost Gamma hC2 heta heta1 heta2).T = 1 by
    simpa [recost] using hT]
  change (∫ t in (0 : ℝ)..1, density Gamma t) = _
  unfold density W S
  simp only [iteratedDeriv_zero]
  let F := functionalIntegrable_of_jointC2 hC2 heta heta1 heta2
  rw [intervalIntegral.integral_add (F.w.add F.s0 |>.add F.s1) F.s2,
    intervalIntegral.integral_add (F.w.add F.s0) F.s1,
    intervalIntegral.integral_add F.w F.s0]

theorem cost_recost_le_markedComponents {p q : Data} (Gamma : NormalPath p q)
    (hT : Gamma.T = 1) (hC2 : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2.eta1))
    (heta2 : Continuous (Function.uncurry hC2.eta2)) :
    cost (recost Gamma hC2 heta heta1 heta2) ≤
      (components Gamma.eta).w + (components Gamma.eta).s0 +
        (components Gamma.eta).s1 + (components Gamma.eta).s2 := by
  rw [cost_recost_eq_components Gamma hT hC2 heta heta1 heta2]
  rfl

/-- With normalized spatial parameter, the physical `W` component is the
perimeter times the normalized `W`.  Once the retained perimeter is at least
one, canonical recosting is bounded by the correctly scaled component sum. -/
theorem cost_recost_le_scaled_components {p q : Data} (Gamma : NormalPath p q)
    (hT : Gamma.T = 1) (hC2 : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2.eta1))
    (heta2 : Continuous (Function.uncurry hC2.eta2))
    {L : ℝ} (hL : 1 ≤ L) :
    cost (recost Gamma hC2 heta heta1 heta2) ≤
      L * W Gamma.eta 1 + S 0 Gamma.eta + S 1 Gamma.eta + S 2 Gamma.eta := by
  rw [cost_recost_eq_components Gamma hT hC2 heta heta1 heta2]
  have hW : 0 ≤ W Gamma.eta 1 := by
    unfold W
    exact intervalIntegral.integral_nonneg (by norm_num) (fun t _ =>
      intervalIntegral.integral_nonneg (by norm_num) (fun u _ => abs_nonneg _))
  have hscale : W Gamma.eta 1 ≤ L * W Gamma.eta 1 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hL hW
  linarith

end CanonicalNormalPathRecost
