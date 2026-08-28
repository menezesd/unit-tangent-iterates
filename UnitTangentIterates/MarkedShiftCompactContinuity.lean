import UnitTangentIterates.ChordArc
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray

/-!
# Compact phase normalization and continuity of marked shifts

The marking parameter of `MarkedSpace.Data` has period one.  Thus an arbitrary
terminal phase can be reduced modulo one, independently of the physical
perimeter.  On the closed tube, translating the marking is continuous jointly
in the datum and the phase.
-/

noncomputable section

open Filter Function Set Topology MarkedSpace

namespace MarkedShiftCompactContinuity

/-- The velocity of a tube datum inherits the normalized period of its curve. -/
theorem periodic_vel_of_tube {c kmin dlt : ℝ} {p : Data}
    (hp : IsTubeMember c kmin dlt p) :
    Periodic (fun u => p.2.1 u) 1 := by
  intro u
  have hinner : HasDerivAt (fun x : ℝ => x + 1) 1 u := by
    simpa using (hasDerivAt_id u).add_const 1
  have hleft : HasDerivAt (fun x => p.1 (x + 1)) (p.2.1 (u + 1)) u := by
    simpa [Function.comp_def] using
      (hp.hasDerivAt_curve (u + 1)).scomp u hinner
  have heq : (fun x => p.1 (x + 1)) = fun x => p.1 x :=
    funext hp.periodic
  rw [heq] at hleft
  exact hleft.unique (hp.hasDerivAt_curve u)

/-- The acceleration of a tube datum also inherits normalized period one. -/
theorem periodic_acc_of_tube {c kmin dlt : ℝ} {p : Data}
    (hp : IsTubeMember c kmin dlt p) :
    Periodic (fun u => p.2.2 u) 1 := by
  have hvel := periodic_vel_of_tube hp
  intro u
  have hinner : HasDerivAt (fun x : ℝ => x + 1) 1 u := by
    simpa using (hasDerivAt_id u).add_const 1
  have hleft : HasDerivAt (fun x => p.2.1 (x + 1)) (p.2.2 (u + 1)) u := by
    simpa [Function.comp_def] using
      (hp.hasDerivAt_vel (u + 1)).scomp u hinner
  have heq : (fun x => p.2.1 (x + 1)) = fun x => p.2.1 x :=
    funext hvel
  rw [heq] at hleft
  exact hleft.unique (hp.hasDerivAt_vel u)

/-- Reducing a marking phase modulo one does not change a tube datum. -/
theorem shiftData_toIcoMod_eq {c kmin dlt : ℝ} {p : Data}
    (hp : IsTubeMember c kmin dlt p) (b : ℝ) :
    MarkedShift.shiftData (toIcoMod one_pos 0 b) p =
      MarkedShift.shiftData b p := by
  let q : ℝ := toIcoMod one_pos 0 b
  change MarkedShift.shiftData q p = MarkedShift.shiftData b p
  have hvel := periodic_vel_of_tube hp
  have hacc := periodic_acc_of_tube hp
  have hmod := (toIcoMod_eq_iff one_pos).1
    (show toIcoMod one_pos 0 b = q from rfl)
  obtain ⟨z, hz⟩ := hmod.2
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    apply BoundedContinuousFunction.ext <;> intro u
  · simp only [MarkedShift.shiftData_curve]
    rw [hz]
    simpa [add_assoc] using (hp.periodic.zsmul z (u + q)).symm
  · simp only [MarkedShift.shiftData_vel]
    rw [hz]
    simpa [add_assoc] using (hvel.zsmul z (u + q)).symm
  · simp only [MarkedShift.shiftData_acc]
    rw [hz]
    simpa [add_assoc] using (hacc.zsmul z (u + q)).symm

/-- For a fixed tube datum, translating all three marked components is
continuous in the phase, uniformly over the parameter line. -/
theorem tendsto_shiftData_fixed {c kmin dlt : ℝ} {p : Data}
    (hp : IsTubeMember c kmin dlt p) {bN : ℕ → ℝ} {b : ℝ}
    (hb : Tendsto bN atTop (nhds b)) :
    Tendsto (fun n => MarkedShift.shiftData (bN n) p) atTop
      (nhds (MarkedShift.shiftData b p)) := by
  have hvel := periodic_vel_of_tube hp
  have hacc := periodic_acc_of_tube hp
  apply Metric.tendsto_atTop.2
  intro eps heps
  obtain ⟨d0, hd0, -, hcurve⟩ :=
    ChordArc.exists_unif_bound p.1.continuous hp.periodic
      (half_pos heps)
  obtain ⟨d1, hd1, -, hvelClose⟩ :=
    ChordArc.exists_unif_bound p.2.1.continuous hvel
      (half_pos heps)
  obtain ⟨d2, hd2, -, haccClose⟩ :=
    ChordArc.exists_unif_bound p.2.2.continuous hacc
      (half_pos heps)
  let d := min d0 (min d1 d2)
  have hd : 0 < d := lt_min hd0 (lt_min hd1 hd2)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hb d hd
  refine ⟨N, fun n hn => ?_⟩
  have hbn : |bN n - b| ≤ d := by
    exact (by simpa [Real.dist_eq] using (hN n hn).le)
  have h0 : dist
      (MarkedShift.shiftData (bN n) p).1
      (MarkedShift.shiftData b p).1 ≤ eps / 2 := by
    refine (BoundedContinuousFunction.dist_le (half_pos heps).le).2 fun u => ?_
    rw [dist_eq_norm]
    exact hcurve _ _ (by
      change |(u + bN n) - (u + b)| ≤ d0
      rw [show (u + bN n) - (u + b) = bN n - b by ring]
      exact hbn.trans (min_le_left _ _))
  have h1 : dist
      (MarkedShift.shiftData (bN n) p).2.1
      (MarkedShift.shiftData b p).2.1 ≤ eps / 2 := by
    refine (BoundedContinuousFunction.dist_le (half_pos heps).le).2 fun u => ?_
    rw [dist_eq_norm]
    exact hvelClose _ _ (by
      change |(u + bN n) - (u + b)| ≤ d1
      rw [show (u + bN n) - (u + b) = bN n - b by ring]
      exact hbn.trans (min_le_right d0 (min d1 d2) |>.trans
        (min_le_left d1 d2)))
  have h2 : dist
      (MarkedShift.shiftData (bN n) p).2.2
      (MarkedShift.shiftData b p).2.2 ≤ eps / 2 := by
    refine (BoundedContinuousFunction.dist_le (half_pos heps).le).2 fun u => ?_
    rw [dist_eq_norm]
    exact haccClose _ _ (by
      change |(u + bN n) - (u + b)| ≤ d2
      rw [show (u + bN n) - (u + b) = bN n - b by ring]
      exact hbn.trans (min_le_right d0 (min d1 d2) |>.trans
        (min_le_right d1 d2)))
  rw [Prod.dist_eq, Prod.dist_eq]
  exact (max_le h0 (max_le h1 h2)).trans_lt (half_lt_self heps)

/-- Joint continuity of marked shift under marked-data convergence and phase
convergence.  The moving datum needs no separate equicontinuity: common-shift
isometry transfers that part of the error to the unshifted marked metric. -/
theorem tendsto_shiftData {c kmin dlt : ℝ} {pN : ℕ → Data} {p : Data}
    (hp : IsTubeMember c kmin dlt p)
    {bN : ℕ → ℝ} {b : ℝ}
    (hP : Tendsto pN atTop (nhds p))
    (hb : Tendsto bN atTop (nhds b)) :
    Tendsto (fun n => MarkedShift.shiftData (bN n) (pN n)) atTop
      (nhds (MarkedShift.shiftData b p)) := by
  have hfixed := tendsto_shiftData_fixed hp hb
  apply Metric.tendsto_atTop.2
  intro eps heps
  have heps2 : 0 < eps / 2 := half_pos heps
  obtain ⟨NP, hNP⟩ := Metric.tendsto_atTop.1 hP (eps / 2) heps2
  obtain ⟨Nb, hNb⟩ := Metric.tendsto_atTop.1 hfixed (eps / 2) heps2
  refine ⟨max NP Nb, fun n hn => ?_⟩
  have hPn := hNP n (le_trans (le_max_left _ _) hn)
  have hbn := hNb n (le_trans (le_max_right _ _) hn)
  calc
    dist (MarkedShift.shiftData (bN n) (pN n))
        (MarkedShift.shiftData b p) ≤
      dist (MarkedShift.shiftData (bN n) (pN n))
          (MarkedShift.shiftData (bN n) p) +
        dist (MarkedShift.shiftData (bN n) p)
          (MarkedShift.shiftData b p) := dist_triangle _ _ _
    _ = dist (pN n) p +
        dist (MarkedShift.shiftData (bN n) p)
          (MarkedShift.shiftData b p) := by
      rw [FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray.dist_shiftData]
    _ < eps / 2 + eps / 2 := add_lt_add hPn hbn
    _ = eps := by ring

end MarkedShiftCompactContinuity
