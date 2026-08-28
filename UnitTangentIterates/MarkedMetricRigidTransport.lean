import UnitTangentIterates.MarkedRigid

/-! Common unit rigid motions preserve the ambient marked `C2` metric. -/

noncomputable section

open MarkedSpace

namespace MarkedRigid

theorem dist_rigidData {a w : ℂ} (hw : ‖w‖ = 1) (p q : Data) :
    dist (rigidData a w p) (rigidData a w q) = dist p q := by
  simp only [Prod.dist_eq]
  congr 1
  · rw [BoundedContinuousFunction.dist_eq_iSup,
      BoundedContinuousFunction.dist_eq_iSup]
    congr 1
    funext u
    simp only [rigidData_curve]
    rw [dist_eq_norm, dist_eq_norm]
    rw [show (a + w * p.1 u) - (a + w * q.1 u) =
      w * (p.1 u - q.1 u) by ring, norm_mul, hw, one_mul]
  · congr 1
    · rw [BoundedContinuousFunction.dist_eq_iSup,
        BoundedContinuousFunction.dist_eq_iSup]
      congr 1
      funext u
      simp only [rigidData_vel]
      rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, hw, one_mul]
    · rw [BoundedContinuousFunction.dist_eq_iSup,
        BoundedContinuousFunction.dist_eq_iSup]
      congr 1
      funext u
      simp only [rigidData_acc]
      rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, hw, one_mul]

end MarkedRigid
