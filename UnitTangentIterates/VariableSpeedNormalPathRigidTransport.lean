import UnitTangentIterates.NormalPathC2IncrementVariableSpeed
import UnitTangentIterates.MarkedRigid

noncomputable section
open Function
namespace NormalPathC2IncrementVariableSpeed
open PathMetric PathMetric.NormalPath

def rigidPath {p q : MarkedSpace.Data} (a w : ℂ) (hw : ‖w‖ = 1)
    (G : NormalPath p q) :
    NormalPath (MarkedRigid.rigidData a w p) (MarkedRigid.rigidData a w q) :=
  MarkedRigid.NormalPathRigid.rigidPathOf hw G (fun _ => rfl) (fun _ => rfl)

theorem isVariableSpeedNormalPath_rigid
    {P0 P1 khat G1 Cg : ℝ} {p q : MarkedSpace.Data}
    (a w : ℂ) (hw : ‖w‖ = 1) (G : NormalPath p q)
    (hG : IsVariableSpeedNormalPath P0 P1 khat G1 Cg G) :
    IsVariableSpeedNormalPath P0 P1 khat G1 Cg (rigidPath a w hw G) := by
  obtain ⟨g, gu, gt, gut, theta, kappa, etas, kt, hgnn, hgub, hguB, hkap,
    hXu, hgud, hthetau, hgt, hgtc, hgtbd, hgut, hgutc, hgutbd,
    hthetat, hetasc, hetas, hkappat, hktc, hkt⟩ := hG
  let phi := Complex.arg w
  have hphase : Complex.exp ((phi : ℂ) * Complex.I) = w := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    rw [hw] at h
    simpa [phi] using h
  refine ⟨g, gu, gt, gut, (fun t u => phi + theta t u), kappa,
    etas, kt, hgnn, hgub, hguB, hkap, ?_, hgud, ?_, hgt, hgtc,
    hgtbd, hgut, hgutc, hgutbd, ?_, hetasc, hetas, hkappat, hktc, hkt⟩
  · intro t u
    have h := ((hXu t u).const_mul w).const_add a
    have hexp : Complex.exp (Complex.I * (((phi + theta t u : ℝ) : ℂ))) =
        w * Complex.exp (Complex.I * ((theta t u : ℝ) : ℂ)) := by
      rw [show Complex.I * (((phi + theta t u : ℝ) : ℂ)) =
          (phi : ℂ) * Complex.I + Complex.I * ((theta t u : ℝ) : ℂ) by
            push_cast
            ring,
        Complex.exp_add, hphase]
    have hder : w * ((g t u : ℂ) * Complex.exp
        (Complex.I * ((theta t u : ℝ) : ℂ))) =
        (g t u : ℂ) * Complex.exp
          (Complex.I * (((phi + theta t u : ℝ) : ℂ))) := by
      rw [hexp]
      ring
    rw [hder] at h
    simpa [rigidPath, MarkedRigid.NormalPathRigid.rigidPathOf] using h
  · intro t u
    exact (hthetau t u).const_add phi
  · intro t u
    exact (hthetat t u).const_add phi

@[simp] theorem cost_rigidPath {p q : MarkedSpace.Data} (a w : ℂ)
    (hw : ‖w‖ = 1) (G : NormalPath p q) :
    cost (rigidPath a w hw G) = cost G := rfl

/-- The oriented velocity-acceleration numerator is invariant under an
orientation-preserving rigid motion. -/
theorem curvatureNumerator_rigid (w v acc : ℂ) (hw : ‖w‖ = 1) :
    ((starRingEnd ℂ) (w * v) * (w * acc)).im =
      ((starRingEnd ℂ) v * acc).im := by
  have hn : Complex.normSq w = 1 := by
    rw [Complex.normSq_eq_norm_sq, hw]
    norm_num
  have hcw : (starRingEnd ℂ) w * w = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    exact_mod_cast hn
  congr 1
  rw [map_mul]
  calc
    ((starRingEnd ℂ) w * (starRingEnd ℂ) v) * (w * acc) =
        ((starRingEnd ℂ) w * w) * ((starRingEnd ℂ) v * acc) := by ring
    _ = (starRingEnd ℂ) v * acc := by rw [hcw, one_mul]

end NormalPathC2IncrementVariableSpeed
