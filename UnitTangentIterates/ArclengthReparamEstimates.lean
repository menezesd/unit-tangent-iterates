import Mathlib
import UnitTangentIterates.PathFunctionalsReparam
import UnitTangentIterates.JacobiArclengthUniform

/-!
# The arclength Jacobi estimates under a change of parameter

The four estimates of `JacobiArclengthUniform.lean` are stated for the rear
normal velocity read in the **arclength of the slice**.  The gauge machinery of
`GaugeNormalPath.lean` reads it instead in a *material* coordinate `x` — one and
the same coordinate for every time, of period `Q` — in which the slice at time
`t` has arclength `φ_t(x)`.  Unless every slice has the same length, the two
readings differ, and the estimates have to be transported.

That transport is exactly the comparison of `PathFunctionalsReparam.lean`: for a
change of parameter with `φ' ≥ m > 0`, `|φ'| ≤ M` and `|φ''| ≤ N` one has

```
  ∫_0^Q |η ∘ φ| ≤ m⁻¹ ∫_0^L |η|,   ‖η ∘ φ‖_∞ ≤ ‖η‖_∞,
  ‖(η ∘ φ)'‖_∞ ≤ M‖η'‖_∞,          ‖(η ∘ φ)''‖_∞ ≤ M²‖η''‖_∞ + N‖η'‖_∞,
```

so the four constants become `C_W/m`, `C₀`, `C₁M`, `C₂M² + C₁N`.

Main result: `estimates_reparam`.
-/

noncomputable section

open Set MeasureTheory MarkedTopology

namespace ArclengthReparamEstimates

open PathFunctionalsReparam

/-! ### The distorted constants -/

/-- The `L¹` constant, distorted by the slowest speed of the change of
parameter. -/
def reparamCW (CW m : ℝ) : ℝ := CW / m

/-- The sup-norm constant is unchanged. -/
def reparamC0 (C0 : ℝ) : ℝ := C0

/-- The first-order constant, distorted by the fastest speed. -/
def reparamC1 (C1 M : ℝ) : ℝ := C1 * M

/-- The second-order constant: the square of the fastest speed, plus the
acceleration acting on the first derivative. -/
def reparamC2 (C1 C2 M N : ℝ) : ℝ := C2 * M ^ 2 + C1 * N

/-! ### The transported estimates -/

/-- **The arclength estimates under a change of parameter.**

`etaA` is the rear normal velocity in the arclength of the slice, obeying the
four estimates over `[0, L]` against the front densities `WF ≤ WF + S0F ≤ …`;
`phi` is the change of parameter from the material coordinate to that arclength,
with `phi 0 = 0`, `phi Q = L`, `m ≤ φ' ≤ M` and `|φ''| ≤ N`.  Then the rear
velocity read in the material coordinate obeys the same four estimates over
`[0, Q]`, with the constants distorted as above. -/
theorem estimates_reparam {Q L m M N CW C0 C1 C2 WF S0F S1F : ℝ}
    {etaA etaA1 etaA2 phi phi1 phi2 : ℝ → ℝ}
    (hm : 0 < m) (hQ : 0 ≤ Q)
    (hA1 : ∀ x, HasDerivAt etaA (etaA1 x) x) (hA2 : ∀ x, HasDerivAt etaA1 (etaA2 x) x)
    (hbdd : BddAbove (Set.range fun x => |etaA x|))
    (hbdd1 : BddAbove (Set.range fun x => |etaA1 x|))
    (hbdd2 : BddAbove (Set.range fun x => |etaA2 x|))
    (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u) (hphi2 : ∀ u, HasDerivAt phi1 (phi2 u) u)
    (hphi1c : Continuous phi1)
    (hlow : ∀ u, m ≤ phi1 u) (hM : ∀ u, |phi1 u| ≤ M) (hN : ∀ u, |phi2 u| ≤ N)
    (hphi0 : phi 0 = 0) (hphiQ : phi Q = L)
    (hS1Fnn : 0 ≤ S1F) (hC1 : 0 ≤ C1)
    (hW : (∫ x in (0:ℝ)..L, |etaA x|) ≤ CW * WF)
    (hS0 : supNorm etaA ≤ C0 * WF)
    (hS1 : supNorm (deriv etaA) ≤ C1 * (WF + S0F))
    (hS2 : supNorm (deriv (deriv etaA)) ≤ C2 * (WF + S0F + S1F)) :
    (∫ x in (0:ℝ)..Q, |etaA (phi x)|) ≤ reparamCW CW m * WF
      ∧ supNorm (fun x => etaA (phi x)) ≤ reparamC0 C0 * WF
      ∧ supNorm (deriv fun x => etaA (phi x)) ≤ reparamC1 C1 M * (WF + S0F)
      ∧ supNorm (deriv (deriv fun x => etaA (phi x)))
          ≤ reparamC2 C1 C2 M N * (WF + S0F + S1F) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hN0 : 0 ≤ N := le_trans (abs_nonneg _) (hN 0)
  have hetac : Continuous etaA := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    exact (hA1 x).continuousAt
  have hd1 : deriv etaA = etaA1 := funext fun x => (hA1 x).deriv
  have hd2 : deriv (deriv etaA) = etaA2 := by
    rw [hd1]; exact funext fun x => (hA2 x).deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the `L¹` density
    have h := integral_abs_comp_le (m := m) (a := 0) (b := Q) (eta := etaA)
      (phi := phi) (phi1 := phi1) hm hQ hetac hphi1 hphi1c hlow
    rw [hphi0, hphiQ] at h
    refine h.trans ?_
    have : (1 / m) * (∫ x in (0:ℝ)..L, |etaA x|) ≤ (1 / m) * (CW * WF) :=
      mul_le_mul_of_nonneg_left hW (by positivity)
    refine this.trans (le_of_eq ?_)
    rw [reparamCW]
    ring
  · -- the sup norm
    exact (supNorm_comp_le hbdd phi).trans hS0
  · -- the first derivative
    have h := supNorm_deriv_comp_le (eta := etaA) (eta1 := etaA1) (phi := phi)
      (phi1 := phi1) (M := M) hA1 hphi1 hbdd1 hM
    rw [← hd1] at h
    refine h.trans ?_
    have : supNorm (deriv etaA) * M ≤ (C1 * (WF + S0F)) * M :=
      mul_le_mul_of_nonneg_right hS1 hM0
    refine this.trans (le_of_eq ?_)
    rw [reparamC1]; ring
  · -- the second derivative
    have h := supNorm_deriv2_comp_le (eta := etaA) (eta1 := etaA1) (eta2 := etaA2)
      (phi := phi) (phi1 := phi1) (phi2 := phi2) (M := M) (N := N)
      hA1 hA2 hphi1 hphi2 hbdd1 hbdd2 hM hN
    rw [← hd1, ← hd2] at h
    refine h.trans ?_
    have e1 : supNorm (deriv (deriv etaA)) * M ^ 2
        ≤ (C2 * (WF + S0F + S1F)) * M ^ 2 :=
      mul_le_mul_of_nonneg_right hS2 (by positivity)
    have e2 : supNorm (deriv etaA) * N ≤ (C1 * (WF + S0F + S1F)) * N := by
      refine mul_le_mul_of_nonneg_right (hS1.trans ?_) hN0
      have : WF + S0F ≤ WF + S0F + S1F := by linarith
      exact mul_le_mul_of_nonneg_left this hC1
    rw [reparamC2]
    nlinarith

end ArclengthReparamEstimates
