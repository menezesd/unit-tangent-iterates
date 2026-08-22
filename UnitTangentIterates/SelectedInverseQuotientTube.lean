import Mathlib
import UnitTangentIterates.RearTrackShiftInjective
import UnitTangentIterates.SelectedInverseQuotientSpeed

/-!
# Non-expansiveness modulo the marking, with the equivariance discharged

`SelectedInverseQuotient.pathDistShift_selInv_le_pathDistShift_of_tube` and the
local Lipschitz statement of `SelectedInverseQuotientSpeed.lean` both ask for
the equivariance of the selected inverse under a shift of the marking, either
directly (`hequiv`) or through the embeddedness of the rear tracks of *every*
shift of the terminal curve (`hinjRb`).

`RearTrackShiftInjective.injOn_rearTrack_shiftData` removes that: embeddedness
of the rear tracks of the curve itself already gives it for every shift of the
marking.  This file restates the two bounds accordingly.

Main results:

* `pathDistShift_selInv_le_pathDistShift_tube` — the bound modulo the marking
  from the tube data of the terminal curve alone;
* `pathDistShift_selInv_le_pathDistShift_gauge_tube` — the local Lipschitz
  bound with the explicit uniform constant `selInvGaugeConst`, with the
  equivariance discharged.
-/

noncomputable section

open Set Function MarkedSpace MarkedShift PathMetric RearTrack

namespace SelectedInverseQuotientTube

variable {c kmin dlt kap : ℝ} {p q : Data}

/-- **Non-expansiveness modulo the marking, from the tube data of the terminal
curve.**  Exactly
`SelectedInverseQuotient.pathDistShift_selInv_le_pathDistShift_of_tube`, with
the embeddedness hypothesis for the shifted markings discharged. -/
theorem pathDistShift_selInv_le_pathDistShift_tube {K : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hkap1 : kap < 1) (hK : 0 ≤ K)
    (hq : IsTubeMember c kmin dlt q)
    (hub : ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kap * ‖q.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K' s) s) →
      Function.Periodic dl (perim q) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev q) Θ dl) (Ico 0 (perim q)))
    (hbound : ∀ b : ℝ,
      pathDistShift (SelectedInverseMap.selInv kap p)
          (SelectedInverseMap.selInv kap (shiftData b q))
        ≤ K * pathDist p (shiftData b q)) :
    pathDistShift (SelectedInverseMap.selInv kap p) (SelectedInverseMap.selInv kap q)
      ≤ K * pathDistShift p q :=
  SelectedInverseQuotient.pathDistShift_selInv_le_pathDistShift_of_tube hc hkmin hkap1 hK
    hq hub hinjR
    (fun b => RearTrackShiftInjective.injOn_rearTrack_shiftData (kap := kap) hc hq hinjR b)
    hbound

/-- **The local Lipschitz bound modulo the marking, with the equivariance
discharged.**  Exactly
`SelectedInverseQuotientSpeed.pathDistShift_selInv_le_pathDistShift_gauge`, with
the shift equivariance of the selected inverse produced from the tube data of
the terminal curve. -/
theorem pathDistShift_selInv_le_pathDistShift_gauge_tube {P0 P1 beta : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin)
    (hP0 : 0 < P0) (hP1 : 0 < P1) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hbeta0 : 0 ≤ beta) (hQ : 0 < perim (SelectedInverseMap.selInv kap p))
    (hbeta : pathDistShift p q < beta)
    (hq : IsTubeMember c kmin dlt q)
    (hub : ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kap * ‖q.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K' s) s) →
      Function.Periodic dl (perim q) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kap)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev q) Θ dl) (Ico 0 (perim q)))
    (hne : ∀ b : ℝ, Nonempty (NormalPath p (shiftData b q)))
    (hcost : ∀ (b : ℝ) (Γ : NormalPath p (shiftData b q)), Γ.T = 1 →
      (∀ t, Γ.m t ≤ (3 / 2) * beta) →
      pathDistShift (SelectedInverseMap.selInv kap p)
          (SelectedInverseMap.selInv kap (shiftData b q))
        ≤ SelectedInverseQuotientSpeed.selInvGaugeConst P0 P1 kap ((3 / 2) * beta)
            (perim (SelectedInverseMap.selInv kap p)) * NormalPath.cost Γ) :
    pathDistShift (SelectedInverseMap.selInv kap p) (SelectedInverseMap.selInv kap q)
      ≤ SelectedInverseQuotientSpeed.selInvGaugeConst P0 P1 kap ((3 / 2) * beta)
          (perim (SelectedInverseMap.selInv kap p)) * pathDistShift p q :=
  SelectedInverseQuotientSpeed.pathDistShift_selInv_le_pathDistShift_gauge hP0 hP1 hkap0
    hkap1 hbeta0 hQ hbeta
    (fun b => RearTrackShiftInjective.selInv_shiftData_of_tube hc hkmin hkap1 hq hub hinjR b)
    hne hcost

end SelectedInverseQuotientTube
