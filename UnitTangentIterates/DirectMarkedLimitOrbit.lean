import UnitTangentIterates.UnconditionalAssemblyRemainder
import UnitTangentIterates.SelectedInverseMap

/-!
# Direct forward orbit from a marked inverse limit

The final shadowing argument only needs the geometric statement that `B p`
is an inverse image of `p`: applying the unit-tangent map to `B p` has the
same range as `p`.  It does not need a total auxiliary map `T`, nor literal
identities `T (B p) = p` away from the constructed orbit.
-/

noncomputable section

open Set Function Complex MarkedSpace Metric

namespace PaperFaithfulAssemblyRemainder

/-- Construct the paper's forward orbit directly from the range realization
of the inverse map.  This is the `T`-free form of
`shadowingOrbit_of_markedLimit`. -/
theorem shadowingOrbit_of_markedLimit_direct
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {Q X : ℕ → Data}
    {c dlt Csh e0 : ℝ}
    (hc : 0 < c)
    (hQmem : ∀ n, IsTubeMember c 0 dlt (Q n))
    (hXmem : ∀ n, IsTubeMember c 0 dlt (X n))
    (hQfront : ∀ n, ev (Q n) =
      TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n))
    (horbit : ∀ n, range (ev (X (n + 1))) =
      range (UnitTangent.unitTangentMap (ev (X n))))
    (hoval : ∀ n, MainTheoremConditional.IsOval (ev (X n)))
    (hclose : ∀ u, ‖(X 0).1 u - (Q 0).1 u‖ ≤ Csh * e0)
    (hperim : |perim (X 0) - perim (Q 0)| ≤ Csh * e0)
    (hQperim : perim (Q 0) = 2 * Hs 0) :
    ∃ (Y : ℕ → ℝ → ℂ) (LY : ℝ),
      (∀ n, MainTheoremConditional.IsOval (Y n)) ∧
      (∀ n, range (Y (n + 1)) = range (UnitTangent.unitTangentMap (Y n))) ∧
      0 < LY ∧ Periodic (Y 0) LY ∧
      hausdorffDist (range (Y 0))
        (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) ≤ Csh * e0 ∧
      2 * Hs 0 - Csh * e0 ≤ LY := by
  let Y : ℕ → ℝ → ℂ := fun n => ev (X n)
  let LY := perim (X 0)
  have hLY : 0 < LY := perim_pos hc (hXmem 0)
  have hYper : Periodic (Y 0) LY := periodic_ev hc (hXmem 0)
  have horbitY : ∀ n,
      range (Y (n + 1)) = range (UnitTangent.unitTangentMap (Y n)) := by
    exact horbit
  have hXR : range (Y 0) = range (⇑(X 0).1) := range_ev hc (hXmem 0)
  have hQR : range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0)) =
      range (⇑(Q 0).1) := by
    rw [← hQfront 0]
    exact range_ev hc (hQmem 0)
  have hhaus : hausdorffDist (range (Y 0))
      (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) ≤ Csh * e0 := by
    rw [hXR, hQR]
    refine CurveDistance.hausdorffDist_range_le
      (le_trans (norm_nonneg _) (hclose 0)) fun u => ?_
    simpa [dist_eq_norm] using hclose u
  have hperiodLower : 2 * Hs 0 - Csh * e0 ≤ LY := by
    rw [← hQperim]
    have h := (abs_le.mp hperim).1
    dsimp [LY]
    linarith
  exact ⟨Y, LY, hoval, horbitY, hLY, hYper, hhaus, hperiodLower⟩

/-- The canonical selected inverse supplies the direct range realization.
This is exactly the geometric component of `SelectedInverseMap.selInv_spec`,
with its orientation reversed to match the direct shadowing interface. -/
theorem range_eq_unitTangent_selInv
    {c kmin dlt kh : ℝ} (hc : 0 < c) (hkmin : 0 < kmin) (hkh1 : kh < 1)
    {p : Data} (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤
      kh * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ K dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ s : ℂ))) s) →
      (∀ s, HasDerivAt Θ (K s) s) →
      Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) →
      InjOn (RearTrack.rearTrack (ev p) Θ dl) (Ico 0 (perim p))) :
    range (ev p) = range (UnitTangent.unitTangentMap
      (ev (SelectedInverseMap.selInv kh p))) := by
  exact (SelectedInverseMap.selInv_spec hc hkmin hkh1 hp hub hinjR).choose_spec.2.2.2.2.symm

end PaperFaithfulAssemblyRemainder
