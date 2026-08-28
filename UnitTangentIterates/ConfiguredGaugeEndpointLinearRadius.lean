import UnitTangentIterates.ConfiguredGaugeEndpointDefect
import UnitTangentIterates.InterpolationVariableSpeedSelInvAdapter
import UnitTangentIterates.ExponentialDiagonalLargeSeparation

/-!
# Absorbing gauge endpoint marking into the diagonal radius

The column shadow radius and the terminal marking defect are not independent
budgets.  On the uniform stage-cost interval the latter is linear in the same
diagonal defect, so adding its explicit coefficient to the row conversion
absorbs both errors into one tail radius.
-/

noncomputable section

open MarkedSpace PathMetric

namespace ConfiguredGaugeEndpointLinearRadius

open ConfiguredGaugeEndpointDefect
  InterpolationVariableSpeedSelInvAdapter
  ExponentialDiagonalLargeSeparation

/-- The exact coefficient in the linearized gauge endpoint estimate. -/
def endpointLinearCoeff
    (ell Lmax kappa kappa2 L kb kL : ℕ → ℝ) (M : ℝ) : ℕ → ℝ :=
  fun n ↦ canonicalMarkingLinearConst
    (Lmax n) (ell n) (kappa n) (kappa2 n) M
    (L n) (kb n) (kL n)

theorem endpointLinearCoeff_nonneg
    {ell Lmax kappa kappa2 L kb kL : ℕ → ℝ} {M : ℝ}
    (hLmax : ∀ n, 0 ≤ Lmax n) (hkappa : ∀ n, 0 ≤ kappa n) :
    ∀ n, 0 ≤ endpointLinearCoeff ell Lmax kappa kappa2 L kb kL M n := by
  intro n
  exact canonicalMarkingLinearConst_nonneg (hLmax n) (hkappa n)

/-- The exact configured endpoint modulus is linear in the stage cost on the
uniform cost interval. -/
theorem rho_le_endpointLinearCoeff_mul
    {ell Lmax kappa kappa2 L kb kL : ℕ → ℝ}
    {stageCost : ℕ → ℕ → ℝ} {M : ℝ}
    (hell : ∀ n, 0 ≤ ell n) (hLmax : ∀ n, 0 ≤ Lmax n)
    (hkappa : ∀ n, 0 ≤ kappa n) (hkappa2 : ∀ n, 0 ≤ kappa2 n)
    (hM : 0 ≤ M) (hL : ∀ n, 0 ≤ L n) (hkb : ∀ n, 0 ≤ kb n)
    (hkL : ∀ n, 0 ≤ kL n) (hcost0 : ∀ n k, 0 ≤ stageCost n k)
    (hcostM : ∀ n k, stageCost n k ≤ M) :
    ∀ n k,
      rho ell Lmax kappa kappa2 L kb kL stageCost n k ≤
        endpointLinearCoeff ell Lmax kappa kappa2 L kb kL M n *
          stageCost n k := by
  intro n k
  simpa only [rho, endpointLinearCoeff] using
    markingC2Bound_flow_le_linear
      (hLmax n) (hell n) (hkappa n) (hkappa2 n) hM
      (hL n) (hkb n) (hkL n) (hcost0 n k) (hcostM n k)

/-- Every shifted diagonal term is bounded by the row tail which starts
before it. -/
theorem shifted_term_le_tail
    {d : ℕ → ℝ} (hsum : Summable d) (hd : ∀ j, 0 ≤ d j)
    (n k : ℕ) : d (n + k) ≤
      ShadowingTails.tail (rowError d n) 0 := by
  have hsrow : Summable (rowError d n) := by
    simpa [rowError, Nat.add_comm] using
      (summable_nat_add_iff (f := d) n).2 hsum
  have hrow0 : ∀ j, 0 ≤ rowError d n j := fun j ↦ hd (n + j)
  have hk := ShadowingTails.le_tail hsrow hrow0 k
  have hterm : d (n + k) ≤ ShadowingTails.tail (rowError d n) k := by
    simpa [rowError] using hk
  exact hterm.trans
    (ShadowingTails.tail_antitone hsrow hrow0 (Nat.zero_le k))

/-- A stage cost controlled by the diagonal term is controlled by the full
row tail. -/
theorem stageCost_le_tail
    {d : ℕ → ℝ} {stageCost : ℕ → ℕ → ℝ}
    (hsum : Summable d) (hd : ∀ j, 0 ≤ d j)
    (hstage : ∀ n k, stageCost n k ≤ d (n + k)) (n k : ℕ) :
    stageCost n k ≤ ShadowingTails.tail (rowError d n) 0 :=
  (hstage n k).trans (shifted_term_le_tail hsum hd n k)

/-- The combined conversion reserves exactly the column-shadow coefficient
plus the endpoint-marking coefficient. -/
def combinedConversion (C E : ℕ → ℝ) : ℕ → ℝ :=
  fun n ↦ C n + E n

theorem combinedConversion_nonneg
    {C E : ℕ → ℝ} (hC : ∀ n, 0 ≤ C n) (hE : ∀ n, 0 ≤ E n) :
    ∀ n, 0 ≤ combinedConversion C E n :=
  fun n ↦ add_nonneg (hC n) (hE n)

/-- The scalar inequality which closes the previously external `hfit`: a
column tail radius plus one endpoint correction fits the radius formed with
the combined conversion. -/
theorem columnRadius_add_endpoint_le_combinedRadius
    {C E d : ℕ → ℝ} {stageCost : ℕ → ℕ → ℝ}
    (hsum : Summable d) (hd : ∀ j, 0 ≤ d j)
    (hE : ∀ n, 0 ≤ E n)
    (hstage : ∀ n k, stageCost n k ≤ d (n + k)) (n k : ℕ) :
    rowRadius C d n + E n * stageCost n k ≤
      rowRadius (combinedConversion C E) d n := by
  have ht := stageCost_le_tail hsum hd hstage n k
  have htail0 := ShadowingTails.tail_nonneg (fun j ↦ hd (n + j)) 0
  unfold rowRadius combinedConversion
  nlinarith [mul_le_mul_of_nonneg_left ht (hE n)]

/-- Distance form used by the selected enriched gauge certificate.  It
combines model-to-column shadowing with the exact terminal marking estimate
and returns the widened diagonal radius directly. -/
theorem terminalBase_dist_le_combinedRadius
    {M column terminal : Data} {C E d : ℕ → ℝ}
    {stageCost : ℕ → ℕ → ℝ}
    (hsum : Summable d) (hd : ∀ j, 0 ≤ d j)
    (hE : ∀ n, 0 ≤ E n)
    (hstage : ∀ n k, stageCost n k ≤ d (n + k)) {n k : ℕ}
    (hcolumn : dist M column ≤ rowRadius C d n)
    (hendpoint : dist column terminal ≤ E n * stageCost n k) :
    dist M terminal ≤ rowRadius (combinedConversion C E) d n := by
  exact (dist_triangle M column terminal).trans
    ((add_le_add hcolumn hendpoint).trans
      (columnRadius_add_endpoint_le_combinedRadius hsum hd hE hstage n k))

end ConfiguredGaugeEndpointLinearRadius
