import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierClosing
import UnitTangentIterates.GeometricCountableNormalTailSchedule
import UnitTangentIterates.GeometricScheduledACTail

/-!
# Configured geometric schedule for the multiplier recost tail

The public closing error is exponentially small in the configured separation,
and separation grows by at least `deltaStep` at every index.  Consequently each
row has a geometric majorant `C (q^2)^k`, exactly in the form consumed by
`GeometricCountableNormalTailSchedule`.
-/

noncomputable section

open MarkedSpace PathMetric PathMetric.NormalPath

namespace ConfiguredRecursiveEdgeRecostMultiplierCountableTailSchedule

open ConfiguredRecursiveEdgeFullRecostMetricDiagonal
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeFiniteColumnScalarClosing
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgeFinitePresentedPaperCapstone
  ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal
  ConfiguredRecursiveEdgeRecostScaledPaperCapstone
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  ConstructedConfiguredInductiveTubeBudget.WeightedData

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}
  {O : GaugeOutput J}

/-- Every final row error has a positive geometric majorant. -/
theorem exists_error_geometric_bound
    (R : RecostClosingOutput J O) (n : ℕ) :
    ∃ C q : ℝ, 0 < C ∧ 0 < q ∧ q < 1 ∧
      ∀ k, R.error n k ≤ C * (q ^ 2) ^ k := by
  obtain ⟨beta, K, hbeta, hK, hdiag⟩ :=
    exists_fullRecostMetricDiagonal_exp_bound O.data
      (E0 := distortionTotal) (C0 := physicalTransitionCeilings.C0)
      (C1 := physicalTransitionCeilings.C1)
      (C2 := physicalTransitionCeilings.C2)
      choice.MA0_nonnegative choice.NA0_nonnegative J.scalar.Mend_positive.le
  let s : ℕ := R.preShift + R.large.N + n
  let q : ℝ := Real.exp (-(beta * O.data.deltaStep / 2))
  let C : ℝ := (K + 1) * Real.exp (-(beta * O.data.Hs s))
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    have := O.data.deltaStep_pos
    nlinarith
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by linarith) (Real.exp_pos _)
  refine ⟨C, q, hC, hq0, hq1, fun k => ?_⟩
  have hsep : O.data.Hs s + k * O.data.deltaStep ≤ O.data.Hs (s + k) := by
    induction k with
    | zero => simp
    | succ k ih =>
        have hs := O.data.separation_step (s + k)
        calc
          O.data.Hs s + (↑(k + 1) : ℝ) * O.data.deltaStep =
              (O.data.Hs s + (k : ℝ) * O.data.deltaStep) +
                O.data.deltaStep := by push_cast; ring
          _ ≤ O.data.Hs (s + k) + O.data.deltaStep := by linarith
          _ ≤ O.data.Hs (s + (k + 1)) := by
            simpa [Nat.add_assoc] using hs
  have hexp : Real.exp (-(beta * O.data.Hs (s + k))) ≤
      Real.exp (-(beta * O.data.Hs s)) * q ^ (2 * k) := by
    have hle : Real.exp (-(beta * O.data.Hs (s + k))) ≤
        Real.exp (-(beta * (O.data.Hs s + k * O.data.deltaStep))) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hsep hbeta.le
      linarith
    calc
      Real.exp (-(beta * O.data.Hs (s + k))) ≤
          Real.exp (-(beta * (O.data.Hs s + k * O.data.deltaStep))) := hle
      _ = Real.exp (-(beta * O.data.Hs s)) * q ^ (2 * k) := by
        dsimp [q]
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        push_cast
        ring
  have hraw : R.error n k ≤
      K * Real.exp (-(beta * O.data.Hs (s + k))) := by
    rw [R.error_eq_multiplierDiagonal]
    simpa [s, Nat.add_assoc] using hdiag (s + k)
  calc
    R.error n k ≤ K * Real.exp (-(beta * O.data.Hs (s + k))) := hraw
    _ ≤ K * (Real.exp (-(beta * O.data.Hs s)) * q ^ (2 * k)) :=
      mul_le_mul_of_nonneg_left hexp hK
    _ ≤ (K + 1) * Real.exp (-(beta * O.data.Hs s)) * q ^ (2 * k) := by
      have he : 0 ≤ Real.exp (-(beta * O.data.Hs s)) * q ^ (2 * k) := by positivity
      nlinarith
    _ = C * (q ^ 2) ^ k := by
      dsimp [C]
      rw [← pow_mul]

/-- The configured row paths admit bounded-speed representatives on a
summable geometric time schedule, with density vanishing at the endpoint. -/
theorem exists_slowPieces
    (R : RecostClosingOutput J O)
    {p : ℕ → MarkedSpace.Data}
    (step : ∀ k, NormalPath (p k) (p (k + 1)))
    (n : ℕ) (hcost : ∀ k, cost (step k) ≤ R.error n k) :
    ∃ C q : ℝ, Nonempty
      (GeometricCountableNormalTailSchedule.SlowPieces step C q) := by
  obtain ⟨C, q, hC, hq0, hq1, hgeo⟩ := exists_error_geometric_bound R n
  exact ⟨C, q,
    GeometricCountableNormalTailSchedule.exists_slowPieces
      step hC hq0 hq1 (fun k => (hcost k).trans (hgeo k))⟩

/-- Configured construction of the paper's countably concatenated
piecewise-smooth/absolutely-continuous terminal path.  The endpoint convergence
is the completion output of the concrete row construction; every quantitative
schedule and path-functional condition is selected here. -/
theorem exists_scheduledACTail
    (R : RecostClosingOutput J O)
    {p : ℕ → MarkedSpace.Data}
    (step : ∀ k, NormalPath (p k) (p (k + 1)))
    (n : ℕ) (hcost : ∀ k, cost (step k) ≤ R.error n k)
    (limit : MarkedSpace.Data)
    (hlim : Filter.Tendsto p Filter.atTop (nhds limit)) :
    ∃ C q : ℝ, Nonempty
      (GeometricScheduledACTail.Certificate step limit C q) := by
  obtain ⟨C, q, H⟩ := exists_slowPieces R step n hcost
  exact ⟨C, q, H.map fun S ↦ ⟨S, hlim⟩⟩

end ConfiguredRecursiveEdgeRecostMultiplierCountableTailSchedule
