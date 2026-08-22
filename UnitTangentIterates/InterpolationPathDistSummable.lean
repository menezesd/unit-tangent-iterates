import Mathlib
import UnitTangentIterates.InterpolationPathDistL1

/-!
# Summable path distances from an exponential `L¹` matching

The shadowing scheme of *A Noncircular Oval with Convex Unit-Tangent Iterates*
consumes a **summable** sequence of defects.  What the theorem
*Curvature-measure matching* produces is an exponentially small `L¹` distance
`εₙ ≤ Cρⁿ` of consecutive curvatures, and `InterpolationPathDistL1.lean` turns
such a distance into a bound for the marked path pseudodistance.  This file
shows that those bounds are summable.

The cost `interpPathCost` of the interpolation is a polynomial in the `L¹`
distance `ε` and the sup distance `d`, with no constant term, multiplied by
exponentials of quantities increasing in `ε`; so on a window `0 ≤ ε ≤ ε₀` it is
dominated by an affine expression `A·ε + B·d` with explicit coefficients
(`interpPathCost_le_affine`).  Substituting for `d` the modulus produced by the
`L¹` distance gives the bound

`interpCostL1 = A·ε + B·(√(4k'ε) + 4ε/L)`  (`pathDist_le_interpCostL1`),

whose square-root term is what makes summability a real statement: a merely
summable sequence `εₙ` need not give a summable `√εₙ`, whereas a geometric one
does, since `√(Cρⁿ) = √C(√ρ)ⁿ` (`summable_interpCostL1_of_geometric`).
-/

noncomputable section

open Real MeasureTheory Set MarkedSpace MarkedTopology PathMetric

namespace InterpolationPathDistSummable

open CurvatureInterpolation InterpolationEstimate InterpolationFrame
  InterpolationPathDist InterpolationPathDistL1

variable {L : ℝ}

/-! ### An affine bound for the cost -/

/-- The coefficient of the `L¹` distance in the affine bound for the cost, on
the window `0 ≤ ε ≤ ε₀`. -/
def costEpsCoeff (kstar kd L eps0 : ℝ) : ℝ :=
  (3/2) * L + Real.exp (rate1Bound kstar L eps0) * ((3/2) * L)
    + (1 + (3/2) * kstar * L) * (2 * L * Real.exp (rate1Bound kstar L eps0))
    + (kd + kstar ^ 2) * ((3/2) * L) * (2 * L * Real.exp (rate1Bound kstar L eps0)) ^ 2
    + (1 + (3/2) * kstar * L) * (rate2Bound kstar kd L eps0 * (2 * L) ^ 2
        * Real.exp (2 * rate1Bound kstar L eps0))

/-- The coefficient of the sup distance in the affine bound for the cost. -/
def costSupCoeff (kstar L eps0 : ℝ) : ℝ := (2 * L * Real.exp (rate1Bound kstar L eps0)) ^ 2

theorem costEpsCoeff_nonneg {kstar kd L eps0 : ℝ} (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd)
    (hL : 0 ≤ L) (heps0 : 0 ≤ eps0) : 0 ≤ costEpsCoeff kstar kd L eps0 := by
  have h2 : 0 ≤ rate2Bound kstar kd L eps0 := by
    unfold rate2Bound; positivity
  unfold costEpsCoeff
  positivity

theorem costSupCoeff_nonneg {kstar L eps0 : ℝ} : 0 ≤ costSupCoeff kstar L eps0 := by
  unfold costSupCoeff; positivity

/-- **The cost is dominated by an affine expression in the two smallness
parameters** on any window `0 ≤ ε ≤ ε₀`. -/
theorem interpPathCost_le_affine {kstar kd dsup L eps eps0 : ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hL : 0 ≤ L) (hdsup : 0 ≤ dsup)
    (heps : 0 ≤ eps) (hle : eps ≤ eps0) :
    interpPathCost kstar kd dsup L eps
      ≤ costEpsCoeff kstar kd L eps0 * eps + costSupCoeff kstar L eps0 * dsup := by
  have heps0 : 0 ≤ eps0 := le_trans heps hle
  have hLe : (0:ℝ) ≤ (3/2) * L * eps := by positivity
  have hcoef : (0:ℝ) ≤ 1 + (3/2) * kstar * L := by positivity
  -- monotonicity of the two rate bounds in the `L¹` distance
  have hr1 : rate1Bound kstar L eps ≤ rate1Bound kstar L eps0 := by
    unfold rate1Bound
    nlinarith [mul_nonneg (mul_nonneg hkstar hL) (sub_nonneg.mpr hle)]
  have hr2 : rate2Bound kstar kd L eps ≤ rate2Bound kstar kd L eps0 := by
    unfold rate2Bound
    nlinarith [mul_nonneg (mul_nonneg hkd hL) (sub_nonneg.mpr hle),
      mul_nonneg hkstar (sub_nonneg.mpr hle),
      mul_nonneg (mul_nonneg (mul_nonneg hkstar hkstar) hL) (sub_nonneg.mpr hle)]
  have hr2nn : 0 ≤ rate2Bound kstar kd L eps := by unfold rate2Bound; positivity
  set E : ℝ := Real.exp (rate1Bound kstar L eps) with hE
  set E0 : ℝ := Real.exp (rate1Bound kstar L eps0) with hE0
  have hEle : E ≤ E0 := Real.exp_le_exp.mpr hr1
  have hEpos : 0 < E := Real.exp_pos _
  have hE0pos : 0 < E0 := Real.exp_pos _
  have hmul : 2 * L * E ≤ 2 * L * E0 :=
    mul_le_mul_of_nonneg_left hEle (by positivity)
  have hsq : (2 * L * E) ^ 2 ≤ (2 * L * E0) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmul)
      (by positivity : (0:ℝ) ≤ 2 * L * E0 + 2 * L * E)]
  have hexp2 : Real.exp (2 * rate1Bound kstar L eps)
      ≤ Real.exp (2 * rate1Bound kstar L eps0) := Real.exp_le_exp.mpr (by linarith)
  have hprod : rate2Bound kstar kd L eps * Real.exp (2 * rate1Bound kstar L eps)
      ≤ rate2Bound kstar kd L eps0 * Real.exp (2 * rate1Bound kstar L eps0) :=
    mul_le_mul hr2 hexp2 (Real.exp_pos _).le (le_trans hr2nn hr2)
  -- the four terms of the cost, bounded one at a time
  have h2 : costTermW kstar L eps ≤ E0 * ((3/2) * L) * eps := by
    unfold costTermW costE
    nlinarith [mul_nonneg (sub_nonneg.mpr hEle) hLe]
  have h3 : costTermS1 kstar L eps ≤ (1 + (3/2) * kstar * L) * (2 * L * E0) * eps := by
    unfold costTermS1 costG1 costFac
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hcoef heps) (by positivity : (0:ℝ) ≤ 2 * L))
      (sub_nonneg.mpr hEle)]
  have h4 : costTermS2 kstar kd dsup L eps
      ≤ (kd + kstar ^ 2) * ((3/2) * L) * (2 * L * E0) ^ 2 * eps
        + (2 * L * E0) ^ 2 * dsup
        + (1 + (3/2) * kstar * L)
            * (rate2Bound kstar kd L eps0 * (2 * L) ^ 2
              * Real.exp (2 * rate1Bound kstar L eps0)) * eps := by
    unfold costTermS2 costG2 costG1 costFac costE
    have hpart1 : (dsup + (kd + kstar ^ 2) * ((3/2) * L * eps)) * (2 * L * E) ^ 2
        ≤ (kd + kstar ^ 2) * ((3/2) * L) * (2 * L * E0) ^ 2 * eps
          + (2 * L * E0) ^ 2 * dsup := by
      nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ dsup + (kd + kstar ^ 2) * ((3/2) * L * eps))
        (sub_nonneg.mpr hsq)]
    have hpart2 : (1 + (3/2) * kstar * L) * eps
          * (rate2Bound kstar kd L eps * (2 * L) ^ 2 * Real.exp (2 * rate1Bound kstar L eps))
        ≤ (1 + (3/2) * kstar * L)
            * (rate2Bound kstar kd L eps0 * (2 * L) ^ 2
              * Real.exp (2 * rate1Bound kstar L eps0)) * eps := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hcoef heps)
        (by positivity : (0:ℝ) ≤ (2 * L) ^ 2)) (sub_nonneg.mpr hprod)]
    linarith
  have hexpand : costEpsCoeff kstar kd L eps0 * eps + costSupCoeff kstar L eps0 * dsup
      = (3/2) * L * eps + E0 * ((3/2) * L) * eps
        + (1 + (3/2) * kstar * L) * (2 * L * E0) * eps
        + ((kd + kstar ^ 2) * ((3/2) * L) * (2 * L * E0) ^ 2 * eps
          + (2 * L * E0) ^ 2 * dsup
          + (1 + (3/2) * kstar * L)
              * (rate2Bound kstar kd L eps0 * (2 * L) ^ 2
                * Real.exp (2 * rate1Bound kstar L eps0)) * eps) := by
    unfold costEpsCoeff costSupCoeff
    rw [← hE0]
    ring
  unfold interpPathCost costE
  rw [hexpand]
  linarith

/-! ### The bound in terms of the `L¹` distance alone -/

/-- The explicit bound for the path pseudodistance in terms of the `L¹`
distance `ε` of the two curvatures alone. -/
def interpCostL1 (kstar kd L eps0 eps : ℝ) : ℝ :=
  costEpsCoeff kstar kd L eps0 * eps
    + costSupCoeff kstar L eps0 * (Real.sqrt (4 * kd * eps) + 4 * eps / L)

/-- **The path-distance bound in terms of the `L¹` distance alone.** -/
theorem pathDist_le_interpCostL1 {k0 k1 k0' k1' : ℝ → ℝ} {θ₀ kstar kd eps0 : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L) (hkd : 0 < kd)
    (hkstar : 0 ≤ kstar)
    (hd0 : ∀ r, HasDerivAt k0 (k0' r) r) (hd1 : ∀ r, HasDerivAt k1 (k1' r) r)
    (hkd0 : ∀ r, |k0' r| ≤ kd) (hkd1 : ∀ r, |k1' r| ≤ kd)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar)
    (hle : curvDist k0 k1 L ≤ eps0) :
    ∃ psi : ℝ → ℝ, Continuous psi ∧ (∀ u, psi (u + 1) = psi u + 2 * L) ∧
      ∀ p q : Data, (∀ u, p.1 u = interpCurve k0 θ₀ L (2 * L * u)) →
        (∀ u, q.1 u = interpCurve k1 θ₀ L (psi u)) →
        pathDist p q ≤ interpCostL1 kstar kd L eps0 (curvDist k0 k1 L) := by
  obtain ⟨psi, hcont, htrans, hbound⟩ :=
    InterpolationPathDistL1.pathDist_le_interpPathCost_of_L1 (θ₀ := θ₀) (kstar := kstar)
      (kd := kd) hk0 hk1 hk0'c hk1'c hper0 hper1 htot0 htot1 hL hkd hd0 hd1 hkd0 hkd1
      hk0nn hk1nn hk0le hk1le
  refine ⟨psi, hcont, htrans, fun p q hp hq => le_trans (hbound p q hp hq) ?_⟩
  set eps : ℝ := curvDist k0 k1 L with hepsdef
  have hepsnn : 0 ≤ eps := InterpolationNormal.integral_abs_sub_nonneg hk0 hk1 hL.le
  have hmodnn : 0 ≤ CurvatureStabilityL1.l1Modulus (2 * kd) eps L :=
    CurvatureStabilityL1.l1Modulus_nonneg _ _ _
  have hmod : CurvatureStabilityL1.l1Modulus (2 * kd) eps L
      ≤ Real.sqrt (4 * kd * eps) + 4 * eps / L := by
    have hsqrt : Real.sqrt (2 * (2 * kd) * eps) = Real.sqrt (4 * kd * eps) := by
      rw [show 2 * (2 * kd) * eps = 4 * kd * eps by ring]
    have hdiv : (0:ℝ) ≤ 4 * eps / L := div_nonneg (by linarith) hL.le
    rw [CurvatureStabilityL1.l1Modulus, hsqrt]
    exact max_le (le_add_of_nonneg_right hdiv)
      (le_add_of_nonneg_left (Real.sqrt_nonneg _))
  have haffine := interpPathCost_le_affine (kstar := kstar) (kd := kd)
    (dsup := CurvatureStabilityL1.l1Modulus (2 * kd) eps L) (L := L) (eps := eps) (eps0 := eps0)
    hkstar hkd.le hL.le hmodnn hepsnn hle
  have hsup : costSupCoeff kstar L eps0 * CurvatureStabilityL1.l1Modulus (2 * kd) eps L
      ≤ costSupCoeff kstar L eps0 * (Real.sqrt (4 * kd * eps) + 4 * eps / L) :=
    mul_le_mul_of_nonneg_left hmod costSupCoeff_nonneg
  unfold interpCostL1
  linarith

/-! ### Summability -/

/-- **The bounds are summable along a geometric sequence of `L¹` distances.**
If `0 ≤ εₙ ≤ Cρⁿ` with `0 ≤ ρ < 1`, then the sequence of cost bounds is
summable — the square-root term contributing the geometric series of ratio
`√ρ`. -/
theorem summable_interpCostL1_of_geometric {kstar kd L eps0 C rho : ℝ} {eps : ℕ → ℝ}
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hL : 0 < L) (heps0 : 0 ≤ eps0)
    (hC : 0 ≤ C) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hnn : ∀ n, 0 ≤ eps n) (hbd : ∀ n, eps n ≤ C * rho ^ n) :
    Summable fun n => interpCostL1 kstar kd L eps0 (eps n) := by
  have hA : 0 ≤ costEpsCoeff kstar kd L eps0 := costEpsCoeff_nonneg hkstar hkd hL.le heps0
  have hB : 0 ≤ costSupCoeff kstar L eps0 := costSupCoeff_nonneg
  have hsqrtpow : ∀ n : ℕ, Real.sqrt (rho ^ n) = Real.sqrt rho ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hrho0 k), ih, pow_succ]
  have hrhosum : Summable fun n : ℕ => rho ^ n := summable_geometric_of_lt_one hrho0 hrho1
  have hsqrtrho : Real.sqrt rho < 1 := by
    have h := Real.sqrt_lt_sqrt hrho0 hrho1
    rwa [Real.sqrt_one] at h
  have hsqrtsum : Summable fun n : ℕ => Real.sqrt rho ^ n :=
    summable_geometric_of_lt_one (Real.sqrt_nonneg _) hsqrtrho
  -- the majorant
  have hmaj : Summable fun n : ℕ =>
      costEpsCoeff kstar kd L eps0 * (C * rho ^ n)
        + costSupCoeff kstar L eps0
          * (Real.sqrt (4 * kd * C) * Real.sqrt rho ^ n + 4 * (C * rho ^ n) / L) := by
    have h1 : Summable fun n : ℕ => costEpsCoeff kstar kd L eps0 * (C * rho ^ n) := by
      simpa [mul_assoc] using (hrhosum.mul_left (costEpsCoeff kstar kd L eps0 * C))
    have h2 : Summable fun n : ℕ =>
        costSupCoeff kstar L eps0 * (Real.sqrt (4 * kd * C) * Real.sqrt rho ^ n) := by
      simpa [mul_assoc] using
        (hsqrtsum.mul_left (costSupCoeff kstar L eps0 * Real.sqrt (4 * kd * C)))
    have h3 : Summable fun n : ℕ => costSupCoeff kstar L eps0 * (4 * (C * rho ^ n) / L) := by
      have := hrhosum.mul_left (costSupCoeff kstar L eps0 * (4 * C / L))
      refine this.congr (fun n => ?_)
      field_simp
    have := (h1.add h2).add h3
    refine this.congr (fun n => ?_)
    ring
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · have h1 : 0 ≤ eps n := hnn n
    have h2 : (0:ℝ) ≤ Real.sqrt (4 * kd * eps n) + 4 * eps n / L :=
      add_nonneg (Real.sqrt_nonneg _) (div_nonneg (by linarith) hL.le)
    unfold interpCostL1
    have := mul_nonneg hA h1
    have := mul_nonneg hB h2
    linarith
  · have h1 : 0 ≤ eps n := hnn n
    have hb : eps n ≤ C * rho ^ n := hbd n
    have hsq : Real.sqrt (4 * kd * eps n) ≤ Real.sqrt (4 * kd * C) * Real.sqrt rho ^ n := by
      have h4 : (0:ℝ) ≤ 4 * kd := by linarith
      have hmono : Real.sqrt (4 * kd * eps n) ≤ Real.sqrt (4 * kd * (C * rho ^ n)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hb h4)
      have hkdC : (0:ℝ) ≤ 4 * kd * C := mul_nonneg h4 hC
      have hsplit : Real.sqrt (4 * kd * (C * rho ^ n))
          = Real.sqrt (4 * kd * C) * Real.sqrt rho ^ n := by
        rw [(show 4 * kd * (C * rho ^ n) = (4 * kd * C) * rho ^ n by ring),
          Real.sqrt_mul hkdC, hsqrtpow]
      rw [hsplit] at hmono
      exact hmono
    have hdiv : 4 * eps n / L ≤ 4 * (C * rho ^ n) / L := by gcongr
    unfold interpCostL1
    have hle1 : costEpsCoeff kstar kd L eps0 * eps n
        ≤ costEpsCoeff kstar kd L eps0 * (C * rho ^ n) := mul_le_mul_of_nonneg_left hb hA
    have hle2 : costSupCoeff kstar L eps0 * (Real.sqrt (4 * kd * eps n) + 4 * eps n / L)
        ≤ costSupCoeff kstar L eps0
          * (Real.sqrt (4 * kd * C) * Real.sqrt rho ^ n + 4 * (C * rho ^ n) / L) :=
      mul_le_mul_of_nonneg_left (by linarith) hB
    linarith

/-- **Exponentially matched curvatures give summable path distances.**  Let
`κₙ` be admissible curvatures of a common half-perimeter `L` — continuous,
`L`-periodic, of total curvature `π`, pinched by `0 ≤ κₙ ≤ κ_*` and with
derivatives bounded by `k'` — whose consecutive `L¹` distances decay
geometrically, `‖κₙ₊₁ − κₙ‖_{L¹(0,L)} ≤ Cρⁿ` with `ρ < 1`.  Then the marked
ovals they define are joined by finite path pseudodistances whose sum
converges: this is the summability hypothesis the shadowing scheme consumes. -/
theorem summable_pathDist_of_geometric_L1 {kap kap' : ℕ → ℝ → ℝ} {θ₀ kstar kd C rho : ℝ}
    (hk : ∀ n, Continuous (kap n)) (hk' : ∀ n, Continuous (kap' n))
    (hper : ∀ n, Function.Periodic (kap n) L)
    (htot : ∀ n, (∫ r in (0:ℝ)..L, kap n r) = Real.pi)
    (hL : 0 < L) (hkd : 0 < kd) (hkstar : 0 ≤ kstar)
    (hderiv : ∀ n r, HasDerivAt (kap n) (kap' n r) r)
    (hbdd : ∀ n r, |kap' n r| ≤ kd)
    (hnn : ∀ n r, 0 ≤ kap n r) (hle : ∀ n r, kap n r ≤ kstar)
    (hC : 0 ≤ C) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hgeom : ∀ n, curvDist (kap n) (kap (n + 1)) L ≤ C * rho ^ n) :
    ∃ psi : ℕ → ℝ → ℝ, (∀ n, Continuous (psi n)) ∧
      (∀ n u, psi n (u + 1) = psi n u + 2 * L) ∧
      ∀ p q : ℕ → Data,
        (∀ n u, (p n).1 u = interpCurve (kap n) θ₀ L (2 * L * u)) →
        (∀ n u, (q n).1 u = interpCurve (kap (n + 1)) θ₀ L (psi n u)) →
        Summable fun n => pathDist (p n) (q n) := by
  have hrhopow : ∀ n : ℕ, rho ^ n ≤ 1 := fun n => pow_le_one₀ hrho0 hrho1.le
  have hbound : ∀ n, curvDist (kap n) (kap (n + 1)) L ≤ C := by
    intro n
    refine le_trans (hgeom n) ?_
    nlinarith [hrhopow n]
  have H : ∀ n : ℕ, ∃ psi : ℝ → ℝ, Continuous psi ∧ (∀ u, psi (u + 1) = psi u + 2 * L) ∧
      ∀ p q : Data, (∀ u, p.1 u = interpCurve (kap n) θ₀ L (2 * L * u)) →
        (∀ u, q.1 u = interpCurve (kap (n + 1)) θ₀ L (psi u)) →
        pathDist p q ≤ interpCostL1 kstar kd L C (curvDist (kap n) (kap (n + 1)) L) :=
    fun n => pathDist_le_interpCostL1 (θ₀ := θ₀) (kstar := kstar) (kd := kd) (eps0 := C)
      (hk n) (hk (n + 1)) (hk' n) (hk' (n + 1)) (hper n) (hper (n + 1)) (htot n) (htot (n + 1))
      hL hkd hkstar (hderiv n) (hderiv (n + 1)) (hbdd n) (hbdd (n + 1))
      (hnn n) (hnn (n + 1)) (hle n) (hle (n + 1)) (hbound n)
  choose psi hcont htrans hmain using H
  refine ⟨psi, hcont, htrans, fun p q hp hq => ?_⟩
  refine Summable.of_nonneg_of_le (fun n => pathDist_nonneg _ _)
    (fun n => hmain n (p n) (q n) (hp n) (hq n)) ?_
  exact summable_interpCostL1_of_geometric (eps := fun n => curvDist (kap n) (kap (n + 1)) L)
    hkstar hkd.le hL hC hC hrho0 hrho1
    (fun n => InterpolationNormal.integral_abs_sub_nonneg (hk n) (hk (n + 1)) hL.le) hgeom

/-- **The exponential form: the matching estimate of the paper.**  If the
`L¹` distances of consecutive curvatures obey `εₙ ≤ Ce^{−βHₙ}` with separations
growing at least linearly, `Hₙ ≥ H₀ + nh` with `h > 0`, then they decay
geometrically, and the path pseudodistances of the corresponding marked ovals
are summable. -/
theorem summable_pathDist_of_exponential_matching {kap kap' : ℕ → ℝ → ℝ}
    {θ₀ kstar kd C beta h H0 : ℝ} {Hs : ℕ → ℝ}
    (hk : ∀ n, Continuous (kap n)) (hk' : ∀ n, Continuous (kap' n))
    (hper : ∀ n, Function.Periodic (kap n) L)
    (htot : ∀ n, (∫ r in (0:ℝ)..L, kap n r) = Real.pi)
    (hL : 0 < L) (hkd : 0 < kd) (hkstar : 0 ≤ kstar)
    (hderiv : ∀ n r, HasDerivAt (kap n) (kap' n r) r)
    (hbdd : ∀ n r, |kap' n r| ≤ kd)
    (hnn : ∀ n r, 0 ≤ kap n r) (hle : ∀ n r, kap n r ≤ kstar)
    (hC : 0 ≤ C) (hbeta : 0 < beta) (hh : 0 < h)
    (hHs : ∀ n : ℕ, H0 + n * h ≤ Hs n)
    (hmatch : ∀ n, curvDist (kap n) (kap (n + 1)) L ≤ C * Real.exp (-(beta * Hs n))) :
    ∃ psi : ℕ → ℝ → ℝ, (∀ n, Continuous (psi n)) ∧
      (∀ n u, psi n (u + 1) = psi n u + 2 * L) ∧
      ∀ p q : ℕ → Data,
        (∀ n u, (p n).1 u = interpCurve (kap n) θ₀ L (2 * L * u)) →
        (∀ n u, (q n).1 u = interpCurve (kap (n + 1)) θ₀ L (psi n u)) →
        Summable fun n => pathDist (p n) (q n) := by
  have hrho1 : Real.exp (-(beta * h)) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  refine summable_pathDist_of_geometric_L1 (C := C * Real.exp (-(beta * H0)))
    (rho := Real.exp (-(beta * h))) hk hk' hper htot hL hkd hkstar hderiv hbdd hnn hle
    (by positivity) (Real.exp_pos _).le hrho1 (fun n => ?_)
  refine le_trans (hmatch n) ?_
  have hexp : Real.exp (-(beta * Hs n)) ≤ Real.exp (-(beta * (H0 + n * h))) :=
    Real.exp_le_exp.mpr (by nlinarith [hHs n])
  have hsplit : Real.exp (-(beta * (H0 + n * h)))
      = Real.exp (-(beta * H0)) * Real.exp (-(beta * h)) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf
  calc C * Real.exp (-(beta * Hs n)) ≤ C * Real.exp (-(beta * (H0 + n * h))) :=
        mul_le_mul_of_nonneg_left hexp hC
    _ = C * Real.exp (-(beta * H0)) * Real.exp (-(beta * h)) ^ n := by rw [hsplit]; ring

/-! ### Non-vacuity of the summability hypotheses -/

/-- **The hypotheses of the summability theorem are satisfiable by a genuinely
moving sequence of ovals.**  The curvatures `1/2 + (1/4)(1/2)ⁿ cos s`, of common
half-perimeter `2π`, are admissible, pairwise distinct, and their consecutive
`L¹` distances decay geometrically. -/
theorem summable_pathDist_hypotheses_nonvacuous :
    ∃ (kap kap' : ℕ → ℝ → ℝ) (C rho : ℝ),
      (∀ n, Continuous (kap n)) ∧ (∀ n, Continuous (kap' n)) ∧
      (∀ n, Function.Periodic (kap n) (2 * Real.pi)) ∧
      (∀ n, (∫ r in (0:ℝ)..(2 * Real.pi), kap n r) = Real.pi) ∧
      (∀ n r, HasDerivAt (kap n) (kap' n r) r) ∧ (∀ n r, |kap' n r| ≤ 1/4) ∧
      (∀ n r, 0 ≤ kap n r) ∧ (∀ n r, kap n r ≤ 3/4) ∧
      0 ≤ C ∧ 0 ≤ rho ∧ rho < 1 ∧
      (∀ n, curvDist (kap n) (kap (n + 1)) (2 * Real.pi) ≤ C * rho ^ n) ∧
      (∀ n, kap n ≠ kap (n + 1)) := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  set c : ℕ → ℝ := fun n => (1/4) * (1/2 : ℝ) ^ n with hc
  have hcpos : ∀ n, 0 < c n := fun n => by positivity
  have hcle : ∀ n, c n ≤ 1/4 := by
    intro n
    have h : (1/2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    simp only [hc]
    linarith
  refine ⟨fun n => kwaveAmp (c n), fun n => kwaveAmpDeriv (c n), Real.pi / 4, 1/2,
    fun n => continuous_kwaveAmp _, fun n => continuous_kwaveAmpDeriv _,
    fun n => kwaveAmp_periodic _, fun n => kwaveAmp_total _,
    fun n r => hasDerivAt_kwaveAmp _ _, ?_, ?_, ?_, by positivity, by norm_num, by norm_num,
    ?_, ?_⟩
  · intro n r
    have h1 := Real.neg_one_le_sin r
    have h2 := Real.sin_le_one r
    have h3 := (hcpos n).le
    have h4 := hcle n
    rw [abs_le]
    constructor <;> simp only [kwaveAmpDeriv] <;> nlinarith
  · intro n r
    have h1 := Real.neg_one_le_cos r
    have h3 := (hcpos n).le
    have h4 := hcle n
    simp only [kwaveAmp]
    nlinarith
  · intro n r
    have h2 := Real.cos_le_one r
    have h3 := (hcpos n).le
    have h4 := hcle n
    simp only [kwaveAmp]
    nlinarith
  · -- the geometric decay of the `L¹` distances
    intro n
    have hdiff : c n - c (n + 1) = (1/8) * (1/2 : ℝ) ^ n := by
      simp only [hc, pow_succ]
      ring
    have hmono : (∫ r in (0:ℝ)..(2 * Real.pi),
        |kwaveAmp (c (n + 1)) r - kwaveAmp (c n) r|)
          ≤ ∫ _ in (0:ℝ)..(2 * Real.pi), (1/8) * (1/2 : ℝ) ^ n := by
      refine intervalIntegral.integral_mono_on hpi.le
        (((continuous_kwaveAmp _).sub (continuous_kwaveAmp _)).abs.intervalIntegrable _ _)
        intervalIntegrable_const ?_
      intro r _
      have h1 := Real.neg_one_le_cos r
      have h2 := Real.cos_le_one r
      have h3 : (0:ℝ) < (1/2 : ℝ) ^ n := by positivity
      rw [abs_le]
      constructor <;> simp only [kwaveAmp] <;> nlinarith [hdiff]
    have hconst : (∫ _ in (0:ℝ)..(2 * Real.pi), (1/8) * (1/2 : ℝ) ^ n)
        = 2 * Real.pi * ((1/8) * (1/2 : ℝ) ^ n) := by
      simp
      ring
    have hle : curvDist (kwaveAmp (c n)) (kwaveAmp (c (n + 1))) (2 * Real.pi)
        ≤ 2 * Real.pi * ((1/8) * (1/2 : ℝ) ^ n) := by
      rw [← hconst]
      exact hmono
    calc curvDist (kwaveAmp (c n)) (kwaveAmp (c (n + 1))) (2 * Real.pi)
        ≤ 2 * Real.pi * ((1/8) * (1/2 : ℝ) ^ n) := hle
      _ = Real.pi / 4 * (1/2 : ℝ) ^ n := by ring
  · -- the curvatures really move
    intro n hEq
    have h := congrFun hEq 0
    simp only [kwaveAmp, Real.cos_zero, mul_one, add_right_inj] at h
    have hne : c n ≠ c (n + 1) := by
      simp only [hc, pow_succ]
      have : (0:ℝ) < (1/2 : ℝ) ^ n := by positivity
      intro hcc
      nlinarith
    exact hne h

end InterpolationPathDistSummable
