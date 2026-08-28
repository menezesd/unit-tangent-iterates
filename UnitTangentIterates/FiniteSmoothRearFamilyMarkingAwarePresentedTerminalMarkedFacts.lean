import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedTerminalMarked

/-! # Physical and intrinsic facts for the marked terminal -/

noncomputable section

open Function Set MarkedSpace PathMetric RearTrack RearOwnArclength ArclengthInverse

namespace FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront GaugeMarkedDataOfRearFamily

variable {a b : Data} {Gamma : NormalPath a b}
  {P0 kh khat Qmax : ℝ}

def MarkedTerminal.physical
    {A : MarkingAwareSource Gamma P0 kh khat Qmax} (M : MarkedTerminal A) :
    ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts M.presented := by
  let psi := terminalAngle A
  let k := terminalCurvature A
  let kp := terminalCurvatureSpatial A
  have hcurve : ∀ x, HasDerivAt (ev M.presented)
      (Complex.exp (Complex.I * (psi x : ℂ))) x := by
    rw [M.ev_eq]
    exact (MarkingAwareSource.successorFrontCore A).front_frenet Gamma.T
  have hangle : ∀ x, HasDerivAt psi (k x) x :=
    (MarkingAwareSource.successorFrontCore A).angle_frenet Gamma.T
  have hcurv : ∀ x, HasDerivAt k (kp x) x := terminalCurvature_deriv A
  have hLip : ∀ x y, |k x - k y| ≤ A.kx * |x - y| := by
    intro x y
    have hkx0 : 0 ≤ A.kx := (A.Kx_nonnegative Gamma.T).trans (A.Kx_le Gamma.T)
    have hdiff : ∀ z ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ k z :=
      fun z _ ↦ (hcurv z).differentiableAt
    have hb : ∀ z ∈ (Set.univ : Set ℝ), ‖deriv k z‖ ≤ A.kx := by
      intro z _
      rw [(hcurv z).deriv, Real.norm_eq_abs]
      exact (A.Kx_bound Gamma.T z).trans (A.Kx_le Gamma.T)
    have H := Convex.norm_image_sub_le_of_norm_deriv_le
      hdiff hb convex_univ (mem_univ x) (mem_univ y)
    simpa [Real.norm_eq_abs, abs_sub_comm] using H
  exact
    { cq := terminalPeriod A
      kmin := 0
      dlt := M.dlt
      L := terminalPeriod A
      kb := rearKappa1 kh
      kL := A.kx
      Theta := psi
      curvature := k
      cq_pos := A.rear_period_pos Gamma.T
      tube := M.tube
      perim_eq := M.period_eq
      curve_frenet := hcurve
      angle_deriv := hangle
      curvature_bound := terminalCurvature_bound A
      curvature_lipschitz := hLip }

def MarkedTerminal.strict
    {A : MarkingAwareSource Gamma P0 kh khat Qmax} (M : MarkedTerminal A)
    (hK0 : ∀ s, 0 ≤ A.K Gamma.T s) :
    UnconditionalAssembly.LimitStrictnessDataH M.presented := by
  let psi := terminalAngle A
  let k := terminalCurvature A
  let kp := terminalCurvatureSpatial A
  have hcurve : ∀ x, HasDerivAt (ev M.presented)
      (Complex.exp (Complex.I * (psi x : ℂ))) x := by
    rw [M.ev_eq]
    exact (MarkingAwareSource.successorFrontCore A).front_frenet Gamma.T
  have hangle : ∀ x, HasDerivAt psi (k x) x :=
    (MarkingAwareSource.successorFrontCore A).angle_frenet Gamma.T
  have hcurv : ∀ x, HasDerivAt k (kp x) x := terminalCurvature_deriv A
  have hkper : Periodic k (perim M.presented) := by
    rw [M.period_eq]
    exact terminalCurvature_periodic A
  have hk0 : ∀ x, 0 ≤ k x := terminalCurvature_nonnegative A
  have hkne : ∃ x, k x ≠ 0 :=
    ⟨0, ne_of_gt (terminalCurvature_positive A hK0 0)⟩
  have hnext : ∀ x,
      0 ≤ (k x + kp x / (1 + k x ^ 2)) / Real.sqrt (1 + k x ^ 2) := by
    intro x
    let z := A.delta Gamma.T (A.sf Gamma.T x)
    let K := A.K Gamma.T (A.sf Gamma.T x)
    have hz0 : 0 ≤ z := A.strip_nonnegative Gamma.T (A.sf Gamma.T x)
    have hz1 : z ≤ Real.arcsin kh := A.strip_le Gamma.T (A.sf Gamma.T x)
    have hcpos : 0 < Real.cos z := SelectedPathData.cos_steering_pos
      A.kh_nonnegative A.kh_lt_one (fun _ ↦ hz0) (fun _ ↦ hz1) 0
    have hc : Real.cos z ≠ 0 := hcpos.ne'
    have htrig := Real.sin_sq_add_cos_sq z
    have hsquare : (1 / Real.cos z) ^ 2 = 1 + Real.tan z ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
      nlinarith
    have hsqrt : Real.sqrt (1 + Real.tan z ^ 2) = 1 / Real.cos z := by
      have hs0 := Real.sqrt_nonneg (1 + Real.tan z ^ 2)
      have hi0 : 0 ≤ 1 / Real.cos z := (one_div_pos.mpr hcpos).le
      have hs2 := Real.sq_sqrt (show 0 ≤ 1 + Real.tan z ^ 2 by positivity)
      nlinarith
    have heq :
        (Real.tan z + ((K - Real.sin z) / Real.cos z ^ 3) /
            (1 + Real.tan z ^ 2)) /
          Real.sqrt (1 + Real.tan z ^ 2) = K := by
      rw [hsqrt, Real.tan_eq_sin_div_cos]
      field_simp
      linear_combination (Real.sin z - K) * htrig
    change 0 ≤ (Real.tan z + ((K - Real.sin z) / Real.cos z ^ 3) /
      (1 + Real.tan z ^ 2)) / Real.sqrt (1 + Real.tan z ^ 2)
    rw [heq]
    exact hK0 (A.sf Gamma.T x)
  let D : UnconditionalAssembly.LimitStrictnessData M.presented :=
    { theta := psi
      k := k
      k' := kp
      curve_deriv := hcurve
      angle_deriv := hangle
      curvature_deriv := hcurv
      curvature_periodic := hkper
      curvature_nonnegative := hk0
      next_nonnegative := hnext
      curvature_nonzero := hkne }
  exact D.toH (fun x ↦ (hcurv x).differentiableAt)

theorem MarkedTerminal.tangent_range
    {A : MarkingAwareSource Gamma P0 kh khat Qmax} (M : MarkedTerminal A) :
    range (UnitTangent.unitTangentMap (ev M.presented)) =
      range (A.F Gamma.T) := by
  let psi := terminalAngle A
  have hcurve : ∀ x, HasDerivAt (ev M.presented)
      (Complex.exp (Complex.I * (psi x : ℂ))) x := by
    rw [M.ev_eq]
    exact (MarkingAwareSource.successorFrontCore A).front_frenet Gamma.T
  have hdc : Continuous (A.delta Gamma.T) :=
    A.steering_contDiff.continuous.comp
      (continuous_const.prodMk continuous_id)
  have hsfsurj : Surjective (A.sf Gamma.T) := by
    intro s
    refine ⟨rearArclength (A.delta Gamma.T) s, ?_⟩
    have hcpos : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by
      nlinarith [A.kh_nonnegative, A.kh_lt_one])
    have hcos : ∀ z, Real.sqrt (1 - kh ^ 2) ≤
        Real.cos (A.delta Gamma.T z) := fun z ↦
      Shadowing.cos_ge_of_mem_strip (A.strip_nonnegative Gamma.T z)
        (A.strip_le Gamma.T z)
    have hmono : StrictMono (rearArclength (A.delta Gamma.T)) :=
      strictMono_of_deriv_ge hcpos
        (fun z ↦ hasDerivAt_rearArclength hdc z) hcos
    exact leftInverse_of_rightInverse hmono.injective
      (A.sf_rightInverse Gamma.T) s
  have hpoint : ∀ x, UnitTangent.unitTangentMap (ev M.presented) x =
      A.F Gamma.T (A.sf Gamma.T x) := by
    intro x
    rw [UnitTangent.unitTangentMap, (hcurve x).deriv, M.ev_eq]
    change rearTrack (A.F Gamma.T) (A.Theta Gamma.T) (A.delta Gamma.T)
        (A.sf Gamma.T x) +
      Complex.exp (Complex.I *
        (rearAngle (A.Theta Gamma.T) (A.delta Gamma.T)
          (A.sf Gamma.T x) : ℂ)) = A.F Gamma.T (A.sf Gamma.T x)
    exact RearTrack.unitTangentMap_rearTrack _
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨A.sf Gamma.T x, (hpoint x).symm⟩
  · rintro _ ⟨s, rfl⟩
    obtain ⟨x, rfl⟩ := hsfsurj s
    exact ⟨x, hpoint x⟩

end FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
