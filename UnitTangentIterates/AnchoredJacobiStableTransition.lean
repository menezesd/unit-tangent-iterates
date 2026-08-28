import UnitTangentIterates.JacobiPathGains
import UnitTangentIterates.ControlledJunctionPathFunctionalBounds

/-!
# Anchored Jacobi transitions and depth-uniform scalar propagation

This module composes the raw selected-rear Jacobi gains with the independent
fixed-spatial-junction estimates.  It then proves the scalar invariant used in
the paper: only the `W` distortion accumulates multiplicatively, while
`S0,S1,S2` are reset from the preceding lower components at every depth.
-/

noncomputable section

open Set MeasureTheory MarkedTopology

namespace AnchoredJacobiStableTransition

open ControlledJunctionPathFunctionalBounds

/-- The four path functionals attached to one normal-velocity field. -/
structure Components where
  w : ℝ
  s0 : ℝ
  s1 : ℝ
  s2 : ℝ

def components (eta : ℝ → ℝ → ℝ) : Components where
  w := W eta 1
  s0 := S 0 eta
  s1 := S 1 eta
  s2 := S 2 eta

structure Components.Nonnegative (x : Components) : Prop where
  w : 0 ≤ x.w
  s0 : 0 ≤ x.s0
  s1 : 0 ≤ x.s1
  s2 : 0 ≤ x.s2

/-- Raw, unanchored selected-rear estimates, in exactly the component form
proved by `JacobiPathGains`. -/
structure RawJacobiBounds
    (front rear : ℝ → ℝ → ℝ) (C0 C1 C2 : ℝ) : Prop where
  w : W rear 1 ≤ W front 1
  s0 : S 0 rear ≤ C0 * W front 1
  s1 : S 1 rear ≤ C1 * (W front 1 + S 0 front)
  s2 : S 2 rear ≤ C2 * (W front 1 + S 0 front + S 1 front)

/-- One selected-rear step followed by its fixed anchoring diffeomorphism. -/
structure Transition
    (x y : Components) (a MA NA C0 C1 C2 : ℝ) : Prop where
  w : y.w ≤ a * x.w
  s0 : y.s0 ≤ C0 * x.w
  s1 : y.s1 ≤ MA * C1 * (x.w + x.s0)
  s2 : y.s2 ≤ MA ^ 2 * C2 * (x.w + x.s0 + x.s1) +
    NA * C1 * (x.w + x.s0)

/-- Compose the raw Jacobi transition with a controlled fixed junction without
passing through the aggregate `reparamCostConst`. -/
theorem transition_of_rawJacobi_and_fixedReparam
    {front rear anchored : ℝ → ℝ → ℝ} {mA MA NA C0 C1 C2 : ℝ}
    (hmA : 0 < mA) (hMA : 0 ≤ MA) (hNA : 0 ≤ NA)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hfront : (components front).Nonnegative)
    (hraw : RawJacobiBounds front rear C0 C1 C2)
    (hanchor : FixedReparamBounds rear anchored mA MA NA) :
    Transition (components front) (components anchored) (1 / mA) MA NA C0 C1 C2 := by
  have ha0 : 0 ≤ (1 / mA) := by positivity
  refine
    { w := hanchor.w.trans (mul_le_mul_of_nonneg_left hraw.w ha0)
      s0 := hanchor.s0.trans hraw.s0
      s1 := ?_
      s2 := ?_ }
  · exact hanchor.s1.trans
      (by simpa [components, mul_assoc] using
        (mul_le_mul_of_nonneg_left hraw.s1 hMA))
  · have hfirst := mul_le_mul_of_nonneg_left hraw.s2 (sq_nonneg MA)
    have hsecond := mul_le_mul_of_nonneg_left hraw.s1 hNA
    exact hanchor.s2.trans (by
      simpa [components, mul_assoc] using add_le_add hfirst hsecond)

/-! ## Summable anchoring distortions -/

/-- Rowwise control of the deviations of an anchoring diffeomorphism from the
identity.  Here `a k = (mA k)⁻¹`; all three displayed distortion sequences of
the paper are retained separately. -/
structure DistortionBudget
    (a MA NA : ℕ → ℝ) (Aw AM AN : ℝ) : Prop where
  a_one : ∀ k, 1 ≤ a k
  MA_one : ∀ k, 1 ≤ MA k
  NA_nonnegative : ∀ k, 0 ≤ NA k
  Aw_nonnegative : 0 ≤ Aw
  AM_nonnegative : 0 ≤ AM
  AN_nonnegative : 0 ≤ AN
  summable_a : Summable (fun k => a k - 1)
  summable_MA : Summable (fun k => MA k - 1)
  summable_NA : Summable NA
  tsum_a_le : (∑' k, (a k - 1)) ≤ Aw
  tsum_MA_le : (∑' k, (MA k - 1)) ≤ AM
  tsum_NA_le : (∑' k, NA k) ≤ AN

namespace DistortionBudget

theorem a_nonnegative {a MA NA : ℕ → ℝ} {Aw AM AN : ℝ}
    (B : DistortionBudget a MA NA Aw AM AN) (k : ℕ) : 0 ≤ a k :=
  zero_le_one.trans (B.a_one k)

theorem MA_nonnegative {a MA NA : ℕ → ℝ} {Aw AM AN : ℝ}
    (B : DistortionBudget a MA NA Aw AM AN) (k : ℕ) : 0 ≤ MA k :=
  zero_le_one.trans (B.MA_one k)

theorem a_prefix_le {a MA NA : ℕ → ℝ} {Aw AM AN : ℝ}
    (B : DistortionBudget a MA NA Aw AM AN) (k : ℕ) :
    (∑ j ∈ Finset.range k, (a j - 1)) ≤ Aw := by
  exact ((B.summable_a.sum_le_tsum (Finset.range k)
    (fun j _ => sub_nonneg.mpr (B.a_one j))).trans B.tsum_a_le)

theorem MA_le {a MA NA : ℕ → ℝ} {Aw AM AN : ℝ}
    (B : DistortionBudget a MA NA Aw AM AN) (k : ℕ) : MA k ≤ 1 + AM := by
  have hk : MA k - 1 ≤ ∑' j, (MA j - 1) := by
    have hs := B.summable_MA.sum_le_tsum ({k} : Finset ℕ)
      (fun j _ => sub_nonneg.mpr (B.MA_one j))
    simpa using hs
  linarith [B.tsum_MA_le]

theorem NA_le {a MA NA : ℕ → ℝ} {Aw AM AN : ℝ}
    (B : DistortionBudget a MA NA Aw AM AN) (k : ℕ) : NA k ≤ AN := by
  have hs := B.summable_NA.sum_le_tsum ({k} : Finset ℕ)
    (fun j _ => B.NA_nonnegative j)
  have hk : NA k ≤ ∑' j, NA j := by simpa using hs
  exact hk.trans B.tsum_NA_le

theorem prod_a_le_exp_prefix {a MA NA : ℕ → ℝ} {Aw AM AN : ℝ}
    (B : DistortionBudget a MA NA Aw AM AN) : ∀ k,
    (∏ j ∈ Finset.range k, a j) ≤
      Real.exp (∑ j ∈ Finset.range k, (a j - 1)) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hak : a k ≤ Real.exp (a k - 1) := by
        have := Real.add_one_le_exp (a k - 1)
        linarith
      calc
        (∏ j ∈ Finset.range (k + 1), a j) =
            (∏ j ∈ Finset.range k, a j) * a k := by rw [Finset.prod_range_succ]
        _ ≤ Real.exp (∑ j ∈ Finset.range k, (a j - 1)) * a k :=
          mul_le_mul_of_nonneg_right ih (B.a_nonnegative k)
        _ ≤ Real.exp (∑ j ∈ Finset.range k, (a j - 1)) *
            Real.exp (a k - 1) :=
          mul_le_mul_of_nonneg_left hak (Real.exp_pos _).le
        _ = Real.exp (∑ j ∈ Finset.range (k + 1), (a j - 1)) := by
          rw [Finset.sum_range_succ, Real.exp_add]

theorem prod_a_le {a MA NA : ℕ → ℝ} {Aw AM AN : ℝ}
    (B : DistortionBudget a MA NA Aw AM AN) (k : ℕ) :
    (∏ j ∈ Finset.range k, a j) ≤ Real.exp Aw :=
  (B.prod_a_le_exp_prefix k).trans
    (Real.exp_le_exp.mpr (B.a_prefix_le k))

end DistortionBudget

/-! ## Depth-uniform transition invariant -/

def wConst (Aw : ℝ) : ℝ := Real.exp Aw

def s0Const (Aw C0 : ℝ) : ℝ := max 1 (C0 * wConst Aw)

def s1Const (Aw AM C0 C1 : ℝ) : ℝ :=
  max 1 ((1 + AM) * C1 * (wConst Aw + s0Const Aw C0))

def s2Const (Aw AM AN C0 C1 C2 : ℝ) : ℝ :=
  max 1 ((1 + AM) ^ 2 * C2 *
      (wConst Aw + s0Const Aw C0 + s1Const Aw AM C0 C1) +
    AN * C1 * (wConst Aw + s0Const Aw C0))

def stableConst (Aw AM AN C0 C1 C2 : ℝ) : ℝ :=
  max (wConst Aw) (max (s0Const Aw C0)
    (max (s1Const Aw AM C0 C1) (s2Const Aw AM AN C0 C1 C2)))

theorem depth_uniform_components
    {V : ℕ → Components} {a MA NA : ℕ → ℝ}
    {Aw AM AN C0 C1 C2 d : ℝ}
    (B : DistortionBudget a MA NA Aw AM AN)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hd : 0 ≤ d)
    (hV : ∀ k, (V k).Nonnegative)
    (hinit : (V 0).w ≤ d ∧ (V 0).s0 ≤ d ∧
      (V 0).s1 ≤ d ∧ (V 0).s2 ≤ d)
    (hstep : ∀ k, Transition (V k) (V (k + 1))
      (a k) (MA k) (NA k) C0 C1 C2) :
    ∀ k,
      (V k).w ≤ stableConst Aw AM AN C0 C1 C2 * d ∧
      (V k).s0 ≤ stableConst Aw AM AN C0 C1 C2 * d ∧
      (V k).s1 ≤ stableConst Aw AM AN C0 C1 C2 * d ∧
      (V k).s2 ≤ stableConst Aw AM AN C0 C1 C2 * d := by
  let Ew := wConst Aw
  let E0 := s0Const Aw C0
  let E1 := s1Const Aw AM C0 C1
  let E2 := s2Const Aw AM AN C0 C1 C2
  let E := stableConst Aw AM AN C0 C1 C2
  have hEw0 : 0 ≤ Ew := by dsimp [Ew, wConst]; positivity
  have hE00 : 0 ≤ E0 := by dsimp [E0, s0Const]; exact zero_le_one.trans (le_max_left _ _)
  have hE10 : 0 ≤ E1 := by dsimp [E1, s1Const]; exact zero_le_one.trans (le_max_left _ _)
  have hE20 : 0 ≤ E2 := by dsimp [E2, s2Const]; exact zero_le_one.trans (le_max_left _ _)
  have h1E0 : 1 ≤ E0 := by dsimp [E0, s0Const]; exact le_max_left _ _
  have h1E1 : 1 ≤ E1 := by dsimp [E1, s1Const]; exact le_max_left _ _
  have h1E2 : 1 ≤ E2 := by dsimp [E2, s2Const]; exact le_max_left _ _
  have hCE0 : C0 * Ew ≤ E0 := by dsimp [E0, s0Const]; exact le_max_right _ _
  have hCE1 : (1 + AM) * C1 * (Ew + E0) ≤ E1 := by
    dsimp [E1, s1Const]; exact le_max_right _ _
  have hCE2 : (1 + AM) ^ 2 * C2 * (Ew + E0 + E1) +
      AN * C1 * (Ew + E0) ≤ E2 := by
    dsimp [E2, s2Const]; exact le_max_right _ _
  have hEwE : Ew ≤ E := by dsimp [E, stableConst]; exact le_max_left _ _
  have hE0E : E0 ≤ E := by
    dsimp [E, stableConst]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hE1E : E1 ≤ E := by
    dsimp [E, stableConst]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hE2E : E2 ≤ E := by
    dsimp [E, stableConst]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hwprod : ∀ k, (V k).w ≤
      (∏ j ∈ Finset.range k, a j) * d := by
    intro k
    induction k with
    | zero => simpa using hinit.1
    | succ k ih =>
        calc
          (V (k + 1)).w ≤ a k * (V k).w := (hstep k).w
          _ ≤ a k * ((∏ j ∈ Finset.range k, a j) * d) :=
            mul_le_mul_of_nonneg_left ih (B.a_nonnegative k)
          _ = (∏ j ∈ Finset.range (k + 1), a j) * d := by
            rw [Finset.prod_range_succ]
            ring
  have hw : ∀ k, (V k).w ≤ Ew * d := by
    intro k
    exact (hwprod k).trans (mul_le_mul_of_nonneg_right
      (by simpa [Ew, wConst] using B.prod_a_le k) hd)
  have hs0 : ∀ k, (V k).s0 ≤ E0 * d := by
    intro k
    cases k with
    | zero => exact hinit.2.1.trans (by nlinarith [h1E0])
    | succ k =>
        exact (hstep k).s0.trans
          ((mul_le_mul_of_nonneg_left (hw k) hC0).trans
            (by simpa [mul_assoc] using mul_le_mul_of_nonneg_right hCE0 hd))
  have hs1 : ∀ k, (V k).s1 ≤ E1 * d := by
    intro k
    cases k with
    | zero => exact hinit.2.2.1.trans (by nlinarith [h1E1])
    | succ k =>
        have hsum : (V k).w + (V k).s0 ≤ (Ew + E0) * d := by
          nlinarith [hw k, hs0 k]
        have hM := B.MA_le k
        have hM0 := B.MA_nonnegative k
        have hfactor0 : 0 ≤ C1 * ((V k).w + (V k).s0) :=
          mul_nonneg hC1 (add_nonneg (hV k).w (hV k).s0)
        have h1AM : 0 ≤ 1 + AM := by linarith [B.AM_nonnegative]
        calc
          (V (k + 1)).s1 ≤ MA k * C1 * ((V k).w + (V k).s0) := (hstep k).s1
          _ ≤ (1 + AM) * C1 * ((V k).w + (V k).s0) := by
            have hMC : MA k * C1 ≤ (1 + AM) * C1 :=
              mul_le_mul_of_nonneg_right hM hC1
            exact mul_le_mul_of_nonneg_right hMC
              (add_nonneg (hV k).w (hV k).s0)
          _ ≤ (1 + AM) * C1 * ((Ew + E0) * d) := by
            exact mul_le_mul_of_nonneg_left hsum (mul_nonneg h1AM hC1)
          _ ≤ E1 * d := by
            calc
              _ = ((1 + AM) * C1 * (Ew + E0)) * d := by ring
              _ ≤ E1 * d := mul_le_mul_of_nonneg_right hCE1 hd
  have hs2 : ∀ k, (V k).s2 ≤ E2 * d := by
    intro k
    cases k with
    | zero => exact hinit.2.2.2.trans (by nlinarith [h1E2])
    | succ k =>
        have hsum2 : (V k).w + (V k).s0 + (V k).s1 ≤
            (Ew + E0 + E1) * d := by nlinarith [hw k, hs0 k, hs1 k]
        have hsum1 : (V k).w + (V k).s0 ≤ (Ew + E0) * d := by
          nlinarith [hw k, hs0 k]
        have hM := B.MA_le k
        have hM0 := B.MA_nonnegative k
        have hMcap0 : 0 ≤ 1 + AM := by linarith [B.AM_nonnegative]
        have hMsq : (MA k) ^ 2 ≤ (1 + AM) ^ 2 := by nlinarith
        have hN := B.NA_le k
        have hterm1nn : 0 ≤ C2 * ((V k).w + (V k).s0 + (V k).s1) :=
          mul_nonneg hC2 (add_nonneg
            (add_nonneg (hV k).w (hV k).s0) (hV k).s1)
        have hterm2nn : 0 ≤ C1 * ((V k).w + (V k).s0) :=
          mul_nonneg hC1 (add_nonneg (hV k).w (hV k).s0)
        calc
          (V (k + 1)).s2 ≤ (MA k) ^ 2 * C2 *
              ((V k).w + (V k).s0 + (V k).s1) +
              NA k * C1 * ((V k).w + (V k).s0) := (hstep k).s2
          _ ≤ (1 + AM) ^ 2 * C2 *
              ((V k).w + (V k).s0 + (V k).s1) +
              AN * C1 * ((V k).w + (V k).s0) :=
            add_le_add (by
                have hMC : (MA k) ^ 2 * C2 ≤ (1 + AM) ^ 2 * C2 :=
                  mul_le_mul_of_nonneg_right hMsq hC2
                exact mul_le_mul_of_nonneg_right hMC
                  (add_nonneg (add_nonneg (hV k).w (hV k).s0) (hV k).s1))
              (by
                have hNC : NA k * C1 ≤ AN * C1 :=
                  mul_le_mul_of_nonneg_right hN hC1
                exact mul_le_mul_of_nonneg_right hNC
                  (add_nonneg (hV k).w (hV k).s0))
          _ ≤ (1 + AM) ^ 2 * C2 * ((Ew + E0 + E1) * d) +
              AN * C1 * ((Ew + E0) * d) :=
            add_le_add
              (mul_le_mul_of_nonneg_left hsum2
                (mul_nonneg (sq_nonneg _) hC2))
              (mul_le_mul_of_nonneg_left hsum1
                (mul_nonneg B.AN_nonnegative hC1))
          _ ≤ E2 * d := by
            calc
              _ = ((1 + AM) ^ 2 * C2 * (Ew + E0 + E1) +
                    AN * C1 * (Ew + E0)) * d := by ring
              _ ≤ E2 * d := mul_le_mul_of_nonneg_right hCE2 hd
  intro k
  exact
    ⟨(hw k).trans (mul_le_mul_of_nonneg_right hEwE hd),
      (hs0 k).trans (mul_le_mul_of_nonneg_right hE0E hd),
      (hs1 k).trans (mul_le_mul_of_nonneg_right hE1E hd),
      (hs2 k).trans (mul_le_mul_of_nonneg_right hE2E hd)⟩

end AnchoredJacobiStableTransition
