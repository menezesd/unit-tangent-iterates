import UnitTangentIterates.AnchoredJacobiStableTransition

/-! # Monotonicity of stable transition distortion parameters -/

noncomputable section

namespace AnchoredJacobiStableTransition

/-- A component transition remains valid after enlarging only its three
nonnegative junction-distortion parameters. -/
def Transition.monoDistortion
    {x y : Components} {a a' MA MA' NA NA' C0 C1 C2 : ℝ}
    (H : Transition x y a MA NA C0 C1 C2)
    (hx : x.Nonnegative)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (ha : a ≤ a') (hMA0 : 0 ≤ MA) (hMA : MA ≤ MA')
    (hNA : NA ≤ NA') :
    Transition x y a' MA' NA' C0 C1 C2 := by
  have hx01 : 0 ≤ x.w + x.s0 := add_nonneg hx.w hx.s0
  have hx012 : 0 ≤ x.w + x.s0 + x.s1 :=
    add_nonneg hx01 hx.s1
  have hMA'0 : 0 ≤ MA' := hMA0.trans hMA
  have hMA_sq : MA ^ 2 ≤ MA' ^ 2 := by nlinarith
  refine
    { w := H.w.trans (mul_le_mul_of_nonneg_right ha hx.w)
      s0 := H.s0
      s1 := H.s1.trans ?_
      s2 := H.s2.trans ?_ }
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hMA hC1) hx01
  · have hfirst : MA ^ 2 * C2 * (x.w + x.s0 + x.s1) ≤
        MA' ^ 2 * C2 * (x.w + x.s0 + x.s1) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMA_sq hC2) hx012
    have hsecond : NA * C1 * (x.w + x.s0) ≤
        NA' * C1 * (x.w + x.s0) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hNA hC1) hx01
    exact add_le_add hfirst hsecond

end AnchoredJacobiStableTransition
