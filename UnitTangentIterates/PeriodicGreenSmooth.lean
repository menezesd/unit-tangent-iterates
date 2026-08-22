import Mathlib
import UnitTangentIterates.PeriodicGreenJoint
import UnitTangentIterates.RearOwnHigherRegularity

/-!
# Higher joint regularity of the periodic Green operator

`PeriodicGreenJoint.lean` shows that the periodic inverse

```
  (𝒢_{A(a,·)} F(a,·))(x) = (1 - e^{-A(a,ℓ)})⁻¹ e^{-A(a,x)} (B(a,x) - B(a,x-ℓ)) ,
        A(a,x) = ∫₀ˣ A(a,·) ,   B(a,y) = ∫₀^y e^{A(a,t)} F(a,t) dt ,
```

moves continuously with its data.  The closed form on the right is built from
the data by *parametric primitives*, exponentials, products and one inversion
of a nonvanishing function, and each of those preserves joint `Cⁿ` regularity —
the primitive by `RearOwnHigherRegularity.contDiff_primitive`.  So the operator
is as smooth in the pair `(a, x)` as its data are.

This is what makes the selected steering angle smooth to all orders: its
derivative in the path parameter is the Green solution of the linearized
equation, so once the steering angle is known to be jointly `Cⁿ`, that
derivative is jointly `Cⁿ` too, and the steering angle is jointly `C^{n+1}`
(see `SteeringArclengthSmooth.lean`).

Main results:

* `contDiff_prim_param` — the parametric primitive of a `Cⁿ` family is `Cⁿ`;
* `contDiff_bigB` — so is the weighted primitive `B`;
* `contDiff_periodicGreen_param_var`, `contDiff_periodicGreen_param` — **the
  Green operator is jointly `Cⁿ` in its data**, for a period moving with the
  parameter and for a fixed period.
-/

noncomputable section

open Function

namespace PeriodicGreenSmooth

open PeriodicGreen PeriodicGreenJoint RearOwnHigherRegularity

variable {A F : ℝ → ℝ → ℝ} {l : ℝ} {n : ℕ}

/-- The primitive of a jointly `Cⁿ` family of coefficients is jointly `Cⁿ`. -/
theorem contDiff_prim_param (hA : ContDiff ℝ (n : ℕ) (uncurry A)) :
    ContDiff ℝ (n : ℕ) (uncurry fun a x => prim (A a) x) :=
  contDiff_primitive n A hA

/-- The weighted primitive `B(a, y) = ∫₀^y e^{A(a,t)} F(a,t) dt` of jointly
`Cⁿ` data is jointly `Cⁿ`. -/
theorem contDiff_bigB (hA : ContDiff ℝ (n : ℕ) (uncurry A))
    (hF : ContDiff ℝ (n : ℕ) (uncurry F)) :
    ContDiff ℝ (n : ℕ) (uncurry fun a y => bigB A F a y) := by
  have hint : ContDiff ℝ (n : ℕ)
      (uncurry fun a t => Real.exp (prim (A a) t) * F a t) :=
    (Real.contDiff_exp.comp (contDiff_prim_param hA)).mul hF
  exact contDiff_primitive n _ hint

/-- **The periodic Green operator is jointly `Cⁿ` in its data**, for a period
which moves `Cⁿ`-smoothly with the parameter. -/
theorem contDiff_periodicGreen_param_var {L : ℝ → ℝ} (hA : ContDiff ℝ (n : ℕ) (uncurry A))
    (hF : ContDiff ℝ (n : ℕ) (uncurry F)) (hL : ContDiff ℝ (n : ℕ) L)
    (hApos : ∀ a, 0 < prim (A a) (L a)) :
    ContDiff ℝ (n : ℕ) (uncurry fun a x => periodicGreen (A a) (L a) (F a) x) := by
  have hAc : Continuous (uncurry A) := hA.continuous
  have hFc : Continuous (uncurry F) := hF.continuous
  have hAslice : ∀ a, Continuous (A a) := fun a =>
    hAc.comp (continuous_const.prodMk continuous_id)
  have hFslice : ∀ a, Continuous (F a) := fun a =>
    hFc.comp (continuous_const.prodMk continuous_id)
  have heq : (uncurry fun a x => periodicGreen (A a) (L a) (F a) x)
      = fun p : ℝ × ℝ => (1 - Real.exp (-prim (A p.1) (L p.1)))⁻¹ *
          Real.exp (-prim (A p.1) p.2) *
          (bigB A F p.1 p.2 - bigB A F p.1 (p.2 - L p.1)) := by
    funext p
    exact periodicGreen_eq_bigB (hAslice p.1) (hFslice p.1) p.2
  rw [heq]
  have hprim : ContDiff ℝ (n : ℕ) (uncurry fun a x => prim (A a) x) := contDiff_prim_param hA
  have hprimp : ContDiff ℝ (n : ℕ) fun p : ℝ × ℝ => prim (A p.1) p.2 := hprim
  have hpriml : ContDiff ℝ (n : ℕ) fun a : ℝ => prim (A a) (L a) :=
    hprim.comp (contDiff_id.prodMk hL)
  have hden : ContDiff ℝ (n : ℕ) fun a : ℝ => 1 - Real.exp (-prim (A a) (L a)) :=
    contDiff_const.sub (Real.contDiff_exp.comp hpriml.neg)
  have hconst : ContDiff ℝ (n : ℕ) fun a : ℝ => (1 - Real.exp (-prim (A a) (L a)))⁻¹ :=
    hden.inv (fun a => ne_of_gt (one_sub_exp_pos (hApos a)))
  have hconstp : ContDiff ℝ (n : ℕ) fun p : ℝ × ℝ => (1 - Real.exp (-prim (A p.1) (L p.1)))⁻¹ :=
    hconst.comp contDiff_fst
  have hB : ContDiff ℝ (n : ℕ) (uncurry fun a y => bigB A F a y) := contDiff_bigB hA hF
  have hB1 : ContDiff ℝ (n : ℕ) fun p : ℝ × ℝ => bigB A F p.1 p.2 := hB
  have hB2 : ContDiff ℝ (n : ℕ) fun p : ℝ × ℝ => bigB A F p.1 (p.2 - L p.1) :=
    hB.comp (contDiff_fst.prodMk (contDiff_snd.sub (hL.comp contDiff_fst)))
  exact (hconstp.mul (Real.contDiff_exp.comp hprimp.neg)).mul (hB1.sub hB2)

/-- **The periodic Green operator is jointly `Cⁿ` in its data**, for a fixed
period. -/
theorem contDiff_periodicGreen_param (hA : ContDiff ℝ (n : ℕ) (uncurry A))
    (hF : ContDiff ℝ (n : ℕ) (uncurry F)) (hApos : ∀ a, 0 < prim (A a) l) :
    ContDiff ℝ (n : ℕ) (uncurry fun a x => periodicGreen (A a) l (F a) x) :=
  contDiff_periodicGreen_param_var (L := fun _ => l) hA hF contDiff_const hApos

end PeriodicGreenSmooth
