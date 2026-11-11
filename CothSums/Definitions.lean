import Mathlib

set_option autoImplicit false

open MeasureTheory

noncomputable def CothSums.chi (r : ℝ) : ℝ :=
  (4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2) *
    ∫ ρ in (0 : ℝ)..r, (Real.sqrt (1 + ρ ^ 4))⁻¹

noncomputable def CothSums.kernel (r : ℝ) : ℝ :=
  CothSums.chi r * (1 - CothSums.chi r)

noncomputable def CothSums.cothTerm (n : ℕ) : ℝ :=
  (Real.cosh (Real.pi * ((n : ℝ) + 1)) /
    Real.sinh (Real.pi * ((n : ℝ) + 1))) / ((n : ℝ) + 1) ^ 5

noncomputable def CothSums.oddTanhTerm (s n : ℕ) : ℝ :=
  Real.tanh (Real.pi * (2 * (n : ℝ) + 1) / 2) / (2 * (n : ℝ) + 1) ^ s

noncomputable def CothSums.lambda (z : ℂ) : ℂ :=
  Complex.Gamma ((1 : ℂ) / 4 + z) * Complex.Gamma ((1 : ℂ) / 4 - z) *
    Complex.Gamma ((1 : ℂ) / 2 + z) * Complex.Gamma ((1 : ℂ) / 2 - z) /
    (Complex.Gamma (1 + z) * Complex.Gamma (1 - z))

noncomputable def CothSums.barnesJIntegrand (u : ℝ) : ℝ :=
  ‖CothSums.lambda (Complex.I * (u : ℂ) / 4)‖ ^ 2 / 16

noncomputable def CothSums.barnesJ : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), CothSums.barnesJIntegrand u

noncomputable def CothSums.secondMoment : ℝ :=
  ∫ r in Set.Ioi (0 : ℝ), CothSums.kernel r ^ 2 / r

noncomputable def CothSums.mellinKernel (u : ℝ) : ℂ :=
  mellin (fun r : ℝ => (CothSums.kernel r : ℂ)) (Complex.I * (u : ℂ))

noncomputable def CothSums.testMoment (P : Polynomial ℝ) : ℝ :=
  ∫ r in Set.Ioi (0 : ℝ), P.eval (CothSums.chi r) / r

noncomputable def CothSums.cosineTest (P : Polynomial ℝ) (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    P.derivative.eval x * Real.cos ((2 * (n : ℝ) + 1) * Real.pi * x)

noncomputable def CothSums.lemniscaticPeriodPair : PeriodPair where
  ω₁ := 1 + Complex.I
  ω₂ := 1 - Complex.I
  indep := by
    rw [Fintype.linearIndependent_iff]
    intro f hf
    have hre := congrArg Complex.re hf
    have him := congrArg Complex.im hf
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      Complex.smul_re, Complex.smul_im] at hre him
    intro i
    fin_cases i <;> norm_num at hre him ⊢ <;> linarith
