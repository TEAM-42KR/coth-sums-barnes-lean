import CothSums

theorem coth_fifth_power_barnes_integral :
  (∑' n : ℕ,
    (Real.cosh (Real.pi * ((n : ℝ) + 1)) /
      Real.sinh (Real.pi * ((n : ℝ) + 1))) / ((n : ℝ) + 1) ^ 5) =
  11 * Real.pi ^ 5 / 2268 -
    Real.pi ^ 3 / (27 * Real.Gamma (1 / 4) ^ 4) *
      (∫ u in Set.Ioi (0 : ℝ),
        ‖Complex.Gamma ((1 : ℂ) / 4 + Complex.I * (u : ℂ) / 4) *
          Complex.Gamma ((1 : ℂ) / 4 - Complex.I * (u : ℂ) / 4) *
          Complex.Gamma ((1 : ℂ) / 2 + Complex.I * (u : ℂ) / 4) *
          Complex.Gamma ((1 : ℂ) / 2 - Complex.I * (u : ℂ) / 4) /
          (Complex.Gamma (1 + Complex.I * (u : ℂ) / 4) *
            Complex.Gamma (1 - Complex.I * (u : ℂ) / 4))‖ ^ 2 / 16) := by
  exact CothSums.fifth_power_evaluation

#print axioms coth_fifth_power_barnes_integral
