import CothSums.Definitions

set_option autoImplicit false
open MeasureTheory Set



set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


open MeasureTheory Set


theorem CothSums.density_continuous : Continuous (fun r : ℝ => (Real.sqrt (1 + r ^ 4))⁻¹) := by
  apply Continuous.inv₀
  · exact (continuous_const.add (continuous_id.pow 4)).sqrt
  · intro r
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity))


theorem CothSums.chi_prefactor_pos : 0 < (4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2 : ℝ) := by
  exact div_pos
    (mul_pos (by norm_num) (Real.sqrt_pos.2 Real.pi_pos))
    (sq_pos_of_pos (Real.Gamma_pos_of_pos (by norm_num)))


theorem CothSums.chi_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ CothSums.chi r := by
  unfold CothSums.chi
  exact mul_nonneg CothSums.chi_prefactor_pos.le
    (intervalIntegral.integral_nonneg_of_forall hr
      (fun u => inv_nonneg.mpr (Real.sqrt_nonneg _)))


theorem CothSums.chi_le_prefactor_mul {r : ℝ} (hr : 0 ≤ r) : CothSums.chi r ≤
    (4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2) * r := by
  have hbound : (∫ u in (0 : ℝ)..r, (Real.sqrt (1 + u ^ 4))⁻¹) ≤ r := by
    calc
      (∫ u in (0 : ℝ)..r, (Real.sqrt (1 + u ^ 4))⁻¹) ≤
          ∫ _ in (0 : ℝ)..r, (1 : ℝ) :=
        intervalIntegral.integral_mono hr
          (CothSums.density_continuous.intervalIntegrable 0 r)
          (continuous_const.intervalIntegrable 0 r)
          (fun u => inv_le_one_of_one_le₀ (by
            simpa only [Real.sqrt_one] using
              Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + u ^ 4 from
                le_add_of_nonneg_right (by positivity))))
      _ = r := by simp
  exact mul_le_mul_of_nonneg_left hbound CothSums.chi_prefactor_pos.le


theorem CothSums.density_head_tail (r : ℝ) (hr : 0 < r) :
    (∫ t in (0 : ℝ)..r, (Real.sqrt (1 + t ^ 4))⁻¹) +
      (∫ t in Set.Ioi r, (Real.sqrt (1 + t ^ 4))⁻¹) =
        ∫ t in Set.Ioi (0 : ℝ), (Real.sqrt (1 + t ^ 4))⁻¹ := by
  have hi : IntegrableOn (fun t : ℝ => (Real.sqrt (1 + t ^ 4))⁻¹) (Ioi 0) := by
    have hc : Continuous (fun t : ℝ => (Real.sqrt (1 + t ^ 4))⁻¹) := by
      apply Continuous.inv₀
      · fun_prop
      · intro t
        exact (Real.sqrt_pos.2 (by positivity : 0 < 1 + t ^ 4)).ne'
    have htail : IntegrableOn (fun t : ℝ => (Real.sqrt (1 + t ^ 4))⁻¹) (Ioi 1) := by
      apply (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := 1)
        (by norm_num) (by norm_num)).mono' hc.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans (by norm_num) ht
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.2 (by positivity)))]
      have hs : t ^ 2 ≤ Real.sqrt (1 + t ^ 4) := by
        have hz : Real.sqrt (t ^ 4) ≤ Real.sqrt (1 + t ^ 4) := Real.sqrt_le_sqrt (by linarith)
        have hid : Real.sqrt (t ^ 4) = t ^ 2 := by
          rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg t)]
        rwa [hid] at hz
      calc
        (Real.sqrt (1 + t ^ 4))⁻¹ ≤ (t ^ 2)⁻¹ := (inv_le_inv₀ (by positivity) (sq_pos_of_pos ht0)).2 hs
        _ = t ^ (-2 : ℝ) := by rw [Real.rpow_neg ht0.le, Real.rpow_two]
    have hhead : IntegrableOn (fun t : ℝ => (Real.sqrt (1 + t ^ 4))⁻¹) (Ioc 0 1) :=
      hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    simpa only [Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)] using hhead.union htail
  exact intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Ioi_subset_Ioi hr.le))


theorem CothSums.density_tail_bound (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => (Real.sqrt (1 + t ^ 4))⁻¹) (Ioi r) ∧
    0 ≤ (∫ t in Ioi r, (Real.sqrt (1 + t ^ 4))⁻¹) ∧
    (∫ t in Ioi r, (Real.sqrt (1 + t ^ 4))⁻¹) ≤ r⁻¹ := by
  have hc : Continuous (fun t : ℝ => (Real.sqrt (1 + t ^ 4))⁻¹) := by
    apply Continuous.inv₀
    · exact (continuous_const.add (continuous_id.pow 4)).sqrt
    · intro t
      exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hdom (t : ℝ) (ht : 0 < t) : (Real.sqrt (1 + t ^ 4))⁻¹ ≤ t ^ (-2 : ℝ) := by
    have hsq : t ^ 2 ≤ Real.sqrt (1 + t ^ 4) := by
      apply (Real.le_sqrt (sq_nonneg _) (by positivity)).mpr
      nlinarith [sq_nonneg (t ^ 2)]
    rw [Real.rpow_neg (le_of_lt ht), Real.rpow_two]
    exact inv_anti₀ (sq_pos_of_pos ht) hsq
  have hb : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi r) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hr
  have hi : IntegrableOn (fun t : ℝ => (Real.sqrt (1 + t ^ 4))⁻¹) (Ioi r) := by
    refine hb.mono' hc.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hdom t (lt_trans hr ht)
  have hp : 0 ≤ (∫ t in Ioi r, (Real.sqrt (1 + t ^ 4))⁻¹) :=
    integral_nonneg (fun t => by positivity)
  have he : (∫ t in Ioi r, t ^ (-2 : ℝ)) = r⁻¹ := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hr]
    norm_num [Real.rpow_neg (le_of_lt hr)]
  refine ⟨hi, hp, ?_⟩
  calc
    (∫ t in Ioi r, (Real.sqrt (1 + t ^ 4))⁻¹) ≤
        ∫ t in Ioi r, t ^ (-2 : ℝ) := by
      apply integral_mono_ae hi hb
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hdom t (lt_trans hr ht)
    _ = r⁻¹ := he


theorem CothSums.density_integral :
    (∫ t in Set.Ioi (0 : ℝ), (Real.sqrt (1 + t ^ 4))⁻¹) =
      Real.Gamma (1 / 4) ^ 2 / (4 * Real.sqrt Real.pi) := by
  have ht : 4 * (∫ t in Ioi (0 : ℝ), (Real.sqrt (1 + t ^ 4))⁻¹) =
      ∫ x in (0 : ℝ)..1, x ^ (-3 / 4 : ℝ) * (1 - x) ^ (-3 / 4 : ℝ) := by
    let g : ℝ → ℝ := fun y => y ^ (-3 / 4 : ℝ) * (1 + y) ^ (-1 / 2 : ℝ)
    have hquartic : 4 * (∫ t in Ioi (0 : ℝ), (Real.sqrt (1 + t ^ 4))⁻¹) =
        ∫ y in Ioi (0 : ℝ), g y := by
      calc
        4 * (∫ t in Ioi (0 : ℝ), (Real.sqrt (1 + t ^ 4))⁻¹) =
            ∫ t in Ioi (0 : ℝ), 4 * (Real.sqrt (1 + t ^ 4))⁻¹ := by
          rw [integral_const_mul]
        _ = ∫ t in Ioi (0 : ℝ), ((4 : ℝ) * t ^ ((4 : ℝ) - 1)) • g (t ^ (4 : ℝ)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          have ht0 : 0 < t := ht
          have hp : t ^ ((4 : ℝ) - 1) * (t ^ (4 : ℝ)) ^ (-3 / 4 : ℝ) = 1 := by
            rw [← Real.rpow_mul ht0.le, ← Real.rpow_add ht0]
            norm_num
          have hf : (1 + t ^ (4 : ℝ)) ^ (-1 / 2 : ℝ) =
              (Real.sqrt (1 + t ^ 4))⁻¹ := by
            rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num,
              Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
            norm_num
          dsimp only [g]
          rw [smul_eq_mul, hf]
          calc
            4 * (Real.sqrt (1 + t ^ 4))⁻¹ =
                4 * (t ^ ((4 : ℝ) - 1) * (t ^ (4 : ℝ)) ^ (-3 / 4 : ℝ)) *
                  (Real.sqrt (1 + t ^ 4))⁻¹ := by rw [hp]; ring
            _ = _ := by ring
        _ = ∫ y in Ioi (0 : ℝ), g y :=
          integral_comp_rpow_Ioi_of_pos (g := g) (p := 4) (by norm_num)
    have himage : (fun x : ℝ => x / (1 - x)) '' Ioo 0 1 = Ioi 0 := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact div_pos hx.1 (sub_pos.mpr hx.2)
      · intro hy
        have hy0 : 0 < y := hy
        have hd : 0 < 1 + y := by linarith
        refine ⟨y / (1 + y), ⟨div_pos hy0 hd, (div_lt_one hd).2 (by linarith)⟩, ?_⟩
        have he : 1 - y / (1 + y) = (1 + y)⁻¹ := by field_simp; ring
        dsimp only
        rw [he, div_inv_eq_mul]
        exact div_mul_cancel₀ y hd.ne'
    have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
        HasDerivWithinAt (fun x : ℝ => x / (1 - x)) ((1 - x) ^ 2)⁻¹ (Ioo 0 1) x := by
      intro x hx
      have hn : 1 - x ≠ 0 := (sub_pos.mpr hx.2).ne'
      have hh : HasDerivAt (fun z : ℝ => z / (1 - z))
          ((1 * (1 - x) - x * (0 - 1)) / (1 - x) ^ 2) x :=
        (hasDerivAt_id x).div ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) hn
      have he : (1 * (1 - x) - x * (0 - 1)) / (1 - x) ^ 2 = ((1 - x) ^ 2)⁻¹ := by ring
      rw [he] at hh
      exact hh.hasDerivWithinAt
    have hinj : InjOn (fun x : ℝ => x / (1 - x)) (Ioo 0 1) := by
      intro x hx y hy he
      have he' := (div_eq_div_iff (sub_pos.mpr hx.2).ne' (sub_pos.mpr hy.2).ne').1 he
      nlinarith
    have hm : (∫ y in Ioi (0 : ℝ), g y) =
        ∫ x in Ioo (0 : ℝ) 1, x ^ (-3 / 4 : ℝ) * (1 - x) ^ (-3 / 4 : ℝ) := by
      rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      have hx0 : 0 < x := hx.1
      have hb : 0 < 1 - x := sub_pos.mpr hx.2
      have he : 1 + x / (1 - x) = (1 - x)⁻¹ := by field_simp; ring
      have hp : ((1 - x) ^ 2)⁻¹ = (1 - x) ^ (-2 : ℝ) := by
        rw [Real.rpow_neg hb.le, Real.rpow_two]
      have hc : (1 - x) ^ (-2 : ℝ) * ((1 - x) ^ (-3 / 4 : ℝ))⁻¹ *
          ((1 - x) ^ (-1 / 2 : ℝ))⁻¹ = (1 - x) ^ (-3 / 4 : ℝ) := by
        rw [← Real.rpow_neg hb.le, ← Real.rpow_neg hb.le,
          ← Real.rpow_add hb, ← Real.rpow_add hb]
        norm_num
      dsimp only
      rw [abs_of_pos (inv_pos.mpr (sq_pos_of_pos hb)), smul_eq_mul, hp]
      dsimp only [g]
      rw [Real.div_rpow hx0.le hb.le, he, Real.inv_rpow hb.le, div_eq_mul_inv]
      calc
        (1 - x) ^ (-2 : ℝ) *
            (x ^ (-3 / 4 : ℝ) * ((1 - x) ^ (-3 / 4 : ℝ))⁻¹ *
              ((1 - x) ^ (-1 / 2 : ℝ))⁻¹) =
            x ^ (-3 / 4 : ℝ) * ((1 - x) ^ (-2 : ℝ) *
              ((1 - x) ^ (-3 / 4 : ℝ))⁻¹ * ((1 - x) ^ (-1 / 2 : ℝ))⁻¹) := by ring
        _ = _ := by rw [hc]
    rw [hquartic, hm]
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
  have hb : (∫ x in (0 : ℝ)..1, x ^ (-3 / 4 : ℝ) * (1 - x) ^ (-3 / 4 : ℝ)) =
      Real.Gamma (1 / 4) ^ 2 / Real.sqrt Real.pi := by
    apply Complex.ofReal_injective
    have hb := Complex.betaIntegral_eq_Gamma_mul_div ((1 : ℂ) / 4) ((1 : ℂ) / 4)
      (by norm_num) (by norm_num)
    have hi : Complex.ofReal (∫ x in (0 : ℝ)..1,
        x ^ (-3 / 4 : ℝ) * (1 - x) ^ (-3 / 4 : ℝ)) =
        Complex.betaIntegral ((1 : ℂ) / 4) ((1 : ℂ) / 4) := by
      rw [← intervalIntegral.integral_ofReal, Complex.betaIntegral]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      dsimp only
      rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1,
        Complex.ofReal_cpow (sub_nonneg.mpr hx.2)]
      push_cast
      norm_num
    rw [hi, hb]
    norm_num only [show (1 : ℂ) / 4 + 1 / 4 = 1 / 2 by norm_num]
    have hq : Complex.Gamma ((1 : ℂ) / 4) = (Real.Gamma ((1 : ℝ) / 4) : ℂ) := by
      simpa using Complex.Gamma_ofReal ((1 : ℝ) / 4)
    have hh : Complex.Gamma ((1 : ℂ) / 2) = (Real.sqrt Real.pi : ℂ) := by
      convert (Complex.Gamma_ofReal ((1 : ℝ) / 2)).trans
        (congrArg Complex.ofReal Real.Gamma_one_half_eq) using 1 <;> norm_num
    rw [hq, hh]
    push_cast
    ring
  rw [hb] at ht
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  apply (eq_div_iff (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hs)).2
  have he := (eq_div_iff hs).1 ht
  nlinarith only [he]


theorem CothSums.kernel_exp_decay :
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
    ‖(CothSums.kernel (Real.exp x) : ℂ)‖ ≤ C * Real.exp (-|x|) := by
  have htotal := CothSums.density_integral
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  have hC : 0 < C := CothSums.chi_prefactor_pos
  have hG : Real.Gamma (1 / 4 : ℝ) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by norm_num))
  have hs : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have htotal' : C * (∫ t in Set.Ioi (0 : ℝ), (Real.sqrt (1 + t ^ 4))⁻¹) = 1 := by
    rw [htotal]
    dsimp [C]
    field_simp [hG, hs]
  have hcomp (r : ℝ) (hr : 0 < r) :
      1 - CothSums.chi r =
        C * (∫ t in Set.Ioi r, (Real.sqrt (1 + t ^ 4))⁻¹) := by
    have hsplit := congrArg (fun v : ℝ => C * v) (CothSums.density_head_tail r hr)
    rw [mul_add, htotal'] at hsplit
    change 1 - C * (∫ t in (0 : ℝ)..r, (Real.sqrt (1 + t ^ 4))⁻¹) = _
    linarith
  have hrange (r : ℝ) (hr : 0 < r) : 0 ≤ CothSums.chi r ∧ CothSums.chi r ≤ 1 := by
    refine ⟨CothSums.chi_nonneg hr.le, ?_⟩
    have htail := (CothSums.density_tail_bound r hr).2.1
    have hh : 0 ≤ 1 - CothSums.chi r := by
      rw [hcomp r hr]
      exact mul_nonneg hC.le htail
    linarith
  have htail (r : ℝ) (hr : 0 < r) : 1 - CothSums.chi r ≤ C * r⁻¹ := by
    rw [hcomp r hr]
    exact mul_le_mul_of_nonneg_left (CothSums.density_tail_bound r hr).2.2 hC.le
  refine ⟨C, hC, ?_⟩
  intro x
  have hxpos := Real.exp_pos x
  have hchi := hrange _ hxpos
  have hprod : 0 ≤ CothSums.chi (Real.exp x) * (1 - CothSums.chi (Real.exp x)) :=
    mul_nonneg hchi.1 (sub_nonneg.mpr hchi.2)
  simp only [CothSums.kernel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hprod]
  by_cases hx : x ≤ 0
  · rw [abs_of_nonpos hx, neg_neg]
    calc
      CothSums.chi (Real.exp x) * (1 - CothSums.chi (Real.exp x)) ≤
          CothSums.chi (Real.exp x) := by
        nlinarith [sq_nonneg (CothSums.chi (Real.exp x))]
      _ ≤ C * Real.exp x := CothSums.chi_le_prefactor_mul hxpos.le
  · have hx' : 0 ≤ x := le_of_lt (lt_of_not_ge hx)
    rw [abs_of_nonneg hx']
    calc
      CothSums.chi (Real.exp x) * (1 - CothSums.chi (Real.exp x)) ≤
          1 - CothSums.chi (Real.exp x) := by
        nlinarith [sq_nonneg (1 - CothSums.chi (Real.exp x))]
      _ ≤ C * (Real.exp x)⁻¹ := htail _ hxpos
      _ = C * Real.exp (-x) := by rw [Real.exp_neg]


theorem CothSums.chi_hasDerivAt (r : ℝ) : HasDerivAt CothSums.chi
    ((4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2) *
      (Real.sqrt (1 + r ^ 4))⁻¹) r := by
  have hf := CothSums.density_continuous
  unfold CothSums.chi
  apply HasDerivAt.const_mul
  exact
    (intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable 0 r)
      (hf.stronglyMeasurableAtFilter volume (nhds r))
      hf.continuousAt)


theorem CothSums.Analysis.continuous_exp_abs_decay_L1_L2 (f : ℝ → ℂ) (hf : Continuous f) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x : ℝ, ‖f x‖ ≤ C * Real.exp (-|x|)) :
    Integrable f ∧ MemLp f 2 := by
  have hbase (b : ℝ) (hb : 0 < b) :
      Integrable (fun x : ℝ => Real.exp (-b * |x|)) := by
    have hleft : IntegrableOn (fun x : ℝ => Real.exp (-b * |x|)) (Iic 0) := by
      apply (integrableOn_congr_fun (g := fun x : ℝ => Real.exp (b * x))
        (s := Iic 0) ?_ measurableSet_Iic).mpr
      · exact integrableOn_exp_mul_Iic hb 0
      · intro x hx
        change Real.exp (-b * |x|) = Real.exp (b * x)
        rw [abs_of_nonpos (show x ≤ 0 from hx)]
        congr 1
        ring
    have hright : IntegrableOn (fun x : ℝ => Real.exp (-b * |x|)) (Ioi 0) := by
      apply (integrableOn_congr_fun (g := fun x : ℝ => Real.exp (-b * x))
        (s := Ioi 0) ?_ measurableSet_Ioi).mpr
      · exact integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) 0
      · intro x hx
        change Real.exp (-b * |x|) = Real.exp (-b * x)
        rw [abs_of_pos (show 0 < x from hx)]
    simpa only [Iic_union_Ioi, integrableOn_univ] using hleft.union hright
  have hL1 : Integrable f := by
    refine ((hbase 1 (by norm_num)).const_mul C).mono' hf.aestronglyMeasurable ?_
    filter_upwards [] with x
    simpa only [neg_mul, one_mul] using hbound x
  have hL2 : Integrable (fun x : ℝ => ‖f x‖ ^ 2) := by
    refine ((hbase 2 (by norm_num)).const_mul (C ^ 2)).mono'
      (hf.norm.pow 2).aestronglyMeasurable ?_
    filter_upwards [] with x
    have he : Real.exp (-|x|) ^ 2 = Real.exp (-2 * |x|) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hh := pow_le_pow_left₀ (norm_nonneg (f x)) (hbound x) 2
    simp only [mul_pow, he] at hh
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f x‖)]
    exact hh
  exact ⟨hL1, (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hL2⟩


theorem CothSums.kernel_logchart_L1_L2 :
  Integrable (fun x : ℝ => (CothSums.kernel (Real.exp (-x)) : ℂ)) ∧
    MemLp (fun x : ℝ => (CothSums.kernel (Real.exp (-x)) : ℂ)) 2 := by
  rcases CothSums.kernel_exp_decay with ⟨C, hC, hbound⟩
  have hc : Continuous CothSums.chi :=
    continuous_iff_continuousAt.mpr (fun r => (CothSums.chi_hasDerivAt r).continuousAt)
  have hk : Continuous CothSums.kernel := by
    exact hc.mul (continuous_const.sub hc)
  have hf : Continuous (fun x : ℝ => (CothSums.kernel (Real.exp (-x)) : ℂ)) :=
    Complex.continuous_ofReal.comp (hk.comp (Real.continuous_exp.comp continuous_neg))
  apply CothSums.Analysis.continuous_exp_abs_decay_L1_L2 _ hf C hC.le
  intro x
  simpa only [abs_neg] using hbound (-x)


set_option autoImplicit false


open MeasureTheory Set


open scoped FourierTransform SchwartzMap ContDiff ComplexConjugate


private theorem fourier_L1L2 (g : ℝ → ℂ) (hg₁ : Integrable g) (hg₂ : MemLp g 2) :
    MemLp (𝓕 g) 2 ∧ (∫ t : ℝ, ‖𝓕 g t‖ ^ 2) = ∫ x : ℝ, ‖g x‖ ^ 2 := by
  let G : Lp ℂ 2 (volume : Measure ℝ) := hg₂.toLp
  let H : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 G
  have hcont : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg₁
  have htest (φ : 𝓢(ℝ, ℂ)) :
      (∫ x : ℝ, φ x • 𝓕 g x) = ∫ x : ℝ, φ x • H x := by
    calc
      _ = ∫ x : ℝ, 𝓕 φ x • g x := by
        symm
        simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
          (ContinuousLinearMap.lsmul ℂ ℂ) (L := innerₗ ℝ)
          Real.continuous_fourierChar continuous_inner φ.integrable hg₁
      _ = ∫ x : ℝ, 𝓕 φ x • G x := by
        apply integral_congr_ae
        filter_upwards [hg₂.coeFn_toLp] with x hx
        rw [hx]
      _ = _ := by
        have he := congrArg (fun T : 𝓢'(ℝ, ℂ) => T φ)
          (Lp.fourier_toTemperedDistribution_eq G)
        simpa only [TemperedDistribution.fourier_apply,
          Lp.toTemperedDistribution_apply] using he
  have hae : 𝓕 g =ᵐ[volume] H := by
    apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
      ((Lp.memLp H).locallyIntegrable (by norm_num))
    intro φ hφ hc
    have hc' : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hc.comp_left rfl
    have hφ' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
    let φc : 𝓢(ℝ, ℂ) := hc'.toSchwartzMap hφ'
    simpa [φc] using htest φc
  refine ⟨(memLp_congr_ae hae).2 (Lp.memLp H), ?_⟩
  have hinner := Lp.inner_fourier_eq G G
  have he : (∫ x : ℝ, (‖H x‖ ^ 2 : ℂ)) =
      ∫ x : ℝ, (‖G x‖ ^ 2 : ℂ) := by
    change (∫ x : ℝ, inner ℂ (H x) (H x)) =
      ∫ x : ℝ, inner ℂ (G x) (G x) at hinner
    simpa only [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow] using! hinner
  have hnorm : (∫ x : ℝ, ‖H x‖ ^ 2) = ∫ x : ℝ, ‖G x‖ ^ 2 := by
    exact_mod_cast he
  calc
    _ = ∫ x : ℝ, ‖H x‖ ^ 2 := integral_congr_ae (hae.fun_comp (fun z : ℂ => ‖z‖ ^ 2))
    _ = ∫ x : ℝ, ‖G x‖ ^ 2 := hnorm
    _ = _ := integral_congr_ae (hg₂.coeFn_toLp.fun_comp (fun z : ℂ => ‖z‖ ^ 2))


private theorem logchart_square (f : ℝ → ℝ) :
    (IntegrableOn (fun r : ℝ => f r ^ 2 / r) (Ioi 0) ↔
      Integrable (fun x : ℝ => f (Real.exp x) ^ 2)) ∧
    (∫ r in Ioi (0 : ℝ), f r ^ 2 / r) =
      ∫ x : ℝ, f (Real.exp x) ^ 2 := by
  have hd : ∀ x ∈ (univ : Set ℝ),
      HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ hd Real.exp_injective.injOn
      (fun r : ℝ => f r ^ 2 / r)
  have he := integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ hd Real.exp_injective.injOn
      (fun r : ℝ => f r ^ 2 / r)
  have hh (x : ℝ) : |Real.exp x| • (f (Real.exp x) ^ 2 / Real.exp x) =
      f (Real.exp x) ^ 2 := by
    rw [abs_of_pos (Real.exp_pos _), smul_eq_mul]
    field_simp
  simp_rw [hh] at hi he
  simpa only [image_univ, Real.range_exp, integrableOn_univ,
    setIntegral_univ] using And.intro hi he


private theorem mellin_real_symmetry (f : ℝ → ℝ) (u : ℝ) :
    mellin (fun r : ℝ => (f r : ℂ)) (Complex.I * ((-u : ℝ) : ℂ)) =
      star (mellin (fun r : ℝ => (f r : ℂ)) (Complex.I * (u : ℂ))) := by
  let g : ℝ → ℂ := fun x => (f (Real.exp (-x)) : ℂ)
  have hm (v : ℝ) :
      mellin (fun r : ℝ => (f r : ℂ)) (Complex.I * (v : ℂ)) =
        𝓕 g (v / (2 * Real.pi)) := by
    simpa [g] using (mellin_eq_fourier (fun r : ℝ => (f r : ℂ))
      (s := Complex.I * (v : ℂ)))
  have hfourier (t : ℝ) : 𝓕 g (-t) = star (𝓕 g t) := by
    calc
      _ = ∫ x : ℝ, Complex.exp ((↑(-2 * Real.pi * x * (-t))) * Complex.I) *
          (f (Real.exp (-x)) : ℂ) := by
        rw [Real.fourier_real_eq_integral_exp_smul]
        rfl
      _ = ∫ x : ℝ, conj (Complex.exp ((↑(-2 * Real.pi * x * t)) * Complex.I) *
          (f (Real.exp (-x)) : ℂ)) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
        congr 1
        push_cast
        ring
      _ = star (𝓕 g t) := by
        have hi := integral_conj (𝕜 := ℂ) (μ := (volume : Measure ℝ))
          (f := fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * x * t)) * Complex.I) *
            (f (Real.exp (-x)) : ℂ))
        simpa only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul, g] using! hi
  rw [hm (-u), hm u]
  simpa only [neg_div] using hfourier (u / (2 * Real.pi))


theorem CothSums.Analysis.mellin_real_halfLine_plancherel (f : ℝ → ℝ)
    (hf₁ : Integrable (fun y : ℝ => (f (Real.exp y) : ℂ)))
    (hf₂ : MemLp (fun y : ℝ => (f (Real.exp y) : ℂ)) 2) :
    IntegrableOn (fun r : ℝ => f r ^ 2 / r) (Ioi 0) ∧
    IntegrableOn (fun u : ℝ =>
      ‖mellin (fun r : ℝ => (f r : ℂ)) (Complex.I * (u : ℂ))‖ ^ 2) (Ioi 0) ∧
    (∫ r in Ioi (0 : ℝ), f r ^ 2 / r) =
      (1 / Real.pi) * ∫ u in Ioi (0 : ℝ),
        ‖mellin (fun r : ℝ => (f r : ℂ)) (Complex.I * (u : ℂ))‖ ^ 2 := by
  let P : ℝ → ℂ := fun y => (f (Real.exp y) : ℂ)
  let g : ℝ → ℂ := fun y => (f (Real.exp (-y)) : ℂ)
  have hg₁ : Integrable g := by
    simpa [g, neg_one_mul] using
      (hf₁.comp_mul_left' (show (-1 : ℝ) ≠ 0 by norm_num))
  have hPsq : Integrable (fun y : ℝ => ‖P y‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hf₂.1).1 hf₂
  have hgsq : Integrable (fun y : ℝ => ‖g y‖ ^ 2) := by
    simpa [g, P, neg_one_mul] using
      (hPsq.comp_mul_left' (show (-1 : ℝ) ≠ 0 by norm_num))
  have hg₂ : MemLp g 2 :=
    (memLp_two_iff_integrable_sq_norm hg₁.aestronglyMeasurable).2 hgsq
  have hfour := fourier_L1L2 g hg₁ hg₂
  have hFint : Integrable (fun y : ℝ => ‖𝓕 g y‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hfour.1.1).1 hfour.1
  have hsource : IntegrableOn (fun r : ℝ => f r ^ 2 / r) (Ioi 0) := by
    apply (logchart_square f).1.mpr
    simpa [P, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hPsq
  have hchart : (∫ r in Ioi (0 : ℝ), f r ^ 2 / r) =
      ∫ y : ℝ, ‖g y‖ ^ 2 := by
    rw [(logchart_square f).2]
    have he := Measure.integral_comp_mul_left (fun y : ℝ => f (Real.exp y) ^ 2) (-1)
    simpa [g, neg_one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs] using he.symm
  let M : ℝ → ℂ := fun u =>
    mellin (fun r : ℝ => (f r : ℂ)) (Complex.I * (u : ℂ))
  let Q : ℝ → ℝ := fun u => ‖M u‖ ^ 2
  have hM (u : ℝ) : M u = 𝓕 g (u / (2 * Real.pi)) := by
    simpa [M, g] using (mellin_eq_fourier (fun r : ℝ => (f r : ℂ))
      (s := Complex.I * (u : ℂ)))
  have hpi : 0 < 2 * Real.pi := by positivity
  have hQ : Integrable Q := by
    simpa only [Q, hM] using hFint.comp_div (ne_of_gt hpi)
  have hfull : (∫ u : ℝ, Q u) =
      (2 * Real.pi) * ∫ r in Ioi (0 : ℝ), f r ^ 2 / r := by
    calc
      _ = ∫ u : ℝ, ‖𝓕 g (u / (2 * Real.pi))‖ ^ 2 := by
        simp only [Q, hM]
      _ = (2 * Real.pi) * ∫ y : ℝ, ‖𝓕 g y‖ ^ 2 := by
        simpa only [abs_of_pos hpi, smul_eq_mul] using
          Measure.integral_comp_div (fun y : ℝ => ‖𝓕 g y‖ ^ 2) (2 * Real.pi)
      _ = _ := by rw [hfour.2, ← hchart]
  have heven (u : ℝ) : Q (-u) = Q u := by
    dsimp [Q, M]
    rw [mellin_real_symmetry f u, norm_star]
  have hsplit : (∫ u : ℝ, Q u) = 2 * ∫ u in Ioi (0 : ℝ), Q u := by
    have habs (u : ℝ) : Q |u| = Q u := by
      by_cases hu : 0 ≤ u
      · rw [abs_of_nonneg hu]
      · rw [abs_of_neg (lt_of_not_ge hu), heven]
    simpa only [habs] using (integral_comp_abs (f := Q))
  refine ⟨hsource, hQ.integrableOn, ?_⟩
  change (∫ r in Ioi (0 : ℝ), f r ^ 2 / r) =
    (1 / Real.pi) * ∫ u in Ioi (0 : ℝ), Q u
  rw [one_div, mul_comm Real.pi⁻¹, ← div_eq_mul_inv]
  apply (eq_div_iff Real.pi_ne_zero).2
  nlinarith [hfull, hsplit]


theorem CothSums.halfLine_mellin_parseval :
    IntegrableOn (fun r : ℝ => CothSums.kernel r ^ 2 / r) (Set.Ioi 0) ∧
    IntegrableOn (fun u : ℝ => ‖CothSums.mellinKernel u‖ ^ 2) (Set.Ioi 0) ∧
    CothSums.secondMoment = (1 / Real.pi) *
      ∫ u in Set.Ioi (0 : ℝ), ‖CothSums.mellinKernel u‖ ^ 2 := by
  have hn := CothSums.kernel_logchart_L1_L2
  have hp₁ : Integrable (fun x : ℝ => (CothSums.kernel (Real.exp x) : ℂ)) := by
    simpa only [neg_neg] using hn.1.comp_neg
  have hp₂ : MemLp (fun x : ℝ => (CothSums.kernel (Real.exp x) : ℂ)) 2 := by
    simpa only [Function.comp_def, neg_neg] using
      hn.2.comp_measurePreserving (Measure.measurePreserving_neg volume)
  simpa only [CothSums.secondMoment, CothSums.mellinKernel] using
    CothSums.Analysis.mellin_real_halfLine_plancherel CothSums.kernel hp₁ hp₂


set_option autoImplicit false


open MeasureTheory


theorem CothSums.Analysis.cubic_cos_moment_antiperiodic (a : ℝ) (ha : a ≠ 0) (hs : Real.sin a = 0)
    (hc : Real.cos a = -1) :
    (∫ x in (0 : ℝ)..1,
      (2 * x - 6 * x ^ 2 + 4 * x ^ 3) * Real.cos (a * x)) =
      -4 / a ^ 2 + 48 / a ^ 4 := by
  let F : ℝ → ℝ := fun x =>
    ((2 * x - 6 * x ^ 2 + 4 * x ^ 3) / a - (24 * x - 12) / a ^ 3) *
        Real.sin (a * x) +
      ((2 - 12 * x + 12 * x ^ 2) / a ^ 2 - 24 / a ^ 4) * Real.cos (a * x)
  have hd (x : ℝ) :
      HasDerivAt F ((2 * x - 6 * x ^ 2 + 4 * x ^ 3) * Real.cos (a * x)) x := by
    have hp : HasDerivAt (fun y : ℝ => 2 * y - 6 * y ^ 2 + 4 * y ^ 3)
        (2 - 12 * x + 12 * x ^ 2) x := by
      exact ((((hasDerivAt_id x).const_mul 2).sub
        (((hasDerivAt_id x).pow 2).const_mul 6)).add
        (((hasDerivAt_id x).pow 3).const_mul 4)).congr_deriv (by simp only [id_eq]; ring)
    have hq : HasDerivAt (fun y : ℝ => 2 - 12 * y + 12 * y ^ 2)
        (24 * x - 12) x := by
      exact (((hasDerivAt_const x (2 : ℝ)).sub
        ((hasDerivAt_id x).const_mul 12)).add
        (((hasDerivAt_id x).pow 2).const_mul 12)).congr_deriv (by simp only [id_eq]; ring)
    have hg := (hp.div_const a).sub
      ((((hasDerivAt_id x).const_mul 24).sub_const 12).div_const (a ^ 3))
    have hh := (hq.div_const (a ^ 2)).sub_const (24 / a ^ 4)
    have hsin := ((hasDerivAt_id x).const_mul a).sin
    have hcos := ((hasDerivAt_id x).const_mul a).cos
    exact ((hg.mul hsin).add (hh.mul hcos)).congr_deriv (by
      simp only [Pi.sub_apply, id_eq]
      field_simp [ha]
      <;> ring)
  have hi : IntervalIntegrable
      (fun x : ℝ => (2 * x - 6 * x ^ 2 + 4 * x ^ 3) * Real.cos (a * x))
      MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous
      (fun x : ℝ => (2 * x - 6 * x ^ 2 + 4 * x ^ 3) * Real.cos (a * x))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi]
  simp [F, hs, hc]
  <;> field_simp [ha] <;> ring


theorem CothSums.evaluation_of_integral_identities
  (fourier_identity : ∀ P : Polynomial ℝ, P.eval 0 = 0 → P.eval 1 = 0 →
    CothSums.testMoment P = 2 * ∑' n : ℕ,
      (Real.tanh (Real.pi * (2 * (n : ℝ) + 1) / 2) / (2 * (n : ℝ) + 1)) *
        CothSums.cosineTest P n)
  (cubic_lambert_evaluation : HasSum (CothSums.oddTanhTerm 3) (Real.pi ^ 3 / 32))
  (quintic_lambert_evaluation : HasSum (CothSums.oddTanhTerm 5)
    (Real.pi ^ 5 / 252 - (9 / 32) * ∑' n : ℕ, CothSums.cothTerm n))
  (coth_summability : Summable CothSums.cothTerm)
  (mellin_identity : ∀ u : ℝ,
    CothSums.mellinKernel u = CothSums.lambda (Complex.I * (u : ℂ) / 4) /
      (4 * (Real.Gamma (1 / 4) : ℂ) ^ 2))
  (plancherel_identity :
    IntegrableOn (fun r : ℝ => CothSums.kernel r ^ 2 / r) (Set.Ioi 0) ∧
    IntegrableOn (fun u : ℝ => ‖CothSums.mellinKernel u‖ ^ 2) (Set.Ioi 0) ∧
    CothSums.secondMoment = (1 / Real.pi) *
      ∫ u in Set.Ioi (0 : ℝ), ‖CothSums.mellinKernel u‖ ^ 2) :
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
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hgpos : 0 < Real.Gamma (1 / 4 : ℝ) :=
    Real.Gamma_pos_of_pos (by norm_num)
  have hg : Real.Gamma (1 / 4 : ℝ) ≠ 0 := ne_of_gt hgpos
  let P : Polynomial ℝ := Polynomial.X ^ 2 * (1 - Polynomial.X) ^ 2
  have htest : CothSums.testMoment P = CothSums.secondMoment := by
    unfold CothSums.testMoment CothSums.secondMoment
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with r
    simp [P, CothSums.kernel, mul_pow]
  have hPd (x : ℝ) : P.derivative.eval x = 2 * x - 6 * x ^ 2 + 4 * x ^ 3 := by
    simp [P, Polynomial.derivative_mul, Polynomial.derivative_pow]
    <;> ring
  have hcoeff (n : ℕ) : CothSums.cosineTest P n =
      -4 / ((2 * (n : ℝ) + 1) * Real.pi) ^ 2 +
        48 / ((2 * (n : ℝ) + 1) * Real.pi) ^ 4 := by
    unfold CothSums.cosineTest
    simp_rw [hPd]
    have ha : (2 * (n : ℝ) + 1) * Real.pi ≠ 0 :=
      mul_ne_zero (by positivity) hp
    have hs : Real.sin ((2 * (n : ℝ) + 1) * Real.pi) = 0 := by
      convert Real.sin_nat_mul_pi (2 * n + 1) using 1 <;> push_cast <;> ring
    have hc : Real.cos ((2 * (n : ℝ) + 1) * Real.pi) = -1 := by
      have hc' := Real.cos_nat_mul_pi (2 * n + 1)
      norm_num [pow_add, pow_mul] at hc'
      convert hc' using 1 <;> push_cast <;> ring
    exact CothSums.Analysis.cubic_cos_moment_antiperiodic _ ha hs hc
  have hterm (n : ℕ) :
      (Real.tanh (Real.pi * (2 * (n : ℝ) + 1) / 2) / (2 * (n : ℝ) + 1)) *
          CothSums.cosineTest P n =
        (-4 / Real.pi ^ 2) * CothSums.oddTanhTerm 3 n +
          (48 / Real.pi ^ 4) * CothSums.oddTanhTerm 5 n := by
    rw [hcoeff]
    unfold CothSums.oddTanhTerm
    have hn : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hp, hn]
    <;> ring
  have hsum := (cubic_lambert_evaluation.mul_left (-4 / Real.pi ^ 2)).add
    (quintic_lambert_evaluation.mul_left (48 / Real.pi ^ 4))
  have hmoment := fourier_identity P (by simp [P]) (by simp [P])
  rw [htest, tsum_congr hterm, hsum.tsum_eq] at hmoment
  have hm : CothSums.secondMoment =
      11 * Real.pi / 84 - 27 * (∑' n : ℕ, CothSums.cothTerm n) / Real.pi ^ 4 := by
    calc
      CothSums.secondMoment = _ := hmoment
      _ = _ := by field_simp [hp] <;> ring
  have hnorm (u : ℝ) : ‖CothSums.mellinKernel u‖ ^ 2 =
      CothSums.barnesJIntegrand u / Real.Gamma (1 / 4) ^ 4 := by
    rw [mellin_identity]
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hgpos]
    norm_num [CothSums.barnesJIntegrand]
    <;> field_simp [hg] <;> ring
  have hi : (∫ u in Set.Ioi (0 : ℝ), ‖CothSums.mellinKernel u‖ ^ 2) =
      CothSums.barnesJ / Real.Gamma (1 / 4) ^ 4 := by
    simp_rw [hnorm, div_eq_mul_inv]
    unfold CothSums.barnesJ
    rw [MeasureTheory.integral_mul_const]
  have hmj : CothSums.secondMoment =
      CothSums.barnesJ / (Real.pi * Real.Gamma (1 / 4) ^ 4) := by
    rw [plancherel_identity.2.2, hi]
    field_simp
  have hs : (∑' n : ℕ, CothSums.cothTerm n) =
      11 * Real.pi ^ 5 / 2268 - Real.pi ^ 4 * CothSums.secondMoment / 27 := by
    field_simp [hp] at hm ⊢
    nlinarith [hm]
  change (∑' n : ℕ, CothSums.cothTerm n) =
    11 * Real.pi ^ 5 / 2268 -
      Real.pi ^ 3 / (27 * Real.Gamma (1 / 4) ^ 4) * CothSums.barnesJ
  rw [hs, hmj]
  field_simp [hp, hg]
  <;> ring


theorem CothSums.evaluation_of_fourier_lambert_mellin
  (fourier_identity : ∀ P : Polynomial ℝ, P.eval 0 = 0 → P.eval 1 = 0 →
    CothSums.testMoment P = 2 * ∑' n : ℕ,
      (Real.tanh (Real.pi * (2 * (n : ℝ) + 1) / 2) / (2 * (n : ℝ) + 1)) *
        CothSums.cosineTest P n)
  (cubic_lambert_evaluation : HasSum (CothSums.oddTanhTerm 3) (Real.pi ^ 3 / 32))
  (quintic_lambert_evaluation : HasSum (CothSums.oddTanhTerm 5)
    (Real.pi ^ 5 / 252 - (9 / 32) * ∑' n : ℕ, CothSums.cothTerm n))
  (coth_summability : Summable CothSums.cothTerm)
  (mellin_identity : ∀ u : ℝ,
    CothSums.mellinKernel u = CothSums.lambda (Complex.I * (u : ℂ) / 4) /
      (4 * (Real.Gamma (1 / 4) : ℂ) ^ 2))
 :
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
  exact CothSums.evaluation_of_integral_identities fourier_identity cubic_lambert_evaluation quintic_lambert_evaluation
    coth_summability mellin_identity CothSums.halfLine_mellin_parseval


theorem CothSums.cothTerm_summable : Summable CothSums.cothTerm := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 5) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hb : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 5) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr hp
  apply (hb.mul_left 2).of_norm_bounded
  intro n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hx : 1 ≤ Real.pi * ((n : ℝ) + 1) := by
    nlinarith [Real.pi_pos, Real.pi_gt_three]
  have hs : 1 ≤ Real.sinh (Real.pi * ((n : ℝ) + 1)) :=
    hx.trans (Real.self_le_sinh_iff.mpr (by linarith))
  have he : Real.exp (-(Real.pi * ((n : ℝ) + 1))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hc := Real.cosh_sub_sinh (Real.pi * ((n : ℝ) + 1))
  have hspos : 0 < Real.sinh (Real.pi * ((n : ℝ) + 1)) := by linarith
  have hratio : Real.cosh (Real.pi * ((n : ℝ) + 1)) /
      Real.sinh (Real.pi * ((n : ℝ) + 1)) ≤ 2 :=
    (div_le_iff₀ hspos).mpr (by linarith)
  have hnonneg : 0 ≤ CothSums.cothTerm n := by
    unfold CothSums.cothTerm
    exact div_nonneg (div_nonneg (Real.cosh_pos _).le hspos.le) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  unfold CothSums.cothTerm
  calc
    _ ≤ 2 / ((n : ℝ) + 1) ^ 5 :=
      div_le_div_of_nonneg_right hratio (by positivity)
    _ = 2 * (1 / ((n : ℝ) + 1) ^ 5) := by ring


theorem CothSums.evaluation_of_fourier_and_lambert_mellin
  (fourier_identity : ∀ P : Polynomial ℝ, P.eval 0 = 0 → P.eval 1 = 0 →
    CothSums.testMoment P = 2 * ∑' n : ℕ,
      (Real.tanh (Real.pi * (2 * (n : ℝ) + 1) / 2) / (2 * (n : ℝ) + 1)) *
        CothSums.cosineTest P n)
  (cubic_lambert_evaluation : HasSum (CothSums.oddTanhTerm 3) (Real.pi ^ 3 / 32))
  (quintic_lambert_evaluation : HasSum (CothSums.oddTanhTerm 5)
    (Real.pi ^ 5 / 252 - (9 / 32) * ∑' n : ℕ, CothSums.cothTerm n))
  (mellin_identity : ∀ u : ℝ,
    CothSums.mellinKernel u = CothSums.lambda (Complex.I * (u : ℂ) / 4) /
      (4 * (Real.Gamma (1 / 4) : ℂ) ^ 2))
 :
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
  exact CothSums.evaluation_of_fourier_lambert_mellin fourier_identity cubic_lambert_evaluation quintic_lambert_evaluation
    CothSums.cothTerm_summable mellin_identity


set_option autoImplicit false


set_option autoImplicit false


open Complex


private theorem coth_pf (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2 + x ^ 2))
      ((Real.pi * (Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x)) - 1 / x) /
        (2 * x)) := by
  let z : ℂ := (x : ℂ) * Complex.I
  have hz : z ∈ Complex.integerComplement := by
    exact UpperHalfPlane.coe_mem_integerComplement
      ⟨z, by simpa [z] using hx⟩
  have ht : HasSum (fun n : ℕ => cotTerm z n)
      ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) - 1 / z) := by
    have hh := (summable_cotTerm hz).hasSum
    have he : (∑' n : ℕ, cotTerm z n) =
        (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) - 1 / z := by
      simpa only [cotTerm] using (cot_series_rep' hz).symm
    rwa [he] at hh
  have hterm (n : ℕ) : (cotTerm z n).im =
      (-2 * x) * (1 / (((n : ℝ) + 1) ^ 2 + x ^ 2)) := by
    simp [cotTerm, z, Complex.div_im, Complex.normSq, pow_two]
    <;> ring
  have hsp : Real.sinh (Real.pi * x) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hx))
  have hcot : Complex.cot ((Real.pi : ℂ) * z) =
      -(((Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x) : ℝ) : ℂ) * Complex.I) := by
    have he : (Real.pi : ℂ) * z = ((Real.pi * x : ℝ) : ℂ) * Complex.I := by
      dsimp [z]
      push_cast
      ring
    rw [he, Complex.cot_eq_cos_div_sin, Complex.cos_mul_I, Complex.sin_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    simp only [Complex.ofReal_div]
    field_simp [Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr hsp]
    <;> simp only [mul_pow, Complex.I_sq]
    <;> ring
  have hlim : (((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) - 1 / z).im) =
      -Real.pi * (Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x)) + 1 / x := by
    rw [hcot]
    simp only [z, Complex.sub_im, Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.div_im, Complex.one_re, Complex.one_im,
      map_mul, Complex.normSq_I, Complex.normSq_ofReal,
      mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul]
    field_simp [hx.ne']
    <;> ring
  have hr : HasSum
      (fun n : ℕ => (-2 * x) * (1 / (((n : ℝ) + 1) ^ 2 + x ^ 2)))
      (-Real.pi * (Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x)) + 1 / x) := by
    simpa only [hterm, hlim] using Complex.hasSum_im ht
  have hs := hr.mul_left ((-2 * x)⁻¹)
  convert! hs using 1
  · ext n
    field_simp [hx.ne']
  · field_simp [hx.ne']
    <;> ring


private theorem tanh_pf (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => 1 / ((2 * (n : ℝ) + 1) ^ 2 + x ^ 2))
      (Real.pi * Real.tanh (Real.pi * x / 2) / (4 * x)) := by
  let f : ℕ → ℝ := fun n => 1 / (((n : ℝ) + 1) ^ 2 + x ^ 2)
  have hf := coth_pf x hx
  have hodd : Summable (fun n : ℕ => f (2 * n)) := hf.summable.comp_injective
    (show Function.Injective (fun n : ℕ => 2 * n) by intro m n h; dsimp at h; omega)
  have heven : HasSum (fun n : ℕ => f (2 * n + 1))
      ((1 / 4) * ((Real.pi * (Real.cosh (Real.pi * (x / 2)) /
        Real.sinh (Real.pi * (x / 2))) - 1 / (x / 2)) / (2 * (x / 2)))) := by
    convert! (coth_pf (x / 2) (by linarith)).mul_left (1 / 4) using 1
    ext n
    dsimp [f]
    push_cast
    field_simp
    <;> ring
  have hadd := hodd.hasSum.even_add_odd heven
  have heq := hf.unique hadd
  have hs : Real.sinh (Real.pi * x / 2) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))
  have hc : Real.cosh (Real.pi * x / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hd : Real.sinh (Real.pi * x) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))
  have hdouble : 2 * (Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x)) -
      Real.cosh (Real.pi * x / 2) / Real.sinh (Real.pi * x / 2) =
      Real.tanh (Real.pi * x / 2) := by
    rw [show Real.pi * x = 2 * (Real.pi * x / 2) by ring,
      Real.cosh_two_mul, Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
    field_simp [hs, hc]
    <;> nlinarith [Real.cosh_sq_sub_sinh_sq (Real.pi * x / 2)]
  have hval : (∑' n : ℕ, f (2 * n)) =
      Real.pi * Real.tanh (Real.pi * x / 2) / (4 * x) := by
    rw [← hdouble]
    have heq' := heq
    simp only [show Real.pi * (x / 2) = Real.pi * x / 2 by ring] at heq'
    field_simp [hx.ne', hs, hc, hd] at heq' ⊢
    nlinarith [heq']
  have hh : HasSum (fun n : ℕ => f (2 * n))
      (Real.pi * Real.tanh (Real.pi * x / 2) / (4 * x)) := hval ▸ hodd.hasSum
  simpa only [f, Nat.cast_mul, Nat.cast_ofNat] using hh


set_option autoImplicit false


theorem CothSums.Analysis.odd_pseries_hasSum (s : ℕ) (A : ℝ)
    (h : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ s) A) :
    HasSum (fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + 1) ^ s)
      ((1 - 1 / (2 : ℝ) ^ s) * A) := by
  let f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ s
  have he : HasSum (fun n : ℕ => f (2 * n)) ((1 / (2 : ℝ) ^ s) * A) := by
    have heq : (fun n : ℕ => f (2 * n)) =
        (fun n : ℕ => (1 / (2 : ℝ) ^ s) * (1 / (n : ℝ) ^ s)) := by
      funext n
      simp only [f, Nat.cast_mul, Nat.cast_ofNat, mul_pow, one_div, mul_inv_rev]
      ring
    rw [heq]
    exact h.mul_left (1 / (2 : ℝ) ^ s)
  have ho : Summable (fun n : ℕ => f (2 * n + 1)) :=
    h.summable.comp_injective (fun n m hnm => by omega)
  have hv : (1 / (2 : ℝ) ^ s) * A + (∑' n : ℕ, f (2 * n + 1)) = A :=
    (he.even_add_odd ho.hasSum).unique h
  have hs : (∑' n : ℕ, f (2 * n + 1)) = (1 - 1 / (2 : ℝ) ^ s) * A := by
    linarith
  convert ho.hasSum using 1
  · ext n
    simp only [f, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  · exact hs.symm


private theorem odd_values :
  HasSum (fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 8) ∧
  HasSum (fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 4) (Real.pi ^ 4 / 96) := by
  constructor
  · convert CothSums.Analysis.odd_pseries_hasSum 2 _ hasSum_zeta_two using 1 <;> norm_num <;> ring
  · convert CothSums.Analysis.odd_pseries_hasSum 4 _ hasSum_zeta_four using 1 <;> norm_num <;> ring


private theorem lattice_value :
    HasSum (fun p : ℕ × ℕ => (1 : ℝ) /
      ((2 * (p.1 : ℝ) + 1) ^ 2 *
        ((2 * (p.1 : ℝ) + 1) ^ 2 + (2 * (p.2 : ℝ) + 1) ^ 2)))
      (Real.pi ^ 4 / 128) := by
  let a : ℕ → ℝ := fun n => (2 * (n : ℝ) + 1) ^ 2
  let W : ℕ × ℕ → ℝ := fun p => 1 / (a p.1 * (a p.1 + a p.2))
  let V : ℕ × ℕ → ℝ := fun p => (1 / a p.1) * (1 / a p.2)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hs : HasSum (fun n : ℕ => 1 / a n) (Real.pi ^ 2 / 8) := odd_values.1
  have hV : Summable V := hs.summable.mul_of_nonneg hs.summable
    (fun n => by positivity) (fun n => by positivity)
  have hW : Summable W := by
    apply hV.of_norm_bounded
    intro p
    have hn : 0 ≤ W p := by dsimp [W]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    calc
      _ ≤ 1 / (a p.1 * a p.2) := by
        apply one_div_le_one_div_of_le (mul_pos (ha p.1) (ha p.2))
        exact mul_le_mul_of_nonneg_left (by linarith [ha p.1]) (ha p.1).le
      _ = V p := by dsimp [V]; ring
  have hVsum : (∑' p : ℕ × ℕ, V p) = (Real.pi ^ 2 / 8) ^ 2 := by
    have hh := hs.summable.tsum_mul_tsum hs.summable hV
    rw [hs.tsum_eq] at hh
    simpa only [pow_two] using hh.symm
  have hpair (p : ℕ × ℕ) : W p + W p.swap = V p := by
    dsimp [W, V]
    field_simp [(ha p.1).ne', (ha p.2).ne',
      (add_pos (ha p.1) (ha p.2)).ne', (add_pos (ha p.2) (ha p.1)).ne']
    <;> ring
  have hswap : (∑' p : ℕ × ℕ, W p.swap) = ∑' p : ℕ × ℕ, W p :=
    (Equiv.prodComm ℕ ℕ).tsum_eq W
  have hadd := hW.tsum_add hW.prod_symm
  have heq : 2 * (∑' p : ℕ × ℕ, W p) = (Real.pi ^ 2 / 8) ^ 2 := by
    simpa only [hpair, hswap, hVsum, two_mul] using hadd.symm
  have heval : (∑' p : ℕ × ℕ, W p) = Real.pi ^ 4 / 128 := by
    nlinarith [heq]
  convert! hW.hasSum using 1
  · exact heval.symm


set_option autoImplicit false


private theorem tanh_summable : Summable (CothSums.oddTanhTerm 3) ∧
    Summable (CothSums.oddTanhTerm 5) := by
  have h (s : ℕ) (hs : 1 < s) : Summable (CothSums.oddTanhTerm s) := by
    have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ s) :=
      Real.summable_one_div_nat_pow.mpr hs
    have hodd : Summable (fun n : ℕ => 1 / (2 * (n : ℝ) + 1) ^ s) := by
      have hh := hp.comp_injective
        (show Function.Injective (fun n : ℕ => 2 * n + 1) by intro m n hmn; dsimp at hmn; omega)
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hh
    apply hodd.of_norm_bounded
    intro n
    unfold CothSums.oddTanhTerm
    simp only [norm_div, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (2 * (n : ℝ) + 1) ^ s)]
    exact div_le_div_of_nonneg_right (Real.abs_tanh_lt_one _).le (by positivity)
  exact ⟨h 3 (by norm_num), h 5 (by norm_num)⟩


theorem CothSums.oddTanhTerm_hasSum_three : HasSum (CothSums.oddTanhTerm 3) (Real.pi ^ 3 / 32) := by
  let W : ℕ × ℕ → ℝ := fun p => (1 : ℝ) /
    ((2 * (p.1 : ℝ) + 1) ^ 2 *
      ((2 * (p.1 : ℝ) + 1) ^ 2 + (2 * (p.2 : ℝ) + 1) ^ 2))
  have hW : HasSum W (Real.pi ^ 4 / 128) := lattice_value
  have hrow (n : ℕ) : (∑' m : ℕ, W (n, m)) =
      (Real.pi / 4) * CothSums.oddTanhTerm 3 n := by
    let a : ℝ := 2 * (n : ℝ) + 1
    have ha : 0 < a := by dsimp [a]; positivity
    have hh := (tanh_pf a ha).mul_left (a ^ 2)⁻¹
    have hhs : HasSum (fun m : ℕ => W (n, m))
        ((Real.pi / 4) * CothSums.oddTanhTerm 3 n) := by
      convert! hh using 1
      · ext m
        dsimp [W, a]
        field_simp
        <;> ring
      · dsimp [CothSums.oddTanhTerm]
        change (Real.pi / 4) * (Real.tanh (Real.pi * a / 2) / a ^ 3) = _
        field_simp [ha.ne']
        <;> ring
    exact hhs.tsum_eq
  have heq : (Real.pi / 4) * (∑' n : ℕ, CothSums.oddTanhTerm 3 n) =
      Real.pi ^ 4 / 128 := by
    calc
      _ = ∑' n : ℕ, (Real.pi / 4) * CothSums.oddTanhTerm 3 n :=
        tsum_mul_left.symm
      _ = ∑' n : ℕ, ∑' m : ℕ, W (n, m) := tsum_congr (fun n => (hrow n).symm)
      _ = ∑' p : ℕ × ℕ, W p := hW.summable.tsum_prod.symm
      _ = _ := hW.tsum_eq
  have hval : (∑' n : ℕ, CothSums.oddTanhTerm 3 n) = Real.pi ^ 3 / 32 := by
    apply (mul_left_cancel₀ (show Real.pi / 4 ≠ 0 by positivity))
    rw [heq]
    ring
  exact hval ▸ tanh_summable.1.hasSum


open MeasureTheory


theorem CothSums.evaluation_of_fourier_quintic_lambert_mellin
  (fourier_identity : ∀ P : Polynomial ℝ, P.eval 0 = 0 → P.eval 1 = 0 →
    CothSums.testMoment P = 2 * ∑' n : ℕ,
      (Real.tanh (Real.pi * (2 * (n : ℝ) + 1) / 2) / (2 * (n : ℝ) + 1)) *
        CothSums.cosineTest P n)
  (quintic_lambert_evaluation : HasSum (CothSums.oddTanhTerm 5)
    (Real.pi ^ 5 / 252 - (9 / 32) * ∑' n : ℕ, CothSums.cothTerm n))
  (mellin_identity : ∀ u : ℝ,
    CothSums.mellinKernel u = CothSums.lambda (Complex.I * (u : ℂ) / 4) /
      (4 * (Real.Gamma (1 / 4) : ℂ) ^ 2))
 :
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
  exact CothSums.evaluation_of_fourier_and_lambert_mellin
    fourier_identity CothSums.oddTanhTerm_hasSum_three quintic_lambert_evaluation mellin_identity


set_option autoImplicit false


open MeasureTheory Set


theorem CothSums.chi_range_and_tail (r : ℝ) (hr : 0 < r) :
  0 ≤ CothSums.chi r ∧ CothSums.chi r ≤ 1 ∧
  1 - CothSums.chi r = (4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2) *
    (∫ t in Set.Ioi r, (Real.sqrt (1 + t ^ 4))⁻¹) ∧
  1 - CothSums.chi r ≤ (4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2) / r := by
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  have hC : 0 < C := CothSums.chi_prefactor_pos
  have hG : Real.Gamma (1 / 4 : ℝ) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by norm_num))
  have hs : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have htotal : C * (∫ t in Set.Ioi (0 : ℝ), (Real.sqrt (1 + t ^ 4))⁻¹) = 1 := by
    rw [CothSums.density_integral]
    dsimp [C]
    field_simp [hG, hs]
  have hcomp : 1 - CothSums.chi r = C * (∫ t in Set.Ioi r,
      (Real.sqrt (1 + t ^ 4))⁻¹) := by
    have hsplit := congrArg (fun v : ℝ => C * v) (CothSums.density_head_tail r hr)
    rw [mul_add, htotal] at hsplit
    change 1 - C * (∫ t in (0 : ℝ)..r, (Real.sqrt (1 + t ^ 4))⁻¹) = _
    linarith
  have htail := CothSums.density_tail_bound r hr
  refine ⟨CothSums.chi_nonneg hr.le, ?_, hcomp, ?_⟩
  · have hnonneg : 0 ≤ 1 - CothSums.chi r := by
      rw [hcomp]
      exact mul_nonneg hC.le htail.2.1
    linarith
  · rw [hcomp]
    simpa only [C, div_eq_mul_inv] using mul_le_mul_of_nonneg_left htail.2.2 hC.le


open Asymptotics


private theorem kernel_mellin_analytic :
  ∀ s : ℂ, (-1 : ℝ) < s.re → s.re < 1 →
    MellinConvergent (fun r : ℝ => (CothSums.kernel r : ℂ)) s ∧
    DifferentiableAt ℂ (mellin (fun r : ℝ => (CothSums.kernel r : ℂ))) s := by
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  have hc : Continuous CothSums.chi :=
    continuous_iff_continuousAt.mpr (fun r => (CothSums.chi_hasDerivAt r).continuousAt)
  have hk : Continuous CothSums.kernel := hc.mul (continuous_const.sub hc)
  have hkc : Continuous (fun r : ℝ => (CothSums.kernel r : ℂ)) :=
    Complex.continuous_ofReal.comp hk
  have hbound (r : ℝ) (hr : 0 < r) :
      ‖(CothSums.kernel r : ℂ)‖ ≤ C * r ∧
      ‖(CothSums.kernel r : ℂ)‖ ≤ C / r := by
    have hchi := CothSums.chi_range_and_tail r hr
    have hp : 0 ≤ CothSums.kernel r :=
      mul_nonneg hchi.1 (sub_nonneg.mpr hchi.2.1)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
    constructor
    · calc
        CothSums.kernel r ≤ CothSums.chi r := by
          unfold CothSums.kernel
          nlinarith [sq_nonneg (CothSums.chi r)]
        _ ≤ C * r := CothSums.chi_le_prefactor_mul hr.le
    · calc
        CothSums.kernel r ≤ 1 - CothSums.chi r := by
          unfold CothSums.kernel
          nlinarith [sq_nonneg (1 - CothSums.chi r)]
        _ ≤ C / r := hchi.2.2.2
  have htop : (fun r : ℝ => (CothSums.kernel r : ℂ)) =O[Filter.atTop]
      (fun r : ℝ => r ^ (-(1 : ℝ))) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
    simpa only [Real.rpow_neg_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), div_eq_mul_inv] using (hbound r hr).2
  have hbot : (fun r : ℝ => (CothSums.kernel r : ℂ)) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun r : ℝ => r ^ (-(-1 : ℝ))) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [neg_neg, Real.rpow_one, Real.norm_eq_abs,
      abs_of_pos (show 0 < r from hr)] using (hbound r hr).1
  have hloc : LocallyIntegrableOn (fun r : ℝ => (CothSums.kernel r : ℂ))
      (Set.Ioi (0 : ℝ)) volume :=
    hkc.locallyIntegrable.locallyIntegrableOn (Set.Ioi (0 : ℝ))
  intro s hs0 hs1
  exact ⟨mellinConvergent_of_isBigO_rpow hloc htop hs1 hbot hs0,
    mellin_differentiableAt_of_isBigO_rpow hloc htop hs1 hbot hs0⟩


open Filter


private theorem weighted_density_integrable (u : ℝ) :
    IntegrableOn (fun r : ℝ => ((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ) *
      (r : ℂ) ^ (Complex.I * (u : ℂ))) (Set.Ioi 0) := by
  have hi : IntegrableOn (fun r : ℝ => (Real.sqrt (1 + r ^ 4))⁻¹) (Ioi 0) := by
    have hc : Continuous (fun t : ℝ => (Real.sqrt (1 + t ^ 4))⁻¹) := by
      apply Continuous.inv₀
      · fun_prop
      · intro t
        exact (Real.sqrt_pos.2 (by positivity : 0 < 1 + t ^ 4)).ne'
    have htail : IntegrableOn (fun t : ℝ => (Real.sqrt (1 + t ^ 4))⁻¹) (Ioi 1) := by
      apply (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := 1)
        (by norm_num) (by norm_num)).mono' hc.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans (by norm_num) ht
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.2 (by positivity)))]
      have hs : t ^ 2 ≤ Real.sqrt (1 + t ^ 4) := by
        have hz : Real.sqrt (t ^ 4) ≤ Real.sqrt (1 + t ^ 4) := Real.sqrt_le_sqrt (by linarith)
        have hid : Real.sqrt (t ^ 4) = t ^ 2 := by
          rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg t)]
        rwa [hid] at hz
      calc
        (Real.sqrt (1 + t ^ 4))⁻¹ ≤ (t ^ 2)⁻¹ := (inv_le_inv₀ (by positivity) (sq_pos_of_pos ht0)).2 hs
        _ = t ^ (-2 : ℝ) := by rw [Real.rpow_neg ht0.le, Real.rpow_two]
    have hhead : IntegrableOn (fun t : ℝ => (Real.sqrt (1 + t ^ 4))⁻¹) (Ioc 0 1) :=
      hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    simpa only [Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)] using hhead.union htail
  have hd : Continuous (fun r : ℝ => ((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ)) := by
    apply Continuous.inv₀
    · fun_prop
    · intro r
      exact_mod_cast (Real.sqrt_pos.2 (by positivity : 0 < 1 + r ^ 4)).ne'
  have hp : ContinuousOn (fun r : ℝ => (r : ℂ) ^ (Complex.I * (u : ℂ))) (Ioi 0) :=
    Complex.continuous_ofReal.continuousOn.cpow_const
      (fun r hr => Complex.ofReal_mem_slitPlane.2 hr)
  refine hi.mono' ((hd.continuousOn.mul hp).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := hr
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_cpow_eq_rpow_re_of_pos hr0]
  simp


theorem CothSums.kernel_mellin_ibp_imaginary (u : ℝ) (hu : u ≠ 0) :
    IntegrableOn (fun r : ℝ =>
      (((1 - 2 * CothSums.chi r) * (Real.sqrt (1 + r ^ 4))⁻¹ : ℝ) : ℂ) *
        (r : ℂ) ^ (Complex.I * (u : ℂ))) (Ioi 0) ∧
    (Complex.I * (u : ℂ)) * mellin (fun r : ℝ => (CothSums.kernel r : ℂ))
      (Complex.I * (u : ℂ)) =
      -((4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2 : ℝ) : ℂ) *
        ∫ r in Ioi (0 : ℝ),
          (((1 - 2 * CothSums.chi r) * (Real.sqrt (1 + r ^ 4))⁻¹ : ℝ) : ℂ) *
            (r : ℂ) ^ (Complex.I * (u : ℂ)) := by
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  let w : ℂ := Complex.I * (u : ℂ)
  let D : ℝ → ℝ := fun r => (Real.sqrt (1 + r ^ 4))⁻¹
  let F : ℝ → ℂ := fun r => (CothSums.kernel r : ℂ)
  let G : ℝ → ℂ := fun r => (r : ℂ) ^ w
  let F' : ℝ → ℂ := fun r => (C : ℂ) * (((1 - 2 * CothSums.chi r) * D r : ℝ) : ℂ)
  let G' : ℝ → ℂ := fun r => w * (r : ℂ) ^ (w - 1)
  let J : ℝ → ℂ := fun r => (((1 - 2 * CothSums.chi r) * D r : ℝ) : ℂ) * G r
  have hw : w ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hu)
  have hwre : w.re = 0 := by simp [w]
  have hc : Continuous CothSums.chi :=
    continuous_iff_continuousAt.mpr (fun r => (CothSums.chi_hasDerivAt r).continuousAt)
  have hF (r : ℝ) (_hr : r ∈ Ioi (0 : ℝ)) : HasDerivAt F (F' r) r := by
    have hr : HasDerivAt CothSums.kernel (C * ((1 - 2 * CothSums.chi r) * D r)) r := by
      change HasDerivAt (fun r => CothSums.chi r * (1 - CothSums.chi r)) _ r
      apply ((CothSums.chi_hasDerivAt r).mul
        ((hasDerivAt_const r (1 : ℝ)).sub (CothSums.chi_hasDerivAt r))).congr_deriv
      dsimp [C, D]
      ring
    convert! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r hr using 1
    · dsimp [F']
      push_cast
      rfl
  have hG (r : ℝ) (hr : r ∈ Ioi (0 : ℝ)) : HasDerivAt G (G' r) r :=
    hasDerivAt_ofReal_cpow_const hr.ne' hw
  have hbound (r : ℝ) (hr : 0 < r) : ‖F r‖ ≤ C * r ∧ ‖F r‖ ≤ C / r := by
    have hh := CothSums.chi_range_and_tail r hr
    have hp : 0 ≤ CothSums.kernel r :=
      mul_nonneg hh.1 (sub_nonneg.mpr hh.2.1)
    simp only [F, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
    constructor
    · calc
        CothSums.kernel r ≤ CothSums.chi r := by
          unfold CothSums.kernel
          nlinarith [sq_nonneg (CothSums.chi r)]
        _ ≤ C * r := CothSums.chi_le_prefactor_mul hr.le
    · calc
        CothSums.kernel r ≤ 1 - CothSums.chi r := by
          unfold CothSums.kernel
          nlinarith [sq_nonneg (1 - CothSums.chi r)]
        _ ≤ C / r := hh.2.2.2
  have hnorm (r : ℝ) (hr : 0 < r) : ‖F r * G r‖ = ‖F r‖ := by
    rw [norm_mul, show ‖G r‖ = 1 by
      dsimp [G]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hr, hwre, Real.rpow_zero]]
    exact mul_one _
  have hzero : Filter.Tendsto (F * G) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hdom : ∀ᶠ r : ℝ in nhdsWithin 0 (Ioi 0), ‖(F * G) r‖ ≤ C * r := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [Pi.mul_apply, hnorm r hr]
      exact (hbound r hr).1
    apply squeeze_zero_norm' hdom
    have hi : Filter.Tendsto (fun r : ℝ => r) (nhdsWithin 0 (Ioi 0)) (nhds (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero] using tendsto_const_nhds.mul hi
  have hinfty : Filter.Tendsto (F * G) Filter.atTop (nhds 0) := by
    have hdom : ∀ᶠ r : ℝ in Filter.atTop, ‖(F * G) r‖ ≤ C * r⁻¹ := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
      rw [Pi.mul_apply, hnorm r hr]
      simpa only [div_eq_mul_inv] using (hbound r hr).2
    apply squeeze_zero_norm' hdom
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero : Filter.Tendsto (fun r : ℝ => r⁻¹) Filter.atTop (nhds 0))
  have hpower : ContinuousOn G (Ioi (0 : ℝ)) :=
    Complex.continuous_ofReal.continuousOn.cpow_const
      (fun r hr => Complex.ofReal_mem_slitPlane.2 hr)
  have hJc : ContinuousOn J (Ioi (0 : ℝ)) := by
    have hDC : Continuous (fun r : ℝ => (D r : ℂ)) :=
      Complex.continuous_ofReal.comp CothSums.density_continuous
    have hfac : Continuous (fun r : ℝ => ((1 - 2 * CothSums.chi r : ℝ) : ℂ)) := by
      fun_prop
    simpa only [J, Complex.ofReal_mul, Pi.mul_apply] using!
      (hfac.continuousOn.mul hDC.continuousOn).mul hpower
  have hJ : IntegrableOn J (Ioi 0) := by
    apply (weighted_density_integrable u).norm.mono'
      (hJc.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hh := CothSums.chi_range_and_tail r hr
    have hab : |1 - 2 * CothSums.chi r| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hh.2.1], by linarith [hh.1]⟩
    dsimp [J, G, D, w]
    rw [Complex.ofReal_mul, norm_mul, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    calc
      |1 - 2 * CothSums.chi r| * |(Real.sqrt (1 + r ^ 4))⁻¹| *
          ‖(r : ℂ) ^ (Complex.I * (u : ℂ))‖ ≤
          1 * |(Real.sqrt (1 + r ^ 4))⁻¹| *
            ‖(r : ℂ) ^ (Complex.I * (u : ℂ))‖ := by gcongr
      _ = _ := by simp [norm_mul]
  have hleft : IntegrableOn (F' * G) (Ioi 0) := by
    have hh : IntegrableOn (fun r : ℝ => (C : ℂ) * J r) (Ioi 0) := hJ.const_mul (C : ℂ)
    apply hh.congr
    filter_upwards with r
    change (C : ℂ) * J r = F' r * G r
    dsimp only [F', J]
    push_cast
    ring
  have hK : IntegrableOn (fun r : ℝ => (r : ℂ) ^ (w - 1) * F r) (Ioi 0) := by
    have hi := (kernel_mellin_analytic w (by rw [hwre]; norm_num)
      (by rw [hwre]; norm_num)).1
    simpa only [MellinConvergent, smul_eq_mul, F] using hi
  have hright : IntegrableOn (F * G') (Ioi 0) := by
    apply (hK.const_mul w).congr
    filter_upwards with r
    dsimp [G']
    ring
  have hIBP := integral_Ioi_mul_deriv_eq_deriv_mul hF hG hright hleft hzero hinfty
  have hL : (∫ r in Ioi (0 : ℝ), F r * G' r) =
      w * mellin (fun r : ℝ => (CothSums.kernel r : ℂ)) w := by
    rw [mellin, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [smul_eq_mul, F, G']
    ring
  have hR : (∫ r in Ioi (0 : ℝ), F' r * G r) = (C : ℂ) * ∫ r in Ioi (0 : ℝ), J r := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp [F', J]
    ring
  rw [hL, hR] at hIBP
  refine ⟨hJ, ?_⟩
  change w * mellin (fun r : ℝ => (CothSums.kernel r : ℂ)) w =
    -(C : ℂ) * ∫ r in Ioi (0 : ℝ), J r
  simpa only [sub_zero, zero_sub, neg_mul] using hIBP


open MeasureTheory Set


set_option autoImplicit false


theorem CothSums.density_weighted_gamma (u : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ), ((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ) *
      (r : ℂ) ^ (Complex.I * (u : ℂ))) =
      Complex.Gamma ((1 : ℂ) / 4 + Complex.I * (u : ℂ) / 4) *
        Complex.Gamma ((1 : ℂ) / 4 - Complex.I * (u : ℂ) / 4) /
          (4 * (Real.sqrt Real.pi : ℂ)) := by
  let w : ℂ := Complex.I * (u : ℂ)
  let a : ℂ := (1 + w) / 4
  let b : ℂ := (1 - w) / 4
  let g : ℝ → ℂ := fun y => (y : ℂ) ^ (a - 1) * ((1 + y : ℝ) : ℂ) ^ (-1 / 2 : ℂ)
  have hhalf (z : ℝ) (hz : 0 ≤ z) :
      (z : ℂ) ^ (-1 / 2 : ℂ) = ((Real.sqrt z)⁻¹ : ℂ) := by
    have he := Complex.ofReal_cpow hz (-1 / 2 : ℝ)
    norm_num only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
      Complex.ofReal_ofNat] at he
    calc
      (z : ℂ) ^ (-1 / 2 : ℂ) = ((z ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
        convert he.symm using 1 <;> norm_num <;> congr 1 <;> ring
      _ = ((Real.sqrt z)⁻¹ : ℂ) := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring,
          Real.rpow_neg hz, ← Real.sqrt_eq_rpow]
        simp
  have hquartic : (4 : ℂ) *
      (∫ r in Ioi (0 : ℝ), ((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ) * (r : ℂ) ^ w) =
        ∫ y in Ioi (0 : ℝ), g y := by
    calc
      (4 : ℂ) * (∫ r in Ioi (0 : ℝ),
          ((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ) * (r : ℂ) ^ w) =
          ∫ r in Ioi (0 : ℝ), (4 : ℂ) *
            (((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ) * (r : ℂ) ^ w) := by rw [integral_const_mul]
      _ = ∫ t in Ioi (0 : ℝ), ((4 : ℝ) * t ^ ((4 : ℝ) - 1)) • g (t ^ (4 : ℝ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have ht0 : 0 < t := ht
        have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
        have hp : (((t ^ 4 : ℝ) : ℂ) ^ (a - 1)) = (t : ℂ) ^ (4 * (a - 1)) := by
          simpa using (Complex.cpow_mul_ofReal_nonneg ht0.le (4 : ℝ) (a - 1)).symm
        have hm : (t : ℂ) ^ 3 * (t : ℂ) ^ (4 * (a - 1)) = (t : ℂ) ^ w := by
          rw [← Complex.cpow_natCast (t : ℂ) 3, ← Complex.cpow_add _ _ htne]
          congr 1
          dsimp only [a]
          ring
        dsimp only [g]
        rw [Real.rpow_ofNat, hp, hhalf (1 + t ^ 4) (by positivity)]
        change (4 : ℂ) * (((Real.sqrt (1 + t ^ 4))⁻¹ : ℂ) * (t : ℂ) ^ w) =
          (((4 : ℝ) * t ^ ((4 : ℝ) - 1) : ℝ) : ℂ) *
            ((t : ℂ) ^ (4 * (a - 1)) * ((Real.sqrt (1 + t ^ 4))⁻¹ : ℂ))
        norm_num only [show (4 : ℝ) - 1 = 3 by norm_num, Real.rpow_ofNat,
          Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_pow]
        calc
          (4 : ℂ) * (((Real.sqrt (1 + t ^ 4))⁻¹ : ℂ) * (t : ℂ) ^ w) =
              4 * ((Real.sqrt (1 + t ^ 4))⁻¹ : ℂ) *
                ((t : ℂ) ^ 3 * (t : ℂ) ^ (4 * (a - 1))) := by rw [hm]; ring
          _ = _ := by ring
      _ = ∫ y in Ioi (0 : ℝ), g y :=
        integral_comp_rpow_Ioi_of_pos (g := g) (p := 4) (by norm_num)
  have himage : (fun x : ℝ => x / (1 - x)) '' Ioo 0 1 = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact div_pos hx.1 (sub_pos.mpr hx.2)
    · intro hy
      have hy0 : 0 < y := hy
      have hd : 0 < 1 + y := by linarith
      refine ⟨y / (1 + y), ⟨div_pos hy0 hd, (div_lt_one hd).2 (by linarith)⟩, ?_⟩
      have he : 1 - y / (1 + y) = (1 + y)⁻¹ := by field_simp; ring
      dsimp only
      rw [he, div_inv_eq_mul]
      exact div_mul_cancel₀ y hd.ne'
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun x : ℝ => x / (1 - x)) ((1 - x) ^ 2)⁻¹ (Ioo 0 1) x := by
    intro x hx
    have hn : 1 - x ≠ 0 := (sub_pos.mpr hx.2).ne'
    have hh : HasDerivAt (fun z : ℝ => z / (1 - z))
        ((1 * (1 - x) - x * (0 - 1)) / (1 - x) ^ 2) x :=
      (hasDerivAt_id x).div ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) hn
    have he : (1 * (1 - x) - x * (0 - 1)) / (1 - x) ^ 2 = ((1 - x) ^ 2)⁻¹ := by ring
    rw [he] at hh
    exact hh.hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ => x / (1 - x)) (Ioo 0 1) := by
    intro x hx y hy he
    have he' := (div_eq_div_iff (sub_pos.mpr hx.2).ne' (sub_pos.mpr hy.2).ne').1 he
    nlinarith
  have hm : (∫ y in Ioi (0 : ℝ), g y) = Complex.betaIntegral a b := by
    rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    have hx0 : 0 < x := hx.1
    have hd : 0 < 1 - x := sub_pos.mpr hx.2
    have hdn : ((1 - x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
    have he : 1 + x / (1 - x) = (1 - x)⁻¹ := by field_simp; ring
    have hp : ((((1 - x) ^ 2)⁻¹ : ℝ) : ℂ) = ((1 - x : ℝ) : ℂ) ^ (-2 : ℂ) := by
      simp [Complex.cpow_neg, Complex.cpow_ofNat]
    have hc : ((1 - x : ℝ) : ℂ) ^ (-2 : ℂ) *
        (((1 - x : ℝ) : ℂ) ^ (a - 1))⁻¹ *
        (((1 - x : ℝ) : ℂ) ^ (-1 / 2 : ℂ))⁻¹ = ((1 - x : ℝ) : ℂ) ^ (b - 1) := by
      rw [← Complex.cpow_neg, ← Complex.cpow_neg,
        ← Complex.cpow_add _ _ hdn, ← Complex.cpow_add _ _ hdn]
      congr 1
      dsimp only [a, b]
      ring
    dsimp only
    rw [abs_of_pos (inv_pos.mpr (sq_pos_of_pos hd))]
    change ((((1 - x) ^ 2)⁻¹ : ℝ) : ℂ) * g (x / (1 - x)) =
      (x : ℂ) ^ (a - 1) * (1 - (x : ℂ)) ^ (b - 1)
    rw [hp]
    dsimp only [g]
    rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hx0.le hd.le,
      he, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hd.le, div_eq_mul_inv]
    have hcast : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast]
    calc
      ((1 - x : ℝ) : ℂ) ^ (-2 : ℂ) *
          ((x : ℂ) ^ (a - 1) * (((1 - x : ℝ) : ℂ) ^ (a - 1))⁻¹ *
            (((1 - x : ℝ) : ℂ) ^ (-1 / 2 : ℂ))⁻¹) =
          (x : ℂ) ^ (a - 1) * (((1 - x : ℝ) : ℂ) ^ (-2 : ℂ) *
            (((1 - x : ℝ) : ℂ) ^ (a - 1))⁻¹ *
              (((1 - x : ℝ) : ℂ) ^ (-1 / 2 : ℂ))⁻¹) := by ring
      _ = _ := by rw [hc]
  have ha : 0 < a.re := by dsimp [a, w]; norm_num
  have hb : 0 < b.re := by dsimp [b, w]; norm_num
  have hab : a + b = (1 : ℂ) / 2 := by dsimp [a, b]; ring
  have hg : Complex.Gamma ((1 : ℂ) / 2) = (Real.sqrt Real.pi : ℂ) := by
    convert (Complex.Gamma_ofReal ((1 : ℝ) / 2)).trans
      (congrArg Complex.ofReal Real.Gamma_one_half_eq) using 1 <;> norm_num
  rw [hm, Complex.betaIntegral_eq_Gamma_mul_div a b ha hb, hab, hg] at hquartic
  have hs : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  apply (eq_div_iff (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hs)).2
  have hq := (eq_div_iff hs).1 hquartic
  have ha' : a = (1 : ℂ) / 4 + Complex.I * (u : ℂ) / 4 := by dsimp [a, w]; ring
  have hb' : b = (1 : ℂ) / 4 - Complex.I * (u : ℂ) / 4 := by dsimp [b, w]; ring
  rw [ha', hb'] at hq
  convert hq using 1 <;> ring


open MeasureTheory Set


set_option autoImplicit false


theorem CothSums.quartic_beta_density_integrable (u : ℝ) :
    IntegrableOn (fun q : ℝ => (q : ℂ) ^ (((1 + Complex.I * (u : ℂ)) / 4) - 1) *
      ((1 + q : ℝ) : ℂ) ^ (-1 / 2 : ℂ)) (Set.Ioi 0) := by
  let w : ℂ := Complex.I * (u : ℂ)
  let a : ℂ := (1 + w) / 4
  let b : ℂ := (1 - w) / 4
  let g : ℝ → ℂ := fun y => (y : ℂ) ^ (a - 1) * ((1 + y : ℝ) : ℂ) ^ (-1 / 2 : ℂ)
  have himage : (fun x : ℝ => x / (1 - x)) '' Ioo 0 1 = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact div_pos hx.1 (sub_pos.mpr hx.2)
    · intro hy
      have hy0 : 0 < y := hy
      have hd : 0 < 1 + y := by linarith
      refine ⟨y / (1 + y), ⟨div_pos hy0 hd, (div_lt_one hd).2 (by linarith)⟩, ?_⟩
      have he : 1 - y / (1 + y) = (1 + y)⁻¹ := by field_simp; ring
      dsimp only
      rw [he, div_inv_eq_mul]
      exact div_mul_cancel₀ y hd.ne'
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun x : ℝ => x / (1 - x)) ((1 - x) ^ 2)⁻¹ (Ioo 0 1) x := by
    intro x hx
    have hn : 1 - x ≠ 0 := (sub_pos.mpr hx.2).ne'
    have hh : HasDerivAt (fun z : ℝ => z / (1 - z))
        ((1 * (1 - x) - x * (0 - 1)) / (1 - x) ^ 2) x :=
      (hasDerivAt_id x).div ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) hn
    have he : (1 * (1 - x) - x * (0 - 1)) / (1 - x) ^ 2 = ((1 - x) ^ 2)⁻¹ := by ring
    rw [he] at hh
    exact hh.hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ => x / (1 - x)) (Ioo 0 1) := by
    intro x hx y hy he
    have he' := (div_eq_div_iff (sub_pos.mpr hx.2).ne' (sub_pos.mpr hy.2).ne').1 he
    nlinarith
  have hpoint : ∀ x ∈ Ioo (0 : ℝ) 1,
      |((1 - x) ^ 2)⁻¹| • g (x / (1 - x)) =
        (x : ℂ) ^ (a - 1) * (1 - (x : ℂ)) ^ (b - 1) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hd : 0 < 1 - x := sub_pos.mpr hx.2
    have hdn : ((1 - x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
    have he : 1 + x / (1 - x) = (1 - x)⁻¹ := by field_simp; ring
    have hp : ((((1 - x) ^ 2)⁻¹ : ℝ) : ℂ) = ((1 - x : ℝ) : ℂ) ^ (-2 : ℂ) := by
      simp [Complex.cpow_neg, Complex.cpow_ofNat]
    have hc : ((1 - x : ℝ) : ℂ) ^ (-2 : ℂ) *
        (((1 - x : ℝ) : ℂ) ^ (a - 1))⁻¹ *
        (((1 - x : ℝ) : ℂ) ^ (-1 / 2 : ℂ))⁻¹ = ((1 - x : ℝ) : ℂ) ^ (b - 1) := by
      rw [← Complex.cpow_neg, ← Complex.cpow_neg,
        ← Complex.cpow_add _ _ hdn, ← Complex.cpow_add _ _ hdn]
      congr 1
      dsimp only [a, b]
      ring
    rw [abs_of_pos (inv_pos.mpr (sq_pos_of_pos hd))]
    change ((((1 - x) ^ 2)⁻¹ : ℝ) : ℂ) * g (x / (1 - x)) =
      (x : ℂ) ^ (a - 1) * (1 - (x : ℂ)) ^ (b - 1)
    rw [hp]
    dsimp only [g]
    rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hx0.le hd.le,
      he, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hd.le, div_eq_mul_inv]
    have hcast : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast]
    calc
      ((1 - x : ℝ) : ℂ) ^ (-2 : ℂ) *
          ((x : ℂ) ^ (a - 1) * (((1 - x : ℝ) : ℂ) ^ (a - 1))⁻¹ *
            (((1 - x : ℝ) : ℂ) ^ (-1 / 2 : ℂ))⁻¹) =
          (x : ℂ) ^ (a - 1) * (((1 - x : ℝ) : ℂ) ^ (-2 : ℂ) *
            (((1 - x : ℝ) : ℂ) ^ (a - 1))⁻¹ *
              (((1 - x : ℝ) : ℂ) ^ (-1 / 2 : ℂ))⁻¹) := by ring
      _ = _ := by rw [hc]
  have hb := Complex.betaIntegral_convergent (u := a) (v := b)
    (by dsimp [a, w]; norm_num) (by dsimp [b, w]; norm_num)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hb
  have hb' := hb.mono_set Ioo_subset_Ioc_self
  change IntegrableOn g (Ioi 0)
  rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hderiv hinj]
  exact (integrableOn_congr_fun hpoint measurableSet_Ioo).mpr hb'


theorem CothSums.quadratic_affine_slice (u q : ℝ) (hq : 0 < q) :
    let a : ℂ := (2 + Complex.I * (u : ℂ)) / 4
    let A : ℝ → ℂ := fun p => (p : ℂ) ^ (-3 / 4 : ℂ) * ((1 + p : ℝ) : ℂ) ^ (-1 / 2 : ℂ)
    let T : ℝ → ℂ := fun y => (q : ℂ) ^ (a - 5 / 4) *
      ((q - (1 + q) * y : ℝ) : ℂ) ^ (-3 / 4 : ℂ) * ((1 - y : ℝ) : ℂ) ^ (-1 / 2 : ℂ)
    let K : ℂ := (q : ℂ) ^ (a - 5 / 4) * ((1 + q : ℝ) : ℂ) ^ (-1 / 2 : ℂ)
    IntegrableOn T (Set.Ioo 0 (q / (1 + q))) ∧
      (∫ y in Set.Ioo 0 (q / (1 + q)), T y) = K * ∫ p in Set.Ioo 0 q, A p ∧
      (∫ y in Set.Ioo 0 (q / (1 + q)), ‖T y‖) =
        ‖K‖ * ∫ p in Set.Ioo 0 q, ‖A p‖  := by
  dsimp only
  let a : ℂ := (2 + Complex.I * (u : ℂ)) / 4
  let A : ℝ → ℂ := fun p => (p : ℂ) ^ (-3 / 4 : ℂ) * ((1 + p : ℝ) : ℂ) ^ (-1 / 2 : ℂ)
  let T : ℝ → ℂ := fun y => (q : ℂ) ^ (a - 5 / 4) *
    ((q - (1 + q) * y : ℝ) : ℂ) ^ (-3 / 4 : ℂ) * ((1 - y : ℝ) : ℂ) ^ (-1 / 2 : ℂ)
  let K : ℂ := (q : ℂ) ^ (a - 5 / 4) * ((1 + q : ℝ) : ℂ) ^ (-1 / 2 : ℂ)
  have h1 : 0 < 1 + q := by linarith
  have hm : 0 < q / (1 + q) := div_pos hq h1
  have hm1 : q / (1 + q) < 1 := (div_lt_one h1).2 (by linarith)
  have himage : (fun y : ℝ => q - (1 + q) * y) '' Ioo 0 (q / (1 + q)) = Ioo 0 q := by
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hh := (lt_div_iff₀ h1).1 hy.2
      constructor <;> nlinarith [mul_pos h1 hy.1]
    · intro hp
      refine ⟨(q - p) / (1 + q), ⟨div_pos (sub_pos.mpr hp.2) h1, ?_⟩, ?_⟩
      · exact (div_lt_div_iff_of_pos_right h1).2 (by linarith [hp.1])
      · dsimp only
        field_simp
        ring
  have hderiv : ∀ y ∈ Ioo (0 : ℝ) (q / (1 + q)),
      HasDerivWithinAt (fun y : ℝ => q - (1 + q) * y) (-(1 + q))
        (Ioo 0 (q / (1 + q))) y := by
    intro y hy
    have hh : HasDerivAt (fun y : ℝ => q - (1 + q) * y) (0 - ((1 + q) * 1)) y :=
      (hasDerivAt_const y q).sub ((hasDerivAt_id y).const_mul (1 + q))
    simpa only [mul_one, zero_sub] using hh.hasDerivWithinAt
  have hinj : InjOn (fun y : ℝ => q - (1 + q) * y) (Ioo 0 (q / (1 + q))) := by
    intro y hy z hz he
    nlinarith
  have hpoint : ∀ y ∈ Ioo (0 : ℝ) (q / (1 + q)),
      |-(1 + q)| • (K * A (q - (1 + q) * y)) = T y := by
    intro y hy
    have hy1 : y < 1 := lt_trans hy.2 hm1
    have hyd : 0 < 1 - y := sub_pos.mpr hy1
    have he : 1 + (q - (1 + q) * y) = (1 + q) * (1 - y) := by ring
    have hp : (((1 + (q - (1 + q) * y) : ℝ)) : ℂ) ^ (-1 / 2 : ℂ) =
        ((1 + q : ℝ) : ℂ) ^ (-1 / 2 : ℂ) * ((1 - y : ℝ) : ℂ) ^ (-1 / 2 : ℂ) := by
      rw [he, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg h1.le hyd.le]
    have hn : ((1 + q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h1.ne'
    have hc : ((1 + q : ℝ) : ℂ) * ((1 + q : ℝ) : ℂ) ^ (-1 / 2 : ℂ) *
        ((1 + q : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = 1 := by
      rw [mul_assoc, ← Complex.cpow_add _ _ hn]
      rw [show (-1 / 2 : ℂ) + -1 / 2 = -1 by ring, Complex.cpow_neg_one]
      exact mul_inv_cancel₀ hn
    rw [abs_neg, abs_of_pos h1]
    change ((1 + q : ℝ) : ℂ) * (K * A (q - (1 + q) * y)) = T y
    dsimp only [K, A, T]
    rw [hp]
    calc
      ((1 + q : ℝ) : ℂ) *
          ((q : ℂ) ^ (a - 5 / 4) * ((1 + q : ℝ) : ℂ) ^ (-1 / 2 : ℂ) *
            (((q - (1 + q) * y : ℝ) : ℂ) ^ (-3 / 4 : ℂ) *
              (((1 + q : ℝ) : ℂ) ^ (-1 / 2 : ℂ) * ((1 - y : ℝ) : ℂ) ^ (-1 / 2 : ℂ)))) =
          ((q : ℂ) ^ (a - 5 / 4) * ((q - (1 + q) * y : ℝ) : ℂ) ^ (-3 / 4 : ℂ) *
            ((1 - y : ℝ) : ℂ) ^ (-1 / 2 : ℂ)) *
            (((1 + q : ℝ) : ℂ) * ((1 + q : ℝ) : ℂ) ^ (-1 / 2 : ℂ) *
              ((1 + q : ℝ) : ℂ) ^ (-1 / 2 : ℂ)) := by ring
      _ = _ := by rw [hc]; ring
  have hA0 : IntegrableOn A (Ioi 0) := by
    simpa only [A, Complex.ofReal_zero, mul_zero, add_zero,
      show (1 : ℂ) / 4 - 1 = -3 / 4 by ring] using
      CothSums.quartic_beta_density_integrable 0
  have hA : IntegrableOn A (Ioo 0 q) := hA0.mono_set Ioo_subset_Ioi_self
  have hi : IntegrableOn (fun p : ℝ => K * A p) (Ioo 0 q) := hA.const_mul K
  have hi' := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo hderiv hinj (fun p : ℝ => K * A p)).mp
      (by simpa only [himage] using hi)
  have ht : IntegrableOn T (Ioo 0 (q / (1 + q))) :=
    (integrableOn_congr_fun hpoint measurableSet_Ioo).mp hi' 
  refine ⟨ht, ?_, ?_⟩
  · change (∫ y in Ioo 0 (q / (1 + q)), T y) = K * ∫ p in Ioo 0 q, A p
    calc
      (∫ y in Ioo 0 (q / (1 + q)), T y) =
          ∫ y in Ioo 0 (q / (1 + q)), |-(1 + q)| • (K * A (q - (1 + q) * y)) :=
        setIntegral_congr_fun measurableSet_Ioo (fun y hy => (hpoint y hy).symm)
      _ = ∫ p in Ioo 0 q, K * A p := by
        rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
      _ = K * ∫ p in Ioo 0 q, A p := integral_const_mul _ _
  · change (∫ y in Ioo 0 (q / (1 + q)), ‖T y‖) = ‖K‖ * ∫ p in Ioo 0 q, ‖A p‖
    have hnpoint : ∀ y ∈ Ioo (0 : ℝ) (q / (1 + q)),
        |-(1 + q)| • ‖K * A (q - (1 + q) * y)‖ = ‖T y‖ := by
      intro y hy
      simpa only [norm_smul, Real.norm_eq_abs, abs_abs, smul_eq_mul] using
        congrArg norm (hpoint y hy)
    calc
      (∫ y in Ioo 0 (q / (1 + q)), ‖T y‖) =
          ∫ y in Ioo 0 (q / (1 + q)), |-(1 + q)| • ‖K * A (q - (1 + q) * y)‖ :=
        setIntegral_congr_fun measurableSet_Ioo (fun y hy => (hnpoint y hy).symm)
      _ = ∫ p in Ioo 0 q, ‖K * A p‖ := by
        rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
      _ = ‖K‖ * ∫ p in Ioo 0 q, ‖A p‖ := by simp_rw [norm_mul]; rw [integral_const_mul]


theorem CothSums.quadratic_beta_tail (u y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) :
    let a : ℂ := (2 + Complex.I * (u : ℂ)) / 4
    IntegrableOn (fun q : ℝ => (q : ℂ) ^ (a - 5 / 4) *
      ((q * (1 - y) - y : ℝ) : ℂ) ^ (-3 / 4 : ℂ)) (Set.Ioi (y / (1 - y))) ∧
    (∫ q in Set.Ioi (y / (1 - y)), (q : ℂ) ^ (a - 5 / 4) *
      ((q * (1 - y) - y : ℝ) : ℂ) ^ (-3 / 4 : ℂ)) =
      (y : ℂ) ^ (a - 1) * ((1 - y : ℝ) : ℂ) ^ (1 / 4 - a) *
        Complex.betaIntegral ((1 : ℂ) / 4) (1 - a) := by
  dsimp only
  let a : ℂ := (2 + Complex.I * (u : ℂ)) / 4
  let c : ℝ := y / (1 - y)
  let F : ℂ := (y : ℂ) ^ (a - 1) * ((1 - y : ℝ) : ℂ) ^ (1 / 4 - a)
  let g : ℝ → ℂ := fun q => (q : ℂ) ^ (a - 5 / 4) *
    ((q * (1 - y) - y : ℝ) : ℂ) ^ (-3 / 4 : ℂ)
  let B : ℝ → ℂ := fun x => (x : ℂ) ^ (-3 / 4 : ℂ) *
    ((1 - x : ℝ) : ℂ) ^ (-a)
  have hyb : 0 < 1 - y := sub_pos.mpr hy1
  have hc : 0 < c := div_pos hy0 hyb
  have hyn : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy0.ne'
  have hybn : ((1 - y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hyb.ne'
  have hcn : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have himage : (fun x : ℝ => c / (1 - x)) '' Ioo 0 1 = Ioi c := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hd : 0 < 1 - x := sub_pos.mpr hx.2
      exact (lt_div_iff₀ hd).2 (by nlinarith [mul_pos hc hx.1])
    · intro hq
      have hq0 : 0 < q := lt_trans hc hq
      refine ⟨1 - c / q, ⟨?_, ?_⟩, ?_⟩
      · exact sub_pos.mpr ((div_lt_one hq0).2 hq)
      · have hh : 0 < c / q := div_pos hc hq0
        linarith
      · dsimp only
        rw [show 1 - (1 - c / q) = c / q by ring]
        field_simp [hc.ne', hq0.ne']
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun x : ℝ => c / (1 - x)) (c / (1 - x) ^ 2) (Ioo 0 1) x := by
    intro x hx
    have hn := (sub_pos.mpr hx.2).ne'
    have hh : HasDerivAt (fun z : ℝ => c / (1 - z))
        ((0 * (1 - x) - c * (0 - 1)) / (1 - x) ^ 2) x :=
      (hasDerivAt_const x c).div
        ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) hn
    have he : (0 * (1 - x) - c * (0 - 1)) / (1 - x) ^ 2 = c / (1 - x) ^ 2 := by ring
    rw [he] at hh
    exact hh.hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ => c / (1 - x)) (Ioo 0 1) := by
    intro x hx z hz he
    have he' := (div_eq_div_iff (sub_pos.mpr hx.2).ne' (sub_pos.mpr hz.2).ne').1 he
    nlinarith
  have hconst : (c : ℂ) * (c : ℂ) ^ (a - 5 / 4) * (y : ℂ) ^ (-3 / 4 : ℂ) = F := by
    have hcp : (c : ℂ) * (c : ℂ) ^ (a - 5 / 4) = (c : ℂ) ^ (a - 1 / 4) := by
      calc
        (c : ℂ) * (c : ℂ) ^ (a - 5 / 4) =
            (c : ℂ) ^ (1 : ℂ) * (c : ℂ) ^ (a - 5 / 4) := by rw [Complex.cpow_one]
        _ = (c : ℂ) ^ (1 + (a - 5 / 4)) := (Complex.cpow_add _ _ hcn).symm
        _ = _ := by congr 1; ring
    rw [hcp]
    dsimp only [c]
    rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hy0.le hyb.le,
      div_eq_mul_inv]
    rw [mul_right_comm, ← Complex.cpow_add _ _ hyn]
    have he1 : a - 1 / 4 + (-3 / 4 : ℂ) = a - 1 := by ring
    rw [he1, ← Complex.cpow_neg]
    have he2 : -(a - 1 / 4) = 1 / 4 - a := by ring
    rw [he2]
  have hpoint : ∀ x ∈ Ioo (0 : ℝ) 1,
      |c / (1 - x) ^ 2| • g (c / (1 - x)) = F * B x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hd : 0 < 1 - x := sub_pos.mpr hx.2
    have hdn : ((1 - x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
    have he : c / (1 - x) * (1 - y) - y = y * x / (1 - x) := by
      dsimp only [c]
      field_simp
      ring
    have hp : (((c / (1 - x) ^ 2 : ℝ)) : ℂ) =
        (c : ℂ) * ((1 - x : ℝ) : ℂ) ^ (-2 : ℂ) := by
      simp [Complex.cpow_neg, Complex.cpow_ofNat, div_eq_mul_inv]
    have hden : ((1 - x : ℝ) : ℂ) ^ (-2 : ℂ) *
        (((1 - x : ℝ) : ℂ) ^ (a - 5 / 4))⁻¹ *
        (((1 - x : ℝ) : ℂ) ^ (-3 / 4 : ℂ))⁻¹ = ((1 - x : ℝ) : ℂ) ^ (-a) := by
      rw [← Complex.cpow_neg, ← Complex.cpow_neg,
        ← Complex.cpow_add _ _ hdn, ← Complex.cpow_add _ _ hdn]
      congr 1
      ring
    rw [abs_of_pos (div_pos hc (sq_pos_of_pos hd))]
    change (((c / (1 - x) ^ 2 : ℝ)) : ℂ) * g (c / (1 - x)) = F * B x
    rw [hp]
    dsimp only [g]
    have hpc : (((c / (1 - x) : ℝ) : ℂ) ^ (a - 5 / 4)) =
        (c : ℂ) ^ (a - 5 / 4) * (((1 - x : ℝ) : ℂ) ^ (a - 5 / 4))⁻¹ := by
      rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hc.le hd.le, div_eq_mul_inv]
    have hpy : (((y * x / (1 - x) : ℝ) : ℂ) ^ (-3 / 4 : ℂ)) =
        (y : ℂ) ^ (-3 / 4 : ℂ) * (x : ℂ) ^ (-3 / 4 : ℂ) *
          (((1 - x : ℝ) : ℂ) ^ (-3 / 4 : ℂ))⁻¹ := by
      rw [Complex.ofReal_div,
        Complex.div_cpow_ofReal_nonneg (mul_nonneg hy0.le hx0.le) hd.le,
        Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hy0.le hx0.le, div_eq_mul_inv]
    rw [he, hpc, hpy]
    calc
      (c : ℂ) * ((1 - x : ℝ) : ℂ) ^ (-2 : ℂ) *
          ((c : ℂ) ^ (a - 5 / 4) * (((1 - x : ℝ) : ℂ) ^ (a - 5 / 4))⁻¹ *
            ((y : ℂ) ^ (-3 / 4 : ℂ) * (x : ℂ) ^ (-3 / 4 : ℂ) *
              (((1 - x : ℝ) : ℂ) ^ (-3 / 4 : ℂ))⁻¹)) =
        ((c : ℂ) * (c : ℂ) ^ (a - 5 / 4) * (y : ℂ) ^ (-3 / 4 : ℂ)) *
          ((x : ℂ) ^ (-3 / 4 : ℂ) * (((1 - x : ℝ) : ℂ) ^ (-2 : ℂ) *
            (((1 - x : ℝ) : ℂ) ^ (a - 5 / 4))⁻¹ *
            (((1 - x : ℝ) : ℂ) ^ (-3 / 4 : ℂ))⁻¹)) := by ring
      _ = F * B x := by rw [hconst, hden]
  have hB : IntegrableOn B (Ioo 0 1) := by
    have hh := Complex.betaIntegral_convergent
      (u := (1 : ℂ) / 4) (v := 1 - a) (by norm_num)
      (by dsimp [a]; norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hh
    have hh' := hh.mono_set Ioo_subset_Ioc_self
    apply (integrableOn_congr_fun (g := fun x : ℝ =>
      (x : ℂ) ^ ((1 : ℂ) / 4 - 1) * (1 - (x : ℂ)) ^ (1 - a - 1))
      ?_ measurableSet_Ioo).mpr hh'
    intro x hx
    change (x : ℂ) ^ (-3 / 4 : ℂ) * ((1 - x : ℝ) : ℂ) ^ (-a) =
      (x : ℂ) ^ ((1 : ℂ) / 4 - 1) * (1 - (x : ℂ)) ^ (1 - a - 1)
    congr 1
    · norm_num
    · rw [Complex.ofReal_sub, Complex.ofReal_one]
      congr 1
      ring
  have hBi : (∫ x in Ioo (0 : ℝ) 1, B x) = Complex.betaIntegral ((1 : ℂ) / 4) (1 - a) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    change (x : ℂ) ^ (-3 / 4 : ℂ) * ((1 - x : ℝ) : ℂ) ^ (-a) =
      (x : ℂ) ^ ((1 : ℂ) / 4 - 1) * (1 - (x : ℂ)) ^ (1 - a - 1)
    congr 1
    · norm_num
    · rw [Complex.ofReal_sub, Complex.ofReal_one]
      congr 1
      ring
  have hi : IntegrableOn g (Ioi c) := by
    rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hderiv hinj]
    exact (integrableOn_congr_fun hpoint measurableSet_Ioo).mpr (hB.const_mul F)
  refine ⟨hi, ?_⟩
  change (∫ q in Ioi c, g q) = F * Complex.betaIntegral ((1 : ℂ) / 4) (1 - a)
  rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
  calc
    (∫ x in Ioo (0 : ℝ) 1, |c / (1 - x) ^ 2| • g (c / (1 - x))) =
        ∫ x in Ioo (0 : ℝ) 1, F * B x := setIntegral_congr_fun measurableSet_Ioo hpoint
    _ = F * Complex.betaIntegral ((1 : ℂ) / 4) (1 - a) := by rw [integral_const_mul, hBi]


theorem CothSums.quadratic_triangular_beta (u : ℝ) :
    let a : ℂ := (2 + Complex.I * (u : ℂ)) / 4
    (∫ q in Set.Ioi (0 : ℝ),
      ((q : ℂ) ^ (a - 5 / 4) * ((1 + q : ℝ) : ℂ) ^ (-1 / 2 : ℂ)) *
        (∫ p in (0 : ℝ)..q, (p : ℂ) ^ (-3 / 4 : ℂ) *
          ((1 + p : ℝ) : ℂ) ^ (-1 / 2 : ℂ))) =
      Complex.betaIntegral ((1 : ℂ) / 4) (1 - a) *
        Complex.betaIntegral a ((3 : ℂ) / 4 - a) := by
  dsimp only
  let a : ℂ := (2 + Complex.I * (u : ℂ)) / 4
  let A : ℝ → ℂ := fun p => (p : ℂ) ^ (-3 / 4 : ℂ) * ((1 + p : ℝ) : ℂ) ^ (-1 / 2 : ℂ)
  let K : ℝ → ℂ := fun q => (q : ℂ) ^ (a - 5 / 4) * ((1 + q : ℝ) : ℂ) ^ (-1 / 2 : ℂ)
  let R : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ 0 < z.2 ∧ z.2 < z.1 / (1 + z.1)}
  let f : ℝ × ℝ → ℂ := fun z => (z.1 : ℂ) ^ (a - 5 / 4) *
    ((z.1 - (1 + z.1) * z.2 : ℝ) : ℂ) ^ (-3 / 4 : ℂ) *
      ((1 - z.2 : ℝ) : ℂ) ^ (-1 / 2 : ℂ)
  let T : ℝ × ℝ → ℂ := R.indicator f
  have hR : MeasurableSet R := by
    dsimp [R]
    measurability
  have hcont : ContinuousOn f R := by
    have hq (z : ℝ × ℝ) (hz : z ∈ R) : 0 < z.1 := hz.1
    have hp (z : ℝ × ℝ) (hz : z ∈ R) : 0 < z.1 - (1 + z.1) * z.2 := by
      have hh := (lt_div_iff₀ (show 0 < 1 + z.1 by linarith [hz.1])).1 hz.2.2
      nlinarith
    have hd (z : ℝ × ℝ) (hz : z ∈ R) : 0 < 1 - z.2 := by
      have hm : z.1 / (1 + z.1) < 1 :=
        (div_lt_one (by linarith [hz.1] : 0 < 1 + z.1)).2 (by linarith)
      linarith [hz.2.2]
    have hc1 : Continuous (fun z : ℝ × ℝ => (z.1 : ℂ)) := by fun_prop
    have hc2 : Continuous (fun z : ℝ × ℝ => ((z.1 - (1 + z.1) * z.2 : ℝ) : ℂ)) := by fun_prop
    have hc3 : Continuous (fun z : ℝ × ℝ => ((1 - z.2 : ℝ) : ℂ)) := by fun_prop
    exact ((hc1.continuousOn.cpow_const (fun z hz => Complex.ofReal_mem_slitPlane.2 (hq z hz))).mul
      (hc2.continuousOn.cpow_const (fun z hz => Complex.ofReal_mem_slitPlane.2 (hp z hz)))).mul
      (hc3.continuousOn.cpow_const (fun z hz => Complex.ofReal_mem_slitPlane.2 (hd z hz)))
  have hm : AEStronglyMeasurable T (volume.prod volume) := by
    exact (aestronglyMeasurable_indicator_iff hR).mpr (hcont.aestronglyMeasurable hR)
  have hslice (q : ℝ) (hq : 0 < q) :
      (fun y : ℝ => T (q, y)) = (Ioo 0 (q / (1 + q))).indicator (fun y => f (q, y)) := by
    funext y
    by_cases hy : y ∈ Ioo 0 (q / (1 + q))
    · have hz : (q, y) ∈ R := ⟨hq, hy.1, hy.2⟩
      simp only [T, indicator_of_mem hz, indicator_of_mem hy]
    · have hz : (q, y) ∉ R := by intro hz; exact hy ⟨hz.2.1, hz.2.2⟩
      simp only [T, indicator_of_notMem hz, indicator_of_notMem hy]
  have hzero (q : ℝ) (hq : ¬ 0 < q) : (fun y : ℝ => T (q, y)) = 0 := by
    funext y
    have hz : (q, y) ∉ R := by intro hz; exact hq hz.1
    simp only [T, indicator_of_notMem hz, Pi.zero_apply]
  have hsint (q : ℝ) : Integrable (fun y : ℝ => T (q, y)) := by
    by_cases hq : 0 < q
    · rw [hslice q hq]
      exact (integrable_indicator_iff measurableSet_Ioo).mpr (CothSums.quadratic_affine_slice u q hq).1
    · rw [hzero q hq]
      exact integrable_zero _ _ _
  have hA0 : IntegrableOn A (Ioi 0) := by
    simpa only [A, Complex.ofReal_zero, mul_zero, add_zero,
      show (1 : ℂ) / 4 - 1 = -3 / 4 by ring] using CothSums.quartic_beta_density_integrable 0
  have hK : IntegrableOn K (Ioi 0) := by
    have he : ((1 + Complex.I * (u : ℂ)) / 4) - 1 = a - 5 / 4 := by dsimp [a]; ring
    simpa only [K, he] using CothSums.quartic_beta_density_integrable u
  let B : ℝ := ∫ p in Ioi (0 : ℝ), ‖A p‖
  have hB : 0 ≤ B := integral_nonneg (fun _ => norm_nonneg _)
  have hbound (q : ℝ) (hq : 0 < q) :
      (∫ y : ℝ, ‖T (q, y)‖) ≤ B * ‖K q‖ := by
    have heq : (fun y : ℝ => ‖T (q, y)‖) =
        (Ioo 0 (q / (1 + q))).indicator (fun y => ‖f (q, y)‖) := by
      funext y
      rw [congrFun (hslice q hq) y]
      by_cases hy : y ∈ Ioo 0 (q / (1 + q)) <;> simp [hy]
    rw [heq, integral_indicator measurableSet_Ioo]
    have he := (CothSums.quadratic_affine_slice u q hq).2.2
    change (∫ y in Ioo 0 (q / (1 + q)), ‖f (q, y)‖) =
      ‖K q‖ * ∫ p in Ioo 0 q, ‖A p‖ at he
    rw [he]
    have hle : (∫ p in Ioo 0 q, ‖A p‖) ≤ B := by
      exact setIntegral_mono_set hA0.norm (by filter_upwards [] with p; exact norm_nonneg _)
        (Filter.Eventually.of_forall (fun p hp => hp.1))
    nlinarith [norm_nonneg (K q)]
  have hH : Integrable ((Ioi (0 : ℝ)).indicator (fun q => B * ‖K q‖)) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (hK.norm.const_mul B)
  have houter : Integrable (fun q : ℝ => ∫ y : ℝ, ‖T (q, y)‖) := by
    refine hH.mono' hm.norm.integral_prod_right' ?_
    filter_upwards [] with q
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    by_cases hq : 0 < q
    · rw [indicator_of_mem (show q ∈ Ioi (0 : ℝ) from hq)]
      exact hbound q hq
    · have hz (y : ℝ) : T (q, y) = 0 := congrFun (hzero q hq) y
      have he : (∫ y : ℝ, ‖T (q, y)‖) = 0 := by simp only [hz, norm_zero, integral_zero]
      rw [he, indicator_of_notMem (show q ∉ Ioi (0 : ℝ) from hq)]
  have hint : Integrable T (volume.prod volume) :=
    (integrable_prod_iff hm).mpr ⟨Filter.Eventually.of_forall hsint, houter⟩
  have hRiff (q y : ℝ) : (q, y) ∈ R ↔ y ∈ Ioo (0 : ℝ) 1 ∧ q ∈ Ioi (y / (1 - y)) := by
    constructor
    · intro hz
      have h1 : 0 < 1 + q := by linarith [hz.1]
      have hm : q / (1 + q) < 1 := (div_lt_one h1).2 (by linarith)
      have hy : y < 1 := lt_trans hz.2.2 hm
      refine ⟨⟨hz.2.1, hy⟩, ?_⟩
      have hh := (lt_div_iff₀ h1).1 hz.2.2
      exact (div_lt_iff₀ (sub_pos.mpr hy)).2 (by nlinarith)
    · rintro ⟨hy, hq⟩
      have hd := sub_pos.mpr hy.2
      have hc : 0 < y / (1 - y) := div_pos hy.1 hd
      have hq0 := lt_trans hc hq
      have hh := (div_lt_iff₀ hd).1 hq
      exact ⟨hq0, hy.1, (lt_div_iff₀ (by linarith : 0 < 1 + q)).2 (by nlinarith)⟩
  have hyslice (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) :
      (fun q : ℝ => T (q, y)) = (Ioi (y / (1 - y))).indicator (fun q => f (q, y)) := by
    funext q
    by_cases hq : q ∈ Ioi (y / (1 - y))
    · have hz := (hRiff q y).2 ⟨hy, hq⟩
      simp only [T, indicator_of_mem hz, indicator_of_mem hq]
    · have hz : (q, y) ∉ R := by intro hz; exact hq ((hRiff q y).1 hz).2
      simp only [T, indicator_of_notMem hz, indicator_of_notMem hq]
  have hyzero (y : ℝ) (hy : y ∉ Ioo (0 : ℝ) 1) : (fun q : ℝ => T (q, y)) = 0 := by
    funext q
    have hz : (q, y) ∉ R := by intro hz; exact hy ((hRiff q y).1 hz).1
    simp only [T, indicator_of_notMem hz, Pi.zero_apply]
  have hleft : (∫ q : ℝ, ∫ y : ℝ, T (q, y)) =
      ∫ q in Ioi (0 : ℝ), K q * ∫ p in (0 : ℝ)..q, A p := by
    have he : (fun q : ℝ => ∫ y : ℝ, T (q, y)) =
        (Ioi (0 : ℝ)).indicator (fun q => K q * ∫ p in (0 : ℝ)..q, A p) := by
      funext q
      by_cases hq : 0 < q
      · rw [indicator_of_mem (show q ∈ Ioi (0 : ℝ) from hq), hslice q hq,
          integral_indicator measurableSet_Ioo]
        have hs := (CothSums.quadratic_affine_slice u q hq).2.1
        change (∫ y in Ioo 0 (q / (1 + q)), f (q, y)) = K q * ∫ p in Ioo 0 q, A p at hs
        rw [intervalIntegral.integral_of_le hq.le, integral_Ioc_eq_integral_Ioo]
        exact hs
      · rw [hzero q hq, indicator_of_notMem (show q ∉ Ioi (0 : ℝ) from hq)]
        change (∫ _ : ℝ, (0 : ℂ)) = 0
        simp
    rw [he, integral_indicator measurableSet_Ioi]
  let G : ℝ → ℂ := fun y => ((1 - y : ℝ) : ℂ) ^ (-1 / 2 : ℂ) *
    ∫ q in Ioi (y / (1 - y)), (q : ℂ) ^ (a - 5 / 4) *
      ((q * (1 - y) - y : ℝ) : ℂ) ^ (-3 / 4 : ℂ)
  have hright : (∫ y : ℝ, ∫ q : ℝ, T (q, y)) =
      Complex.betaIntegral ((1 : ℂ) / 4) (1 - a) * Complex.betaIntegral a ((3 : ℂ) / 4 - a) := by
    have he : (fun y : ℝ => ∫ q : ℝ, T (q, y)) = (Ioo (0 : ℝ) 1).indicator G := by
      funext y
      by_cases hy : y ∈ Ioo (0 : ℝ) 1
      · rw [indicator_of_mem hy, hyslice y hy, integral_indicator measurableSet_Ioi]
        have hp (q : ℝ) : f (q, y) = ((1 - y : ℝ) : ℂ) ^ (-1 / 2 : ℂ) *
            ((q : ℂ) ^ (a - 5 / 4) * ((q * (1 - y) - y : ℝ) : ℂ) ^ (-3 / 4 : ℂ)) := by
          dsimp only [f]
          rw [show q - (1 + q) * y = q * (1 - y) - y by ring]
          ring
        simp_rw [hp]
        exact integral_const_mul _ _
      · rw [hyzero y hy, indicator_of_notMem hy]
        change (∫ _ : ℝ, (0 : ℂ)) = 0
        simp
    rw [he, integral_indicator measurableSet_Ioo]
    calc
      (∫ y in Ioo (0 : ℝ) 1, G y) =
          ∫ y in Ioo (0 : ℝ) 1, Complex.betaIntegral ((1 : ℂ) / 4) (1 - a) *
            ((y : ℂ) ^ (a - 1) * (1 - (y : ℂ)) ^ (((3 : ℂ) / 4 - a) - 1)) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro y hy
        have ht := (CothSums.quadratic_beta_tail u y hy.1 hy.2).2
        change (∫ q in Ioi (y / (1 - y)), (q : ℂ) ^ (a - 5 / 4) *
          ((q * (1 - y) - y : ℝ) : ℂ) ^ (-3 / 4 : ℂ)) =
          (y : ℂ) ^ (a - 1) * ((1 - y : ℝ) : ℂ) ^ (1 / 4 - a) *
            Complex.betaIntegral ((1 : ℂ) / 4) (1 - a) at ht
        dsimp only [G]
        rw [ht]
        have hn : ((1 - y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_pos.mpr hy.2).ne'
        have hp : ((1 - y : ℝ) : ℂ) ^ (-1 / 2 : ℂ) *
            ((1 - y : ℝ) : ℂ) ^ (1 / 4 - a) =
              ((1 - y : ℝ) : ℂ) ^ (((3 : ℂ) / 4 - a) - 1) := by
          rw [← Complex.cpow_add _ _ hn]
          congr 1
          ring
        have hcast : (1 : ℂ) - (y : ℂ) = ((1 - y : ℝ) : ℂ) := by push_cast; rfl
        rw [hcast]
        calc
          ((1 - y : ℝ) : ℂ) ^ (-1 / 2 : ℂ) *
              ((y : ℂ) ^ (a - 1) * ((1 - y : ℝ) : ℂ) ^ (1 / 4 - a) *
                Complex.betaIntegral ((1 : ℂ) / 4) (1 - a)) =
              Complex.betaIntegral ((1 : ℂ) / 4) (1 - a) *
                ((y : ℂ) ^ (a - 1) * (((1 - y : ℝ) : ℂ) ^ (-1 / 2 : ℂ) *
                  ((1 - y : ℝ) : ℂ) ^ (1 / 4 - a))) := by ring
          _ = _ := by rw [hp]
      _ = Complex.betaIntegral ((1 : ℂ) / 4) (1 - a) * Complex.betaIntegral a ((3 : ℂ) / 4 - a) := by
        have hb : (∫ y in Ioo (0 : ℝ) 1,
            (y : ℂ) ^ (a - 1) * (1 - (y : ℂ)) ^ (((3 : ℂ) / 4 - a) - 1)) =
              Complex.betaIntegral a ((3 : ℂ) / 4 - a) := by
          rw [Complex.betaIntegral,
            intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
        rw [integral_const_mul, hb]
  change (∫ q in Ioi (0 : ℝ), K q * ∫ p in (0 : ℝ)..q, A p) = _
  rw [← hleft, integral_integral_swap (f := fun q y => T (q, y)) hint, hright]


theorem CothSums.chi_density_weighted_gamma (u : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ), (CothSums.chi r : ℂ) *
      ((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ) * (r : ℂ) ^ (Complex.I * (u : ℂ))) =
      ((4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2 : ℝ) : ℂ) / 4 *
        (Complex.Gamma ((2 + Complex.I * (u : ℂ)) / 4) *
          Complex.Gamma ((2 - Complex.I * (u : ℂ)) / 4) *
          Complex.Gamma ((5 : ℂ) / 4) *
          Complex.Gamma ((1 - Complex.I * (u : ℂ)) / 4) /
            (Complex.Gamma ((3 : ℂ) / 4) *
              Complex.Gamma ((3 - Complex.I * (u : ℂ)) / 4))) := by
  let w : ℂ := Complex.I * (u : ℂ)
  let a : ℂ := (2 + w) / 4
  let C : ℂ := ((4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2 : ℝ) : ℂ)
  let A : ℝ → ℂ := fun p => (p : ℂ) ^ (-3 / 4 : ℂ) * ((1 + p : ℝ) : ℂ) ^ (-1 / 2 : ℂ)
  let K : ℝ → ℂ := fun q => (q : ℂ) ^ (a - 5 / 4) * ((1 + q : ℝ) : ℂ) ^ (-1 / 2 : ℂ)
  let H : ℝ → ℂ := fun q => ∫ p in (0 : ℝ)..q, A p
  let Z : ℝ → ℂ := fun r => ((∫ t in (0 : ℝ)..r, (Real.sqrt (1 + t ^ 4))⁻¹ : ℝ) : ℂ)
  have hhalf (z : ℝ) (hz : 0 ≤ z) :
      (z : ℂ) ^ (-1 / 2 : ℂ) = ((Real.sqrt z)⁻¹ : ℂ) := by
    have he := Complex.ofReal_cpow hz (-1 / 2 : ℝ)
    norm_num only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
      Complex.ofReal_ofNat] at he
    calc
      (z : ℂ) ^ (-1 / 2 : ℂ) = ((z ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
        convert he.symm using 1 <;> norm_num <;> congr 1 <;> ring
      _ = ((Real.sqrt z)⁻¹ : ℂ) := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring,
          Real.rpow_neg hz, ← Real.sqrt_eq_rpow]
        simp
  have hpointA (t : ℝ) (ht : 0 < t) :
      (4 * t ^ 3 : ℝ) • A (t ^ 4) = (4 : ℂ) * ((Real.sqrt (1 + t ^ 4))⁻¹ : ℂ) := by
    have htn : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hp : (((t ^ 4 : ℝ) : ℂ) ^ (-3 / 4 : ℂ)) = (t : ℂ) ^ (-3 : ℂ) := by
      have hh := (Complex.cpow_mul_ofReal_nonneg ht.le (4 : ℝ) (-3 / 4 : ℂ)).symm
      convert hh using 1 <;> norm_num
    have hc : (t : ℂ) ^ 3 * (t : ℂ) ^ (-3 : ℂ) = 1 := by
      rw [← Complex.cpow_natCast (t : ℂ) 3, ← Complex.cpow_add _ _ htn]
      norm_num
    change ((4 * t ^ 3 : ℝ) : ℂ) * A (t ^ 4) = _
    dsimp only [A]
    rw [hp, hhalf _ (by positivity)]
    push_cast
    calc
      (4 : ℂ) * (t : ℂ) ^ 3 * ((t : ℂ) ^ (-3 : ℂ) * ((Real.sqrt (1 + t ^ 4))⁻¹ : ℂ)) =
          4 * ((t : ℂ) ^ 3 * (t : ℂ) ^ (-3 : ℂ)) * ((Real.sqrt (1 + t ^ 4))⁻¹ : ℂ) := by ring
      _ = _ := by rw [hc]; ring
  have hhead (r : ℝ) (hr : 0 < r) : H (r ^ 4) = 4 * Z r := by
    have himage : (fun t : ℝ => t ^ 4) '' Ioo 0 r = Ioo 0 (r ^ 4) := by
      ext p
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨pow_pos ht.1 4, pow_lt_pow_left₀ ht.2 ht.1.le (by norm_num)⟩
      · intro hp
        have hp0 : 0 < p := hp.1
        have ht4 : (p ^ (1 / 4 : ℝ)) ^ 4 = p := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
          norm_num
        have hrroot : (r ^ 4) ^ (1 / 4 : ℝ) = r := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
          norm_num
        refine ⟨p ^ (1 / 4 : ℝ), ⟨Real.rpow_pos_of_pos hp0 _, ?_⟩, ht4⟩
        rw [← hrroot]
        exact Real.rpow_lt_rpow hp0.le hp.2 (by norm_num)
    have hderiv : ∀ t ∈ Ioo (0 : ℝ) r,
        HasDerivWithinAt (fun t : ℝ => t ^ 4) (4 * t ^ 3) (Ioo 0 r) t := by
      intro t ht
      simpa using (hasDerivAt_pow 4 t).hasDerivWithinAt (s := Ioo 0 r)
    have hinj : InjOn (fun t : ℝ => t ^ 4) (Ioo 0 r) := by
      intro s hs t ht he
      exact (pow_left_inj₀ hs.1.le ht.1.le (by norm_num : (4 : ℕ) ≠ 0)).1 he
    have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj A
    rw [himage] at he
    dsimp only [H, Z]
    rw [intervalIntegral.integral_of_le (pow_nonneg hr.le 4), integral_Ioc_eq_integral_Ioo, he]
    calc
      (∫ t in Ioo (0 : ℝ) r, |4 * t ^ 3| • A (t ^ 4)) =
          ∫ t in Ioo (0 : ℝ) r, (4 : ℂ) * ((Real.sqrt (1 + t ^ 4))⁻¹ : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro t ht
        dsimp only
        rw [abs_of_pos (mul_pos (by norm_num) (pow_pos ht.1 3))]
        exact hpointA t ht.1
      _ = 4 * Z r := by
        rw [integral_const_mul]
        dsimp only [Z]
        rw [← intervalIntegral.integral_ofReal, intervalIntegral.integral_of_le hr.le,
          integral_Ioc_eq_integral_Ioo]
        simp only [Complex.ofReal_inv]
  have hpowK (r : ℝ) (hr : 0 < r) :
      (r : ℂ) ^ 3 * (((r ^ 4 : ℝ) : ℂ) ^ (a - 5 / 4)) = (r : ℂ) ^ w := by
    have hrn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hp := (Complex.cpow_mul_ofReal_nonneg hr.le (4 : ℝ) (a - 5 / 4)).symm
    have hp' : (((r ^ 4 : ℝ) : ℂ) ^ (a - 5 / 4)) = (r : ℂ) ^ (4 * (a - 5 / 4)) := by
      simpa using hp
    rw [hp', ← Complex.cpow_natCast (r : ℂ) 3, ← Complex.cpow_add _ _ hrn]
    congr 1
    dsimp only [a]
    ring
  have hchi (r : ℝ) : (CothSums.chi r : ℂ) = C * Z r := by
    simp only [CothSums.chi, Complex.ofReal_mul, C, Z]
  have hmain : C * (∫ q in Ioi (0 : ℝ), K q * H q) =
      (16 : ℂ) * (∫ r in Ioi (0 : ℝ), (CothSums.chi r : ℂ) *
        ((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ) * (r : ℂ) ^ w) := by
    rw [← integral_comp_rpow_Ioi_of_pos (g := fun q => K q * H q) (p := 4) (by norm_num)]
    rw [← integral_const_mul, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr0 : 0 < r := hr
    dsimp only
    rw [Real.rpow_ofNat, hhead r hr0, hchi r]
    dsimp only [K]
    rw [hhalf _ (by positivity)]
    change C * (((4 * r ^ ((4 : ℝ) - 1) : ℝ) : ℂ) *
      ((((r ^ 4 : ℝ) : ℂ) ^ (a - 5 / 4) * ((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ)) * (4 * Z r))) = _
    norm_num only [show (4 : ℝ) - 1 = 3 by norm_num, Real.rpow_ofNat]
    have hcoef : ((4 * r ^ 3 : ℝ) : ℂ) = 4 * (r : ℂ) ^ 3 := by push_cast; rfl
    rw [hcoef]
    calc
      C * (4 * (r : ℂ) ^ 3 *
          ((((r ^ 4 : ℝ) : ℂ) ^ (a - 5 / 4) * ((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ)) * (4 * Z r))) =
          16 * (C * Z r * ((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ) *
            ((r : ℂ) ^ 3 * (((r ^ 4 : ℝ) : ℂ) ^ (a - 5 / 4)))) := by ring
      _ = _ := by rw [hpowK r hr0]
  have hT := CothSums.quadratic_triangular_beta u
  change (∫ q in Ioi (0 : ℝ), K q * H q) =
      Complex.betaIntegral ((1 : ℂ) / 4) (1 - a) * Complex.betaIntegral a ((3 : ℂ) / 4 - a) at hT
  rw [hT] at hmain
  have he : (∫ r in Ioi (0 : ℝ), (CothSums.chi r : ℂ) *
      ((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ) * (r : ℂ) ^ w) =
      C * (Complex.betaIntegral ((1 : ℂ) / 4) (1 - a) * Complex.betaIntegral a ((3 : ℂ) / 4 - a)) / 16 := by
    calc
      _ = (16 * (∫ r in Ioi (0 : ℝ), (CothSums.chi r : ℂ) *
        ((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ) * (r : ℂ) ^ w)) / 16 := by ring
      _ = _ := congrArg (fun z : ℂ => z / 16) hmain.symm
  have hb1 := Complex.betaIntegral_eq_Gamma_mul_div ((1 : ℂ) / 4) (1 - a)
    (by norm_num) (by dsimp [a, w]; norm_num)
  have hb2 := Complex.betaIntegral_eq_Gamma_mul_div a ((3 : ℂ) / 4 - a)
    (by dsimp [a, w]; norm_num) (by dsimp [a, w]; norm_num)
  rw [hb1, hb2] at he
  have he1 : 1 - a = (2 - w) / 4 := by dsimp [a]; ring
  have he2 : (3 : ℂ) / 4 - a = (1 - w) / 4 := by dsimp [a]; ring
  have he3 : (1 : ℂ) / 4 + (1 - a) = (3 - w) / 4 := by dsimp [a]; ring
  have he4 : a + ((3 : ℂ) / 4 - a) = (3 : ℂ) / 4 := by ring
  rw [he3, he4, he1, he2] at he
  have hg : Complex.Gamma ((5 : ℂ) / 4) = Complex.Gamma ((1 : ℂ) / 4) / 4 := by
    calc
      Complex.Gamma ((5 : ℂ) / 4) = Complex.Gamma ((1 : ℂ) / 4 + 1) := by congr 1; ring
      _ = ((1 : ℂ) / 4) * Complex.Gamma ((1 : ℂ) / 4) := Complex.Gamma_add_one _ (by norm_num)
      _ = _ := by ring
  rw [he, hg]
  dsimp only [C, a, w]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring


open MeasureTheory Set


set_option autoImplicit false


theorem CothSums.gamma_moment_difference (u : ℝ) (hu : u ≠ 0) :
    -((4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2 : ℝ) : ℂ) *
      (Complex.Gamma ((1 : ℂ) / 4 + Complex.I * (u : ℂ) / 4) *
        Complex.Gamma ((1 : ℂ) / 4 - Complex.I * (u : ℂ) / 4) /
          (4 * (Real.sqrt Real.pi : ℂ)) -
        2 * (((4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2 : ℝ) : ℂ) / 4 *
          (Complex.Gamma ((2 + Complex.I * (u : ℂ)) / 4) *
            Complex.Gamma ((2 - Complex.I * (u : ℂ)) / 4) *
            Complex.Gamma ((5 : ℂ) / 4) *
            Complex.Gamma ((1 - Complex.I * (u : ℂ)) / 4) /
              (Complex.Gamma ((3 : ℂ) / 4) *
                Complex.Gamma ((3 - Complex.I * (u : ℂ)) / 4))))) =
      (Complex.I * (u : ℂ)) *
        (CothSums.lambda (Complex.I * (u : ℂ) / 4) /
          (4 * (Real.Gamma (1 / 4) : ℂ) ^ 2)) := by
  let z : ℂ := Complex.I * (u : ℂ) / 4
  let g : ℂ := (Real.Gamma (1 / 4) : ℂ)
  let s : ℂ := (Real.sqrt Real.pi : ℂ)
  let q : ℂ := (Real.sqrt 2 : ℂ)
  let p : ℂ := (Real.pi : ℂ)
  let A : ℂ := Complex.Gamma ((1 : ℂ) / 4 + z)
  let B : ℂ := Complex.Gamma ((1 : ℂ) / 4 - z)
  let E : ℂ := Complex.Gamma ((1 : ℂ) / 2 + z) * Complex.Gamma ((1 : ℂ) / 2 - z)
  let d : ℂ := Complex.Gamma ((3 : ℂ) / 4)
  let c : ℂ := Complex.Gamma ((3 : ℂ) / 4 - z)
  let H : ℂ := Complex.Gamma (1 + z) * Complex.Gamma (1 - z)
  let C : ℂ := 4 * s / g ^ 2
  have hzre : z.re = 0 := by simp [z]
  have hzim : z.im = u / 4 := by simp [z]
  have hz : z ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    rw [hzim, Complex.zero_im] at hi
    exact hu (by linarith)
  have hp : p ≠ 0 := by dsimp only [p]; exact_mod_cast Real.pi_ne_zero
  have hs : s ≠ 0 := by dsimp only [s]; exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : q ≠ 0 := by dsimp only [q]; exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hg : g ≠ 0 := by dsimp only [g]; exact_mod_cast (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 4)).ne'
  have hs2 : s ^ 2 = p := by
    dsimp only [s, p]
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hq2 : q ^ 2 = 2 := by
    dsimp only [q]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hA : A ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num [z])
  have hd : d ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hc : c ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num [z])
  have hH : H ≠ 0 := mul_ne_zero
    (Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.add_re, hzre]; norm_num))
    (Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.sub_re, hzre]; norm_num))
  have hE : E ≠ 0 := mul_ne_zero
    (Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.add_re, hzre]; norm_num))
    (Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.sub_re, hzre]; norm_num))
  have hG : Complex.Gamma ((1 : ℂ) / 4) = g := by
    simpa [g] using Complex.Gamma_ofReal ((1 : ℝ) / 4)
  have hS : Complex.sin (p / 4) = q / 2 := by
    convert congrArg Complex.ofReal Real.sin_pi_div_four using 1 <;> push_cast <;> rfl
  have hCo : Complex.cos (p / 4) = q / 2 := by
    convert congrArg Complex.ofReal Real.cos_pi_div_four using 1 <;> push_cast <;> rfl
  have hgd : g * d = p * q := by
    have hh := Complex.Gamma_mul_Gamma_one_sub ((1 : ℂ) / 4)
    rw [hG, show (1 : ℂ) - 1 / 4 = 3 / 4 by ring,
      show (Real.pi : ℂ) * (1 / 4) = p / 4 by dsimp [p]; ring, hS] at hh
    change g * d = p / (q / 2) at hh
    rw [hh]
    field_simp [hq]
    exact hq2.symm
  have hP : A * c = p / Complex.sin (p * ((1 : ℂ) / 4 + z)) := by
    simpa only [A, c, p, show (1 : ℂ) - (1 / 4 + z) = 3 / 4 - z by ring] using
      Complex.Gamma_mul_Gamma_one_sub ((1 : ℂ) / 4 + z)
  have hshift : q * Complex.sin (p * ((1 : ℂ) / 4 + z)) =
      Complex.cos (p * z) + Complex.sin (p * z) := by
    rw [show p * ((1 : ℂ) / 4 + z) = p / 4 + p * z by ring,
      Complex.sin_add, hS, hCo]
    linear_combination ((Complex.cos (p * z) + Complex.sin (p * z)) / 2) * hq2
  have hEeq : E = p / Complex.cos (p * z) := by
    have hh := Complex.Gamma_mul_Gamma_one_sub ((1 : ℂ) / 2 + z)
    rw [show (1 : ℂ) - (1 / 2 + z) = 1 / 2 - z by ring,
      show (Real.pi : ℂ) * ((1 : ℂ) / 2 + z) = (Real.pi : ℂ) / 2 + p * z by dsimp [p]; ring,
      Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two] at hh
    simpa only [one_mul, zero_mul, add_zero, E, p] using hh
  have hcos : Complex.cos (p * z) ≠ 0 := by
    intro he
    rw [he, div_zero] at hEeq
    exact hE hEeq
  have hsinshift : Complex.sin (p * ((1 : ℂ) / 4 + z)) ≠ 0 := by
    intro he
    rw [he, div_zero] at hP
    exact mul_ne_zero hA hc hP
  have hsin : Complex.sin (p * z) ≠ 0 := by
    intro he
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp he
    have hi := congrArg Complex.im hk
    have hzero : Real.pi * (u / 4) = 0 := by
      simpa [p, Complex.mul_im, hzim] using hi.symm
    have hu0 := (mul_eq_zero.mp hzero).resolve_left Real.pi_ne_zero
    exact hu (by linarith)
  have hHsin : H * Complex.sin (p * z) = p * z := by
    have hh := Complex.Gamma_mul_Gamma_one_sub z
    have hr : Complex.Gamma (1 + z) = z * Complex.Gamma z := by
      convert Complex.Gamma_add_one z hz using 1 <;> ring
    calc
      H * Complex.sin (p * z) =
          z * (Complex.Gamma z * Complex.Gamma (1 - z)) * Complex.sin (p * z) := by dsimp [H]; rw [hr]; ring
      _ = z * (p / Complex.sin (p * z)) * Complex.sin (p * z) := by rw [hh]
      _ = p * z := by
        field_simp [hsin]
        simpa [mul_comm] using (div_self hsin)
  have hratio : q * E / (A * c) = 1 + Complex.sin (p * z) / Complex.cos (p * z) := by
    rw [hP, hEeq]
    field_simp [hp, hcos, hsinshift]
    have he : p * (1 + z * 4) / 4 = p * ((1 : ℂ) / 4 + z) := by ring
    rw [he]
    exact hshift
  have hHR : z * E / H = Complex.sin (p * z) / Complex.cos (p * z) := by
    rw [hEeq]
    calc
      z * (p / Complex.cos (p * z)) / H = (p * z) / (H * Complex.cos (p * z)) := by field_simp [hH, hcos]
      _ = (H * Complex.sin (p * z)) / (H * Complex.cos (p * z)) := by rw [hHsin]
      _ = _ := by field_simp [hH, hcos]
  have hQ : 2 * C * (C / 4 * (E * (g / 4) * B / (d * c))) =
      (A * B) / g ^ 2 * (q * E / (A * c)) := by
    calc
      _ = (2 * s ^ 2 * E * B) / (g ^ 3 * d * c) := by
        dsimp only [C]
        field_simp [hg, hd, hc] <;> ring
      _ = (q * E * B) / (g ^ 2 * c) := by
        rw [hs2]
        have he : g ^ 3 * d * c = g ^ 2 * (p * q) * c := by rw [← hgd]; ring
        rw [he]
        field_simp [hg, hq, hc, hp]
        rw [hq2]; ring
      _ = _ := by field_simp [hg, hA, hc] <;> ring
  have hD : C * (A * B / (4 * s)) = (A * B) / g ^ 2 := by
    dsimp only [C]
    field_simp [hg, hs] <;> ring
  have hC : ((4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2 : ℝ) : ℂ) = C := by
    dsimp only [C, s, g]
    push_cast
    rfl
  have h5 : Complex.Gamma ((5 : ℂ) / 4) = g / 4 := by
    calc
      Complex.Gamma ((5 : ℂ) / 4) = Complex.Gamma ((1 : ℂ) / 4 + 1) := by congr 1; ring
      _ = ((1 : ℂ) / 4) * Complex.Gamma ((1 : ℂ) / 4) := Complex.Gamma_add_one _ (by norm_num)
      _ = g / 4 := by rw [hG]; ring
  have h2p : (2 + Complex.I * (u : ℂ)) / 4 = (1 : ℂ) / 2 + z := by dsimp [z]; ring
  have h2m : (2 - Complex.I * (u : ℂ)) / 4 = (1 : ℂ) / 2 - z := by dsimp [z]; ring
  have h1m : (1 - Complex.I * (u : ℂ)) / 4 = (1 : ℂ) / 4 - z := by dsimp [z]; ring
  have h3m : (3 - Complex.I * (u : ℂ)) / 4 = (3 : ℂ) / 4 - z := by dsimp [z]; ring
  have hLam : CothSums.lambda z = A * B * E / H := by
    dsimp only [CothSums.lambda, A, B, E, H]
    ring
  rw [hC, h5, h2p, h2m, h1m, h3m, hLam]
  change -C * (A * B / (4 * s) - 2 * (C / 4 * (E * (g / 4) * B / (d * c)))) =
    (Complex.I * (u : ℂ)) * (A * B * E / H / (4 * g ^ 2))
  rw [show Complex.I * (u : ℂ) = 4 * z by dsimp [z]; ring]
  calc
    _ = 2 * C * (C / 4 * (E * (g / 4) * B / (d * c))) - C * (A * B / (4 * s)) := by ring
    _ = (A * B) / g ^ 2 * (1 + Complex.sin (p * z) / Complex.cos (p * z)) - (A * B) / g ^ 2 := by
      rw [hQ, hD, hratio]
    _ = (A * B) / g ^ 2 * (z * E / H) := by rw [hHR]; ring
    _ = _ := by ring


theorem CothSums.mellin_kernel_gamma_nonzero (u : ℝ) (hu : u ≠ 0) :
    CothSums.mellinKernel u = CothSums.lambda (Complex.I * (u : ℂ) / 4) /
      (4 * (Real.Gamma (1 / 4) : ℂ) ^ 2) := by
  let J : ℝ → ℂ := fun r => (((1 - 2 * CothSums.chi r) * (Real.sqrt (1 + r ^ 4))⁻¹ : ℝ) : ℂ) *
    (r : ℂ) ^ (Complex.I * (u : ℂ))
  let D : ℝ → ℂ := fun r => ((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ) * (r : ℂ) ^ (Complex.I * (u : ℂ))
  let Q : ℝ → ℂ := fun r => (CothSums.chi r : ℂ) *
    ((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ) * (r : ℂ) ^ (Complex.I * (u : ℂ))
  have hibp := CothSums.kernel_mellin_ibp_imaginary u hu
  have hJ : IntegrableOn J (Ioi 0) := hibp.1
  have hD : IntegrableOn D (Ioi 0) := weighted_density_integrable u
  have hQ : IntegrableOn Q (Ioi 0) := by
    have hi : IntegrableOn (fun r : ℝ => (1 / 2 : ℂ) * (D r - J r)) (Ioi 0) :=
      (hD.sub hJ).const_mul (1 / 2 : ℂ)
    apply hi.congr
    filter_upwards with r
    dsimp only [D, J, Q]
    push_cast
    ring
  have hJint : (∫ r in Ioi (0 : ℝ), J r) =
      (∫ r in Ioi (0 : ℝ), D r) - 2 * (∫ r in Ioi (0 : ℝ), Q r) := by
    have hpoint : J = fun r => D r - 2 * Q r := by
      funext r
      dsimp only [D, J, Q]
      push_cast
      ring
    rw [hpoint, integral_sub hD (hQ.const_mul 2), integral_const_mul]
  have heq : (Complex.I * (u : ℂ)) * CothSums.mellinKernel u =
      (Complex.I * (u : ℂ)) * (CothSums.lambda (Complex.I * (u : ℂ) / 4) /
        (4 * (Real.Gamma (1 / 4) : ℂ) ^ 2)) := by
    calc
      _ = -((4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2 : ℝ) : ℂ) *
          (∫ r in Ioi (0 : ℝ), J r) := hibp.2
      _ = -((4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2 : ℝ) : ℂ) *
          ((∫ r in Ioi (0 : ℝ), D r) - 2 * (∫ r in Ioi (0 : ℝ), Q r)) := by rw [hJint]
      _ = _ := by
        change -((4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2 : ℝ) : ℂ) *
          ((∫ r in Ioi (0 : ℝ), ((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ) * (r : ℂ) ^ (Complex.I * (u : ℂ))) -
            2 * (∫ r in Ioi (0 : ℝ), (CothSums.chi r : ℂ) *
              ((Real.sqrt (1 + r ^ 4))⁻¹ : ℂ) * (r : ℂ) ^ (Complex.I * (u : ℂ)))) = _
        rw [CothSums.density_weighted_gamma u, CothSums.chi_density_weighted_gamma u]
        exact CothSums.gamma_moment_difference u hu
  exact mul_left_cancel₀ (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hu)) heq


set_option autoImplicit false


theorem CothSums.lambda_analytic_nonzero_strip (z : ℂ) (hz0 : (-1 / 4 : ℝ) < z.re) (hz1 : z.re < 1 / 4) :
    DifferentiableAt ℂ CothSums.lambda z ∧ CothSums.lambda z ≠ 0 := by
  have hgp (w : ℂ) (hw : 0 < w.re) : DifferentiableAt ℂ Complex.Gamma w := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have he := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at he
    have hn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have ha : 0 < ((1 : ℂ) / 4 + z).re := by norm_num; linarith
  have hb : 0 < ((1 : ℂ) / 4 - z).re := by norm_num; linarith
  have hc : 0 < ((1 : ℂ) / 2 + z).re := by norm_num; linarith
  have hd : 0 < ((1 : ℂ) / 2 - z).re := by norm_num; linarith
  have he : 0 < ((1 : ℂ) + z).re := by norm_num; linarith
  have hf : 0 < ((1 : ℂ) - z).re := by norm_num; linarith
  have hda : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma ((1 : ℂ) / 4 + w)) z :=
    (hgp _ ha).comp z (by fun_prop)
  have hdb : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma ((1 : ℂ) / 4 - w)) z :=
    (hgp _ hb).comp z (by fun_prop)
  have hdc : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma ((1 : ℂ) / 2 + w)) z :=
    (hgp _ hc).comp z (by fun_prop)
  have hdd : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma ((1 : ℂ) / 2 - w)) z :=
    (hgp _ hd).comp z (by fun_prop)
  have hde : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (1 + w)) z :=
    (hgp _ he).comp z (by fun_prop)
  have hdf : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (1 - w)) z :=
    (hgp _ hf).comp z (by fun_prop)
  have hden := mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos he)
    (Complex.Gamma_ne_zero_of_re_pos hf)
  constructor
  · exact ((hda.mul hdb).mul hdc |>.mul hdd).div (hde.mul hdf) hden
  · exact div_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos ha)
        (Complex.Gamma_ne_zero_of_re_pos hb))
      (Complex.Gamma_ne_zero_of_re_pos hc)) (Complex.Gamma_ne_zero_of_re_pos hd)) hden


theorem CothSums.mellin_kernel_gamma : ∀ u : ℝ,
    CothSums.mellinKernel u = CothSums.lambda (Complex.I * (u : ℂ) / 4) /
      (4 * (Real.Gamma (1 / 4) : ℂ) ^ 2) := by
  intro u
  by_cases hu : u = 0
  · subst u
    have hM : ContinuousAt CothSums.mellinKernel (0 : ℝ) := by
      have hd := (kernel_mellin_analytic (Complex.I * ((0 : ℝ) : ℂ))
        (by norm_num) (by norm_num)).2.continuousAt
      have hc : ContinuousAt (fun t : ℝ => Complex.I * (t : ℂ)) 0 := by fun_prop
      exact ContinuousAt.comp (f := fun t : ℝ => Complex.I * (t : ℂ))
        (g := mellin (fun r : ℝ => (CothSums.kernel r : ℂ))) hd hc
    have hL : ContinuousAt (fun t : ℝ => CothSums.lambda (Complex.I * (t : ℂ) / 4) /
        (4 * (Real.Gamma (1 / 4) : ℂ) ^ 2)) (0 : ℝ) := by
      have hd := (CothSums.lambda_analytic_nonzero_strip
        (Complex.I * ((0 : ℝ) : ℂ) / 4) (by norm_num) (by norm_num)).1.continuousAt
      have hc : ContinuousAt (fun t : ℝ => Complex.I * (t : ℂ) / 4) 0 := by fun_prop
      exact (ContinuousAt.comp (f := fun t : ℝ => Complex.I * (t : ℂ) / 4)
        (g := CothSums.lambda) hd hc).div_const _
    have heq : CothSums.mellinKernel =ᶠ[nhdsWithin (0 : ℝ) ({0}ᶜ)]
        (fun t : ℝ => CothSums.lambda (Complex.I * (t : ℂ) / 4) /
          (4 * (Real.Gamma (1 / 4) : ℂ) ^ 2)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact CothSums.mellin_kernel_gamma_nonzero t (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht)
    exact tendsto_nhds_unique_of_eventuallyEq
      (hM.mono_left nhdsWithin_le_nhds) (hL.mono_left nhdsWithin_le_nhds) heq
  · exact CothSums.mellin_kernel_gamma_nonzero u hu


open MeasureTheory


theorem CothSums.evaluation_of_fourier_and_quintic_lambert
  (fourier_identity : ∀ P : Polynomial ℝ, P.eval 0 = 0 → P.eval 1 = 0 →
    CothSums.testMoment P = 2 * ∑' n : ℕ,
      (Real.tanh (Real.pi * (2 * (n : ℝ) + 1) / 2) / (2 * (n : ℝ) + 1)) *
        CothSums.cosineTest P n)
  (quintic_lambert_evaluation : HasSum (CothSums.oddTanhTerm 5)
    (Real.pi ^ 5 / 252 - (9 / 32) * ∑' n : ℕ, CothSums.cothTerm n))
 :
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
  exact CothSums.evaluation_of_fourier_quintic_lambert_mellin
    fourier_identity quintic_lambert_evaluation CothSums.mellin_kernel_gamma


set_option autoImplicit false


set_option autoImplicit false


open Complex


private theorem complex_pf (x : ℂ) (hx : 0 < x.re) :
    HasSum (fun n : ℕ => 1 / (((n : ℂ) + 1) ^ 2 + x ^ 2))
      (((Real.pi : ℂ) * (Complex.cosh ((Real.pi : ℂ) * x) /
        Complex.sinh ((Real.pi : ℂ) * x)) - 1 / x) / (2 * x)) := by
  let z : ℂ := x * Complex.I
  have hx0 : x ≠ 0 := by intro he; simpa only [he, Complex.zero_re, lt_self_iff_false] using hx
  have hz : z ∈ Complex.integerComplement :=
    UpperHalfPlane.coe_mem_integerComplement ⟨z, by simpa [z] using hx⟩
  have ht : HasSum (fun n : ℕ => cotTerm z n)
      ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) - 1 / z) := by
    have hh := (summable_cotTerm hz).hasSum
    have he : (∑' n : ℕ, cotTerm z n) =
        (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) - 1 / z := by
      simpa only [cotTerm] using (cot_series_rep' hz).symm
    rwa [he] at hh
  have hterm (n : ℕ) : cotTerm z n =
      (-2 * x * Complex.I) * (1 / (((n : ℂ) + 1) ^ 2 + x ^ 2)) := by
    have he : (z + ((n : ℂ) + 1)) * (z - ((n : ℂ) + 1)) =
        -(((n : ℂ) + 1) ^ 2 + x ^ 2) := by
      dsimp [z]
      ring_nf
      simp only [Complex.I_sq]
      ring
    rw [cotTerm_identity hz, he]
    simp only [z, div_eq_mul_inv, inv_neg, one_mul]
    ring
  have hcot : Complex.cot ((Real.pi : ℂ) * z) =
      -((Complex.cosh ((Real.pi : ℂ) * x) /
        Complex.sinh ((Real.pi : ℂ) * x)) * Complex.I) := by
    rw [show (Real.pi : ℂ) * z = ((Real.pi : ℂ) * x) * Complex.I by dsimp [z]; ring,
      Complex.cot_eq_cos_div_sin, Complex.cos_mul_I, Complex.sin_mul_I,
      div_mul_eq_div_div, Complex.div_I]
  have hcoef : -2 * x * Complex.I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hx0) Complex.I_ne_zero
  have hh := ht.mul_left ((-2 * x * Complex.I)⁻¹)
  convert! hh using 1
  · ext n
    rw [hterm, ← mul_assoc, inv_mul_cancel₀ hcoef, one_mul]
  · rw [hcot]
    dsimp [z]
    field_simp [hx0, Complex.I_ne_zero]
    <;> simp only [Complex.I_sq]
    <;> ring


private theorem gaussian_transform : HasSum (fun n : ℕ =>
 (Complex.cosh ((Real.pi : ℂ) * ((1 + Complex.I) / 2) * ((n : ℂ) + 1)) / Complex.sinh ((Real.pi : ℂ) * ((1 + Complex.I) / 2) * ((n : ℂ) + 1))) / ((n : ℂ) + 1) ^ 5 +
 (1 / 4 : ℂ) * ((Complex.cosh ((Real.pi : ℂ) * (1 - Complex.I) * ((n : ℂ) + 1)) / Complex.sinh ((Real.pi : ℂ) * (1 - Complex.I) * ((n : ℂ) + 1))) / ((n : ℂ) + 1) ^ 5)) ((Real.pi : ℂ) ^ 5 / 252) := by
  let a : ℂ := (1 + Complex.I) / 2
  let b : ℂ := 1 - Complex.I
  let N : ℕ → ℂ := fun n => (n : ℂ) + 1
  let R : ℕ → ℝ := fun n => (n : ℝ) + 1
  let A : ℂ → ℕ × ℕ → ℂ := fun t p =>
    1 / (N p.1 ^ 4 * (N p.2 ^ 2 + t ^ 2 * N p.1 ^ 2))
  let Q : ℂ → ℕ → ℂ := fun t n =>
    (Complex.cosh ((Real.pi : ℂ) * t * N n) /
      Complex.sinh ((Real.pi : ℂ) * t * N n)) / N n ^ 5
  have hN (n : ℕ) : N n = (R n : ℂ) := by simp [N, R]
  have hR (n : ℕ) : 0 < R n := by dsimp [R]; positivity
  have hN0 (n : ℕ) : N n ≠ 0 := by rw [hN]; exact Complex.ofReal_ne_zero.mpr (hR n).ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz6real : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 6) (Real.pi ^ 6 / 945) := by
    have hB5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
    have hB6 : bernoulli 6 = 1 / 42 := by
      rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
      norm_num [Finset.sum_range_succ, hB5, show Nat.choose 6 2 = 15 by decide, show Nat.choose 6 4 = 15 by decide]
    convert! hasSum_zeta_nat (show (3 : ℕ) ≠ 0 by decide) using 1 <;>
      norm_num [hB6, Nat.factorial] <;> ring
  have hshift (s : ℕ) (hs : 0 < s) (c : ℝ)
      (hh : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ s) c) :
      HasSum (fun n : ℕ => 1 / R n ^ s) c := by
    have hv : (∑ i ∈ Finset.range 1, (1 : ℝ) / (i : ℝ) ^ s) = 0 := by simp [hs.ne']
    have hi := (hasSum_nat_add_iff' 1).mpr hh
    simpa only [Nat.cast_add, Nat.cast_one, hv, sub_zero, R] using hi
  have h2r := hshift 2 (by norm_num) _ hasSum_zeta_two
  have h4r := hshift 4 (by norm_num) _ hasSum_zeta_four
  have h6r := hshift 6 (by norm_num) _ hz6real
  have hcast (s : ℕ) (c : ℝ) (hh : HasSum (fun n : ℕ => 1 / R n ^ s) c) :
      HasSum (fun n : ℕ => (1 : ℂ) / N n ^ s) (c : ℂ) := by
    simpa only [hN, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow] using
      Complex.hasSum_ofReal.mpr hh
  have h2 := hcast 2 _ h2r
  have h4 := hcast 4 _ h4r
  have h6 := hcast 6 _ h6r
  have hprod : Summable (fun p : ℕ × ℕ => (1 / R p.1 ^ 4) * (1 / R p.2 ^ 2)) :=
    h4r.summable.mul_of_nonneg h2r.summable (fun n => by positivity) (fun n => by positivity)
  have hD (t : ℂ) (ht : (t ^ 2).re = 0) (n m : ℕ) :
      R m ^ 2 ≤ ‖N m ^ 2 + t ^ 2 * N n ^ 2‖ := by
    have he : (N m ^ 2 + t ^ 2 * N n ^ 2).re = R m ^ 2 := by
      simp only [hN, ← Complex.ofReal_pow, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, ht, zero_mul, mul_zero, sub_zero, add_zero]
    calc
      _ = |(N m ^ 2 + t ^ 2 * N n ^ 2).re| := by rw [he, abs_of_nonneg (sq_nonneg _)]
      _ ≤ _ := Complex.abs_re_le_norm _
  have hAs (t : ℂ) (ht : (t ^ 2).re = 0) : Summable (A t) := by
    apply hprod.of_norm_bounded
    intro p
    have hnorm : ‖A t p‖ = 1 / (R p.1 ^ 4 * ‖N p.2 ^ 2 + t ^ 2 * N p.1 ^ 2‖) := by
      dsimp [A]
      rw [norm_div, norm_one, norm_mul, norm_pow, hN]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hR _)]
    rw [hnorm]
    calc
      _ ≤ 1 / (R p.1 ^ 4 * R p.2 ^ 2) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact mul_le_mul_of_nonneg_left (hD t ht p.1 p.2) (by positivity)
      _ = _ := by ring
  have hS (t : ℂ) (ht : 0 < t.re) (ht2 : (t ^ 2).re = 0) :
      HasSum (Q t) (((Real.pi ^ 6 / 945 : ℝ) : ℂ) / ((Real.pi : ℂ) * t) +
        (2 * t / (Real.pi : ℂ)) * ∑' p : ℕ × ℕ, A t p) := by
    have ht0 : t ≠ 0 := by intro he; simpa only [he, Complex.zero_re, lt_self_iff_false] using ht
    have hrow (n : ℕ) : (∑' m : ℕ, A t (n, m)) =
        (N n ^ 4)⁻¹ * (((Real.pi : ℂ) *
          (Complex.cosh ((Real.pi : ℂ) * t * N n) /
            Complex.sinh ((Real.pi : ℂ) * t * N n)) - 1 / (t * N n)) / (2 * (t * N n))) := by
      have htn : 0 < (t * N n).re := by
        rw [hN, Complex.mul_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        exact mul_pos ht (hR n)
      have hh := (complex_pf (t * N n) htn).mul_left (N n ^ 4)⁻¹
      have hhe : HasSum (fun m : ℕ => A t (n, m))
          ((N n ^ 4)⁻¹ * (((Real.pi : ℂ) *
            (Complex.cosh ((Real.pi : ℂ) * t * N n) /
              Complex.sinh ((Real.pi : ℂ) * t * N n)) - 1 / (t * N n)) /
                (2 * (t * N n)))) := by
        convert! hh using 1
        · ext m
          dsimp [A, N]
          simp only [mul_pow, one_div, mul_inv_rev]
          ring
        · congr 3 <;> ring
      exact hhe.tsum_eq
    have heq (n : ℕ) : Q t n =
        (1 / ((Real.pi : ℂ) * t)) * (1 / N n ^ 6) +
        (2 * t / (Real.pi : ℂ)) * (∑' m : ℕ, A t (n, m)) := by
      rw [hrow]
      dsimp [Q]
      generalize (Complex.cosh ((Real.pi : ℂ) * t * N n) /
        Complex.sinh ((Real.pi : ℂ) * t * N n)) = z
      field_simp [hpi, ht0, hN0 n]
      <;> ring
    have hh := (h6.mul_left (1 / ((Real.pi : ℂ) * t))).add
      ((hAs t ht2).prod.hasSum.mul_left (2 * t / (Real.pi : ℂ)))
    convert! hh using 1
    · ext n
      exact heq n
    · rw [← (hAs t ht2).tsum_prod]
      ring
  have ha2 : a ^ 2 = Complex.I / 2 := by
    norm_num [a, Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq,
      Complex.mul_re, Complex.mul_im, pow_succ]
  have hb2 : b ^ 2 = -2 * Complex.I := by
    norm_num [b, Complex.ext_iff, Complex.mul_re, Complex.mul_im, pow_succ]
  have haR : 0 < a.re := by norm_num [a, Complex.div_re, Complex.normSq]
  have hbR : 0 < b.re := by norm_num [b]
  have ha20 : (a ^ 2).re = 0 := by rw [ha2]; norm_num
  have hb20 : (b ^ 2).re = 0 := by rw [hb2]; norm_num
  have ha0 : a ≠ 0 := by intro he; simpa [he] using haR
  have hb0 : b ≠ 0 := by intro he; simpa [he] using hbR
  have hab : a * b = 1 := by
    norm_num [a, b, Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq,
      Complex.mul_re, Complex.mul_im]
  have hia : a⁻¹ = b := by apply mul_left_cancel₀ ha0; rw [mul_inv_cancel₀ ha0, hab]
  have hib : b⁻¹ = a := by apply mul_right_cancel₀ hb0; rw [inv_mul_cancel₀ hb0, hab]
  have hcoeff : b = -4 * a ^ 3 := by
    norm_num [a, b, Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq,
      Complex.mul_re, Complex.mul_im, pow_succ]
  let P : ℕ × ℕ → ℂ := fun p => (1 / N p.1 ^ 4) * (1 / N p.2 ^ 2)
  have hPs : Summable P := by
    simpa only [P, hN, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_pow] using Complex.summable_ofReal.mpr hprod
  have hPval : (∑' p : ℕ × ℕ, P p) =
      ((Real.pi ^ 4 / 90 : ℝ) : ℂ) * ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
    have hh := h4.summable.tsum_mul_tsum h2.summable hPs
    rw [h4.tsum_eq, h2.tsum_eq] at hh
    exact hh.symm
  have hden (t : ℂ) (ht : (t ^ 2).re = 0) (n m : ℕ) :
      N m ^ 2 + t ^ 2 * N n ^ 2 ≠ 0 := by
    apply norm_pos_iff.mp
    exact lt_of_lt_of_le (sq_pos_of_pos (hR m)) (hD t ht n m)
  have hterm (p : ℕ × ℕ) : A a p - a ^ 2 * A b p.swap = P p - a ^ 2 * P p.swap := by
    have hDa := hden a ha20 p.1 p.2
    have hDb := hden b hb20 p.2 p.1
    dsimp only [A, P, Prod.swap, Prod.fst, Prod.snd]
    generalize heD : N p.2 ^ 2 + a ^ 2 * N p.1 ^ 2 = d at hDa ⊢
    generalize heE : N p.1 ^ 2 + b ^ 2 * N p.2 ^ 2 = e at hDb ⊢
    field_simp [hN0 p.1, hN0 p.2, hDa, hDb]
    rw [← heD, ← heE]
    dsimp [a, b]
    field_simp
    apply Complex.ext <;>
      simp only [hN, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, pow_succ]
      <;> norm_num <;> ring
  have hswapA : (∑' p : ℕ × ℕ, A b p.swap) = ∑' p : ℕ × ℕ, A b p :=
    (Equiv.prodComm ℕ ℕ).tsum_eq (A b)
  have hswapP : (∑' p : ℕ × ℕ, P p.swap) = ∑' p : ℕ × ℕ, P p :=
    (Equiv.prodComm ℕ ℕ).tsum_eq P
  have hsum : (∑' p : ℕ × ℕ, A a p) - a ^ 2 * (∑' p : ℕ × ℕ, A b p) =
      (1 - a ^ 2) * (((Real.pi ^ 4 / 90 : ℝ) : ℂ) * ((Real.pi ^ 2 / 6 : ℝ) : ℂ)) := by
    calc
      _ = ∑' p : ℕ × ℕ, (A a p - a ^ 2 * A b p.swap) := by
        rw [(hAs a ha20).tsum_sub ((hAs b hb20).prod_symm.mul_left (a ^ 2)),
          tsum_mul_left, hswapA]
      _ = ∑' p : ℕ × ℕ, (P p - a ^ 2 * P p.swap) := tsum_congr hterm
      _ = _ := by
        rw [hPs.tsum_sub (hPs.prod_symm.mul_left (a ^ 2)), tsum_mul_left, hswapP, hPval]
        ring
  have hlin (X Y Z : ℂ) :
      Z / ((Real.pi : ℂ) * a) + (2 * a / (Real.pi : ℂ)) * X +
        (1 / 4 : ℂ) * (Z / ((Real.pi : ℂ) * b) + (2 * b / (Real.pi : ℂ)) * Y) =
      Z * (b + a / 4) / (Real.pi : ℂ) +
        (2 * a / (Real.pi : ℂ)) * (X - a ^ 2 * Y) := by
    simp only [div_eq_mul_inv, mul_inv_rev, hia, hib]
    rw [hcoeff]
    ring
  have heval :
      ((Real.pi ^ 6 / 945 : ℝ) : ℂ) / ((Real.pi : ℂ) * a) +
        (2 * a / (Real.pi : ℂ)) * (∑' p : ℕ × ℕ, A a p) +
        (1 / 4 : ℂ) * (((Real.pi ^ 6 / 945 : ℝ) : ℂ) / ((Real.pi : ℂ) * b) +
          (2 * b / (Real.pi : ℂ)) * (∑' p : ℕ × ℕ, A b p)) =
      (Real.pi : ℂ) ^ 5 / 252 := by
    rw [hlin, hsum]
    dsimp [a, b]
    simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
    field_simp [hpi]
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, pow_succ]
      <;> norm_num <;> ring
  have hh := (hS a haR ha20).add ((hS b hbR hb20).mul_left (1 / 4))
  rw [heval] at hh
  exact hh


set_option autoImplicit false


private theorem gaussian_parity (n : ℕ) :
 (Complex.cosh ((Real.pi : ℂ) * ((1 + Complex.I) / 2) * (2 * (n : ℂ) + 2)) / Complex.sinh ((Real.pi : ℂ) * ((1 + Complex.I) / 2) * (2 * (n : ℂ) + 2))) = ((Real.cosh (Real.pi * ((n : ℝ) + 1)) / Real.sinh (Real.pi * ((n : ℝ) + 1)) : ℝ) : ℂ) ∧
 (Complex.cosh ((Real.pi : ℂ) * ((1 + Complex.I) / 2) * (2 * (n : ℂ) + 1)) / Complex.sinh ((Real.pi : ℂ) * ((1 + Complex.I) / 2) * (2 * (n : ℂ) + 1))) = (Real.tanh (Real.pi * (2 * (n : ℝ) + 1) / 2) : ℂ) ∧
 (Complex.cosh ((Real.pi : ℂ) * (1 - Complex.I) * ((n : ℂ) + 1)) / Complex.sinh ((Real.pi : ℂ) * (1 - Complex.I) * ((n : ℂ) + 1))) = ((Real.cosh (Real.pi * ((n : ℝ) + 1)) / Real.sinh (Real.pi * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
  let q : ℂ → ℂ := fun z => Complex.cosh z / Complex.sinh z
  have hq (z : ℂ) : q z = (Complex.tanh z)⁻¹ := by
    dsimp [q]
    rw [Complex.tanh_eq_sinh_div_cosh, inv_div]
  have hp : Function.Periodic q ((Real.pi : ℂ) * Complex.I) := by
    intro z
    rw [hq, hq, Complex.tanh_add_pi_mul_I]
  have hh (z : ℂ) : q (z + (Real.pi : ℂ) / 2 * Complex.I) = Complex.tanh z := by
    dsimp [q]
    rw [Complex.cosh_add, Complex.sinh_add, Complex.cosh_mul_I,
      Complex.sinh_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    simp only [mul_zero, zero_mul, zero_add, add_zero, one_mul, mul_one,
      Complex.tanh_eq_sinh_div_cosh]
    exact mul_div_mul_right _ _ Complex.I_ne_zero
  have hcast (r : ℝ) : q (r : ℂ) =
      ((Real.cosh r / Real.sinh r : ℝ) : ℂ) := by
    dsimp [q]
    simp only [Complex.ofReal_div, Complex.ofReal_cosh, Complex.ofReal_sinh]
  constructor
  · change q _ = _
    rw [show (Real.pi : ℂ) * ((1 + Complex.I) / 2) * (2 * (n : ℂ) + 2) =
      (Real.pi * ((n : ℝ) + 1) : ℝ) + ((n : ℂ) + 1) * ((Real.pi : ℂ) * Complex.I) by
        push_cast; ring]
    have he := (hp.nat_mul (n + 1)) ((Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ)
    simpa only [Nat.cast_add, Nat.cast_one] using he.trans (hcast _)
  · constructor
    · change q _ = _
      rw [show (Real.pi : ℂ) * ((1 + Complex.I) / 2) * (2 * (n : ℂ) + 1) =
        (((Real.pi * (2 * (n : ℝ) + 1) / 2 : ℝ) : ℂ) +
          (Real.pi : ℂ) / 2 * Complex.I) + (n : ℂ) * ((Real.pi : ℂ) * Complex.I) by
            push_cast; ring]
      rw [(hp.nat_mul n) _, hh]
      exact (Complex.ofReal_tanh _).symm
    · change q _ = _
      rw [show (Real.pi : ℂ) * (1 - Complex.I) * ((n : ℂ) + 1) =
        ((Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) -
          ((n : ℂ) + 1) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring]
      have he := hp.sub_nat_mul_eq (x := ((Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ)) (n + 1)
      simpa only [Nat.cast_add, Nat.cast_one] using he.trans (hcast _)


set_option autoImplicit false


private theorem coth_summable : Summable CothSums.cothTerm := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 5) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hb : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 5) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr hp
  apply (hb.mul_left 2).of_norm_bounded
  intro n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hx : 1 ≤ Real.pi * ((n : ℝ) + 1) := by
    nlinarith [Real.pi_pos, Real.pi_gt_three]
  have hs : 1 ≤ Real.sinh (Real.pi * ((n : ℝ) + 1)) :=
    hx.trans (Real.self_le_sinh_iff.mpr (by linarith))
  have he : Real.exp (-(Real.pi * ((n : ℝ) + 1))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hc := Real.cosh_sub_sinh (Real.pi * ((n : ℝ) + 1))
  have hspos : 0 < Real.sinh (Real.pi * ((n : ℝ) + 1)) := by linarith
  have hratio : Real.cosh (Real.pi * ((n : ℝ) + 1)) /
      Real.sinh (Real.pi * ((n : ℝ) + 1)) ≤ 2 :=
    (div_le_iff₀ hspos).mpr (by linarith)
  have hnonneg : 0 ≤ CothSums.cothTerm n := by
    unfold CothSums.cothTerm
    exact div_nonneg (div_nonneg (Real.cosh_pos _).le hspos.le) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  unfold CothSums.cothTerm
  calc
    _ ≤ 2 / ((n : ℝ) + 1) ^ 5 :=
      div_le_div_of_nonneg_right hratio (by positivity)
    _ = 2 * (1 / ((n : ℝ) + 1) ^ 5) := by ring


set_option autoImplicit false


theorem CothSums.oddTanhTerm_hasSum_five : HasSum (CothSums.oddTanhTerm 5)
    (Real.pi ^ 5 / 252 - (9 / 32) * ∑' n : ℕ, CothSums.cothTerm n) := by
  let Q : ℂ → ℕ → ℂ := fun t n =>
    (Complex.cosh ((Real.pi : ℂ) * t * ((n : ℂ) + 1)) /
      Complex.sinh ((Real.pi : ℂ) * t * ((n : ℂ) + 1))) / ((n : ℂ) + 1) ^ 5
  let a : ℂ := (1 + Complex.I) / 2
  let b : ℂ := 1 - Complex.I
  let T : ℝ := ∑' n : ℕ, CothSums.oddTanhTerm 5 n
  let S : ℝ := ∑' n : ℕ, CothSums.cothTerm n
  have hodd (n : ℕ) : Q a (2 * n) = (CothSums.oddTanhTerm 5 n : ℂ) := by
    dsimp [Q, a]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [(gaussian_parity n).2.1]
    simp only [CothSums.oddTanhTerm, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ofNat,
      Complex.ofReal_one]
  have heven (n : ℕ) : Q a (2 * n + 1) = (1 / 32 : ℂ) * (CothSums.cothTerm n : ℂ) := by
    dsimp [Q, a]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [show 2 * (n : ℂ) + 1 + 1 = 2 * (n : ℂ) + 2 by ring, (gaussian_parity n).1]
    simp only [CothSums.cothTerm, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ofNat,
      Complex.ofReal_one]
    rw [show 2 * (n : ℂ) + 2 = 2 * ((n : ℂ) + 1) by ring]
    simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
    norm_num
    <;> ring
  have hbeta (n : ℕ) : Q b n = (CothSums.cothTerm n : ℂ) := by
    dsimp [Q, b]
    rw [(gaussian_parity n).2.2]
    simp only [CothSums.cothTerm, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ofNat,
      Complex.ofReal_one]
  have hT : HasSum (fun n : ℕ => (CothSums.oddTanhTerm 5 n : ℂ)) (T : ℂ) :=
    Complex.hasSum_ofReal.mpr tanh_summable.2.hasSum
  have hS : HasSum (fun n : ℕ => (CothSums.cothTerm n : ℂ)) (S : ℂ) :=
    Complex.hasSum_ofReal.mpr coth_summable.hasSum
  have hA : HasSum (Q a) ((T : ℂ) + (1 / 32 : ℂ) * (S : ℂ)) := by
    have ho : HasSum (fun n : ℕ => Q a (2 * n)) (T : ℂ) := by
      simpa only [hodd] using hT
    have he : HasSum (fun n : ℕ => Q a (2 * n + 1)) ((1 / 32 : ℂ) * (S : ℂ)) := by
      simpa only [heven] using hS.mul_left (1 / 32)
    exact ho.even_add_odd he
  have hB : HasSum (Q b) (S : ℂ) := by
    have hf : Q b = (fun n : ℕ => (CothSums.cothTerm n : ℂ)) := funext hbeta
    rw [hf]
    exact hS
  have htrans : HasSum (fun n : ℕ => Q a n + (1 / 4 : ℂ) * Q b n)
      ((Real.pi : ℂ) ^ 5 / 252) := gaussian_transform
  have heq := (hA.add (hB.mul_left (1 / 4))).unique htrans
  have heqR : T + (1 / 32) * S + (1 / 4) * S = Real.pi ^ 5 / 252 := by
    have heq' : ((T + (1 / 32) * S + (1 / 4) * S : ℝ) : ℂ) =
        ((Real.pi ^ 5 / 252 : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
        Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_one] using heq
    exact Complex.ofReal_injective heq'
  have hval : T = Real.pi ^ 5 / 252 - (9 / 32) * S := by linarith [heqR]
  exact hval ▸ tanh_summable.2.hasSum


theorem CothSums.evaluation_of_fourier_identity
  (fourier_identity : ∀ P : Polynomial ℝ, P.eval 0 = 0 → P.eval 1 = 0 →
    CothSums.testMoment P = 2 * ∑' n : ℕ,
      (Real.tanh (Real.pi * (2 * (n : ℝ) + 1) / 2) / (2 * (n : ℝ) + 1)) *
        CothSums.cosineTest P n)
 :
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
  exact CothSums.evaluation_of_fourier_and_quintic_lambert
    fourier_identity CothSums.oddTanhTerm_hasSum_five


set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


open MeasureTheory Set Filter


theorem CothSums.ComplexAnalysis.square_cauchy_kernel_boundary (a : ℝ) (ha : 0 < a) :
    (∫ t : ℝ in -a..a, ((t : ℂ) - (a : ℂ) * Complex.I)⁻¹) -
    (∫ t : ℝ in -a..a, ((t : ℂ) + (a : ℂ) * Complex.I)⁻¹) +
    Complex.I * (∫ t : ℝ in -a..a, ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹) -
    Complex.I * (∫ t : ℝ in -a..a, (-(a : ℂ) + (t : ℂ) * Complex.I)⁻¹) =
      2 * (Real.pi : ℂ) * Complex.I := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hn1 (t : ℝ) : (t : ℂ) - (a : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_sub, neg_eq_zero] at this
    apply ha.ne'
    simpa using (neg_eq_zero.mp (by simpa using this : -a = (0 : ℝ)))
  have hn2 (t : ℝ) : (t : ℂ) + (a : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact ha.ne' this
  have hn3 (t : ℝ) : (a : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact ha.ne' this
  have hn4 (t : ℝ) : -(a : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact ha.ne' this
  have h1 : IntervalIntegrable (fun t : ℝ => ((t : ℂ) - (a : ℂ) * Complex.I)⁻¹) MeasureTheory.volume (-a) a :=
    (Continuous.inv₀ (by fun_prop) hn1).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t : ℝ => ((t : ℂ) + (a : ℂ) * Complex.I)⁻¹) MeasureTheory.volume (-a) a :=
    (Continuous.inv₀ (by fun_prop) hn2).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun t : ℝ => ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹) MeasureTheory.volume (-a) a :=
    (Continuous.inv₀ (by fun_prop) hn3).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun t : ℝ => (-(a : ℂ) + (t : ℂ) * Complex.I)⁻¹) MeasureTheory.volume (-a) a :=
    (Continuous.inv₀ (by fun_prop) hn4).intervalIntegrable _ _
  have hi (t : ℝ) :
      ((t : ℂ) - (a : ℂ) * Complex.I)⁻¹ - ((t : ℂ) + (a : ℂ) * Complex.I)⁻¹ +
        Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹ -
        Complex.I * (-(a : ℂ) + (t : ℂ) * Complex.I)⁻¹ =
      (4 * (a : ℂ) * Complex.I) * ((a ^ 2 + t ^ 2 : ℝ) : ℂ)⁻¹ := by
    have hab : ((a ^ 2 + t ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
    have hd1 := hn1 t
    have hd2 := hn2 t
    have hd3 := hn3 t
    have hd4 := hn4 t
    clear h1 h2 h3 h4 hn1 hn2 hn3 hn4
    push_cast at hab ⊢
    field_simp [hd1, hd2, hd3, hd4, hab]
    ring_nf
    norm_num
    simp only [show Complex.I ^ 2 = (-1 : ℂ) by norm_num,
      show Complex.I ^ 3 = -Complex.I by norm_num,
      show Complex.I ^ 4 = (1 : ℂ) by norm_num,
      show Complex.I ^ 5 = Complex.I by norm_num [pow_succ, Complex.I_sq],
      show Complex.I ^ 6 = (-1 : ℂ) by norm_num [pow_succ, Complex.I_sq]]
    <;> ring
  calc
    _ = ∫ t : ℝ in -a..a,
      ((t : ℂ) - (a : ℂ) * Complex.I)⁻¹ - ((t : ℂ) + (a : ℂ) * Complex.I)⁻¹ +
        Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹ -
        Complex.I * (-(a : ℂ) + (t : ℂ) * Complex.I)⁻¹ := by
      rw [intervalIntegral.integral_sub ((h1.sub h2).add (h3.const_mul _)) (h4.const_mul _),
        intervalIntegral.integral_add (h1.sub h2) (h3.const_mul _),
        intervalIntegral.integral_sub h1 h2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ = (4 * (a : ℂ) * Complex.I) *
        ((∫ t : ℝ in -a..a, (a ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ) := by
      simp_rw [hi]
      rw [intervalIntegral.integral_const_mul, ← intervalIntegral.integral_ofReal]
      simp only [Complex.ofReal_inv]
    _ = _ := by
      rw [integral_inv_sq_add_sq ha.ne']
      simp only [div_self ha.ne', neg_div, Real.arctan_one, Real.arctan_neg]
      push_cast
      field_simp
      <;> ring


theorem CothSums.ComplexAnalysis.square_cauchy_formula (q : ℂ → ℂ) (a : ℝ) (ha : 0 < a)
    (hq : DifferentiableOn ℂ q (Set.Icc (-a) a ×ℂ Set.Icc (-a) a)) :
    (∫ t : ℝ in -a..a, q ((t : ℂ) - (a : ℂ) * Complex.I) /
      ((t : ℂ) - (a : ℂ) * Complex.I)) -
    (∫ t : ℝ in -a..a, q ((t : ℂ) + (a : ℂ) * Complex.I) /
      ((t : ℂ) + (a : ℂ) * Complex.I)) +
    Complex.I * (∫ t : ℝ in -a..a, q ((a : ℂ) + (t : ℂ) * Complex.I) /
      ((a : ℂ) + (t : ℂ) * Complex.I)) -
    Complex.I * (∫ t : ℝ in -a..a, q (-(a : ℂ) + (t : ℂ) * Complex.I) /
      (-(a : ℂ) + (t : ℂ) * Complex.I)) =
        2 * (Real.pi : ℂ) * Complex.I * q 0 := by
  let S : Set ℂ := Icc (-a) a ×ℂ Icc (-a) a
  have hle : -a ≤ a := by linarith
  have hS : S ∈ nhds (0 : ℂ) := by
    have h0 : (0 : ℂ) ∈ (Ioo (-a) a ×ℂ Ioo (-a) a) := by
      change (-a < 0 ∧ 0 < a) ∧ (-a < 0 ∧ 0 < a)
      constructor <;> constructor <;> linarith
    exact Filter.mem_of_superset ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds h0)
      (fun z hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩)
  have hds : DifferentiableOn ℂ (dslope q 0) S :=
    (Complex.differentiableOn_dslope hS).mpr hq
  have hzero := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (dslope q 0) (-(a : ℂ) - (a : ℂ) * Complex.I)
    ((a : ℂ) + (a : ℂ) * Complex.I)
    (by simpa [S, uIcc_of_le hle] using hds)
  have hz :
      (∫ t : ℝ in -a..a, dslope q 0 ((t : ℂ) - (a : ℂ) * Complex.I)) -
      (∫ t : ℝ in -a..a, dslope q 0 ((t : ℂ) + (a : ℂ) * Complex.I)) +
      Complex.I * (∫ t : ℝ in -a..a, dslope q 0 ((a : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I * (∫ t : ℝ in -a..a, dslope q 0 (-(a : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
    simpa [sub_eq_add_neg, smul_eq_mul] using hzero
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hn1 (t : ℝ) : (t : ℂ) - (a : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_sub, neg_eq_zero] at this
    apply ha.ne'
    simpa using (neg_eq_zero.mp (by simpa using this : -a = (0 : ℝ)))
  have hn2 (t : ℝ) : (t : ℂ) + (a : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact ha.ne' this
  have hn3 (t : ℝ) : (a : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact ha.ne' this
  have hn4 (t : ℝ) : -(a : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact ha.ne' this
  have hk1 : IntervalIntegrable (fun t : ℝ => ((t : ℂ) - (a : ℂ) * Complex.I)⁻¹) MeasureTheory.volume (-a) a :=
    (Continuous.inv₀ (by fun_prop) hn1).intervalIntegrable _ _
  have hk2 : IntervalIntegrable (fun t : ℝ => ((t : ℂ) + (a : ℂ) * Complex.I)⁻¹) MeasureTheory.volume (-a) a :=
    (Continuous.inv₀ (by fun_prop) hn2).intervalIntegrable _ _
  have hk3 : IntervalIntegrable (fun t : ℝ => ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹) MeasureTheory.volume (-a) a :=
    (Continuous.inv₀ (by fun_prop) hn3).intervalIntegrable _ _
  have hk4 : IntervalIntegrable (fun t : ℝ => (-(a : ℂ) + (t : ℂ) * Complex.I)⁻¹) MeasureTheory.volume (-a) a :=
    (Continuous.inv₀ (by fun_prop) hn4).intervalIntegrable _ _
  have hpath (p : ℝ → ℂ) (hp : Continuous p) (hpm : MapsTo p (Icc (-a) a) S) :
      IntervalIntegrable (fun t => dslope q 0 (p t)) volume (-a) a :=
    ContinuousOn.intervalIntegrable_of_Icc hle (hds.continuousOn.comp hp.continuousOn hpm)
  have hd1 : IntervalIntegrable (fun t : ℝ => dslope q 0 ((t : ℂ) - (a : ℂ) * Complex.I)) volume (-a) a := by
    apply hpath _ (by fun_prop)
    intro t ht
    change ((t : ℂ) - (a : ℂ) * Complex.I).re ∈ Icc (-a) a ∧
      ((t : ℂ) - (a : ℂ) * Complex.I).im ∈ Icc (-a) a
    simpa using And.intro ht (show -a ∈ Icc (-a) a from ⟨le_rfl, hle⟩)
  have hd2 : IntervalIntegrable (fun t : ℝ => dslope q 0 ((t : ℂ) + (a : ℂ) * Complex.I)) volume (-a) a := by
    apply hpath _ (by fun_prop)
    intro t ht
    change ((t : ℂ) + (a : ℂ) * Complex.I).re ∈ Icc (-a) a ∧
      ((t : ℂ) + (a : ℂ) * Complex.I).im ∈ Icc (-a) a
    simpa using And.intro ht (show a ∈ Icc (-a) a from ⟨hle, le_rfl⟩)
  have hd3 : IntervalIntegrable (fun t : ℝ => dslope q 0 ((a : ℂ) + (t : ℂ) * Complex.I)) volume (-a) a := by
    apply hpath _ (by fun_prop)
    intro t ht
    change ((a : ℂ) + (t : ℂ) * Complex.I).re ∈ Icc (-a) a ∧
      ((a : ℂ) + (t : ℂ) * Complex.I).im ∈ Icc (-a) a
    simpa using And.intro (show a ∈ Icc (-a) a from ⟨hle, le_rfl⟩) ht
  have hd4 : IntervalIntegrable (fun t : ℝ => dslope q 0 (-(a : ℂ) + (t : ℂ) * Complex.I)) volume (-a) a := by
    apply hpath _ (by fun_prop)
    intro t ht
    change (-(a : ℂ) + (t : ℂ) * Complex.I).re ∈ Icc (-a) a ∧
      (-(a : ℂ) + (t : ℂ) * Complex.I).im ∈ Icc (-a) a
    simpa using And.intro (show -a ∈ Icc (-a) a from ⟨le_rfl, hle⟩) ht
  have hquot (z : ℂ) (hz : z ≠ 0) : q z / z = dslope q 0 z + q 0 * z⁻¹ := by
    rw [dslope_of_ne q hz, slope_def_field, sub_zero]
    ring
  have he1 : (∫ t : ℝ in -a..a, q ((t : ℂ) - (a : ℂ) * Complex.I) / ((t : ℂ) - (a : ℂ) * Complex.I)) =
      (∫ t : ℝ in -a..a, dslope q 0 ((t : ℂ) - (a : ℂ) * Complex.I)) + q 0 * (∫ t : ℝ in -a..a, ((t : ℂ) - (a : ℂ) * Complex.I)⁻¹) := by
    calc
      _ = ∫ t : ℝ in -a..a, dslope q 0 ((t : ℂ) - (a : ℂ) * Complex.I) + q 0 * ((t : ℂ) - (a : ℂ) * Complex.I)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact hquot _ (hn1 t)
      _ = _ := by rw [intervalIntegral.integral_add hd1 (hk1.const_mul _), intervalIntegral.integral_const_mul]
  have he2 : (∫ t : ℝ in -a..a, q ((t : ℂ) + (a : ℂ) * Complex.I) / ((t : ℂ) + (a : ℂ) * Complex.I)) =
      (∫ t : ℝ in -a..a, dslope q 0 ((t : ℂ) + (a : ℂ) * Complex.I)) + q 0 * (∫ t : ℝ in -a..a, ((t : ℂ) + (a : ℂ) * Complex.I)⁻¹) := by
    calc
      _ = ∫ t : ℝ in -a..a, dslope q 0 ((t : ℂ) + (a : ℂ) * Complex.I) + q 0 * ((t : ℂ) + (a : ℂ) * Complex.I)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact hquot _ (hn2 t)
      _ = _ := by rw [intervalIntegral.integral_add hd2 (hk2.const_mul _), intervalIntegral.integral_const_mul]
  have he3 : (∫ t : ℝ in -a..a, q ((a : ℂ) + (t : ℂ) * Complex.I) / ((a : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ t : ℝ in -a..a, dslope q 0 ((a : ℂ) + (t : ℂ) * Complex.I)) + q 0 * (∫ t : ℝ in -a..a, ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹) := by
    calc
      _ = ∫ t : ℝ in -a..a, dslope q 0 ((a : ℂ) + (t : ℂ) * Complex.I) + q 0 * ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact hquot _ (hn3 t)
      _ = _ := by rw [intervalIntegral.integral_add hd3 (hk3.const_mul _), intervalIntegral.integral_const_mul]
  have he4 : (∫ t : ℝ in -a..a, q (-(a : ℂ) + (t : ℂ) * Complex.I) / (-(a : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ t : ℝ in -a..a, dslope q 0 (-(a : ℂ) + (t : ℂ) * Complex.I)) + q 0 * (∫ t : ℝ in -a..a, (-(a : ℂ) + (t : ℂ) * Complex.I)⁻¹) := by
    calc
      _ = ∫ t : ℝ in -a..a, dslope q 0 (-(a : ℂ) + (t : ℂ) * Complex.I) + q 0 * (-(a : ℂ) + (t : ℂ) * Complex.I)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact hquot _ (hn4 t)
      _ = _ := by rw [intervalIntegral.integral_add hd4 (hk4.const_mul _), intervalIntegral.integral_const_mul]
  rw [he1, he2, he3, he4]
  have hkernel := CothSums.ComplexAnalysis.square_cauchy_kernel_boundary a ha
  linear_combination hz + q 0 * hkernel


theorem CothSums.ComplexAnalysis.square_antiperiodic_exponential_integral
    (U q : ℂ → ℂ) (k : ℂ)
    (hU1 : ∀ z : ℂ, U (z + 1) = -U z)
    (hUI : ∀ z : ℂ, U (z + Complex.I) = -U z)
    (hk : Complex.exp k = -1)
    (hq : DifferentiableOn ℂ q (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ℂ
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2)))
    (hqu : ∀ z : ℂ, z ≠ 0 → q z = z * U z) :
    (1 + Complex.exp (k * Complex.I)) *
      (∫ t : ℝ in -(1 / 2 : ℝ)..(1 / 2 : ℝ),
        U ((t : ℂ) - (1 / 2 : ℂ) * Complex.I) *
          Complex.exp (k * ((t : ℂ) - (1 / 2 : ℂ) * Complex.I))) =
      2 * (Real.pi : ℂ) * Complex.I * q 0 := by
  have hQ : DifferentiableOn ℂ (fun z => q z * Complex.exp (k * z))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ℂ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    hq.mul (by fun_prop)
  have hc := CothSums.ComplexAnalysis.square_cauchy_formula
    (fun z => q z * Complex.exp (k * z)) (1 / 2) (by norm_num) hQ
  have hv (z : ℂ) (hz : z ≠ 0) : q z * Complex.exp (k * z) / z =
      U z * Complex.exp (k * z) := by
    rw [hqu z hz]
    field_simp
  have hb (t : ℝ) :
      q ((t : ℂ) - (1 / 2 : ℂ) * Complex.I) *
          Complex.exp (k * ((t : ℂ) - (1 / 2 : ℂ) * Complex.I)) /
          ((t : ℂ) - (1 / 2 : ℂ) * Complex.I) =
        U ((t : ℂ) - (1 / 2 : ℂ) * Complex.I) *
          Complex.exp (k * ((t : ℂ) - (1 / 2 : ℂ) * Complex.I)) := by
    apply hv
    intro hz
    have := congrArg Complex.im hz
    norm_num at this
  have ht (t : ℝ) :
      q ((t : ℂ) + (1 / 2 : ℂ) * Complex.I) *
          Complex.exp (k * ((t : ℂ) + (1 / 2 : ℂ) * Complex.I)) /
          ((t : ℂ) + (1 / 2 : ℂ) * Complex.I) =
        -(Complex.exp (k * Complex.I)) *
          (U ((t : ℂ) - (1 / 2 : ℂ) * Complex.I) *
            Complex.exp (k * ((t : ℂ) - (1 / 2 : ℂ) * Complex.I))) := by
    rw [hv _ (by intro hz; have := congrArg Complex.im hz; norm_num at this)]
    rw [show (t : ℂ) + (1 / 2 : ℂ) * Complex.I =
      ((t : ℂ) - (1 / 2 : ℂ) * Complex.I) + Complex.I by ring, hUI,
      mul_add, Complex.exp_add]
    ring
  have hr (t : ℝ) :
      q ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp (k * ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) /
          ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
        q (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp (k * (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)) /
          (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
    rw [hv _ (by intro hz; have := congrArg Complex.re hz; norm_num at this),
      hv _ (by intro hz; have := congrArg Complex.re hz; norm_num at this)]
    rw [show (1 / 2 : ℂ) + (t : ℂ) * Complex.I =
      (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I) + 1 by ring,
      hU1, mul_add, Complex.exp_add, mul_one, hk]
    ring
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hc
  simp_rw [hb, ht, hr] at hc
  rw [intervalIntegral.integral_const_mul] at hc
  try simp only [mul_zero, Complex.exp_zero, mul_one] at hc
  linear_combination hc


open MeasureTheory Set Filter


set_option autoImplicit false


theorem CothSums.ComplexAnalysis.square_exponential_difference_shift
    (U q : ℂ → ℂ) (k : ℂ)
    (hU1 : ∀ z : ℂ, U (z + 1) = -U z)
    (hk : Complex.exp k = -1)
    (hq : DifferentiableOn ℂ q (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ℂ
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2)))
    (hqu : ∀ z : ℂ, z ≠ 0 → q z = z * U z) :
    IntervalIntegrable (fun x : ℝ => U (x : ℂ) *
      (Complex.exp (k * (x : ℂ)) - Complex.exp (-k * (x : ℂ)))) volume
      (-(1 / 2 : ℝ)) (1 / 2) ∧
    (∫ x : ℝ in -(1 / 2 : ℝ)..(1 / 2 : ℝ), U (x : ℂ) *
      (Complex.exp (k * (x : ℂ)) - Complex.exp (-k * (x : ℂ)))) =
      ∫ x : ℝ in -(1 / 2 : ℝ)..(1 / 2 : ℝ),
        U ((x : ℂ) - (1 / 2 : ℂ) * Complex.I) *
          (Complex.exp (k * ((x : ℂ) - (1 / 2 : ℂ) * Complex.I)) -
            Complex.exp (-k * ((x : ℂ) - (1 / 2 : ℂ) * Complex.I))) := by
  let S : Set ℂ := Icc (-(1 / 2 : ℝ)) (1 / 2) ×ℂ Icc (-(1 / 2 : ℝ)) (1 / 2)
  let E : ℂ → ℂ := fun z => Complex.exp (k * z) - Complex.exp (-k * z)
  let G : ℂ → ℂ := fun z => U z * E z
  let H : ℂ → ℂ := fun z => q z * dslope E 0 z
  have hE0 : E 0 = 0 := by simp [E]
  have hEd : DifferentiableOn ℂ E univ := by dsimp only [E]; fun_prop
  have hds : DifferentiableOn ℂ (dslope E 0) univ :=
    (Complex.differentiableOn_dslope (by simp : (univ : Set ℂ) ∈ nhds (0 : ℂ))).mpr hEd
  have hH : DifferentiableOn ℂ H S := hq.mul (hds.mono (subset_univ _))
  have hv (z : ℂ) (hz : z ≠ 0) : H z = G z := by
    dsimp only [H, G]
    rw [hqu z hz, dslope_of_ne E hz, slope_def_field, hE0, sub_zero, sub_zero]
    field_simp
  have hkn : Complex.exp (-k) = -1 := by rw [Complex.exp_neg, hk]; norm_num
  have hper (z : ℂ) : G (z + 1) = G z := by
    dsimp only [G, E]
    rw [hU1, mul_add, mul_add, Complex.exp_add, Complex.exp_add, mul_one, mul_one, hk, hkn]
    ring
  have hhlower : DifferentiableOn ℂ H
      (Icc (-(1 / 2 : ℝ)) (1 / 2) ×ℂ Icc (-(1 / 2 : ℝ)) 0) := by
    apply hH.mono
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1, le_trans hz.2.2 (by norm_num)⟩⟩
  have hz := Complex.integral_boundary_rect_eq_zero_of_differentiableOn H
    (-(1 / 2 : ℂ) - (1 / 2 : ℂ) * Complex.I) ((1 / 2 : ℂ) + 0 * Complex.I)
    (by simpa [uIcc_of_le (show -(1 / 2 : ℝ) ≤ (1 / 2) by norm_num)] using hhlower)
  have hvert (t : ℝ) : H ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
      H (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
    rw [hv _ (by intro he; have hh := congrArg Complex.re he; norm_num at hh),
      hv _ (by intro he; have hh := congrArg Complex.re he; norm_num at hh)]
    rw [show (1 / 2 : ℂ) + (t : ℂ) * Complex.I =
      (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I) + 1 by ring, hper]
  have heq : (∫ x : ℝ in -(1 / 2 : ℝ)..(1 / 2 : ℝ), H (x : ℂ)) =
      ∫ x : ℝ in -(1 / 2 : ℝ)..(1 / 2 : ℝ), H ((x : ℂ) - (1 / 2 : ℂ) * Complex.I) := by
    norm_num at hz
    simp_rw [hvert] at hz
    simpa [smul_eq_mul, sub_eq_zero] using (sub_eq_zero.mp (by linear_combination hz :
      (∫ x : ℝ in -(1 / 2 : ℝ)..(1 / 2 : ℝ), H ((x : ℂ) - (1 / 2 : ℂ) * Complex.I)) -
        (∫ x : ℝ in -(1 / 2 : ℝ)..(1 / 2 : ℝ), H (x : ℂ)) = 0)).symm
  have hAE : (fun x : ℝ => H (x : ℂ)) =ᵐ[volume] (fun x : ℝ => G (x : ℂ)) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    exact hv _ (Complex.ofReal_ne_zero.mpr hx)
  have hIntH : IntervalIntegrable (fun x : ℝ => H (x : ℂ)) volume (-(1 / 2 : ℝ)) (1 / 2) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    refine hH.continuousOn.comp (by fun_prop) ?_
    intro x hx
    change x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ∧ 0 ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
    exact ⟨hx, by constructor <;> norm_num⟩
  refine ⟨hIntH.congr_ae (ae_restrict_of_ae hAE), ?_⟩
  change (∫ x : ℝ in -(1 / 2 : ℝ)..(1 / 2 : ℝ), G (x : ℂ)) = _
  rw [← intervalIntegral.integral_congr_ae (Filter.Eventually.mono hAE (fun x hx _ => hx)), heq]
  apply intervalIntegral.integral_congr
  intro x hx
  exact hv _ (by intro he; have hh := congrArg Complex.im he; norm_num at hh)


theorem CothSums.ComplexAnalysis.square_antiperiodic_sine_integral
    (U q : ℂ → ℂ)
    (hU1 : ∀ z : ℂ, U (z + 1) = -U z)
    (hUI : ∀ z : ℂ, U (z + Complex.I) = -U z)
    (hq : DifferentiableOn ℂ q (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ℂ
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2)))
    (hqu : ∀ z : ℂ, z ≠ 0 → q z = z * U z)
    (hq0 : q 0 = 1) (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    IntervalIntegrable (fun x : ℝ => U (x : ℂ) *
      Complex.sin ((n : ℂ) * (Real.pi : ℂ) * (x : ℂ))) volume 0 1 ∧
    (∫ x : ℝ in (0 : ℝ)..1, U (x : ℂ) *
      Complex.sin ((n : ℂ) * (Real.pi : ℂ) * (x : ℂ))) =
        (Real.pi * Real.tanh (Real.pi * (n : ℝ) / 2) : ℝ) := by
  let k : ℂ := (n : ℂ) * (Real.pi : ℂ) * Complex.I
  let N : ℝ := Real.pi * (n : ℝ)
  let p : ℝ → ℂ := fun t => (t : ℂ) - (1 / 2 : ℂ) * Complex.I
  let F : ℝ → ℂ := fun x => U (x : ℂ) * Complex.sin ((n : ℂ) * (Real.pi : ℂ) * (x : ℂ))
  have hk : Complex.exp k = -1 := by
    rw [show k = (n : ℂ) * ((Real.pi : ℂ) * Complex.I) by dsimp [k]; ring,
      Complex.exp_nat_mul, Complex.exp_pi_mul_I, hodd.neg_one_pow]
  have hkn : Complex.exp (-k) = -1 := by rw [Complex.exp_neg, hk]; norm_num
  have hkI : k * Complex.I = (-N : ℝ) := by
    dsimp only [k, N]
    push_cast
    calc
      (n : ℂ) * (Real.pi : ℂ) * Complex.I * Complex.I =
          (n : ℂ) * (Real.pi : ℂ) * (Complex.I * Complex.I) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  have hknI : -k * Complex.I = (N : ℂ) := by rw [neg_mul, hkI]; simp
  have hphase (z : ℂ) : Complex.exp (k * z) - Complex.exp (-k * z) =
      (2 * Complex.I) * Complex.sin ((n : ℂ) * (Real.pi : ℂ) * z) := by
    rw [show k * z = ((n : ℂ) * (Real.pi : ℂ) * z) * Complex.I by dsimp [k]; ring,
      show -k * z = -((n : ℂ) * (Real.pi : ℂ) * z) * Complex.I by dsimp [k]; ring,
      Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  have h2I : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hS := CothSums.ComplexAnalysis.square_exponential_difference_shift U q k hU1 hk hq hqu
  have hFi : IntervalIntegrable F volume (-(1 / 2 : ℝ)) (1 / 2) := by
    have hh := hS.1.const_mul ((2 * Complex.I)⁻¹)
    apply hh.congr_ae
    filter_upwards [] with x
    change (2 * Complex.I)⁻¹ *
      (U (x : ℂ) * (Complex.exp (k * (x : ℂ)) - Complex.exp (-k * (x : ℂ)))) = F x
    rw [hphase]
    dsimp only [F]
    field_simp
  have hpnone (t : ℝ) : p t ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    norm_num [p] at hh
  have hbq (t : ℝ) : q (p t) / p t = U (p t) := by
    rw [hqu _ (hpnone t)]
    exact mul_div_cancel_left₀ _ (hpnone t)
  have hbi (v : ℂ) : IntervalIntegrable (fun t : ℝ => U (p t) * Complex.exp (v * p t)) volume
      (-(1 / 2 : ℝ)) (1 / 2) := by
    have hcq : ContinuousOn (fun t : ℝ => q (p t)) (Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
      apply hq.continuousOn.comp (by fun_prop)
      intro t ht
      change (p t).re ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ∧ (p t).im ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
      simpa [p] using And.intro ht (show -(1 / 2 : ℝ) ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) by norm_num)
    have hcp : Continuous p := by dsimp only [p]; fun_prop
    have hc : ContinuousOn (fun t : ℝ => q (p t) / p t * Complex.exp (v * p t))
        (Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
      (hcq.div hcp.continuousOn (fun t _ => hpnone t)).mul (by fun_prop)
    have hh : IntervalIntegrable (fun t : ℝ => q (p t) / p t * Complex.exp (v * p t)) volume
        (-(1 / 2 : ℝ)) (1 / 2) :=
      ContinuousOn.intervalIntegrable_of_Icc (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2) hc
    apply hh.congr_ae
    filter_upwards [] with t
    rw [hbq]
  have hplus := CothSums.ComplexAnalysis.square_antiperiodic_exponential_integral U q k hU1 hUI hk hq hqu
  have hminus := CothSums.ComplexAnalysis.square_antiperiodic_exponential_integral U q (-k) hU1 hUI hkn hq hqu
  rw [hq0, hkI, mul_one] at hplus
  rw [hq0, hknI, mul_one] at hminus
  have hdenp : (1 + Complex.exp ((-N : ℝ) : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  have hdenm : (1 + Complex.exp (N : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  have hpval : (∫ t : ℝ in -(1 / 2 : ℝ)..(1 / 2 : ℝ), U (p t) * Complex.exp (k * p t)) =
      2 * (Real.pi : ℂ) * Complex.I / (1 + Complex.exp ((-N : ℝ) : ℂ)) := by
    apply (eq_div_iff hdenp).2
    exact (mul_comm _ _).trans hplus
  have hmval : (∫ t : ℝ in -(1 / 2 : ℝ)..(1 / 2 : ℝ), U (p t) * Complex.exp (-k * p t)) =
      2 * (Real.pi : ℂ) * Complex.I / (1 + Complex.exp (N : ℂ)) := by
    apply (eq_div_iff hdenm).2
    exact (mul_comm _ _).trans hminus
  have hdiff : (1 + Real.exp (-N))⁻¹ - (1 + Real.exp N)⁻¹ = Real.tanh (N / 2) := by
    let a : ℝ := Real.exp (N / 2)
    have ha : 0 < a := Real.exp_pos _
    have hN : Real.exp N = a ^ 2 := by dsimp only [a]; rw [sq, ← Real.exp_add]; congr 1; ring
    have hNN : Real.exp (-N) = (a ^ 2)⁻¹ := by rw [Real.exp_neg, hN]
    have ht : Real.tanh (N / 2) = (a ^ 2 - 1) / (a ^ 2 + 1) := by
      rw [Real.tanh_eq, Real.exp_neg]
      change (a - a⁻¹) / (a + a⁻¹) = _
      field_simp <;> ring
    rw [hN, hNN, ht]
    field_simp <;> ring
  have hcenter : (∫ x : ℝ in -(1 / 2 : ℝ)..(1 / 2 : ℝ), F x) =
      ((Real.pi * Real.tanh (N / 2) : ℝ) : ℂ) := by
    have hs := hS.2
    simp_rw [hphase] at hs
    have hleft : (∫ x : ℝ in -(1 / 2 : ℝ)..(1 / 2 : ℝ), U (x : ℂ) *
        ((2 * Complex.I) * Complex.sin ((n : ℂ) * (Real.pi : ℂ) * (x : ℂ)))) =
        (2 * Complex.I) * ∫ x : ℝ in -(1 / 2 : ℝ)..(1 / 2 : ℝ), F x := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      change U (x : ℂ) * _ = (2 * Complex.I) * F x
      dsimp only [F]
      ring
    have hright : (∫ x : ℝ in -(1 / 2 : ℝ)..(1 / 2 : ℝ), U (p x) *
        (Complex.exp (k * p x) - Complex.exp (-k * p x))) =
          2 * (Real.pi : ℂ) * Complex.I * ((Real.tanh (N / 2) : ℝ) : ℂ) := by
      simp_rw [mul_sub]
      rw [intervalIntegral.integral_sub (hbi k) (hbi (-k)), hpval, hmval]
      have hc := congrArg Complex.ofReal hdiff
      push_cast at hc
      calc
        _ = 2 * (Real.pi : ℂ) * Complex.I *
            ((1 + Complex.exp ((-N : ℝ) : ℂ))⁻¹ - (1 + Complex.exp (N : ℂ))⁻¹) := by ring
        _ = _ := by
          rw [Complex.ofReal_neg, hc]
          have hcast : ((N / 2 : ℝ) : ℂ) = (N : ℂ) / 2 := by push_cast; rfl
          rw [← hcast, ← Complex.ofReal_tanh]
    have hright' : (∫ x : ℝ in -(1 / 2 : ℝ)..(1 / 2 : ℝ), U (p x) *
        ((2 * Complex.I) * Complex.sin ((n : ℂ) * (Real.pi : ℂ) * p x))) =
          2 * (Real.pi : ℂ) * Complex.I * ((Real.tanh (N / 2) : ℝ) : ℂ) := by
      simpa only [hphase] using hright
    rw [hleft] at hs
    have he : (2 * Complex.I) * (∫ x : ℝ in -(1 / 2 : ℝ)..(1 / 2 : ℝ), F x) =
        (2 * Complex.I) * ((Real.pi * Real.tanh (N / 2) : ℝ) : ℂ) := by
      rw [hs, hright']
      push_cast
      ring
    exact mul_left_cancel₀ h2I he
  have hper : Function.Periodic F 1 := by
    intro x
    change U ((x + 1 : ℝ) : ℂ) * Complex.sin ((n : ℂ) * (Real.pi : ℂ) * ((x + 1 : ℝ) : ℂ)) = F x
    rw [Complex.ofReal_add, Complex.ofReal_one, hU1]
    have hcosn : Complex.cos ((n : ℂ) * (Real.pi : ℂ)) = -1 := by
      have hh := congrArg Complex.ofReal (Real.cos_nat_mul_pi n)
      have hr : ((-1 : ℝ) ^ n) = -1 := hodd.neg_one_pow
      rw [hr] at hh
      simpa only [Complex.ofReal_cos, Complex.ofReal_mul, Complex.ofReal_natCast,
        Complex.ofReal_neg, Complex.ofReal_one] using hh
    have hsin : Complex.sin ((n : ℂ) * (Real.pi : ℂ) * ((x : ℂ) + 1)) =
        -Complex.sin ((n : ℂ) * (Real.pi : ℂ) * (x : ℂ)) := by
      rw [mul_add, mul_one, Complex.sin_add, Complex.sin_nat_mul_pi,
        hcosn]
      ring
    rw [hsin]
    dsimp only [F]
    ring
  have hall := hper.intervalIntegrable (t := -(1 / 2 : ℝ)) (by norm_num : (1 : ℝ) ≠ 0)
    (by simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] using hFi) 0 1
  refine ⟨hall, ?_⟩
  have he := hper.intervalIntegral_add_eq (0 : ℝ) (-(1 / 2 : ℝ))
  norm_num only [zero_add, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at he
  change (∫ x : ℝ in (0 : ℝ)..1, F x) = _
  rw [he, hcenter]


set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


theorem CothSums.Analysis.sine_endpoint_linear_bounds
    (a x : ℝ) (ha : 0 ≤ a) (hs : Real.sin a = 0) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |Real.sin (a * x)| ≤ a * x ∧ |Real.sin (a * x)| ≤ a * (1 - x) := by
  have hx1 := hx.2
  constructor
  · exact Real.abs_sin_le_abs.trans_eq (abs_of_nonneg (mul_nonneg ha hx.1))
  · have h := Real.abs_sin_sub_sin_le (a * x) a
    rw [hs, sub_zero, abs_of_nonpos (by nlinarith : a * x - a ≤ 0)] at h
    nlinarith


set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


open MeasureTheory


open MeasureTheory Set


set_option autoImplicit false


theorem CothSums.density_integrable :
    IntegrableOn (fun t : ℝ => (Real.sqrt (1 + t ^ 4))⁻¹) (Set.Ioi 0) := by
  have hc : Continuous (fun t : ℝ => (Real.sqrt (1 + t ^ 4))⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro t
      exact (Real.sqrt_pos.2 (by positivity : 0 < 1 + t ^ 4)).ne'
  have htail : IntegrableOn (fun t : ℝ => (Real.sqrt (1 + t ^ 4))⁻¹) (Ioi 1) := by
    apply (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := 1)
      (by norm_num) (by norm_num)).mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans (by norm_num) ht
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.2 (by positivity)))]
    have hs : t ^ 2 ≤ Real.sqrt (1 + t ^ 4) := by
      have hz : Real.sqrt (t ^ 4) ≤ Real.sqrt (1 + t ^ 4) := Real.sqrt_le_sqrt (by linarith)
      have hid : Real.sqrt (t ^ 4) = t ^ 2 := by
        rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg t)]
      rwa [hid] at hz
    calc
      (Real.sqrt (1 + t ^ 4))⁻¹ ≤ (t ^ 2)⁻¹ := (inv_le_inv₀ (by positivity) (sq_pos_of_pos ht0)).2 hs
      _ = t ^ (-2 : ℝ) := by rw [Real.rpow_neg ht0.le, Real.rpow_two]
  have hhead : IntegrableOn (fun t : ℝ => (Real.sqrt (1 + t ^ 4))⁻¹) (Ioc 0 1) :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  simpa only [Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)] using hhead.union htail


set_option autoImplicit false


open MeasureTheory


theorem CothSums.chi_sine_div_integrable (a : ℝ) (ha : 0 ≤ a) (hs : Real.sin a = 0) :
    IntegrableOn (fun r : ℝ => Real.sin (a * CothSums.chi r) / r) (Set.Ioi 0) ∧
    ∀ r : ℝ, 0 < r → |Real.sin (a * CothSums.chi r) / r| ≤
      2 * a * (4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2) *
        (Real.sqrt (1 + r ^ 4))⁻¹ := by
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  have hC : 0 < C := CothSums.chi_prefactor_pos
  have hb (r : ℝ) (hr : 0 < r) : |Real.sin (a * CothSums.chi r) / r| ≤
      2 * a * C * (Real.sqrt (1 + r ^ 4))⁻¹ := by
    obtain ⟨hc0, hc1, _, htail⟩ := CothSums.chi_range_and_tail r hr
    obtain ⟨hs0, hs1⟩ := CothSums.Analysis.sine_endpoint_linear_bounds a (CothSums.chi r) ha hs ⟨hc0, hc1⟩
    have hsr : 0 < Real.sqrt (1 + r ^ 4) := Real.sqrt_pos.mpr (by positivity)
    have hAC : 0 ≤ a * C := mul_nonneg ha hC.le
    rw [abs_div, abs_of_pos hr]
    by_cases hr1 : r ≤ 1
    · have hr4 : r ^ 4 ≤ 1 := pow_le_one₀ hr.le hr1
      have hsqrt : Real.sqrt (1 + r ^ 4) ≤ 2 := by
        apply (Real.sqrt_le_iff).mpr
        constructor <;> nlinarith
      have hhead : |Real.sin (a * CothSums.chi r)| ≤ a * (C * r) :=
        hs0.trans (mul_le_mul_of_nonneg_left (CothSums.chi_le_prefactor_mul hr.le) ha)
      calc
        |Real.sin (a * CothSums.chi r)| / r ≤ a * C := by
          apply (div_le_iff₀ hr).mpr
          nlinarith [hhead]
        _ ≤ 2 * a * C * (Real.sqrt (1 + r ^ 4))⁻¹ := by
          rw [← div_eq_mul_inv]
          apply (le_div_iff₀ hsr).mpr
          nlinarith [mul_le_mul_of_nonneg_left hsqrt hAC]
    · have hr1 : 1 ≤ r := le_of_lt (lt_of_not_ge hr1)
      have hr4 : 1 ≤ r ^ 4 := one_le_pow₀ hr1
      have hsqrt : Real.sqrt (1 + r ^ 4) ≤ 2 * r ^ 2 := by
        apply (Real.sqrt_le_iff).mpr
        constructor
        · positivity
        · nlinarith
      have hsmall : |Real.sin (a * CothSums.chi r)| ≤ a * (C / r) :=
        hs1.trans (mul_le_mul_of_nonneg_left htail ha)
      calc
        |Real.sin (a * CothSums.chi r)| / r ≤ (a * C / r) / r :=
          div_le_div_of_nonneg_right (by simpa only [mul_div_assoc] using hsmall) hr.le
        _ = a * C / r ^ 2 := by ring
        _ ≤ 2 * a * C * (Real.sqrt (1 + r ^ 4))⁻¹ := by
          rw [← div_eq_mul_inv]
          apply (div_le_div_iff₀ (sq_pos_of_pos hr) hsr).mpr
          nlinarith [mul_le_mul_of_nonneg_left hsqrt hAC]
  refine ⟨?_, hb⟩
  have hchi : Continuous CothSums.chi :=
    continuous_iff_continuousAt.mpr fun r => (CothSums.chi_hasDerivAt r).continuousAt
  have hm : Measurable (fun r : ℝ => Real.sin (a * CothSums.chi r) / r) := by
    fun_prop
  apply (CothSums.density_integrable.const_mul (2 * a * C)).mono'
    hm.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  simpa only [Real.norm_eq_abs] using hb r hr


set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


open MeasureTheory


theorem CothSums.chi_sine_log_boundary (a : ℝ) (ha : 0 ≤ a) (hs : Real.sin a = 0) :
    Filter.Tendsto (fun r : ℝ => Real.sin (a * CothSums.chi r) * Real.log r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun r : ℝ => Real.sin (a * CothSums.chi r) * Real.log r)
      Filter.atTop (nhds 0) := by
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  constructor
  · refine squeeze_zero_norm' (a := fun r : ℝ => (a * C) * |Real.log r * r|) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hh := CothSums.chi_range_and_tail r hr
      have he := (CothSums.Analysis.sine_endpoint_linear_bounds a (CothSums.chi r) ha hs ⟨hh.1, hh.2.1⟩).1
      have hb : |Real.sin (a * CothSums.chi r)| ≤ a * C * r := by
        have hn := mul_le_mul_of_nonneg_left (CothSums.chi_le_prefactor_mul hr.le) ha
        exact he.trans (by dsimp only [C]; nlinarith [hn])
      rw [Real.norm_eq_abs, abs_mul]
      have hm := mul_le_mul_of_nonneg_right hb (abs_nonneg (Real.log r))
      simpa only [abs_mul, abs_of_pos (show 0 < r from hr), mul_assoc, mul_comm, mul_left_comm] using hm
    · have h := (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1)).norm.const_mul (a * C)
      simpa only [Real.rpow_one, Real.norm_eq_abs, norm_zero, mul_zero] using h
  · refine squeeze_zero_norm' (a := fun r : ℝ => (a * C) * |Real.log r / r|) ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
      have hh := CothSums.chi_range_and_tail r hr
      have he := (CothSums.Analysis.sine_endpoint_linear_bounds a (CothSums.chi r) ha hs ⟨hh.1, hh.2.1⟩).2
      have hb : |Real.sin (a * CothSums.chi r)| ≤ a * C / r := by
        have hn := mul_le_mul_of_nonneg_left hh.2.2.2 ha
        exact he.trans (by simpa only [C, mul_div_assoc] using hn)
      rw [Real.norm_eq_abs, abs_mul]
      have hm := mul_le_mul_of_nonneg_right hb (abs_nonneg (Real.log r))
      calc
        |Real.sin (a * CothSums.chi r)| * |Real.log r| ≤ (a * C / r) * |Real.log r| := hm
        _ = (a * C) * |Real.log r / r| := by rw [abs_div, abs_of_pos hr]; ring
    · simpa only [Real.norm_eq_abs, id_eq, norm_zero, mul_zero] using
        Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.norm.const_mul (a * C)


set_option autoImplicit false


open MeasureTheory Set


open Asymptotics


open Filter


private theorem chi_strict : StrictMono CothSums.chi := by
  apply strictMono_of_hasDerivAt_pos CothSums.chi_hasDerivAt
  intro r
  exact mul_pos CothSums.chi_prefactor_pos
    (inv_pos.mpr (Real.sqrt_pos.2 (by positivity)))


private theorem chi_limit : Filter.Tendsto CothSums.chi Filter.atTop (nhds (1 : ℝ)) := by
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  have hdom : ∀ᶠ r : ℝ in Filter.atTop, |1 - CothSums.chi r| ≤ C * r⁻¹ := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
    have hh := CothSums.chi_range_and_tail r hr
    rw [abs_of_nonneg (sub_nonneg.mpr hh.2.1)]
    simpa only [C, div_eq_mul_inv] using hh.2.2.2
  have hz : Filter.Tendsto (fun r : ℝ => 1 - CothSums.chi r) Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm'
    · simpa only [Real.norm_eq_abs] using hdom
    · simpa only [mul_zero] using tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero : Filter.Tendsto (fun r : ℝ => r⁻¹) Filter.atTop (nhds 0))
  simpa only [sub_sub_cancel, sub_zero] using
    (tendsto_const_nhds.sub hz : Filter.Tendsto
      (fun r : ℝ => 1 - (1 - CothSums.chi r)) Filter.atTop (nhds (1 - 0)))


theorem CothSums.density_log_integrable :
    IntegrableOn (fun r : ℝ => (Real.sqrt (1 + r ^ 4))⁻¹ * Real.log r) (Set.Ioi 0) := by
  have hd : Continuous (fun r : ℝ => (Real.sqrt (1 + r ^ 4))⁻¹) := CothSums.density_continuous
  have hh : IntervalIntegrable (fun r : ℝ => (Real.sqrt (1 + r ^ 4))⁻¹ * Real.log r) volume 0 1 := by
    simpa only [mul_comm] using (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)).mul_continuousOn hd.continuousOn
  have hhead : IntegrableOn (fun r : ℝ => (Real.sqrt (1 + r ^ 4))⁻¹ * Real.log r) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hh
  have htail : IntegrableOn (fun r : ℝ => (Real.sqrt (1 + r ^ 4))⁻¹ * Real.log r) (Ioi 1) := by
    have hb := (integrableOn_Ioi_rpow_of_lt (a := (-3 / 2 : ℝ)) (c := 1)
      (by norm_num) (by norm_num)).const_mul (2 : ℝ)
    have hm : AEStronglyMeasurable (fun r : ℝ => (Real.sqrt (1 + r ^ 4))⁻¹ * Real.log r)
        (volume.restrict (Ioi 1)) := by
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      exact hd.continuousOn.mul (Real.continuousOn_log.mono
        (fun r hr => ne_of_gt (show 0 < r by have hr1 : 1 < r := hr; linarith)))
    refine hb.mono' hm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := lt_trans (by norm_num) hr
    have hdpos : 0 < (Real.sqrt (1 + r ^ 4))⁻¹ := by positivity
    have hlog : 0 ≤ Real.log r := Real.log_nonneg hr.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hdpos.le hlog)]
    have hs : r ^ 2 ≤ Real.sqrt (1 + r ^ 4) := by
      have hz := Real.sqrt_le_sqrt (show r ^ 4 ≤ 1 + r ^ 4 by linarith)
      have he : Real.sqrt (r ^ 4) = r ^ 2 := by rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg r)]
      rwa [he] at hz
    have hden : (Real.sqrt (1 + r ^ 4))⁻¹ ≤ r ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hr0.le, Real.rpow_two]
      exact (inv_le_inv₀ (by positivity) (sq_pos_of_pos hr0)).2 hs
    have hl : Real.log r ≤ 2 * r ^ (1 / 2 : ℝ) := by
      have h := Real.log_le_rpow_div hr0.le (by norm_num : (0 : ℝ) < 1 / 2)
      linarith
    calc
      (Real.sqrt (1 + r ^ 4))⁻¹ * Real.log r ≤ r ^ (-2 : ℝ) * (2 * r ^ (1 / 2 : ℝ)) :=
        mul_le_mul hden hl hlog (Real.rpow_nonneg hr0.le _)
      _ = 2 * r ^ (-3 / 2 : ℝ) := by
        rw [mul_left_comm, ← Real.rpow_add hr0]
        norm_num
  simpa only [Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)] using hhead.union htail


set_option autoImplicit false


open MeasureTheory Set


open Asymptotics


open Filter


theorem CothSums.chi_positive_coordinate_bijective : Set.BijOn CothSums.chi (Ioi (0 : ℝ)) (Ioo (0 : ℝ) 1) := by
  have hz : CothSums.chi 0 = 0 := by simp [CothSums.chi]
  have hcont : Continuous CothSums.chi :=
    continuous_iff_continuousAt.mpr (fun r => (CothSums.chi_hasDerivAt r).continuousAt)
  refine ⟨?_, chi_strict.injective.injOn, ?_⟩
  · intro r hr
    constructor
    · simpa only [hz] using (chi_strict hr)
    · have hlt : CothSums.chi r < CothSums.chi (r + 1) := chi_strict (by linarith)
      exact hlt.trans_le (CothSums.chi_range_and_tail (r + 1) (by have hr0 : 0 < r := hr; linarith)).2.1
  · intro x hx
    have he : ∀ᶠ r : ℝ in Filter.atTop, x < CothSums.chi r :=
      chi_limit.eventually (lt_mem_nhds hx.2)
    obtain ⟨R, hxR, hR⟩ := (he.and (Filter.eventually_gt_atTop (0 : ℝ))).exists
    have hxi : x ∈ Ioo (CothSums.chi 0) (CothSums.chi R) := by
      simpa only [hz, Set.mem_Ioo] using And.intro hx.1 hxR
    obtain ⟨r, hr, heq⟩ := intermediate_value_Ioo hR.le hcont.continuousOn hxi
    exact ⟨r, hr.1, heq⟩


set_option autoImplicit false


open MeasureTheory Set


open Asymptotics


theorem CothSums.chi_strictMono : StrictMono CothSums.chi := by
  apply strictMono_of_hasDerivAt_pos CothSums.chi_hasDerivAt
  intro r
  exact mul_pos CothSums.chi_prefactor_pos
    (inv_pos.mpr (Real.sqrt_pos.2 (by positivity)))


theorem CothSums.inverse_log_cosine_ibp (a : ℝ) (ha : 0 ≤ a) (hs : Real.sin a = 0) :
    IntegrableOn (fun x : ℝ => Real.log (Function.invFun CothSums.chi x) *
      Real.cos (a * x)) (Set.Ioo 0 1) ∧
    a * (∫ x in Set.Ioo (0 : ℝ) 1,
      Real.log (Function.invFun CothSums.chi x) * Real.cos (a * x)) =
      -(∫ r in Set.Ioi (0 : ℝ), Real.sin (a * CothSums.chi r) / r) := by
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  let D : ℝ → ℝ := fun r => C * (Real.sqrt (1 + r ^ 4))⁻¹
  let F : ℝ → ℝ := fun r => Real.sin (a * CothSums.chi r)
  let F' : ℝ → ℝ := fun r => a * Real.cos (a * CothSums.chi r) * D r
  let R : ℝ → ℝ := fun r => D r * Real.log r * Real.cos (a * CothSums.chi r)
  let G : ℝ → ℝ := fun x => Real.log (Function.invFun CothSums.chi x) * Real.cos (a * x)
  have hC : 0 < C := CothSums.chi_prefactor_pos
  have hc : Continuous CothSums.chi :=
    continuous_iff_continuousAt.mpr fun r => (CothSums.chi_hasDerivAt r).continuousAt
  have hR : IntegrableOn R (Set.Ioi 0) := by
    have hi := CothSums.density_log_integrable.norm.const_mul C
    have hm : AEStronglyMeasurable R (volume.restrict (Set.Ioi 0)) := by
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      exact ((continuous_const.mul CothSums.density_continuous).continuousOn.mul
        (Real.continuousOn_log.mono (fun r hr => ne_of_gt hr))).mul
        ((Real.continuous_cos.comp (continuous_const.mul hc)).continuousOn)
    apply hi.mono' hm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hb := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (a * CothSums.chi r))
      (show 0 ≤ C * |(Real.sqrt (1 + r ^ 4))⁻¹ * Real.log r| by positivity)
    simpa only [R, D, Real.norm_eq_abs, abs_mul, abs_of_pos hC, mul_one, mul_assoc] using hb
  have hFR : IntegrableOn (F' * Real.log) (Set.Ioi 0) := by
    exact (hR.const_mul a).congr (Filter.Eventually.of_forall fun r => by
      change a * R r = F' r * Real.log r
      dsimp [F', R]
      ring)
  have hFG : IntegrableOn (F * (fun r : ℝ => r⁻¹)) (Set.Ioi 0) := by
    convert (CothSums.chi_sine_div_integrable a ha hs).1 using 1 <;> rfl
  have hboundary := CothSums.chi_sine_log_boundary a ha hs
  have hIBP := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := F) (u' := F') (v := Real.log) (v' := fun r : ℝ => r⁻¹)
    (fun r hr => by
      apply ((Real.hasDerivAt_sin (a * CothSums.chi r)).comp r
        ((CothSums.chi_hasDerivAt r).const_mul a)).congr_deriv
      dsimp [F', D]
      ring)
    (fun r hr => Real.hasDerivAt_log (ne_of_gt hr))
    hFG hFR hboundary.1 hboundary.2
  have hbij := CothSums.chi_positive_coordinate_bijective
  have himage : CothSums.chi '' Set.Ioi (0 : ℝ) = Set.Ioo 0 1 := hbij.image_eq
  have hderiv : ∀ r ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt CothSums.chi (D r) (Set.Ioi 0) r :=
    fun r _ => (CothSums.chi_hasDerivAt r).hasDerivWithinAt
  have hpoint : ∀ r ∈ Set.Ioi (0 : ℝ), |D r| • G (CothSums.chi r) = R r := by
    intro r hr
    have hd : 0 < D r := mul_pos hC (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)))
    rw [abs_of_pos hd, smul_eq_mul]
    dsimp only [G, R]
    rw [Function.leftInverse_invFun CothSums.chi_strictMono.injective r]
    ring
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hbij.injOn G
  rw [himage] at hchange
  have hG : IntegrableOn G (Set.Ioo 0 1) := by
    rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hbij.injOn]
    exact (integrableOn_congr_fun hpoint measurableSet_Ioi).mpr hR
  refine ⟨hG, ?_⟩
  change a * (∫ x in Set.Ioo (0 : ℝ) 1, G x) = _
  rw [hchange]
  have hchange' : (∫ r in Set.Ioi (0 : ℝ), |D r| • G (CothSums.chi r)) =
      ∫ r in Set.Ioi (0 : ℝ), R r :=
    setIntegral_congr_fun measurableSet_Ioi hpoint
  rw [hchange']
  have hrep : (∫ r in Set.Ioi (0 : ℝ), F' r * Real.log r) =
      a * ∫ r in Set.Ioi (0 : ℝ), R r := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp [F', R]
    ring
  rw [hrep] at hIBP
  dsimp only [F] at hIBP
  simp only [zero_sub, sub_zero, ← div_eq_mul_inv] at hIBP
  linarith


set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


open MeasureTheory


open MeasureTheory Set


set_option autoImplicit false


set_option autoImplicit false


open MeasureTheory


set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


set_option autoImplicit false


open MeasureTheory Set


set_option autoImplicit false


open MeasureTheory


set_option autoImplicit false


open MeasureTheory Set


open Asymptotics


open Filter


set_option autoImplicit false


open MeasureTheory Set


open Asymptotics


open Filter


set_option autoImplicit false


open MeasureTheory Set


open Asymptotics


set_option autoImplicit false


open MeasureTheory Set


open Asymptotics


theorem CothSums.chi_invFun_hasDerivAt (r : ℝ) :
    HasDerivAt (Function.invFun CothSums.chi)
      (Real.sqrt (1 + r ^ 4) / (4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2))
      (CothSums.chi r) := by
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  have hdcont : Continuous (fun y : ℝ => C * (Real.sqrt (1 + y ^ 4))⁻¹) :=
    continuous_const.mul CothSums.density_continuous
  have hd : HasStrictDerivAt CothSums.chi (C * (Real.sqrt (1 + r ^ 4))⁻¹) r :=
    hasStrictDerivAt_of_hasDerivAt_of_continuousAt
      (Filter.Eventually.of_forall CothSums.chi_hasDerivAt) hdcont.continuousAt
  have hp : 0 < C * (Real.sqrt (1 + r ^ 4))⁻¹ :=
    mul_pos CothSums.chi_prefactor_pos (inv_pos.mpr (Real.sqrt_pos.2 (by positivity)))
  have hinv : ∀ᶠ y : ℝ in nhds r, Function.invFun CothSums.chi (CothSums.chi y) = y :=
    Filter.Eventually.of_forall (Function.leftInverse_invFun chi_strict.injective)
  have hh := (hd.to_local_left_inverse hp.ne' hinv).hasDerivAt
  exact hh.congr_deriv (by simp only [C, mul_inv_rev, inv_inv, div_eq_mul_inv])


theorem CothSums.inverse_log_sine_change_of_variables (a : ℝ) (ha : 0 ≤ a) (hs : Real.sin a = 0) :
    IntegrableOn (fun x : ℝ =>
      deriv (fun t : ℝ => Real.log (Function.invFun CothSums.chi t)) x *
        Real.sin (a * x)) (Set.Ioo 0 1) ∧
    (∫ x in Set.Ioo (0 : ℝ) 1,
      deriv (fun t : ℝ => Real.log (Function.invFun CothSums.chi t)) x *
        Real.sin (a * x)) =
      ∫ r in Set.Ioi (0 : ℝ), Real.sin (a * CothSums.chi r) / r := by
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  let D : ℝ → ℝ := fun r => C * (Real.sqrt (1 + r ^ 4))⁻¹
  let G : ℝ → ℝ := fun x =>
    deriv (fun t : ℝ => Real.log (Function.invFun CothSums.chi t)) x * Real.sin (a * x)
  have hC : 0 < C := CothSums.chi_prefactor_pos
  have hbij := CothSums.chi_positive_coordinate_bijective
  have himage : CothSums.chi '' Set.Ioi (0 : ℝ) = Set.Ioo 0 1 := hbij.image_eq
  have hderiv : ∀ r ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt CothSums.chi (D r) (Set.Ioi 0) r :=
    fun r _ => (CothSums.chi_hasDerivAt r).hasDerivWithinAt
  have hpoint : ∀ r ∈ Set.Ioi (0 : ℝ), |D r| • G (CothSums.chi r) =
      Real.sin (a * CothSums.chi r) / r := by
    intro r hr
    have hinv : Function.invFun CothSums.chi (CothSums.chi r) = r :=
      Function.leftInverse_invFun CothSums.chi_strictMono.injective r
    have hd : HasDerivAt (Function.invFun CothSums.chi)
        (Real.sqrt (1 + r ^ 4) / C) (CothSums.chi r) :=
      CothSums.chi_invFun_hasDerivAt r
    have hlog := hd.log (show Function.invFun CothSums.chi (CothSums.chi r) ≠ 0 by
      rw [hinv]; exact (show 0 < r from hr).ne')
    have hld := hlog.deriv
    rw [hinv] at hld
    have hsqrt : 0 < Real.sqrt (1 + r ^ 4) := Real.sqrt_pos.mpr (by positivity)
    have hDp : 0 < D r := mul_pos hC (inv_pos.mpr hsqrt)
    rw [abs_of_pos hDp, smul_eq_mul]
    dsimp only [G, D]
    rw [hld]
    field_simp [hC.ne', (show 0 < r from hr).ne', hsqrt.ne']
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hbij.injOn G
  rw [himage] at hchange
  have hG : IntegrableOn G (Set.Ioo 0 1) := by
    rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hbij.injOn]
    exact (integrableOn_congr_fun hpoint measurableSet_Ioi).mpr
      (CothSums.chi_sine_div_integrable a ha hs).1
  refine ⟨hG, ?_⟩
  change (∫ x in Set.Ioo (0 : ℝ) 1, G x) = _
  rw [hchange]
  exact setIntegral_congr_fun measurableSet_Ioi hpoint


theorem CothSums.inverse_log_odd_cosine_of_complex_data
    (U q : ℂ → ℂ)
    (hU1 : ∀ z : ℂ, U (z + 1) = -U z)
    (hUI : ∀ z : ℂ, U (z + Complex.I) = -U z)
    (hq : DifferentiableOn ℂ q (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ℂ
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2)))
    (hqu : ∀ z : ℂ, z ≠ 0 → q z = z * U z)
    (hq0 : q 0 = 1)
    (hreal : ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 →
      U (x : ℂ) = (deriv (fun t : ℝ => Real.log (Function.invFun CothSums.chi t)) x : ℂ))
    (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    (∫ x in Set.Ioo (0 : ℝ) 1,
      Real.log (Function.invFun CothSums.chi x) * Real.cos ((n : ℝ) * Real.pi * x)) =
      -(Real.tanh (Real.pi * (n : ℝ) / 2) / (n : ℝ)) := by
  have hcast (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
      U (x : ℂ) = ((deriv (fun t : ℝ => Real.log (Function.invFun CothSums.chi t)) x : ℝ) : ℂ) := by
    obtain ⟨r, hr, hrx⟩ := CothSums.chi_positive_coordinate_bijective.surjOn hx
    have hd := CothSums.chi_invFun_hasDerivAt r
    rw [hrx] at hd
    have hnR : Function.invFun CothSums.chi x ≠ 0 := by
      rw [← hrx, Function.leftInverse_invFun CothSums.chi_strictMono.injective r]
      exact (show 0 < r from hr).ne'
    have hl := hd.log hnR
    rw [hreal x hx, hl.ofReal_comp.deriv, hl.deriv]
  have hs := CothSums.ComplexAnalysis.square_antiperiodic_sine_integral U q hU1 hUI hq hqu hq0 n hn hodd
  have heq : (∫ x : ℝ in (0 : ℝ)..1, U (x : ℂ) *
      Complex.sin ((n : ℂ) * (Real.pi : ℂ) * (x : ℂ))) =
      ((∫ x in Set.Ioo (0 : ℝ) 1,
        deriv (fun t : ℝ => Real.log (Function.invFun CothSums.chi t)) x *
          Real.sin ((n : ℝ) * Real.pi * x) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
    rw [← _root_.integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    dsimp only
    rw [hcast x hx]
    simp only [Complex.ofReal_mul, Complex.ofReal_sin, Complex.ofReal_natCast]
  rw [heq] at hs
  have hsreal := Complex.ofReal_inj.mp hs.2
  have hfreq : 0 ≤ (n : ℝ) * Real.pi := mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le
  have hsin : Real.sin ((n : ℝ) * Real.pi) = 0 := Real.sin_nat_mul_pi n
  have hb := (CothSums.inverse_log_cosine_ibp ((n : ℝ) * Real.pi) hfreq hsin).2
  have hv := (CothSums.inverse_log_sine_change_of_variables ((n : ℝ) * Real.pi) hfreq hsin).2
  rw [hv] at hsreal
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [← neg_div]
  apply (eq_div_iff hn0).mpr
  have hh : (n : ℝ) * Real.pi *
      (∫ x in Set.Ioo (0 : ℝ) 1,
        Real.log (Function.invFun CothSums.chi x) * Real.cos ((n : ℝ) * Real.pi * x)) =
        -(Real.pi * Real.tanh (Real.pi * (n : ℝ) / 2)) := by
    exact hb.trans (congrArg Neg.neg hsreal)
  apply (mul_left_cancel₀ Real.pi_ne_zero)
  nlinarith [hh]


set_option autoImplicit false


open MeasureTheory Set


open Asymptotics


open Filter


private theorem chi_bij : Set.BijOn CothSums.chi (Ioi (0 : ℝ)) (Ioo (0 : ℝ) 1) := by
  have hz : CothSums.chi 0 = 0 := by simp [CothSums.chi]
  have hcont : Continuous CothSums.chi :=
    continuous_iff_continuousAt.mpr (fun r => (CothSums.chi_hasDerivAt r).continuousAt)
  refine ⟨?_, chi_strict.injective.injOn, ?_⟩
  · intro r hr
    constructor
    · simpa only [hz] using (chi_strict hr)
    · have hlt : CothSums.chi r < CothSums.chi (r + 1) := chi_strict (by linarith)
      exact hlt.trans_le (CothSums.chi_range_and_tail (r + 1) (by have hr0 : 0 < r := hr; linarith)).2.1
  · intro x hx
    have he : ∀ᶠ r : ℝ in Filter.atTop, x < CothSums.chi r :=
      chi_limit.eventually (lt_mem_nhds hx.2)
    obtain ⟨R, hxR, hR⟩ := (he.and (Filter.eventually_gt_atTop (0 : ℝ))).exists
    have hxi : x ∈ Ioo (CothSums.chi 0) (CothSums.chi R) := by
      simpa only [hz, Set.mem_Ioo] using And.intro hx.1 hxR
    obtain ⟨r, hr, heq⟩ := intermediate_value_Ioo hR.le hcont.continuousOn hxi
    exact ⟨r, hr.1, heq⟩


private theorem chi_recip (r : ℝ) (hr : 0 < r) : CothSums.chi r⁻¹ = 1 - CothSums.chi r := by
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  let H : ℝ → ℝ := fun t => CothSums.chi t⁻¹ + CothSums.chi t
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt H 0 t := by
    have hs : Real.sqrt (1 + (t⁻¹) ^ 4) = Real.sqrt (1 + t ^ 4) / t ^ 2 := by
      have he : 1 + (t⁻¹) ^ 4 = (1 + t ^ 4) / (t ^ 2) ^ 2 := by
        field_simp
        <;> ring
      rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq (sq_nonneg t)]
    have hh := ((CothSums.chi_hasDerivAt t⁻¹).comp t (hasDerivAt_inv ht.ne')).add
      (CothSums.chi_hasDerivAt t)
    apply hh.congr_deriv
    rw [hs]
    have hp : Real.sqrt (1 + t ^ 4) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    field_simp [ht.ne', hp]
    <;> ring
  have hconst (t : ℝ) (ht : 0 < t) : H t = H r := by
    apply isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
      (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hd t ht).deriv) ht hr
  have hz : CothSums.chi 0 = 0 := by simp [CothSums.chi]
  have hlim : Tendsto H atTop (nhds (1 : ℝ)) := by
    have hc := (CothSums.chi_hasDerivAt 0).continuousAt.tendsto.comp
      (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0))
    simpa only [H, Function.comp_def, hz, zero_add] using hc.add chi_limit
  have hlim' : Tendsto H atTop (nhds (H r)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (hconst t ht).symm
  have he : H r = 1 := (tendsto_nhds_unique hlim hlim').symm
  dsimp [H] at he
  linarith


private theorem log_reflect (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.log (Function.invFun CothSums.chi (1 - x)) =
      -Real.log (Function.invFun CothSums.chi x) := by
  obtain ⟨r, hr, he⟩ := chi_bij.surjOn hx
  have hrec := chi_recip r hr
  rw [← he, ← hrec, Function.leftInverse_invFun chi_strict.injective,
    Function.leftInverse_invFun chi_strict.injective, Real.log_inv]


theorem CothSums.chi_invFun_log_even_cosine_integral (n : ℕ) :
    (∫ x in Ioo (0 : ℝ) 1, Real.log (Function.invFun CothSums.chi x) *
      Real.cos ((2 * (n : ℝ)) * Real.pi * x)) = 0 := by
  let f : ℝ → ℝ := fun x => Real.log (Function.invFun CothSums.chi x) *
      Real.cos ((2 * (n : ℝ)) * Real.pi * x)
  have hcos (x : ℝ) : Real.cos ((2 * (n : ℝ)) * Real.pi * (1 - x)) =
      Real.cos ((2 * (n : ℝ)) * Real.pi * x) := by
    rw [show (2 * (n : ℝ)) * Real.pi * (1 - x) =
      -((2 * (n : ℝ)) * Real.pi * x) + (n : ℝ) * (2 * Real.pi) by ring,
      (Real.cos_periodic.nat_mul n) _, Real.cos_neg]
  have hpoint (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : f (1 - x) = -f x := by
    dsimp [f]
    rw [log_reflect x hx, hcos, neg_mul]
  have hreflect : (∫ x in Ioo (0 : ℝ) 1, f (1 - x)) =
      ∫ x in Ioo (0 : ℝ) 1, f x := by
    have hh := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) f 1
    simpa only [sub_self, sub_zero, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo] using hh
  have he : (∫ x in Ioo (0 : ℝ) 1, f (1 - x)) =
      -(∫ x in Ioo (0 : ℝ) 1, f x) := by
    rw [← integral_neg]
    exact setIntegral_congr_fun measurableSet_Ioo hpoint
  change (∫ x in Ioo (0 : ℝ) 1, f x) = 0
  linarith [he, hreflect]


open MeasureTheory Set Filter


open scoped ComplexConjugate


set_option autoImplicit false


theorem CothSums.Fourier.interval_inner_parseval {a b : ℝ} (hab : a < b)
    (f g : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Set.Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Set.Ioc a b))) :
    HasSum (fun n : ℤ => star (fourierCoeffOn hab f n) * fourierCoeffOn hab g n)
      (((b - a)⁻¹ : ℝ) • ∫ x in a..b, star (f x) * g x) := by
  let T : ℝ := b - a
  haveI : Fact (0 < T) := ⟨sub_pos.mpr hab⟩
  have hf0 : MemLp f 2 (volume.restrict (Ioc a (a + T))) := by simpa [T] using hf
  have hg0 : MemLp g 2 (volume.restrict (Ioc a (a + T))) := by simpa [T] using hg
  have hF := hf0.memLp_liftIoc.haarAddCircle
  have hG := hg0.memLp_liftIoc.haarAddCircle
  let F : Lp ℂ 2 (AddCircle.haarAddCircle (T := T)) := hF.toLp
  let G : Lp ℂ 2 (AddCircle.haarAddCircle (T := T)) := hG.toLp
  have hcF (n : ℤ) : fourierCoeff F n = fourierCoeffOn hab f n := by
    rw [fourierCoeff_congr_ae hF.coeFn_toLp, fourierCoeff_liftIoc_eq]
    simp only [T, add_sub_cancel] 
  have hcG (n : ℤ) : fourierCoeff G n = fourierCoeffOn hab g n := by
    rw [fourierCoeff_congr_ae hG.coeFn_toLp, fourierCoeff_liftIoc_eq]
    simp only [T, add_sub_cancel]
  have hs := (@fourierBasis T _).hasSum_inner_mul_inner F G
  have hterm (n : ℤ) : inner ℂ F (fourierBasis n) * inner ℂ (fourierBasis n) G =
      star (fourierCoeffOn hab f n) * fourierCoeffOn hab g n := by
    rw [← inner_conj_symm F (fourierBasis n), ← HilbertBasis.repr_apply_apply,
      ← HilbertBasis.repr_apply_apply, fourierBasis_repr, fourierBasis_repr, hcF, hcG]
    rfl
  have hinner : inner ℂ F G = ((b - a)⁻¹ : ℝ) •
      ∫ x in a..b, star (f x) * g x := by
    rw [MeasureTheory.L2.inner_def]
    have he : (∫ x : AddCircle T, inner ℂ (F x) (G x) ∂AddCircle.haarAddCircle) =
        ∫ x : AddCircle T, star ((AddCircle.liftIoc T a f) x) * (AddCircle.liftIoc T a g) x ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x hx hy
      simp only [F, G, hx, hy, RCLike.inner_apply']
      rfl
    rw [he, AddCircle.integral_haarAddCircle]
    have hh : (∫ x : AddCircle T, star (AddCircle.liftIoc T a f x) * AddCircle.liftIoc T a g x) =
        ∫ x in a..(a + T), star (f x) * g x := by
      rw [← AddCircle.integral_liftIoc_eq_intervalIntegral]
      apply integral_congr_ae
      filter_upwards [] with x
      rfl
    rw [hh]
    simp only [T, add_sub_cancel]
  simpa only [hterm, hinner] using hs


open MeasureTheory Set


set_option autoImplicit false


theorem CothSums.Fourier.even_extension_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (hf : IntegrableOn f (Set.Ioo (0 : ℝ) 1)) :
    IntegrableOn (fun x : ℝ => f |x|) (Set.Ioc (-1) 1) ∧
      (∫ x in (-1 : ℝ)..1, f |x|) = (2 : ℝ) • ∫ x in (0 : ℝ)..1, f x := by
  have hf' : IntegrableOn f (Ioc (0 : ℝ) 1) := by
    change Integrable f (volume.restrict (Ioc (0 : ℝ) 1))
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact hf
  have hh : IntervalIntegrable (fun x : ℝ => f |x|) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply hf'.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [abs_of_pos hx.1]
  have hn : IntervalIntegrable (fun x : ℝ => f |x|) volume (-1) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simpa only [abs_neg, neg_neg, neg_zero] using hh.symm
  have hwhole := hn.trans hh
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp hwhole, ?_⟩
  have hleft : (∫ x in (-1 : ℝ)..0, f |x|) = ∫ x in (0 : ℝ)..1, f x := by
    have he := intervalIntegral.integral_comp_neg (fun x : ℝ => f |x|) (a := (0 : ℝ)) (b := 1)
    simp only [abs_neg, neg_zero] at he
    rw [← he]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    change f |x| = f x
    rw [abs_of_nonneg hx.1]
  have hright : (∫ x in (0 : ℝ)..1, f |x|) = ∫ x in (0 : ℝ)..1, f x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    change f |x| = f x
    rw [abs_of_nonneg hx.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals hn hh, hleft, hright]
  simp only [two_smul]


theorem CothSums.Fourier.even_extension_L2 (f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioo (0 : ℝ) 1))) :
    MemLp (fun x : ℝ => (f |x| : ℂ)) 2 (volume.restrict (Set.Ioc (-1) 1)) := by
  have hi : IntegrableOn f (Ioo (0 : ℝ) 1) := hf.integrable (by norm_num)
  have he := CothSums.Fourier.even_extension_integral f hi
  have hs := CothSums.Fourier.even_extension_integral (fun x : ℝ => f x ^ 2) hf.integrable_sq
  have hr : MemLp (fun x : ℝ => f |x|) 2 (volume.restrict (Ioc (-1) 1)) :=
    (memLp_two_iff_integrable_sq he.1.aestronglyMeasurable).mpr hs.1
  exact hr.ofReal


theorem CothSums.Fourier.even_extension_fourierCoeff (f : ℝ → ℝ)
    (hf : IntegrableOn f (Set.Ioo (0 : ℝ) 1)) (n : ℤ) :
    fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) (fun x : ℝ => (f |x| : ℂ)) n =
      ((∫ x in (0 : ℝ)..1, f x * Real.cos ((n : ℝ) * Real.pi * x)) : ℂ) := by
  let F : ℝ → ℂ := fun x => (f |x| : ℂ)
  let k : ℝ → ℂ := fun x => Complex.exp (-((n : ℂ) * (Real.pi : ℂ) * x) * Complex.I)
  have hF := (CothSums.Fourier.even_extension_integral (fun x : ℝ => (f x : ℂ)) hf.ofReal).1
  have hFi : IntervalIntegrable F volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mpr hF
  have hk : Continuous k := by fun_prop
  have hKi : IntervalIntegrable (fun x : ℝ => k x * F x) volume (-1) 1 := by
    simpa only [mul_comm] using hFi.mul_continuousOn hk.continuousOn
  have hKleft : IntervalIntegrable (fun x : ℝ => k x * F x) volume (-1) 0 :=
    hKi.mono_set (by norm_num; exact Icc_subset_Icc (by norm_num) (by norm_num))
  have hKright : IntervalIntegrable (fun x : ℝ => k x * F x) volume 0 1 :=
    hKi.mono_set (by norm_num; exact Icc_subset_Icc (by norm_num) (by norm_num))
  have hleft : (∫ x in (-1 : ℝ)..0, k x * F x) = ∫ x in (0 : ℝ)..1, k (-x) * (f x : ℂ) := by
    have he := intervalIntegral.integral_comp_neg (fun x : ℝ => k x * F x) (a := (0 : ℝ)) (b := 1)
    simp only [neg_zero] at he
    rw [← he]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    change k (-x) * (f |-x| : ℂ) = k (-x) * (f x : ℂ)
    rw [abs_neg, abs_of_nonneg hx.1]
  have hright : (∫ x in (0 : ℝ)..1, k x * F x) = ∫ x in (0 : ℝ)..1, k x * (f x : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    change k x * (f |x| : ℂ) = k x * (f x : ℂ)
    rw [abs_of_nonneg hx.1]
  have hsum (x : ℝ) : k (-x) + k x = 2 * (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) := by
    dsimp only [k]
    rw [Complex.ofReal_neg]
    have h1 : -((n : ℂ) * (Real.pi : ℂ) * -(x : ℂ)) * Complex.I =
        ((n : ℂ) * (Real.pi : ℂ) * x) * Complex.I := by ring
    rw [h1, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  have hpoint (x : ℝ) : fourier (-n) (x : AddCircle (1 - (-1 : ℝ))) • F x = k x * F x := by
    rw [fourier_coe_apply, smul_eq_mul]
    congr 1
    dsimp only [k]
    push_cast
    congr 1
    ring
  rw [fourierCoeffOn_eq_integral]
  change ((1 / (1 - (-1 : ℝ))) : ℝ) •
    (∫ x in (-1 : ℝ)..1, fourier (-n) (x : AddCircle (1 - (-1 : ℝ))) • F x) = _
  simp_rw [hpoint]
  norm_num only [show (1 : ℝ) - -1 = 2 by norm_num]
  rw [← intervalIntegral.integral_add_adjacent_intervals hKleft hKright, hleft, hright]
  have hraw : IntervalIntegrable (fun x : ℝ => (f x : ℂ)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (by change Integrable _ _; rw [← restrict_Ioo_eq_restrict_Ioc]; exact hf.ofReal)
  have h1 : IntervalIntegrable (fun x : ℝ => k (-x) * (f x : ℂ)) volume 0 1 := by
    simpa only [mul_comm, Function.comp_apply] using hraw.mul_continuousOn (hk.comp continuous_neg).continuousOn
  have h2 : IntervalIntegrable (fun x : ℝ => k x * (f x : ℂ)) volume 0 1 := by
    simpa only [mul_comm] using hraw.mul_continuousOn hk.continuousOn
  rw [← intervalIntegral.integral_add h1 h2]
  have he : (∫ x in (0 : ℝ)..1, k (-x) * (f x : ℂ) + k x * (f x : ℂ)) =
      (2 : ℂ) * ((∫ x in (0 : ℝ)..1, f x * Real.cos ((n : ℝ) * Real.pi * x)) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    calc
      _ = (k (-x) + k x) * (f x : ℂ) := by ring
      _ = _ := by rw [hsum]; ring
  rw [he]
  norm_num
  ring


theorem CothSums.Fourier.cosine_pairing_L2 (f g : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioo (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Set.Ioo (0 : ℝ) 1))) :
    Summable (fun n : ℕ =>
      (∫ x in (0 : ℝ)..1, f x * Real.cos (((n : ℝ) + 1) * Real.pi * x)) *
      (∫ x in (0 : ℝ)..1, g x * Real.cos (((n : ℝ) + 1) * Real.pi * x))) ∧
    (∫ x in (0 : ℝ)..1, f x * g x) =
      (∫ x in (0 : ℝ)..1, f x) * (∫ x in (0 : ℝ)..1, g x) +
        2 * ∑' n : ℕ,
          (∫ x in (0 : ℝ)..1, f x * Real.cos (((n : ℝ) + 1) * Real.pi * x)) *
          (∫ x in (0 : ℝ)..1, g x * Real.cos (((n : ℝ) + 1) * Real.pi * x)) := by
  let F : ℝ → ℂ := fun x => (f |x| : ℂ)
  let G : ℝ → ℂ := fun x => (g |x| : ℂ)
  let A : ℤ → ℝ := fun n => ∫ x in (0 : ℝ)..1, f x * Real.cos ((n : ℝ) * Real.pi * x)
  let B : ℤ → ℝ := fun n => ∫ x in (0 : ℝ)..1, g x * Real.cos ((n : ℝ) * Real.pi * x)
  let H : ℤ → ℝ := fun n => A n * B n
  have hf1 := hf.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hg1 := hg.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hprod : IntegrableOn (fun x : ℝ => f x * g x) (Ioo 0 1) := hf.integrable_mul hg
  have hs := CothSums.Fourier.interval_inner_parseval (by norm_num : (-1 : ℝ) < 1) F G
    (CothSums.Fourier.even_extension_L2 f hf) (CothSums.Fourier.even_extension_L2 g hg)
  have hterm (n : ℤ) : star (fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) F n) *
      fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) G n = (H n : ℂ) := by
    rw [CothSums.Fourier.even_extension_fourierCoeff f hf1 n,
      CothSums.Fourier.even_extension_fourierCoeff g hg1 n]
    simp only [H, A, B]
    simp_rw [← Complex.ofReal_mul, intervalIntegral.integral_ofReal]
    simp
  have he : (∫ x in (-1 : ℝ)..1, star (F x) * G x) =
      (2 : ℝ) • Complex.ofReal (∫ x in (0 : ℝ)..1, f x * g x) := by
    have he' := (CothSums.Fourier.even_extension_integral
      (fun x : ℝ => ((f x * g x : ℝ) : ℂ)) hprod.ofReal).2
    simp_rw [intervalIntegral.integral_ofReal] at he'
    calc
      (∫ x in (-1 : ℝ)..1, star (F x) * G x) =
          ∫ x in (-1 : ℝ)..1, ((f |x| * g |x| : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change star (f |x| : ℂ) * (g |x| : ℂ) = ((f |x| * g |x| : ℝ) : ℂ)
        simp
      _ = _ := by rw [intervalIntegral.integral_ofReal]; exact he'
  have hval : (((1 : ℝ) - -1)⁻¹ : ℝ) •
      (∫ x in (-1 : ℝ)..1, star (F x) * G x) =
        Complex.ofReal (∫ x in (0 : ℝ)..1, f x * g x) := by
    rw [he, smul_smul]
    norm_num
  have hsC : HasSum (fun n : ℤ => (H n : ℂ)) (Complex.ofReal (∫ x in (0 : ℝ)..1, f x * g x)) := by
    simpa only [hterm, hval] using hs
  have hsR : HasSum H (∫ x in (0 : ℝ)..1, f x * g x) := by
    simpa only [Complex.reCLM_apply, Complex.ofReal_re] using hsC.mapL Complex.reCLM
  have hneg (n : ℤ) : H (-n) = H n := by
    dsimp only [H, A, B]
    simp only [Int.cast_neg, neg_mul, Real.cos_neg]
  have hpos : Summable (fun n : ℕ => H ((n : ℤ) + 1)) :=
    hsR.summable.comp_injective (by intro n m he; exact_mod_cast (add_right_cancel he))
  have hnegpos : HasSum (fun n : ℕ => H (-((n : ℤ) + 1)))
      (∑' n : ℕ, H ((n : ℤ) + 1)) := by
    simpa only [hneg] using hpos.hasSum
  have ht := hpos.hasSum.of_add_one_of_neg_add_one hnegpos
  have htotal := hsR.unique ht
  have hzero : H 0 = (∫ x in (0 : ℝ)..1, f x) * (∫ x in (0 : ℝ)..1, g x) := by simp [H, A, B]
  have hcast (n : ℕ) : H ((n : ℤ) + 1) =
      (∫ x in (0 : ℝ)..1, f x * Real.cos (((n : ℝ) + 1) * Real.pi * x)) *
      (∫ x in (0 : ℝ)..1, g x * Real.cos (((n : ℝ) + 1) * Real.pi * x)) := by
    simp only [H, A, B, Int.cast_add, Int.cast_natCast, Int.cast_one]
  refine ⟨by simpa only [hcast] using hpos, ?_⟩
  rw [hzero] at htotal
  simp_rw [hcast] at htotal
  linarith


theorem CothSums.Fourier.polynomial_cosine_pairing (f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioo (0 : ℝ) 1)))
    (P : Polynomial ℝ) (h0 : P.eval 0 = 0) (h1 : P.eval 1 = 0) :
    IntegrableOn (fun x : ℝ => f x * P.derivative.eval x) (Set.Ioo 0 1) ∧
    Summable (fun n : ℕ =>
      (∫ x in (0 : ℝ)..1, f x * Real.cos (((n : ℝ) + 1) * Real.pi * x)) *
      (∫ x in (0 : ℝ)..1, P.derivative.eval x * Real.cos (((n : ℝ) + 1) * Real.pi * x))) ∧
    (∫ x in (0 : ℝ)..1, f x * P.derivative.eval x) =
      2 * ∑' n : ℕ,
        (∫ x in (0 : ℝ)..1, f x * Real.cos (((n : ℝ) + 1) * Real.pi * x)) *
        (∫ x in (0 : ℝ)..1, P.derivative.eval x * Real.cos (((n : ℝ) + 1) * Real.pi * x)) := by
  have hg : MemLp (fun x : ℝ => P.derivative.eval x) 2 (volume.restrict (Ioo 0 1)) := by
    have hm : AEStronglyMeasurable (fun x : ℝ => P.derivative.eval x) (volume.restrict (Ioo 0 1)) :=
      P.derivative.continuous.aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq hm).mpr
    exact (P.derivative.continuous.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hh := CothSums.Fourier.cosine_pairing_L2 f (fun x : ℝ => P.derivative.eval x) hf hg
  have hmean : (∫ x in (0 : ℝ)..1, P.derivative.eval x) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => P.hasDerivAt x) (P.derivative.continuous.intervalIntegrable _ _), h0, h1, sub_self]
  refine ⟨hf.integrable_mul hg, hh.1, ?_⟩
  simpa only [hmean, mul_zero, zero_add] using hh.2


theorem CothSums.Fourier.odd_coefficient_polynomial_pairing (f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioo (0 : ℝ) 1)))
    (hcoeff : ∀ n : ℕ, 0 < n →
      (∫ x in (0 : ℝ)..1, f x * Real.cos ((n : ℝ) * Real.pi * x)) =
        if Odd n then -(Real.tanh (Real.pi * (n : ℝ) / 2) / (n : ℝ)) else 0)
    (P : Polynomial ℝ) (h0 : P.eval 0 = 0) (h1 : P.eval 1 = 0) :
    (∫ x in (0 : ℝ)..1, f x * P.derivative.eval x) =
      -2 * ∑' n : ℕ,
        (Real.tanh (Real.pi * (2 * (n : ℝ) + 1) / 2) / (2 * (n : ℝ) + 1)) *
        (∫ x in (0 : ℝ)..1, P.derivative.eval x *
          Real.cos ((2 * (n : ℝ) + 1) * Real.pi * x)) := by
  let A : ℕ → ℝ := fun n => ∫ x in (0 : ℝ)..1, f x * Real.cos ((n : ℝ) * Real.pi * x)
  let B : ℕ → ℝ := fun n => ∫ x in (0 : ℝ)..1, P.derivative.eval x * Real.cos ((n : ℝ) * Real.pi * x)
  let K : ℕ → ℝ := fun n => A n * B n
  have hh := CothSums.Fourier.polynomial_cosine_pairing f hf P h0 h1
  have hsum : Summable K := by
    apply (summable_nat_add_iff 1).mp
    simpa only [K, A, B, Nat.cast_add, Nat.cast_one] using hh.2.1
  have hB0 : B 0 = 0 := by
    dsimp only [B]
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => P.hasDerivAt x) (P.derivative.continuous.intervalIntegrable _ _), h0, h1, sub_self]
  have hK0 : K 0 = 0 := by simp only [K, hB0, mul_zero]
  have ht : (∫ x in (0 : ℝ)..1, f x * P.derivative.eval x) = 2 * ∑' n : ℕ, K n := by
    rw [hsum.tsum_eq_zero_add]
    simpa only [hK0, zero_add, K, A, B, Nat.cast_add, Nat.cast_one] using hh.2.2
  have heven (n : ℕ) : K (2 * n) = 0 := by
    by_cases hn : n = 0
    · subst n
      simpa only [mul_zero] using hK0
    · have he : ¬ Odd (2 * n) := by simp
      have hc := hcoeff (2 * n) (by omega)
      rw [if_neg he] at hc
      dsimp only [K, A]
      rw [hc, zero_mul]
  have hodd (n : ℕ) : K (2 * n + 1) =
      -((Real.tanh (Real.pi * (2 * (n : ℝ) + 1) / 2) / (2 * (n : ℝ) + 1)) *
        (∫ x in (0 : ℝ)..1, P.derivative.eval x * Real.cos ((2 * (n : ℝ) + 1) * Real.pi * x))) := by
    have hc := hcoeff (2 * n + 1) (by omega)
    rw [if_pos (by simp : Odd (2 * n + 1))] at hc
    dsimp only [K, A, B]
    rw [hc]
    push_cast
    ring
  have hes : Summable (fun n : ℕ => K (2 * n)) :=
    hsum.comp_injective (by intro n m he; change 2 * n = 2 * m at he; omega)
  have hos : Summable (fun n : ℕ => K (2 * n + 1)) :=
    hsum.comp_injective (by intro n m he; change 2 * n + 1 = 2 * m + 1 at he; omega)
  rw [← tsum_even_add_odd hes hos] at ht
  simp_rw [heven, tsum_zero, zero_add, hodd] at ht
  rw [tsum_neg] at ht
  linarith


set_option autoImplicit false


open MeasureTheory Set


open Asymptotics


open Filter


theorem CothSums.density_log_sq_integrable :
    IntegrableOn (fun r : ℝ => (Real.sqrt (1 + r ^ 4))⁻¹ * Real.log r ^ 2) (Set.Ioi 0) := by
  have hm : ContinuousOn (fun r : ℝ => (Real.sqrt (1 + r ^ 4))⁻¹ * Real.log r ^ 2) (Ioi 0) :=
    CothSums.density_continuous.continuousOn.mul
      ((Real.continuousOn_log.mono (fun r hr => ne_of_gt hr)).pow 2)
  have hhead : IntegrableOn (fun r : ℝ => (Real.sqrt (1 + r ^ 4))⁻¹ * Real.log r ^ 2) (Ioc 0 1) := by
    have hb : IntegrableOn (fun r : ℝ => 16 * r ^ (-1 / 2 : ℝ)) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -1 / 2))).const_mul 16
    refine hb.mono' ((hm.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 < r := hr.1
    have hlog : |Real.log r| ≤ 4 * r ^ (-1 / 4 : ℝ) := by
      have hh := Real.log_le_rpow_div (inv_nonneg.mpr hr0.le) (by norm_num : (0 : ℝ) < 1 / 4)
      rw [Real.log_inv, Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le] at hh
      rw [abs_of_nonpos (Real.log_nonpos hr0.le hr.2)]
      norm_num at hh ⊢
      linarith
    have hl2 : Real.log r ^ 2 ≤ 16 * r ^ (-1 / 2 : ℝ) := by
      have hh := sq_le_sq₀ (abs_nonneg (Real.log r)) (by positivity : 0 ≤ 4 * r ^ (-1 / 4 : ℝ)) |>.2 hlog
      have hp : (r ^ (-1 / 4 : ℝ)) ^ 2 = r ^ (-1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast (r ^ (-1 / 4 : ℝ)) 2, ← Real.rpow_mul hr0.le]
        norm_num
      rw [sq_abs, mul_pow, hp] at hh
      norm_num at hh ⊢
      exact hh
    have hs : 1 ≤ Real.sqrt (1 + r ^ 4) := by
      exact (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith [pow_nonneg hr0.le 4])
    have hd : (Real.sqrt (1 + r ^ 4))⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 hs
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (mul_le_of_le_one_left (sq_nonneg _) hd).trans hl2
  have htail : IntegrableOn (fun r : ℝ => (Real.sqrt (1 + r ^ 4))⁻¹ * Real.log r ^ 2) (Ioi 1) := by
    have hb := (integrableOn_Ioi_rpow_of_lt (a := (-3 / 2 : ℝ)) (c := 1)
      (by norm_num) (by norm_num)).const_mul (16 : ℝ)
    refine hb.mono' ((hm.mono (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := lt_trans (by norm_num) hr
    have hlog : Real.log r ≤ 4 * r ^ (1 / 4 : ℝ) := by
      have hh := Real.log_le_rpow_div hr0.le (by norm_num : (0 : ℝ) < 1 / 4)
      linarith
    have hl2 : Real.log r ^ 2 ≤ 16 * r ^ (1 / 2 : ℝ) := by
      have hh := sq_le_sq₀ (Real.log_nonneg hr.le) (by positivity : 0 ≤ 4 * r ^ (1 / 4 : ℝ)) |>.2 hlog
      have hp : (r ^ (1 / 4 : ℝ)) ^ 2 = r ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast (r ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hr0.le]
        norm_num
      rw [mul_pow, hp] at hh
      norm_num at hh ⊢
      exact hh
    have hs : r ^ 2 ≤ Real.sqrt (1 + r ^ 4) := by
      have hh := Real.sqrt_le_sqrt (show r ^ 4 ≤ 1 + r ^ 4 by linarith)
      have he : Real.sqrt (r ^ 4) = r ^ 2 := by
        rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg r)]
      rwa [he] at hh
    have hd : (Real.sqrt (1 + r ^ 4))⁻¹ ≤ r ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hr0.le, Real.rpow_two]
      exact (inv_le_inv₀ (by positivity) (sq_pos_of_pos hr0)).2 hs
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      (Real.sqrt (1 + r ^ 4))⁻¹ * Real.log r ^ 2 ≤ r ^ (-2 : ℝ) * (16 * r ^ (1 / 2 : ℝ)) :=
        mul_le_mul hd hl2 (sq_nonneg _) (by positivity)
      _ = 16 * r ^ (-3 / 2 : ℝ) := by rw [mul_left_comm, ← Real.rpow_add hr0]; norm_num
  simpa only [Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)] using hhead.union htail


theorem CothSums.chi_inverse_hasDerivAt (r : ℝ) :
    HasDerivAt (Function.invFun CothSums.chi)
      (Real.sqrt (1 + r ^ 4) / (4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2))
      (CothSums.chi r) := by
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  have hdcont : Continuous (fun y : ℝ => C * (Real.sqrt (1 + y ^ 4))⁻¹) :=
    continuous_const.mul CothSums.density_continuous
  have hd : HasStrictDerivAt CothSums.chi (C * (Real.sqrt (1 + r ^ 4))⁻¹) r :=
    hasStrictDerivAt_of_hasDerivAt_of_continuousAt
      (Filter.Eventually.of_forall CothSums.chi_hasDerivAt) hdcont.continuousAt
  have hp : 0 < C * (Real.sqrt (1 + r ^ 4))⁻¹ :=
    mul_pos CothSums.chi_prefactor_pos (inv_pos.mpr (Real.sqrt_pos.2 (by positivity)))
  have hinv : ∀ᶠ y : ℝ in nhds r, Function.invFun CothSums.chi (CothSums.chi y) = y :=
    Filter.Eventually.of_forall (Function.leftInverse_invFun chi_strict.injective)
  have hh := (hd.to_local_left_inverse hp.ne' hinv).hasDerivAt
  exact hh.congr_deriv (by simp only [C, mul_inv_rev, inv_inv, div_eq_mul_inv])


theorem CothSums.inverse_log_L1_L2 :
    IntegrableOn (fun x : ℝ => Real.log (Function.invFun CothSums.chi x)) (Set.Ioo 0 1) ∧
    MemLp (fun x : ℝ => Real.log (Function.invFun CothSums.chi x)) 2
      (volume.restrict (Set.Ioo 0 1)) := by
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  let D : ℝ → ℝ := fun r => C * (Real.sqrt (1 + r ^ 4))⁻¹
  let f : ℝ → ℝ := fun x => Real.log (Function.invFun CothSums.chi x)
  have hC : 0 < C := CothSums.chi_prefactor_pos
  have hbij := CothSums.chi_positive_coordinate_bijective
  have himage : CothSums.chi '' Ioi (0 : ℝ) = Ioo 0 1 := hbij.image_eq
  have hm : AEStronglyMeasurable f (volume.restrict (Ioo 0 1)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
    intro x hx
    obtain ⟨r, hr, rfl⟩ := hbij.surjOn hx
    have hi : Function.invFun CothSums.chi (CothSums.chi r) = r :=
      Function.leftInverse_invFun chi_strict.injective r
    have hl : ContinuousAt Real.log (Function.invFun CothSums.chi (CothSums.chi r)) := by
      rw [hi]
      exact Real.continuousAt_log (ne_of_gt hr)
    exact (hl.comp (CothSums.chi_inverse_hasDerivAt r).continuousAt).continuousWithinAt
  have hderiv : ∀ r ∈ Ioi (0 : ℝ), HasDerivWithinAt CothSums.chi (D r) (Ioi 0) r :=
    fun r _ => (CothSums.chi_hasDerivAt r).hasDerivWithinAt
  have hi : IntegrableOn (fun x : ℝ => f x ^ 2) (Ioo 0 1) := by
    rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hbij.injOn]
    have hh : IntegrableOn (fun r : ℝ => C * ((Real.sqrt (1 + r ^ 4))⁻¹ * Real.log r ^ 2)) (Ioi 0) :=
      CothSums.density_log_sq_integrable.const_mul C
    apply hh.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hD : 0 < D r := mul_pos hC (inv_pos.mpr (Real.sqrt_pos.2 (by positivity)))
    rw [abs_of_pos hD, smul_eq_mul]
    dsimp only [f, D]
    rw [Function.leftInverse_invFun chi_strict.injective r]
    ring
  have hL2 : MemLp f 2 (volume.restrict (Ioo 0 1)) :=
    (memLp_two_iff_integrable_sq hm).mpr hi
  exact ⟨hL2.integrable (by norm_num), hL2⟩


set_option autoImplicit false


open MeasureTheory Set


open Asymptotics


open Filter


theorem CothSums.kernel_mellin_analytic_strip :
  ∀ s : ℂ, (-1 : ℝ) < s.re → s.re < 1 →
    MellinConvergent (fun r : ℝ => (CothSums.kernel r : ℂ)) s ∧
    DifferentiableAt ℂ (mellin (fun r : ℝ => (CothSums.kernel r : ℂ))) s := by
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  have hc : Continuous CothSums.chi :=
    continuous_iff_continuousAt.mpr (fun r => (CothSums.chi_hasDerivAt r).continuousAt)
  have hk : Continuous CothSums.kernel := hc.mul (continuous_const.sub hc)
  have hkc : Continuous (fun r : ℝ => (CothSums.kernel r : ℂ)) :=
    Complex.continuous_ofReal.comp hk
  have hbound (r : ℝ) (hr : 0 < r) :
      ‖(CothSums.kernel r : ℂ)‖ ≤ C * r ∧
      ‖(CothSums.kernel r : ℂ)‖ ≤ C / r := by
    have hchi := CothSums.chi_range_and_tail r hr
    have hp : 0 ≤ CothSums.kernel r :=
      mul_nonneg hchi.1 (sub_nonneg.mpr hchi.2.1)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
    constructor
    · calc
        CothSums.kernel r ≤ CothSums.chi r := by
          unfold CothSums.kernel
          nlinarith [sq_nonneg (CothSums.chi r)]
        _ ≤ C * r := CothSums.chi_le_prefactor_mul hr.le
    · calc
        CothSums.kernel r ≤ 1 - CothSums.chi r := by
          unfold CothSums.kernel
          nlinarith [sq_nonneg (1 - CothSums.chi r)]
        _ ≤ C / r := hchi.2.2.2
  have htop : (fun r : ℝ => (CothSums.kernel r : ℂ)) =O[Filter.atTop]
      (fun r : ℝ => r ^ (-(1 : ℝ))) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
    simpa only [Real.rpow_neg_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), div_eq_mul_inv] using (hbound r hr).2
  have hbot : (fun r : ℝ => (CothSums.kernel r : ℂ)) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun r : ℝ => r ^ (-(-1 : ℝ))) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [neg_neg, Real.rpow_one, Real.norm_eq_abs,
      abs_of_pos (show 0 < r from hr)] using (hbound r hr).1
  have hloc : LocallyIntegrableOn (fun r : ℝ => (CothSums.kernel r : ℂ))
      (Set.Ioi (0 : ℝ)) volume :=
    hkc.locallyIntegrable.locallyIntegrableOn (Set.Ioi (0 : ℝ))
  intro s hs0 hs1
  exact ⟨mellinConvergent_of_isBigO_rpow hloc htop hs1 hbot hs0,
    mellin_differentiableAt_of_isBigO_rpow hloc htop hs1 hbot hs0⟩


theorem CothSums.Polynomials.endpoint_zero_one_factor (P : Polynomial ℝ) (h0 : P.eval 0 = 0) (h1 : P.eval 1 = 0) :
    ∃ Q : Polynomial ℝ, P = Polynomial.X * (1 - Polynomial.X) * Q := by
  have hx : Polynomial.X ∣ P := by
    simpa only [Polynomial.C_0, sub_zero] using
      (Polynomial.dvd_iff_isRoot.mpr h0 : Polynomial.X - Polynomial.C (0 : ℝ) ∣ P)
  obtain ⟨Q, hQ⟩ := hx
  have hq1 : Q.eval 1 = 0 := by simpa [hQ] using h1
  have hd : Polynomial.X - Polynomial.C (1 : ℝ) ∣ Q :=
    Polynomial.dvd_iff_isRoot.mpr hq1
  obtain ⟨R, hR⟩ := hd
  refine ⟨-R, ?_⟩
  rw [hQ, hR]
  simp only [Polynomial.C_1]
  ring


theorem CothSums.testMoment_integrable (P : Polynomial ℝ)
    (h0 : P.eval 0 = 0) (h1 : P.eval 1 = 0) :
    IntegrableOn (fun r : ℝ => P.eval (CothSums.chi r) / r) (Set.Ioi 0) := by
  obtain ⟨Q, hPQ⟩ := CothSums.Polynomials.endpoint_zero_one_factor P h0 h1
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn Q.continuous.continuousOn
  have hc : Continuous CothSums.chi :=
    continuous_iff_continuousAt.mpr (fun r => (CothSums.chi_hasDerivAt r).continuousAt)
  have hk : Continuous (fun r : ℝ => (CothSums.kernel r : ℂ)) :=
    Complex.continuous_ofReal.comp (hc.mul (continuous_const.sub hc))
  have hbound (r : ℝ) (hr : 0 < r) :
      ‖Complex.ofReal (P.eval (CothSums.chi r))‖ ≤ B * ‖(CothSums.kernel r : ℂ)‖ := by
    have hh := CothSums.chi_range_and_tail r hr
    have he : P.eval (CothSums.chi r) =
        CothSums.kernel r * Q.eval (CothSums.chi r) := by
      rw [hPQ]
      simp [CothSums.kernel, mul_assoc]
    rw [he]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    simpa only [Real.norm_eq_abs, mul_comm] using
      mul_le_mul_of_nonneg_left (hB _ ⟨hh.1, hh.2.1⟩)
        (abs_nonneg (CothSums.kernel r))
  have hkm := (CothSums.kernel_mellin_analytic_strip (0 : ℂ)
    (by norm_num) (by norm_num)).1
  have hb0 := (mellin_convergent_iff_norm (s := (0 : ℂ)) (Set.Subset.rfl)
    measurableSet_Ioi hk.aestronglyMeasurable.restrict).mp hkm
  have hb : IntegrableOn (fun r : ℝ => r⁻¹ * ‖(CothSums.kernel r : ℂ)‖) (Ioi 0) := by
    simpa only [Complex.zero_re, zero_sub, Real.rpow_neg_one] using hb0
  have hmeas : AEStronglyMeasurable (fun r : ℝ => P.eval (CothSums.chi r) / r)
      (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact (P.continuous.comp hc).continuousOn.div continuous_id.continuousOn
      (fun r hr => ne_of_gt hr)
  refine (hb.const_mul B).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hh := hbound r hr
  rw [Real.norm_eq_abs, abs_div, (show |r| = r from abs_of_pos hr)]
  have hi : 0 ≤ r⁻¹ := le_of_lt (inv_pos.mpr hr)
  have hmul := mul_le_mul_of_nonneg_right hh hi
  simpa only [Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using hmul


theorem CothSums.polynomial_chi_log_boundary (P : Polynomial ℝ)
    (h0 : P.eval 0 = 0) (h1 : P.eval 1 = 0) :
    Filter.Tendsto (fun r : ℝ => P.eval (CothSums.chi r) * Real.log r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun r : ℝ => P.eval (CothSums.chi r) * Real.log r)
      Filter.atTop (nhds 0) := by
  obtain ⟨Q, hPQ⟩ := CothSums.Polynomials.endpoint_zero_one_factor P h0 h1
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  have hC : 0 < C := CothSums.chi_prefactor_pos
  have hc : Continuous CothSums.chi :=
    continuous_iff_continuousAt.mpr (fun r => (CothSums.chi_hasDerivAt r).continuousAt)
  have hz : CothSums.chi 0 = 0 := by simp [CothSums.chi]
  have hcl : Tendsto CothSums.chi (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa only [hz] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hsmall : Tendsto (fun r : ℝ => CothSums.chi r * Real.log r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    refine squeeze_zero_norm' (a := fun r : ℝ => C * |Real.log r * r|) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with r hr
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (CothSums.chi_nonneg hr.le)]
      have he := mul_le_mul_of_nonneg_right (CothSums.chi_le_prefactor_mul hr.le) (abs_nonneg (Real.log r))
      simpa only [abs_mul, abs_of_pos (show 0 < r from hr), mul_assoc, mul_comm, mul_left_comm] using he
    · have h := (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1)).norm.const_mul C
      simpa only [Real.rpow_one, Real.norm_eq_abs, abs_mul, abs_of_pos (show (0 : ℝ) < 1 by norm_num),
        norm_zero, mul_zero] using h
  have hlarge : Tendsto (fun r : ℝ => (1 - CothSums.chi r) * Real.log r) atTop (nhds 0) := by
    refine squeeze_zero_norm' (a := fun r : ℝ => C * |Real.log r / r|) ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      have hh := CothSums.chi_range_and_tail r hr
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hh.2.1)]
      calc
        (1 - CothSums.chi r) * |Real.log r| ≤ (C / r) * |Real.log r| :=
          mul_le_mul_of_nonneg_right hh.2.2.2 (abs_nonneg (Real.log r))
        _ = C * |Real.log r / r| := by rw [abs_div, abs_of_pos hr]; ring
    · simpa only [Real.norm_eq_abs, id_eq, norm_zero, mul_zero] using
        Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.norm.const_mul C
  have heval (r : ℝ) : P.eval (CothSums.chi r) =
      CothSums.chi r * (1 - CothSums.chi r) * Q.eval (CothSums.chi r) := by
    rw [hPQ]
    simp
  constructor
  · have ht := (((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 0 (Ioi 0)) (nhds 1)).sub hcl).mul
      (Q.continuous.continuousAt.tendsto.comp hcl)).mul hsmall
    simp only [sub_zero, mul_zero] at ht
    apply ht.congr'
    filter_upwards [] with r
    simp only [Function.comp_apply]
    rw [heval]
    ring
  · have ht := (chi_limit.mul (Q.continuous.continuousAt.tendsto.comp chi_limit)).mul hlarge
    simp only [sub_zero, mul_zero] at ht
    apply ht.congr'
    filter_upwards [] with r
    simp only [Function.comp_apply]
    rw [heval]
    ring


theorem CothSums.polynomial_coordinate_transfer (P : Polynomial ℝ)
    (h0 : P.eval 0 = 0) (h1 : P.eval 1 = 0) :
    IntegrableOn (fun x : ℝ => P.derivative.eval x *
      Real.log (Function.invFun CothSums.chi x)) (Set.Ioo 0 1) ∧
    CothSums.testMoment P =
      -(∫ x in Set.Ioo (0 : ℝ) 1, P.derivative.eval x *
        Real.log (Function.invFun CothSums.chi x)) := by
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  let D : ℝ → ℝ := fun r => C * (Real.sqrt (1 + r ^ 4))⁻¹
  let F : ℝ → ℝ := fun r => P.eval (CothSums.chi r)
  let F' : ℝ → ℝ := fun r => P.derivative.eval (CothSums.chi r) * D r
  let R : ℝ → ℝ := fun r => F' r * Real.log r
  let G : ℝ → ℝ := fun x => P.derivative.eval x * Real.log (Function.invFun CothSums.chi x)
  have hC : 0 < C := CothSums.chi_prefactor_pos
  have hc : Continuous CothSums.chi :=
    continuous_iff_continuousAt.mpr (fun r => (CothSums.chi_hasDerivAt r).continuousAt)
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    P.derivative.continuous.continuousOn
  have hR : IntegrableOn R (Ioi 0) := by
    have hi := CothSums.density_log_integrable.norm.const_mul (M * C)
    have hm : AEStronglyMeasurable R (volume.restrict (Ioi 0)) := by
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      have hF : Continuous F' := by
        exact (P.derivative.continuous.comp hc).mul
          (continuous_const.mul CothSums.density_continuous)
      exact hF.continuousOn.mul (Real.continuousOn_log.mono (fun r hr => ne_of_gt hr))
    refine hi.mono' hm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hh := CothSums.chi_range_and_tail r hr
    have hb := mul_le_mul_of_nonneg_right (hM (CothSums.chi r) ⟨hh.1, hh.2.1⟩)
      (show 0 ≤ C * |(Real.sqrt (1 + r ^ 4))⁻¹ * Real.log r| by positivity)
    dsimp only [R, F', D]
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos hC,
      mul_assoc, mul_comm, mul_left_comm] using hb
  have hFG : IntegrableOn (F * (fun r : ℝ => r⁻¹)) (Ioi 0) := by
    change IntegrableOn (fun r : ℝ => P.eval (CothSums.chi r) * r⁻¹) (Ioi 0)
    have hi := CothSums.testMoment_integrable P h0 h1
    exact hi.congr (Filter.Eventually.of_forall (fun r => by
      change P.eval (CothSums.chi r) / r = P.eval (CothSums.chi r) * r⁻¹
      exact div_eq_mul_inv _ _))
  have hFR : IntegrableOn (F' * Real.log) (Ioi 0) := hR
  have hboundary := CothSums.polynomial_chi_log_boundary P h0 h1
  have hIBP := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := F) (u' := F') (v := Real.log) (v' := fun r : ℝ => r⁻¹)
    (fun r hr => (P.hasDerivAt (CothSums.chi r)).comp r (CothSums.chi_hasDerivAt r))
    (fun r hr => Real.hasDerivAt_log (ne_of_gt hr))
    hFG hFR hboundary.1 hboundary.2
  have htest : CothSums.testMoment P = -(∫ r in Ioi (0 : ℝ), R r) := by
    simpa only [F, F', D, R, CothSums.testMoment, div_eq_mul_inv, zero_sub, sub_zero] using hIBP
  have hbij := CothSums.chi_positive_coordinate_bijective
  have himage : CothSums.chi '' Ioi (0 : ℝ) = Ioo 0 1 := hbij.image_eq
  have hderiv : ∀ r ∈ Ioi (0 : ℝ), HasDerivWithinAt CothSums.chi (D r) (Ioi 0) r :=
    fun r _ => (CothSums.chi_hasDerivAt r).hasDerivWithinAt
  have hpoint : ∀ r ∈ Ioi (0 : ℝ), |D r| • G (CothSums.chi r) = R r := by
    intro r hr
    have hd : 0 < D r := mul_pos hC (inv_pos.mpr (Real.sqrt_pos.2 (by positivity)))
    rw [abs_of_pos hd, smul_eq_mul]
    dsimp only [G, R, F']
    rw [Function.leftInverse_invFun chi_strict.injective r]
    ring
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv
    hbij.injOn G
  rw [himage] at hchange
  have hG : IntegrableOn G (Ioo 0 1) := by
    rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hbij.injOn]
    exact (integrableOn_congr_fun hpoint measurableSet_Ioi).mpr hR
  refine ⟨hG, ?_⟩
  change CothSums.testMoment P = -(∫ x in Ioo (0 : ℝ) 1, G x)
  rw [htest, hchange]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => (hpoint r hr).symm)


theorem CothSums.polynomial_fourier_from_complex_data
    (U q : ℂ → ℂ)
    (hU1 : ∀ z : ℂ, U (z + 1) = -U z)
    (hUI : ∀ z : ℂ, U (z + Complex.I) = -U z)
    (hq : DifferentiableOn ℂ q (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ℂ
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2)))
    (hqu : ∀ z : ℂ, z ≠ 0 → q z = z * U z)
    (hq0 : q 0 = 1)
    (hreal : ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 →
      U (x : ℂ) = (deriv (fun t : ℝ => Real.log (Function.invFun CothSums.chi t)) x : ℂ)) :
∀ P : Polynomial ℝ, P.eval 0 = 0 → P.eval 1 = 0 → CothSums.testMoment P = 2 * ∑' n : ℕ, (Real.tanh (Real.pi * (2 * (n : ℝ) + 1) / 2) / (2 * (n : ℝ) + 1)) * CothSums.cosineTest P n := by
  have hcoeff : ∀ n : ℕ, 0 < n →
      (∫ x in (0 : ℝ)..1,
        Real.log (Function.invFun CothSums.chi x) * Real.cos ((n : ℝ) * Real.pi * x)) =
        if Odd n then -(Real.tanh (Real.pi * (n : ℝ) / 2) / (n : ℝ)) else 0 := by
    intro n hn
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
    by_cases ho : Odd n
    · rw [if_pos ho]
      exact CothSums.inverse_log_odd_cosine_of_complex_data U q hU1 hUI hq hqu hq0 hreal n hn ho
    · rw [if_neg ho]
      obtain ⟨k, hk⟩ := (Nat.not_odd_iff_even.mp ho)
      have hn2 : n = 2 * k := by omega
      rw [hn2]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using CothSums.chi_invFun_log_even_cosine_integral k
  intro P h0 h1
  have hpair := CothSums.Fourier.odd_coefficient_polynomial_pairing
    (fun x : ℝ => Real.log (Function.invFun CothSums.chi x))
    CothSums.inverse_log_L1_L2.2 hcoeff P h0 h1
  have hcoord := (CothSums.polynomial_coordinate_transfer P h0 h1).2
  rw [hcoord]
  have hleft : (∫ x in (0 : ℝ)..1,
      Real.log (Function.invFun CothSums.chi x) * P.derivative.eval x) =
      ∫ x in Set.Ioo (0 : ℝ) 1,
        P.derivative.eval x * Real.log (Function.invFun CothSums.chi x) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
    congr 1
    ext x
    ring
  rw [hleft] at hpair
  simp only [CothSums.cosineTest, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] at hpair ⊢
  linarith


set_option autoImplicit false


open Complex


private theorem square_rotation :
 let L := CothSums.lemniscaticPeriodPair
 (∀ z : ℂ, L.weierstrassP (Complex.I * z) = -L.weierstrassP z) ∧
 (∀ z : ℂ, L.derivWeierstrassP (Complex.I * z) = Complex.I * L.derivWeierstrassP z) ∧
 L.g₃ = 0 ∧ L.weierstrassP 1 = 0 ∧ L.derivWeierstrassP 1 = 0 := by
  let L := CothSums.lemniscaticPeriodPair
  change (∀ z : ℂ, L.weierstrassP (Complex.I * z) = -L.weierstrassP z) ∧
    (∀ z : ℂ, L.derivWeierstrassP (Complex.I * z) = Complex.I * L.derivWeierstrassP z) ∧
    L.g₃ = 0 ∧ L.weierstrassP 1 = 0 ∧ L.derivWeierstrassP 1 = 0
  have hmem (z : ℂ) (hz : z ∈ L.lattice) : Complex.I * z ∈ L.lattice := by
    obtain ⟨m, n, he⟩ := PeriodPair.mem_lattice.mp hz
    apply PeriodPair.mem_lattice.mpr
    refine ⟨n, -m, ?_⟩
    rw [← he]
    dsimp [L, CothSums.lemniscaticPeriodPair]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  let e : L.lattice ≃ L.lattice :=
    { toFun := fun z => ⟨Complex.I * z, hmem z z.property⟩
      invFun := fun z => ⟨-(Complex.I * z), L.lattice.neg_mem (hmem z z.property)⟩
      left_inv := by
        intro z
        apply Subtype.ext
        change -(Complex.I * (Complex.I * (z : ℂ))) = z
        rw [← mul_assoc, show Complex.I * Complex.I = (-1 : ℂ) by norm_num]
        ring
      right_inv := by
        intro z
        apply Subtype.ext
        change Complex.I * -(Complex.I * (z : ℂ)) = z
        rw [mul_neg, ← mul_assoc, show Complex.I * Complex.I = (-1 : ℂ) by norm_num]
        ring }
  have he (z : L.lattice) : (e z : ℂ) = Complex.I * (z : ℂ) := rfl
  have hp (z : ℂ) : L.weierstrassP (Complex.I * z) = -L.weierstrassP z := by
    calc
      _ = ∑' l : L.lattice, (1 / (Complex.I * z - (e l : ℂ)) ^ 2 - 1 / (e l : ℂ) ^ 2) :=
        (e.tsum_eq (fun l : L.lattice =>
          (1 / (Complex.I * z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2))).symm
      _ = ∑' l : L.lattice, -(1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2) := by
        apply tsum_congr
        intro l
        rw [he, show Complex.I * z - Complex.I * (l : ℂ) = Complex.I * (z - (l : ℂ)) by ring]
        simp only [mul_pow, Complex.I_sq, neg_one_mul, one_div, inv_neg]
        ring
      _ = _ := tsum_neg
  have hpd (z : ℂ) : L.derivWeierstrassP (Complex.I * z) = Complex.I * L.derivWeierstrassP z := by
    calc
      _ = -(∑' l : L.lattice, 2 / (Complex.I * z - (e l : ℂ)) ^ 3) := by
        exact congrArg Neg.neg (e.tsum_eq (fun l : L.lattice =>
          2 / (Complex.I * z - (l : ℂ)) ^ 3)).symm
      _ = -(∑' l : L.lattice, Complex.I * (2 / (z - (l : ℂ)) ^ 3)) := by
        congr 1
        apply tsum_congr
        intro l
        rw [he, show Complex.I * z - Complex.I * (l : ℂ) = Complex.I * (z - (l : ℂ)) by ring]
        simp only [mul_pow, show Complex.I ^ 3 = -Complex.I by norm_num,
          div_eq_mul_inv, mul_inv_rev, inv_neg, Complex.inv_I]
        ring
      _ = _ := by rw [tsum_mul_left]; change -(Complex.I * _) = Complex.I * -_; ring
  have hG : L.G 6 = 0 := by
    have hh := e.tsum_eq (fun l : L.lattice => ((l : ℂ) ^ 6)⁻¹)
    have hterm (l : L.lattice) : ((e l : ℂ) ^ 6)⁻¹ = -((l : ℂ) ^ 6)⁻¹ := by
      rw [he, mul_pow, show Complex.I ^ 6 = -1 by
        rw [show Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 by ring, Complex.I_sq]
        norm_num]
      simp only [neg_one_mul, inv_neg]
    simp_rw [hterm] at hh
    rw [tsum_neg] at hh
    change -L.G 6 = L.G 6 at hh
    exact (CharZero.eq_neg_self_iff).mp hh.symm
  have hg3 : L.g₃ = 0 := by simp only [PeriodPair.g₃, hG, mul_zero]
  have hω2 : (1 - Complex.I : ℂ) ∈ L.lattice := by exact L.ω₂_mem_lattice
  have hp1 : L.weierstrassP 1 = 0 := by
    have hh := L.weierstrassP_add_coe Complex.I ⟨1 - Complex.I, hω2⟩
    have he : Complex.I + (1 - Complex.I) = (1 : ℂ) := by ring
    change L.weierstrassP (Complex.I + (1 - Complex.I)) = L.weierstrassP Complex.I at hh
    rw [he, show Complex.I = Complex.I * 1 by ring, hp] at hh
    exact (CharZero.eq_neg_self_iff).mp hh
  have htwo : (2 : ℂ) ∈ L.lattice := by
    have hh := L.lattice.add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice
    convert! hh using 1
    dsimp [L, CothSums.lemniscaticPeriodPair]
    ring
  have hpd1 : L.derivWeierstrassP 1 = 0 := by
    have hh := L.derivWeierstrassP_add_coe (-1) ⟨2, htwo⟩
    change L.derivWeierstrassP (-1 + 2) = L.derivWeierstrassP (-1) at hh
    rw [show (-1 : ℂ) + 2 = 1 by ring, L.derivWeierstrassP_neg] at hh
    exact (CharZero.eq_neg_self_iff).mp hh
  exact ⟨hp, hpd, hg3, hp1, hpd1⟩


set_option maxRecDepth 3000


set_option maxHeartbeats 250000


private theorem half_product_order (x : ℂ) :
    0 ≤ meromorphicOrderAt (fun z : ℂ =>
      CothSums.lemniscaticPeriodPair.weierstrassP z *
        CothSums.lemniscaticPeriodPair.weierstrassP (z+1)) x := by
  classical
  let L := CothSums.lemniscaticPeriodPair
  let P := L.weierstrassP
  let f : ℂ → ℂ := fun w => P w * P (w + 1)
  have hrot := square_rotation
  change (∀ w : ℂ, L.weierstrassP (Complex.I * w) = -L.weierstrassP w) ∧
    (∀ w : ℂ, L.derivWeierstrassP (Complex.I * w) = Complex.I * L.derivWeierstrassP w) ∧
    L.g₃ = 0 ∧ L.weierstrassP 1 = 0 ∧ L.derivWeierstrassP 1 = 0 at hrot
  have hp1 : P 1 = 0 := hrot.2.2.2.1
  have hpd1 : L.derivWeierstrassP 1 = 0 := hrot.2.2.2.2
  have hnot : (1 : ℂ) ∉ L.lattice := by
    intro hm
    obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp hm
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    dsimp [L, CothSums.lemniscaticPeriodPair] at hr hi
    have hr' : (1 : ℝ) = (m : ℝ) + (n : ℝ) := by simpa using hr.symm
    have hi' : (0 : ℝ) = (m : ℝ) - (n : ℝ) := by simpa [sub_eq_add_neg] using hi.symm
    have hri : (1 : ℤ) = m + n := by exact_mod_cast hr'
    have hii : (0 : ℤ) = m - n := by exact_mod_cast hi'
    omega
  have htwo : (2 : ℂ) ∈ L.lattice := by
    convert L.lattice.add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice using 1
    dsimp [L, CothSums.lemniscaticPeriodPair]
    ring
  have hf : Meromorphic f := by
    have hm := L.meromorphic_weierstrassP
    intro x
    exact (hm x).mul ((hm (x+1)).comp_analyticAt (g := fun w : ℂ => w+1) (by fun_prop))
  have hper (w p : ℂ) (hp : p ∈ L.lattice) : f (w+p) = f w := by
    dsimp [f,P]
    rw [L.weierstrassP_add_coe w ⟨p,hp⟩]
    rw [show w + p + 1 = w + 1 + p by ring,
      L.weierstrassP_add_coe (w+1) ⟨p,hp⟩]
  have hper1 (w : ℂ) : f (w+1) = f w := by
    dsimp [f,P]
    rw [show w+1+1 = w+2 by ring,L.weierstrassP_add_coe w ⟨2,htwo⟩]
    ring
  let F : ℂ → ℂ := fun w => P (w+1)
  have hFa : AnalyticAt ℂ F 0 := by
    have ha : AnalyticAt ℂ P ((0:ℂ)+1) := by simpa [P] using L.analyticOnNhd_weierstrassP 1 hnot
    exact ha.comp (f := fun w : ℂ => w+1) (by fun_prop)
  have hF0 : F 0 = 0 := by simpa [F] using hp1
  have hF'0 : deriv F 0 = 0 := by
    simpa [F,P,deriv_comp_add_const,L.deriv_weierstrassP] using hpd1
  have hForder : (2 : ℕ∞) ≤ analyticOrderAt F 0 := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n:=2) hFa).mpr
    intro i hi
    obtain rfl | rfl : i=0 ∨ i=1 := by omega
    · simpa using hF0
    · simpa using hF'0
  have hFmorder : (2 : WithTop ℤ) ≤ meromorphicOrderAt F 0 := by
    rw [hFa.meromorphicOrderAt_eq]
    have hmono : Monotone (ENat.map (fun n : ℕ => (n : ℤ))) :=
      ENat.monotone_map_iff.mpr Nat.mono_cast
    simpa using hmono hForder
  have ho0 : 0 ≤ meromorphicOrderAt f 0 := by
    change 0 ≤ meromorphicOrderAt (L.weierstrassP * F) 0
    rw [meromorphicOrderAt_mul (L.meromorphic_weierstrassP 0) hFa.meromorphicAt,
      L.order_weierstrassP 0 (zero_mem L.lattice)]
    simpa [add_comm] using add_le_add_left hFmorder (-2 : WithTop ℤ)
  have ho (x : ℂ) : 0 ≤ meromorphicOrderAt f x := by
    by_cases hx : x ∈ L.lattice
    · have he : meromorphicOrderAt f x = meromorphicOrderAt f 0 := by
        have he := meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (f:=f) (c:=x) (x:=0)
        simp only [zero_add] at he
        have he' : (fun w => f (w+x)) = f := funext (fun w => hper w x hx)
        rw [he'] at he
        exact he.symm
      rwa [he]
    by_cases hx1 : x+1 ∈ L.lattice
    · have he1 : meromorphicOrderAt f x = meromorphicOrderAt f (x+1) := by
        rw [← meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (c:=1) (x:=x)]
        simp_rw [hper1]
      have he2 : meromorphicOrderAt f (x+1) = meromorphicOrderAt f 0 := by
        have he := meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (f:=f) (c:=x+1) (x:=0)
        simp only [zero_add] at he
        have he' : (fun w => f (w+(x+1))) = f := funext (fun w => hper w (x+1) hx1)
        rw [he'] at he
        exact he.symm
      rwa [he1,he2]
    · have ha : AnalyticAt ℂ f x :=
        (L.analyticOnNhd_weierstrassP x hx).mul
          ((L.analyticOnNhd_weierstrassP (x+1) hx1).comp (f:= fun w : ℂ => w+1) (by fun_prop))
      exact ha.meromorphicOrderAt_nonneg
  exact ho x


open Filter


open scoped Topology


set_option maxHeartbeats 350000


private theorem half_product_regularized_constant (z : ℂ) :
    let f : ℂ → ℂ := fun w => CothSums.lemniscaticPeriodPair.weierstrassP w *
      CothSums.lemniscaticPeriodPair.weierstrassP (w+1)
    toMeromorphicNFOn f Set.univ z = toMeromorphicNFOn f Set.univ 0 := by
  classical
  let L := CothSums.lemniscaticPeriodPair
  let P := L.weierstrassP
  let f : ℂ → ℂ := fun w => P w * P (w+1)
  have hf : Meromorphic f := by
    have hm := L.meromorphic_weierstrassP
    intro x
    exact (hm x).mul ((hm (x+1)).comp_analyticAt (g := fun w : ℂ => w+1) (by fun_prop))
  have hper (w p : ℂ) (hp : p ∈ L.lattice) : f (w+p) = f w := by
    dsimp [f,P]
    rw [L.weierstrassP_add_coe w ⟨p,hp⟩]
    rw [show w + p + 1 = w + 1 + p by ring,
      L.weierstrassP_add_coe (w+1) ⟨p,hp⟩]
  have ho (x : ℂ) : 0 ≤ meromorphicOrderAt f x := half_product_order x
  let R := toMeromorphicNFOn f Set.univ
  have hmOn : MeromorphicOn f Set.univ := fun w _ => hf w
  have hRa (x : ℂ) : AnalyticAt ℂ R x := by
    apply (meromorphicNFOn_toMeromorphicNFOn f Set.univ (Set.mem_univ x)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    simpa only [R,meromorphicOrderAt_toMeromorphicNFOn hmOn (Set.mem_univ x)] using ho x
  have hRper (w p : ℂ) (hp : p ∈ L.lattice) : R (w+p) = R w := by
    have ht : Tendsto (fun v : ℂ => v+p) (𝓝[≠] w) (𝓝[≠] (w+p)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (continuousAt_id.add_const p).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with v hv
        simpa using hv
    have he : (fun v : ℂ => R (v+p)) =ᶠ[𝓝[≠] w] R := by
      filter_upwards [(hmOn.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ (w+p))).comp_tendsto ht,
        hmOn.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ w)] with v hv1 hv2
      change R (v+p) = f (v+p) at hv1
      change R v = f v at hv2
      rw [hv1,hv2,hper v p hp]
    have hc : ContinuousAt (fun v : ℂ => R (v+p)) w :=
      (hRa (w+p)).continuousAt.comp (f:=fun v : ℂ => v+p) (by fun_prop)
    exact ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hc (hRa w).continuousAt).mp he).eq_of_nhds
  have hRd : Differentiable ℂ R := fun x => (hRa x).differentiableAt
  have hconst (x : ℂ) : R x = R 0 :=
    hRd.apply_eq_apply_of_bounded (IsZLattice.isCompact_range_of_periodic L.lattice _
      hRd.continuous hRper).isBounded x 0
  exact hconst z


private theorem square_second_derivative (z : ℂ) (hz : z ∉ CothSums.lemniscaticPeriodPair.lattice) :
  deriv CothSums.lemniscaticPeriodPair.derivWeierstrassP z =
    6 * CothSums.lemniscaticPeriodPair.weierstrassP z ^ 2 - CothSums.lemniscaticPeriodPair.g₂ / 2 := by
  let L := CothSums.lemniscaticPeriodPair
  have hrot := square_rotation
  change (∀ z : ℂ, L.weierstrassP (Complex.I * z) = -L.weierstrassP z) ∧
    (∀ z : ℂ, L.derivWeierstrassP (Complex.I * z) = Complex.I * L.derivWeierstrassP z) ∧
    L.g₃ = 0 ∧ L.weierstrassP 1 = 0 ∧ L.derivWeierstrassP 1 = 0 at hrot
  have hnot : (1 : ℂ) ∉ L.lattice := by
    intro hm
    obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp hm
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    dsimp [L, CothSums.lemniscaticPeriodPair] at hr hi
    have hr' : (1 : ℝ) = (m : ℝ) + (n : ℝ) := by simpa using hr.symm
    have hi' : (0 : ℝ) = (m : ℝ) - (n : ℝ) := by simpa [sub_eq_add_neg] using hi.symm
    have hri : (1 : ℤ) = m + n := by exact_mod_cast hr'
    have hii : (0 : ℤ) = m - n := by exact_mod_cast hi'
    omega
  have hc : IsPreconnected (L.lattice : Set ℂ)ᶜ := by
    exact (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
  have hprod (w : ℂ) (hw : w ∉ L.lattice) :
      L.derivWeierstrassP w * (2 * deriv L.derivWeierstrassP w -
        12 * L.weierstrassP w ^ 2 + L.g₂) = 0 := by
    have hp := (L.differentiableOn_weierstrassP w hw).differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hw)
    have hd := (L.differentiableOn_derivWeierstrassP w hw).differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hw)
    have hp' : HasDerivAt L.weierstrassP (L.derivWeierstrassP w) w := by
      simpa only [L.deriv_weierstrassP] using hp.hasDerivAt
    have he : (fun v => L.derivWeierstrassP v ^ 2) =ᶠ[𝓝 w]
        (fun v => 4 * L.weierstrassP v ^ 3 - L.g₂ * L.weierstrassP v - L.g₃) := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hw] with v hv
      exact L.derivWeierstrassP_sq v hv
    have hl := (hd.hasDerivAt.pow 2).congr_of_eventuallyEq he.symm
    have hr := (((hp'.pow 3).const_mul 4).sub (hp'.const_mul L.g₂)).sub_const L.g₃
    have hh := hl.unique hr
    dsimp at hh
    linear_combination hh
  have hg : AnalyticOnNhd ℂ (fun w => 2 * deriv L.derivWeierstrassP w -
      12 * L.weierstrassP w ^ 2 + L.g₂) (L.lattice : Set ℂ)ᶜ := by
    intro w hw
    have h1 := L.analyticOnNhd_derivWeierstrassP.deriv w hw
    have h2 := L.analyticOnNhd_weierstrassP w hw
    fun_prop
  rcases L.analyticOnNhd_derivWeierstrassP.eq_zero_or_eq_zero_of_mul_eq_zero hg hprod hc with hzero | hzero
  · have heq : Set.EqOn L.weierstrassP (fun _ => (0 : ℂ)) (L.lattice : Set ℂ)ᶜ := by
      apply L.isClosed_lattice.isOpen_compl.eqOn_of_deriv_eq hc
        L.differentiableOn_weierstrassP (differentiableOn_const (0 : ℂ))
      · intro w hw
        simpa only [L.deriv_weierstrassP, deriv_const] using hzero w hw
      · exact hnot
      · exact hrot.2.2.2.1
    have hall : L.weierstrassP = fun _ => 0 := by
      funext w
      by_cases hw : w ∈ L.lattice
      · exact L.weierstrassP_coe ⟨w,hw⟩
      · exact heq hw
    exact False.elim (L.not_continuousAt_weierstrassP 0 (zero_mem L.lattice)
      (by rw [hall]; exact continuousAt_const))
  · have hh := hzero z hz
    change deriv L.derivWeierstrassP z = _
    linear_combination hh / 2

attribute [local fun_prop] AnalyticAt.contDiffAt


set_option maxHeartbeats 350000


private theorem half_period_product (z : ℂ)
    (hz : z ∉ CothSums.lemniscaticPeriodPair.lattice)
    (hz1 : z + 1 ∉ CothSums.lemniscaticPeriodPair.lattice) :
    CothSums.lemniscaticPeriodPair.weierstrassP z *
      CothSums.lemniscaticPeriodPair.weierstrassP (z + 1) =
        -CothSums.lemniscaticPeriodPair.g₂ / 4 := by
  classical
  let L := CothSums.lemniscaticPeriodPair
  let P := L.weierstrassP
  let f : ℂ → ℂ := fun w => P w * P (w+1)
  let F : ℂ → ℂ := fun w => P (w+1)
  have hrot := square_rotation
  change (∀ w : ℂ, L.weierstrassP (Complex.I * w) = -L.weierstrassP w) ∧
    (∀ w : ℂ, L.derivWeierstrassP (Complex.I * w) = Complex.I * L.derivWeierstrassP w) ∧
    L.g₃ = 0 ∧ L.weierstrassP 1 = 0 ∧ L.derivWeierstrassP 1 = 0 at hrot
  have hp1 : P 1 = 0 := hrot.2.2.2.1
  have hpd1 : L.derivWeierstrassP 1 = 0 := hrot.2.2.2.2
  have hnot : (1 : ℂ) ∉ L.lattice := by
    intro hm
    obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp hm
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    dsimp [L, CothSums.lemniscaticPeriodPair] at hr hi
    have hr' : (1 : ℝ) = (m : ℝ) + (n : ℝ) := by simpa using hr.symm
    have hi' : (0 : ℝ) = (m : ℝ) - (n : ℝ) := by simpa [sub_eq_add_neg] using hi.symm
    have hri : (1 : ℤ) = m + n := by exact_mod_cast hr'
    have hii : (0 : ℤ) = m - n := by exact_mod_cast hi'
    omega
  have hf : Meromorphic f := by
    intro x
    exact (L.meromorphic_weierstrassP x).mul
      ((L.meromorphic_weierstrassP (x+1)).comp_analyticAt (g:=fun w : ℂ => w+1) (by fun_prop))
  have hmOn : MeromorphicOn f Set.univ := fun w _ => hf w
  let R := toMeromorphicNFOn f Set.univ
  have hconst (x : ℂ) : R x = R 0 := half_product_regularized_constant x
  have hFa : AnalyticAt ℂ F 0 := by
    have ha : AnalyticAt ℂ P ((0:ℂ)+1) := by simpa [P] using L.analyticOnNhd_weierstrassP 1 hnot
    exact ha.comp (f:=fun w : ℂ => w+1) (by fun_prop)
  have hF0 : F 0 = 0 := by simpa [F] using hp1
  have hF'0 : deriv F 0 = 0 := by
    simpa [F,P,deriv_comp_add_const,L.deriv_weierstrassP] using hpd1
  let K := R 0
  have hFK : f =ᶠ[𝓝[≠] (0 : ℂ)] (fun _ => K) := by
    filter_upwards [hmOn.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ (0:ℂ))] with w hw
    exact hw.symm.trans (hconst w)
  let A : ℂ → ℂ := fun w => (L.weierstrassPExcept 0 w * w^2 + 1) * F w
  have hAeq : A =ᶠ[𝓝 (0 : ℂ)] (fun w => K * w^2) := by
    apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
    · filter_upwards [hFK,self_mem_nhdsWithin] with w hw hne
      have hpp := L.weierstrassPExcept_add ⟨0,zero_mem L.lattice⟩ w
      have hpp' : P w = L.weierstrassPExcept 0 w + 1 / w^2 := by simpa [P] using hpp.symm
      change (L.weierstrassPExcept 0 w * w^2 + 1) * P (w+1) = K*w^2
      change P w * P (w+1) = K at hw
      have hw0 : w ≠ 0 := by simpa using hne
      calc
        _ = w^2 * (P w * P (w+1)) := by
          rw [hpp']
          field_simp [hw0]
          <;> ring
        _ = K*w^2 := by rw [hw]; ring
    · simp [A,F,hp1]
  have hF2 : iteratedDeriv 2 F 0 = -L.g₂/2 := by
    change iteratedDeriv 2 (fun w : ℂ => P (w+1)) 0 = _
    rw [iteratedDeriv_comp_add_const]
    simp only [zero_add]
    change iteratedDeriv 2 P 1 = _
    rw [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ',iteratedDeriv_one]
    change deriv (deriv L.weierstrassP) 1 = _
    rw [L.deriv_weierstrassP,square_second_derivative 1 hnot]
    change 6 * P 1 ^ 2 - L.g₂/2 = _
    rw [hp1]
    ring
  have haA : AnalyticAt ℂ (fun w => L.weierstrassPExcept 0 w * w^2+1) 0 := by
    have := L.analyticAt_weierstrassPExcept 0
    fun_prop
  have hprodDeriv := iteratedDeriv_fun_mul (n:=2) (x:=(0:ℂ))
    (f:=fun w : ℂ => L.weierstrassPExcept 0 w*w^2+1) (g:=F)
    haA.contDiffAt hFa.contDiffAt
  have he2 := hAeq.iteratedDeriv_eq (n:=2)
  rw [hprodDeriv] at he2
  simp only [Finset.sum_range_succ,Finset.sum_range_zero] at he2
  norm_num only [Nat.choose_zero_right,Nat.choose_self,iteratedDeriv_zero,iteratedDeriv_one,
    hF0,hF'0,hF2,iteratedDeriv_const_mul_field,iteratedDeriv_pow] at he2
  have hK : K = -L.g₂/4 := by linear_combination -1 / 2 * he2
  have haz : AnalyticAt ℂ f z :=
    (L.analyticOnNhd_weierstrassP z hz).mul
      ((L.analyticOnNhd_weierstrassP (z+1) hz1).comp (f:=fun w : ℂ => w+1) (by fun_prop))
  have heR : R z = f z := by
    change toMeromorphicNFOn f Set.univ z = f z
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hmOn (Set.mem_univ z),
      toMeromorphicNFAt_eq_self.mpr haz.meromorphicNFAt]
  change f z = -L.g₂/4
  exact heR.symm.trans ((hconst z).trans hK)


open MeasureTheory


private theorem square_g2_negative : CothSums.lemniscaticPeriodPair.g₂.re < 0 := by
  let L := CothSums.lemniscaticPeriodPair
  let f : ℕ → ℤ → ℝ := fun s k => 1 / (k : ℝ) ^ s
  have hz (s : ℕ) (hs : 0 < s) (he : Even s) (c : ℝ)
      (hh : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ s) c) :
      HasSum (f s) (2 * c) := by
    have hv : (∑ i ∈ Finset.range 1, (1 : ℝ) / (i : ℝ) ^ s) = 0 := by simp [hs.ne']
    have hi := (hasSum_nat_add_iff' 1).mpr hh
    have hshift : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ s) c := by
      simpa only [Nat.cast_add, Nat.cast_one, hv, sub_zero] using hi
    have hneg : HasSum (fun n : ℕ => f s (-(n + 1 : ℤ))) c := by
      simpa only [f, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, he.neg_pow]
        using hshift
    have hnat : HasSum (fun n : ℕ => f s n) c := by
      simpa only [f, Int.cast_natCast] using hh
    simpa only [two_mul] using hnat.of_nat_of_neg_add_one hneg
  have h2 : HasSum (f 2) (Real.pi ^ 2 / 3) := by
    convert! hz 2 (by norm_num) (by decide) _ hasSum_zeta_two using 1 <;> ring
  have h4 : HasSum (f 4) (Real.pi ^ 4 / 45) := by
    convert! hz 4 (by norm_num) (by decide) _ hasSum_zeta_four using 1 <;> ring
  have hf2 (k : ℤ) : 0 ≤ f 2 k := by dsimp [f]; positivity
  have hf4 (k : ℤ) : 0 ≤ f 4 k := by dsimp [f]; positivity
  let d : ℤ → ℝ := fun k => if k = 0 then 1 else 0
  have hd : HasSum d 1 := by simpa only [d] using hasSum_ite_eq (0 : ℤ) (1 : ℝ)
  have hdnonneg (k : ℤ) : 0 ≤ d k := by dsimp [d]; split_ifs <;> norm_num
  let A1 : ℤ × ℤ → ℝ := fun p => f 4 p.1 * d p.2
  let A2 : ℤ × ℤ → ℝ := fun p => d p.1 * f 4 p.2
  let B : ℤ × ℤ → ℝ := fun p => (1 / 4) * (f 2 p.1 * f 2 p.2)
  have hA1 : Summable A1 := h4.summable.mul_of_nonneg hd.summable hf4 hdnonneg
  have hA2 : Summable A2 := hd.summable.mul_of_nonneg h4.summable hdnonneg hf4
  have hB0 : Summable (fun p : ℤ × ℤ => f 2 p.1 * f 2 p.2) :=
    h2.summable.mul_of_nonneg h2.summable hf2 hf2
  have hB : Summable B := hB0.mul_left (1 / 4)
  have hA1val : (∑' p : ℤ × ℤ, A1 p) = Real.pi ^ 4 / 45 := by
    have hh := h4.summable.tsum_mul_tsum hd.summable hA1
    rw [h4.tsum_eq, hd.tsum_eq, mul_one] at hh
    exact hh.symm
  have hA2val : (∑' p : ℤ × ℤ, A2 p) = Real.pi ^ 4 / 45 := by
    have hh := hd.summable.tsum_mul_tsum h4.summable hA2
    rw [hd.tsum_eq, h4.tsum_eq, one_mul] at hh
    exact hh.symm
  have hBval : (∑' p : ℤ × ℤ, B p) = (1 / 4) * (Real.pi ^ 2 / 3) ^ 2 := by
    rw [show B = (fun p => (1 / 4) * (f 2 p.1 * f 2 p.2)) by rfl, tsum_mul_left]
    have hh := h2.summable.tsum_mul_tsum h2.summable hB0
    rw [h2.tsum_eq] at hh
    rw [← hh]
    ring
  let F : ℤ × ℤ → ℂ := fun p => (((p.1 : ℂ) - Complex.I * (p.2 : ℂ)) ^ 4)⁻¹
  have hnorm (p : ℤ × ℤ) : ‖F p‖ = 1 / (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ 2) := by
    have he : ‖(p.1 : ℂ) - Complex.I * (p.2 : ℂ)‖ ^ 4 =
        ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, ← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, pow_two]
    dsimp [F]
    rw [norm_inv, norm_pow, he]
    simp only [one_div]
  have hbound (p : ℤ × ℤ) (hm : p.1 ≠ 0) (hn : p.2 ≠ 0) : ‖F p‖ ≤ B p := by
    have hm' : (p.1 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
    have hn' : (p.2 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
    rw [hnorm]
    calc
      _ ≤ 1 / (4 * (p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2) := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [sq_nonneg ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2)]
      _ = B p := by dsimp [B, f]; field_simp <;> ring
  have hFaxis1 (m : ℤ) : F (m, 0) = (f 4 m : ℂ) := by
    dsimp [F, f]
    push_cast
    simp
  have hFaxis2 (n : ℤ) : F (0, n) = (f 4 n : ℂ) := by
    have hI : (-Complex.I) ^ 4 = (1 : ℂ) := by
      rw [show (-Complex.I) ^ 4 = ((-Complex.I) ^ 2) ^ 2 by ring]
      norm_num
    dsimp only [F, f]
    simp only [Int.cast_zero, zero_sub, ← neg_mul, mul_pow, hI, one_mul]
    push_cast
    simp only [one_div]
  have hmaj (p : ℤ × ℤ) : ‖F p‖ ≤ A1 p + A2 p + B p := by
    by_cases hm : p.1 = 0
    · rcases p with ⟨m,n⟩
      dsimp only at hm
      subst m
      rw [hFaxis2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf4 n)]
      simp [A1, A2, B, d, f]
    · by_cases hn : p.2 = 0
      · rcases p with ⟨m,n⟩
        dsimp only at hn
        subst n
        rw [hFaxis1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf4 m)]
        simp [A1, A2, B, d, f]
      · simpa only [A1, A2, d, if_neg hm, if_neg hn, zero_mul, mul_zero, zero_add] using hbound p hm hn
  have hlow (p : ℤ × ℤ) : A1 p + A2 p - B p ≤ (F p).re := by
    by_cases hm : p.1 = 0
    · rcases p with ⟨m,n⟩
      dsimp only at hm
      subst m
      rw [hFaxis2, Complex.ofReal_re]
      simp [A1, A2, B, d, f]
    · by_cases hn : p.2 = 0
      · rcases p with ⟨m,n⟩
        dsimp only at hn
        subst n
        rw [hFaxis1, Complex.ofReal_re]
        simp [A1, A2, B, d, f]
      · have hh := (abs_le.mp (Complex.abs_re_le_norm (F p))).1
        have hb := hbound p hm hn
        simp only [A1, A2, d, if_neg hm, if_neg hn, zero_mul, mul_zero, zero_add, zero_sub]
        linarith
  have hFs : Summable F := ((hA1.add hA2).add hB).of_norm_bounded hmaj
  have hFr : Summable (fun p => (F p).re) := Complex.reCLM.summable hFs
  have hLower : Real.pi ^ 4 / 60 ≤ (∑' p : ℤ × ℤ, F p).re := by
    have hh := ((hA1.add hA2).sub hB).tsum_le_tsum hlow hFr
    rw [(hA1.add hA2).tsum_sub hB, hA1.tsum_add hA2, hA1val, hA2val, hBval] at hh
    rw [Complex.re_tsum hFs]
    convert! hh using 1 <;> ring
  have hterm (p : ℤ × ℤ) :
      (((L.latticeEquivProd.symm p : L.lattice) : ℂ) ^ 4)⁻¹ = -(1 / 4 : ℂ) * F p := by
    rw [L.latticeEquiv_symm_apply]
    change (((p.1 : ℂ) * (1 + Complex.I) + (p.2 : ℂ) * (1 - Complex.I)) ^ 4)⁻¹ = _
    rw [show (p.1 : ℂ) * (1 + Complex.I) + (p.2 : ℂ) * (1 - Complex.I) =
      (1 + Complex.I) * ((p.1 : ℂ) - Complex.I * (p.2 : ℂ)) by
        ring_nf; simp only [Complex.I_sq]; ring, mul_pow]
    have he : (1 + Complex.I) ^ 4 = (-4 : ℂ) := by
      norm_num [Complex.ext_iff, pow_succ, Complex.mul_re, Complex.mul_im]
    rw [he, mul_inv_rev]
    dsimp [F]
    norm_num
    <;> ring
  have hG : L.G 4 = -(1 / 4 : ℂ) * ∑' p : ℤ × ℤ, F p := by
    calc
      _ = ∑' p : ℤ × ℤ, (((L.latticeEquivProd.symm p : L.lattice) : ℂ) ^ 4)⁻¹ :=
        (L.latticeEquivProd.toEquiv.symm.tsum_eq (fun l : L.lattice => ((l : ℂ) ^ 4)⁻¹)).symm
      _ = _ := by simp only [hterm, tsum_mul_left]
  change L.g₂.re < 0
  rw [PeriodPair.g₂, hG, Complex.mul_re, Complex.mul_re]
  norm_num
  have hp : 0 < Real.pi ^ 4 / 60 := by positivity
  nlinarith [hLower]


set_option maxHeartbeats 400000


theorem CothSums.square_lattice_log_derivative_antiperiodic :
    let L := CothSums.lemniscaticPeriodPair
    let U : ℂ → ℂ := fun z => -L.derivWeierstrassP z / (2*L.weierstrassP z)
    (∀ z : ℂ, U (z+1) = -U z) ∧
      (∀ z : ℂ, U (z+Complex.I) = -U z) := by
  classical
  let L := CothSums.lemniscaticPeriodPair
  let P := L.weierstrassP
  let D := L.derivWeierstrassP
  let U : ℂ → ℂ := fun w => -D w / (2*P w)
  change (∀ z : ℂ, U (z+1) = -U z) ∧ (∀ z : ℂ, U (z+Complex.I) = -U z)
  have hgn : L.g₂ ≠ 0 := by
    intro he
    have hh := square_g2_negative
    change L.g₂.re < 0 at hh
    simp [he] at hh
  have hc : -L.g₂/4 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hgn) (by norm_num)
  have hpd1 : D 1 = 0 := square_rotation.2.2.2.2
  have htwo : (2 : ℂ) ∈ L.lattice := by
    convert L.lattice.add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice using 1
    dsimp [L,CothSums.lemniscaticPeriodPair]
    ring
  have hUper (w p : ℂ) (hp : p ∈ L.lattice) : U (w+p) = U w := by
    dsimp [U,D,P]
    rw [L.derivWeierstrassP_add_coe w ⟨p,hp⟩,L.weierstrassP_add_coe w ⟨p,hp⟩]
  have hUzero (w : ℂ) (hw : w ∈ L.lattice) : U w = 0 := by
    dsimp [U,D,P]
    rw [L.derivWeierstrassP_coe ⟨w,hw⟩]
    simp
  have hUhalfzero (w : ℂ) (hw : w ∈ L.lattice) : U (w+1) = 0 := by
    have hh := L.derivWeierstrassP_add_coe 1 ⟨w,hw⟩
    change D (1+w) = D 1 at hh
    rw [show 1+w = w+1 by ring,hpd1] at hh
    simp only [U,hh,neg_zero,zero_div]
  have hanti1 (z : ℂ) : U (z+1) = -U z := by
    by_cases hz : z ∈ L.lattice
    · rw [hUzero z hz,hUhalfzero z hz,neg_zero]
    by_cases hz1 : z+1 ∈ L.lattice
    · have h0 := hUhalfzero (z+1) hz1
      rw [show z+1+1 = z+2 by ring,hUper z 2 htwo] at h0
      rw [hUzero (z+1) hz1,h0,neg_zero]
    · have hp : P z * P (z+1) = -L.g₂/4 := half_period_product z hz hz1
      have hprod : P z * P (z+1) ≠ 0 := by rw [hp]; exact hc
      have hn0 : P z ≠ 0 := (mul_ne_zero_iff.mp hprod).1
      have hn1 : P (z+1) ≠ 0 := (mul_ne_zero_iff.mp hprod).2
      have hpz : HasDerivAt P (D z) z := by
        have hh := (L.differentiableOn_weierstrassP z hz).differentiableAt
          (L.isClosed_lattice.isOpen_compl.mem_nhds hz)
        simpa only [P,D,L.deriv_weierstrassP] using hh.hasDerivAt
      have hpz1 : HasDerivAt (fun w : ℂ => P (w+1)) (D (z+1)) z := by
        have hh := (L.differentiableOn_weierstrassP (z+1) hz1).differentiableAt
          (L.isClosed_lattice.isOpen_compl.mem_nhds hz1)
        have hd : HasDerivAt P (D (z+1)) (z+1) := by
          simpa only [P,D,L.deriv_weierstrassP] using hh.hasDerivAt
        exact HasDerivAt.comp_add_const z 1 hd
      have he : (fun w : ℂ => P w * P (w+1)) =ᶠ[𝓝 z] (fun _ => -L.g₂/4) := by
        filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz,
          (show ContinuousAt (fun w : ℂ => w+1) z by fun_prop).preimage_mem_nhds
            (L.isClosed_lattice.isOpen_compl.mem_nhds hz1)] with w hw hw1
        exact half_period_product w hw hw1
      have hsum := ((hpz.mul hpz1).congr_of_eventuallyEq he.symm).unique
        (hasDerivAt_const z (-L.g₂/4))
      dsimp only [U]
      field_simp [hn0,hn1]
      linear_combination -hsum
  have hi : Complex.I - 1 ∈ L.lattice := by
    convert L.lattice.neg_mem L.ω₂_mem_lattice using 1
    dsimp [L,CothSums.lemniscaticPeriodPair]
    ring
  refine ⟨hanti1,?_⟩
  intro z
  calc
    U (z+Complex.I) = U (z+1+(Complex.I-1)) := by congr 1; ring
    _ = U (z+1) := hUper (z+1) (Complex.I-1) hi
    _ = -U z := hanti1 z


set_option autoImplicit false


open Complex


set_option maxRecDepth 3000


set_option maxHeartbeats 250000


open Filter


open scoped Topology


set_option maxHeartbeats 350000


set_option maxHeartbeats 350000


open MeasureTheory


open Set


private theorem local_log_residue (L : PeriodPair) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧ q 0 = 1 ∧
      q =ᶠ[nhdsWithin (0 : ℂ) {0}ᶜ]
        (fun z : ℂ => z * (-L.derivWeierstrassP z / (2 * L.weierstrassP z))) := by
  let E : ℂ → ℂ := L.weierstrassPExcept 0
  let E' : ℂ → ℂ := L.derivWeierstrassPExcept 0
  let den : ℂ → ℂ := fun z => 1 + z ^ 2 * E z
  let q : ℂ → ℂ := fun z => (1 - z ^ 3 * E' z / 2) / den z
  have hE : AnalyticAt ℂ E 0 := L.analyticAt_weierstrassPExcept 0
  have hE' : AnalyticAt ℂ E' 0 := L.analyticAt_derivWeierstrassPExcept 0
  have hd : AnalyticAt ℂ den 0 := analyticAt_const.add ((analyticAt_id.pow 2).mul hE)
  have hn : AnalyticAt ℂ (fun z : ℂ => 1 - z ^ 3 * E' z / 2) 0 :=
    analyticAt_const.sub (((analyticAt_id.pow 3).mul hE').div_const)
  have hd0 : den 0 ≠ 0 := by norm_num [den]
  refine ⟨q, hn.div hd hd0, ?_, ?_⟩
  · norm_num [q, den]
  · have hnear : ∀ᶠ z : ℂ in nhds (0 : ℂ), den z ≠ 0 := hd.continuousAt.eventually_ne hd0
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hdz hz
    have hz0 : z ≠ 0 := by simpa using hz
    have he0 := L.weierstrassPExcept_def (0 : L.lattice) z
    have hep0 := L.derivWeierstrassPExcept_def (0 : L.lattice) z
    simp only [ZeroMemClass.coe_zero, zero_pow (by norm_num : 2 ≠ 0), div_zero,
      sub_zero, zero_sub] at he0
    simp only [ZeroMemClass.coe_zero, sub_zero] at hep0
    have he : L.weierstrassP z = E z + 1 / z ^ 2 := by
      dsimp only [E]
      linear_combination -he0
    have hep : L.derivWeierstrassP z = E' z - 2 / z ^ 3 := by
      dsimp only [E']
      linear_combination -hep0
    have hdval : den z = z ^ 2 * L.weierstrassP z := by
      rw [he]
      dsimp only [den]
      field_simp [hz0]
      <;> ring
    have hp0 : L.weierstrassP z ≠ 0 := by
      intro hp
      rw [hdval, hp, mul_zero] at hdz
      exact hdz rfl
    dsimp only [q]
    rw [hdval, hep]
    field_simp [hz0, hp0]
    <;> ring


private theorem central_geometry (z : ℂ)
  (hre : z.re ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2))
  (him : z.im ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :
  (z ∈ CothSums.lemniscaticPeriodPair.lattice → z = 0) ∧
  z + 1 ∉ CothSums.lemniscaticPeriodPair.lattice := by
  let L := CothSums.lemniscaticPeriodPair
  have hcoord (w : ℂ) (hw : w ∈ L.lattice) :
      ∃ m n : ℤ, (m : ℝ) + (n : ℝ) = w.re ∧ (m : ℝ) - (n : ℝ) = w.im := by
    obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp hw
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    dsimp [L,CothSums.lemniscaticPeriodPair] at hr hi
    exact ⟨m,n,by simpa using hr,by simpa [sub_eq_add_neg] using hi⟩
  constructor
  · intro hz
    obtain ⟨m,n,hr,hi⟩ := hcoord z hz
    have hrl : (-1 : ℤ) < m + n := by exact_mod_cast (show (-1 : ℝ) < (m : ℝ) + (n : ℝ) by linarith [hre.1])
    have hru : m + n < (1 : ℤ) := by exact_mod_cast (show (m : ℝ) + (n : ℝ) < (1 : ℝ) by linarith [hre.2])
    have hil : (-1 : ℤ) < m - n := by exact_mod_cast (show (-1 : ℝ) < (m : ℝ) - (n : ℝ) by linarith [him.1])
    have hiu : m - n < (1 : ℤ) := by exact_mod_cast (show (m : ℝ) - (n : ℝ) < (1 : ℝ) by linarith [him.2])
    have hm : m = 0 := by omega
    have hn : n = 0 := by omega
    apply Complex.ext
    · simpa [hm,hn] using hr.symm
    · simpa [hm,hn] using hi.symm
  · intro hz
    obtain ⟨m,n,hr,hi⟩ := hcoord (z + 1) hz
    simp only [Complex.add_re,Complex.one_re,Complex.add_im,Complex.one_im,add_zero] at hr hi
    have hrl : (0 : ℤ) < m + n := by exact_mod_cast (show (0 : ℝ) < (m : ℝ) + (n : ℝ) by linarith [hre.1])
    have hru : m + n < (2 : ℤ) := by exact_mod_cast (show (m : ℝ) + (n : ℝ) < (2 : ℝ) by linarith [hre.2])
    have hil : (-1 : ℤ) < m - n := by exact_mod_cast (show (-1 : ℝ) < (m : ℝ) - (n : ℝ) by linarith [him.1])
    have hiu : m - n < (1 : ℤ) := by exact_mod_cast (show (m : ℝ) - (n : ℝ) < (1 : ℝ) by linarith [him.2])
    omega


set_option maxHeartbeats 400000


theorem CothSums.square_lattice_log_derivative_regularized_square :
    let L := CothSums.lemniscaticPeriodPair
    let U : ℂ → ℂ := fun z => -L.derivWeierstrassP z / (2*L.weierstrassP z)
    ∃ q : ℂ → ℂ,
      AnalyticOnNhd ℂ q (Set.Icc (-(1/2:ℝ)) (1/2) ×ℂ Set.Icc (-(1/2:ℝ)) (1/2)) ∧
      q 0 = 1 ∧ ∀ z : ℂ, z ≠ 0 → q z = z*U z := by
  classical
  let L := CothSums.lemniscaticPeriodPair
  let U : ℂ → ℂ := fun z => -L.derivWeierstrassP z / (2*L.weierstrassP z)
  let q : ℂ → ℂ := fun z => if z=0 then 1 else z*U z
  change ∃ q : ℂ → ℂ,
      AnalyticOnNhd ℂ q (Set.Icc (-(1/2:ℝ)) (1/2) ×ℂ Set.Icc (-(1/2:ℝ)) (1/2)) ∧
      q 0 = 1 ∧ ∀ z : ℂ, z ≠ 0 → q z = z*U z
  obtain ⟨q0,hq0,hq00,heq⟩ := local_log_residue L
  have hqAnalytic0 : AnalyticAt ℂ q 0 := by
    apply hq0.congr
    apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
    · filter_upwards [heq,self_mem_nhdsWithin] with z hz hne
      have hz0 : z ≠ 0 := by simpa using hne
      simpa only [q,if_neg hz0,U] using hz
    · simpa [q] using hq00
  have hgn : L.g₂ ≠ 0 := by
    intro he
    have hh := square_g2_negative
    change L.g₂.re < 0 at hh
    simp [he] at hh
  have hc : -L.g₂/4 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hgn) (by norm_num)
  refine ⟨q,?_,?_,?_⟩
  · intro z hz
    by_cases hz0 : z=0
    · simpa [hz0] using hqAnalytic0
    · have hre : z.re ∈ Set.Icc (-1/2:ℝ) (1/2) := by
        simpa only [Set.mem_preimage,neg_div] using hz.1
      have him : z.im ∈ Set.Icc (-1/2:ℝ) (1/2) := by
        simpa only [Set.mem_preimage,neg_div] using hz.2
      have hg := central_geometry z hre him
      have hnL : z ∉ L.lattice := fun h => hz0 (hg.1 h)
      have hp : L.weierstrassP z * L.weierstrassP (z+1) = -L.g₂/4 :=
        half_period_product z hnL hg.2
      have hprod : L.weierstrassP z * L.weierstrassP (z+1) ≠ 0 := by rw [hp]; exact hc
      have hnP : L.weierstrassP z ≠ 0 := (mul_ne_zero_iff.mp hprod).1
      have hPa := L.analyticOnNhd_weierstrassP z hnL
      have hDa := L.analyticOnNhd_derivWeierstrassP z hnL
      have hden : AnalyticAt ℂ (fun w : ℂ => 2*L.weierstrassP w) z := analyticAt_const.mul hPa
      have hU : AnalyticAt ℂ U z := hDa.neg.div hden (mul_ne_zero (by norm_num) hnP)
      have ha : AnalyticAt ℂ (fun w : ℂ => w*U w) z := analyticAt_id.mul hU
      apply ha.congr
      filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
      simp only [q,if_neg hw]
  · simp only [q,if_pos rfl]
  · intro z hz
    simp only [q,if_neg hz]


set_option autoImplicit false


open Complex


open scoped ComplexConjugate


open Filter


open scoped Topology


private theorem square_second (z : ℂ) (hz : z ∉ CothSums.lemniscaticPeriodPair.lattice) :
  deriv CothSums.lemniscaticPeriodPair.derivWeierstrassP z =
    6 * CothSums.lemniscaticPeriodPair.weierstrassP z ^ 2 - CothSums.lemniscaticPeriodPair.g₂ / 2 := by
  let L := CothSums.lemniscaticPeriodPair
  have hrot := square_rotation
  change (∀ z : ℂ, L.weierstrassP (Complex.I * z) = -L.weierstrassP z) ∧
    (∀ z : ℂ, L.derivWeierstrassP (Complex.I * z) = Complex.I * L.derivWeierstrassP z) ∧
    L.g₃ = 0 ∧ L.weierstrassP 1 = 0 ∧ L.derivWeierstrassP 1 = 0 at hrot
  have hnot : (1 : ℂ) ∉ L.lattice := by
    intro hm
    obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp hm
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    dsimp [L, CothSums.lemniscaticPeriodPair] at hr hi
    have hr' : (1 : ℝ) = (m : ℝ) + (n : ℝ) := by simpa using hr.symm
    have hi' : (0 : ℝ) = (m : ℝ) - (n : ℝ) := by simpa [sub_eq_add_neg] using hi.symm
    have hri : (1 : ℤ) = m + n := by exact_mod_cast hr'
    have hii : (0 : ℤ) = m - n := by exact_mod_cast hi'
    omega
  have hc : IsPreconnected (L.lattice : Set ℂ)ᶜ := by
    exact (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
  have hprod (w : ℂ) (hw : w ∉ L.lattice) :
      L.derivWeierstrassP w * (2 * deriv L.derivWeierstrassP w -
        12 * L.weierstrassP w ^ 2 + L.g₂) = 0 := by
    have hp := (L.differentiableOn_weierstrassP w hw).differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hw)
    have hd := (L.differentiableOn_derivWeierstrassP w hw).differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hw)
    have hp' : HasDerivAt L.weierstrassP (L.derivWeierstrassP w) w := by
      simpa only [L.deriv_weierstrassP] using hp.hasDerivAt
    have he : (fun v => L.derivWeierstrassP v ^ 2) =ᶠ[𝓝 w]
        (fun v => 4 * L.weierstrassP v ^ 3 - L.g₂ * L.weierstrassP v - L.g₃) := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hw] with v hv
      exact L.derivWeierstrassP_sq v hv
    have hl := (hd.hasDerivAt.pow 2).congr_of_eventuallyEq he.symm
    have hr := (((hp'.pow 3).const_mul 4).sub (hp'.const_mul L.g₂)).sub_const L.g₃
    have hh := hl.unique hr
    dsimp at hh
    linear_combination hh
  have hg : AnalyticOnNhd ℂ (fun w => 2 * deriv L.derivWeierstrassP w -
      12 * L.weierstrassP w ^ 2 + L.g₂) (L.lattice : Set ℂ)ᶜ := by
    intro w hw
    have h1 := L.analyticOnNhd_derivWeierstrassP.deriv w hw
    have h2 := L.analyticOnNhd_weierstrassP w hw
    fun_prop
  rcases L.analyticOnNhd_derivWeierstrassP.eq_zero_or_eq_zero_of_mul_eq_zero hg hprod hc with hzero | hzero
  · have heq : Set.EqOn L.weierstrassP (fun _ => (0 : ℂ)) (L.lattice : Set ℂ)ᶜ := by
      apply L.isClosed_lattice.isOpen_compl.eqOn_of_deriv_eq hc
        L.differentiableOn_weierstrassP (differentiableOn_const (0 : ℂ))
      · intro w hw
        simpa only [L.deriv_weierstrassP, deriv_const] using hzero w hw
      · exact hnot
      · exact hrot.2.2.2.1
    have hall : L.weierstrassP = fun _ => 0 := by
      funext w
      by_cases hw : w ∈ L.lattice
      · exact L.weierstrassP_coe ⟨w,hw⟩
      · exact heq hw
    exact False.elim (L.not_continuousAt_weierstrassP 0 (zero_mem L.lattice)
      (by rw [hall]; exact continuousAt_const))
  · have hh := hzero z hz
    change deriv L.derivWeierstrassP z = _
    linear_combination hh / 2


private theorem square_reality :
 let L := CothSums.lemniscaticPeriodPair
 (∀ z : ℂ, L.weierstrassP (star z) = star (L.weierstrassP z)) ∧
 (∀ z : ℂ, L.derivWeierstrassP (star z) = star (L.derivWeierstrassP z)) ∧
 L.g₂.im = 0 := by
  let L := CothSums.lemniscaticPeriodPair
  change (∀ z : ℂ, L.weierstrassP (star z) = star (L.weierstrassP z)) ∧
    (∀ z : ℂ, L.derivWeierstrassP (star z) = star (L.derivWeierstrassP z)) ∧ L.g₂.im = 0
  have hmem (z : ℂ) (hz : z ∈ L.lattice) : conj z ∈ L.lattice := by
    obtain ⟨m, n, he⟩ := PeriodPair.mem_lattice.mp hz
    apply PeriodPair.mem_lattice.mpr
    refine ⟨n, m, ?_⟩
    rw [← he]
    dsimp [L, CothSums.lemniscaticPeriodPair]
    simp only [map_add, map_mul, map_sub, map_one, Complex.conj_I, map_intCast]
    ring
  let e : L.lattice ≃ L.lattice :=
    { toFun := fun z => ⟨conj z, hmem z z.property⟩
      invFun := fun z => ⟨conj z, hmem z z.property⟩
      left_inv := by intro z; apply Subtype.ext; exact star_star _
      right_inv := by intro z; apply Subtype.ext; exact star_star _ }
  have he (z : L.lattice) : (e z : ℂ) = conj (z : ℂ) := rfl
  have hp (z : ℂ) : L.weierstrassP (conj z) = conj (L.weierstrassP z) := by
    simp only [PeriodPair.weierstrassP, Complex.conj_tsum]
    rw [← e.tsum_eq (fun l : L.lattice => 1 / (conj z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)]
    apply tsum_congr
    intro l
    simp only [he, map_sub, map_div₀, map_one, map_pow]
  have hpd (z : ℂ) : L.derivWeierstrassP (conj z) = conj (L.derivWeierstrassP z) := by
    simp only [PeriodPair.derivWeierstrassP, map_neg, Complex.conj_tsum]
    congr 1
    rw [← e.tsum_eq (fun l : L.lattice => 2 / (conj z - (l : ℂ)) ^ 3)]
    apply tsum_congr
    intro l
    simp only [he, map_div₀, map_ofNat, map_pow, map_sub]
  have hG : conj (L.G 4) = L.G 4 := by
    rw [PeriodPair.G, Complex.conj_tsum]
    have hh := e.tsum_eq (fun l : L.lattice => ((l : ℂ) ^ 4)⁻¹)
    simpa only [he, map_inv₀, map_pow] using hh
  have hg : conj L.g₂ = L.g₂ := by
    simp only [PeriodPair.g₂, map_mul, map_ofNat, hG]
  have hi := congrArg Complex.im hg
  simp only [Complex.conj_im] at hi
  refine ⟨hp, hpd, ?_⟩
  linarith


private theorem square_negative : CothSums.lemniscaticPeriodPair.g₂.re < 0 := by
  let L := CothSums.lemniscaticPeriodPair
  let f : ℕ → ℤ → ℝ := fun s k => 1 / (k : ℝ) ^ s
  have hz (s : ℕ) (hs : 0 < s) (he : Even s) (c : ℝ)
      (hh : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ s) c) :
      HasSum (f s) (2 * c) := by
    have hv : (∑ i ∈ Finset.range 1, (1 : ℝ) / (i : ℝ) ^ s) = 0 := by simp [hs.ne']
    have hi := (hasSum_nat_add_iff' 1).mpr hh
    have hshift : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ s) c := by
      simpa only [Nat.cast_add, Nat.cast_one, hv, sub_zero] using hi
    have hneg : HasSum (fun n : ℕ => f s (-(n + 1 : ℤ))) c := by
      simpa only [f, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, he.neg_pow]
        using hshift
    have hnat : HasSum (fun n : ℕ => f s n) c := by
      simpa only [f, Int.cast_natCast] using hh
    simpa only [two_mul] using hnat.of_nat_of_neg_add_one hneg
  have h2 : HasSum (f 2) (Real.pi ^ 2 / 3) := by
    convert! hz 2 (by norm_num) (by decide) _ hasSum_zeta_two using 1 <;> ring
  have h4 : HasSum (f 4) (Real.pi ^ 4 / 45) := by
    convert! hz 4 (by norm_num) (by decide) _ hasSum_zeta_four using 1 <;> ring
  have hf2 (k : ℤ) : 0 ≤ f 2 k := by dsimp [f]; positivity
  have hf4 (k : ℤ) : 0 ≤ f 4 k := by dsimp [f]; positivity
  let d : ℤ → ℝ := fun k => if k = 0 then 1 else 0
  have hd : HasSum d 1 := by simpa only [d] using hasSum_ite_eq (0 : ℤ) (1 : ℝ)
  have hdnonneg (k : ℤ) : 0 ≤ d k := by dsimp [d]; split_ifs <;> norm_num
  let A1 : ℤ × ℤ → ℝ := fun p => f 4 p.1 * d p.2
  let A2 : ℤ × ℤ → ℝ := fun p => d p.1 * f 4 p.2
  let B : ℤ × ℤ → ℝ := fun p => (1 / 4) * (f 2 p.1 * f 2 p.2)
  have hA1 : Summable A1 := h4.summable.mul_of_nonneg hd.summable hf4 hdnonneg
  have hA2 : Summable A2 := hd.summable.mul_of_nonneg h4.summable hdnonneg hf4
  have hB0 : Summable (fun p : ℤ × ℤ => f 2 p.1 * f 2 p.2) :=
    h2.summable.mul_of_nonneg h2.summable hf2 hf2
  have hB : Summable B := hB0.mul_left (1 / 4)
  have hA1val : (∑' p : ℤ × ℤ, A1 p) = Real.pi ^ 4 / 45 := by
    have hh := h4.summable.tsum_mul_tsum hd.summable hA1
    rw [h4.tsum_eq, hd.tsum_eq, mul_one] at hh
    exact hh.symm
  have hA2val : (∑' p : ℤ × ℤ, A2 p) = Real.pi ^ 4 / 45 := by
    have hh := hd.summable.tsum_mul_tsum h4.summable hA2
    rw [hd.tsum_eq, h4.tsum_eq, one_mul] at hh
    exact hh.symm
  have hBval : (∑' p : ℤ × ℤ, B p) = (1 / 4) * (Real.pi ^ 2 / 3) ^ 2 := by
    rw [show B = (fun p => (1 / 4) * (f 2 p.1 * f 2 p.2)) by rfl, tsum_mul_left]
    have hh := h2.summable.tsum_mul_tsum h2.summable hB0
    rw [h2.tsum_eq] at hh
    rw [← hh]
    ring
  let F : ℤ × ℤ → ℂ := fun p => (((p.1 : ℂ) - Complex.I * (p.2 : ℂ)) ^ 4)⁻¹
  have hnorm (p : ℤ × ℤ) : ‖F p‖ = 1 / (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ 2) := by
    have he : ‖(p.1 : ℂ) - Complex.I * (p.2 : ℂ)‖ ^ 4 =
        ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, ← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, pow_two]
    dsimp [F]
    rw [norm_inv, norm_pow, he]
    simp only [one_div]
  have hbound (p : ℤ × ℤ) (hm : p.1 ≠ 0) (hn : p.2 ≠ 0) : ‖F p‖ ≤ B p := by
    have hm' : (p.1 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
    have hn' : (p.2 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
    rw [hnorm]
    calc
      _ ≤ 1 / (4 * (p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2) := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [sq_nonneg ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2)]
      _ = B p := by dsimp [B, f]; field_simp <;> ring
  have hFaxis1 (m : ℤ) : F (m, 0) = (f 4 m : ℂ) := by
    dsimp [F, f]
    push_cast
    simp
  have hFaxis2 (n : ℤ) : F (0, n) = (f 4 n : ℂ) := by
    have hI : (-Complex.I) ^ 4 = (1 : ℂ) := by
      rw [show (-Complex.I) ^ 4 = ((-Complex.I) ^ 2) ^ 2 by ring]
      norm_num
    dsimp only [F, f]
    simp only [Int.cast_zero, zero_sub, ← neg_mul, mul_pow, hI, one_mul]
    push_cast
    simp only [one_div]
  have hmaj (p : ℤ × ℤ) : ‖F p‖ ≤ A1 p + A2 p + B p := by
    by_cases hm : p.1 = 0
    · rcases p with ⟨m,n⟩
      dsimp only at hm
      subst m
      rw [hFaxis2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf4 n)]
      simp [A1, A2, B, d, f]
    · by_cases hn : p.2 = 0
      · rcases p with ⟨m,n⟩
        dsimp only at hn
        subst n
        rw [hFaxis1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf4 m)]
        simp [A1, A2, B, d, f]
      · simpa only [A1, A2, d, if_neg hm, if_neg hn, zero_mul, mul_zero, zero_add] using hbound p hm hn
  have hlow (p : ℤ × ℤ) : A1 p + A2 p - B p ≤ (F p).re := by
    by_cases hm : p.1 = 0
    · rcases p with ⟨m,n⟩
      dsimp only at hm
      subst m
      rw [hFaxis2, Complex.ofReal_re]
      simp [A1, A2, B, d, f]
    · by_cases hn : p.2 = 0
      · rcases p with ⟨m,n⟩
        dsimp only at hn
        subst n
        rw [hFaxis1, Complex.ofReal_re]
        simp [A1, A2, B, d, f]
      · have hh := (abs_le.mp (Complex.abs_re_le_norm (F p))).1
        have hb := hbound p hm hn
        simp only [A1, A2, d, if_neg hm, if_neg hn, zero_mul, mul_zero, zero_add, zero_sub]
        linarith
  have hFs : Summable F := ((hA1.add hA2).add hB).of_norm_bounded hmaj
  have hFr : Summable (fun p => (F p).re) := Complex.reCLM.summable hFs
  have hLower : Real.pi ^ 4 / 60 ≤ (∑' p : ℤ × ℤ, F p).re := by
    have hh := ((hA1.add hA2).sub hB).tsum_le_tsum hlow hFr
    rw [(hA1.add hA2).tsum_sub hB, hA1.tsum_add hA2, hA1val, hA2val, hBval] at hh
    rw [Complex.re_tsum hFs]
    convert! hh using 1 <;> ring
  have hterm (p : ℤ × ℤ) :
      (((L.latticeEquivProd.symm p : L.lattice) : ℂ) ^ 4)⁻¹ = -(1 / 4 : ℂ) * F p := by
    rw [L.latticeEquiv_symm_apply]
    change (((p.1 : ℂ) * (1 + Complex.I) + (p.2 : ℂ) * (1 - Complex.I)) ^ 4)⁻¹ = _
    rw [show (p.1 : ℂ) * (1 + Complex.I) + (p.2 : ℂ) * (1 - Complex.I) =
      (1 + Complex.I) * ((p.1 : ℂ) - Complex.I * (p.2 : ℂ)) by
        ring_nf; simp only [Complex.I_sq]; ring, mul_pow]
    have he : (1 + Complex.I) ^ 4 = (-4 : ℂ) := by
      norm_num [Complex.ext_iff, pow_succ, Complex.mul_re, Complex.mul_im]
    rw [he, mul_inv_rev]
    dsimp [F]
    norm_num
    <;> ring
  have hG : L.G 4 = -(1 / 4 : ℂ) * ∑' p : ℤ × ℤ, F p := by
    calc
      _ = ∑' p : ℤ × ℤ, (((L.latticeEquivProd.symm p : L.lattice) : ℂ) ^ 4)⁻¹ :=
        (L.latticeEquivProd.toEquiv.symm.tsum_eq (fun l : L.lattice => ((l : ℂ) ^ 4)⁻¹)).symm
      _ = _ := by simp only [hterm, tsum_mul_left]
  change L.g₂.re < 0
  rw [PeriodPair.g₂, hG, Complex.mul_re, Complex.mul_re]
  norm_num
  have hp : 0 < Real.pi ^ 4 / 60 := by positivity
  nlinarith [hLower]


private theorem square_real_branch (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
  let L := CothSums.lemniscaticPeriodPair
  (x : ℂ) ∉ L.lattice ∧ (L.weierstrassP x).im = 0 ∧ (L.derivWeierstrassP x).im = 0 ∧
  0 < (L.weierstrassP x).re ∧ (L.derivWeierstrassP x).re < 0 ∧
  HasDerivAt (fun y : ℝ => (L.weierstrassP y).re) (L.derivWeierstrassP x).re x ∧
  HasDerivAt (fun y : ℝ => (L.derivWeierstrassP y).re)
    (6 * (L.weierstrassP x).re ^ 2 - L.g₂.re / 2) x := by
  let L := CothSums.lemniscaticPeriodPair
  let P : ℝ → ℝ := fun y => (L.weierstrassP y).re
  let Q : ℝ → ℝ := fun y => (L.derivWeierstrassP y).re
  have hrot := square_rotation
  change (∀ z : ℂ, L.weierstrassP (Complex.I * z) = -L.weierstrassP z) ∧
    (∀ z : ℂ, L.derivWeierstrassP (Complex.I * z) = Complex.I * L.derivWeierstrassP z) ∧
    L.g₃ = 0 ∧ L.weierstrassP 1 = 0 ∧ L.derivWeierstrassP 1 = 0 at hrot
  have hreal := square_reality
  change (∀ z : ℂ, L.weierstrassP (star z) = star (L.weierstrassP z)) ∧
    (∀ z : ℂ, L.derivWeierstrassP (star z) = star (L.derivWeierstrassP z)) ∧ L.g₂.im = 0 at hreal
  have hneg : L.g₂.re < 0 := square_negative
  have hnot (y : ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 2) : (y : ℂ) ∉ L.lattice := by
    intro hm
    obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp hm
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    dsimp [L, CothSums.lemniscaticPeriodPair] at hr hi
    have hr' : (m : ℝ) + (n : ℝ) = y := by simpa using hr
    have hi' : (m : ℝ) - (n : ℝ) = 0 := by simpa [sub_eq_add_neg] using hi
    have hmn : m = n := by exact_mod_cast (sub_eq_zero.mp hi')
    subst n
    have hmlo : (0 : ℝ) < (m : ℝ) := by linarith [hy.1]
    have hmhi : (m : ℝ) < 1 := by linarith [hy.2]
    have hi0 : (0 : ℤ) < m := by exact_mod_cast hmlo
    have hi1 : m < (1 : ℤ) := by exact_mod_cast hmhi
    omega
  have hpim (y : ℝ) : (L.weierstrassP y).im = 0 := by
    have hh : L.weierstrassP (conj (y : ℂ)) = conj (L.weierstrassP (y : ℂ)) := hreal.1 _
    rw [Complex.conj_ofReal] at hh
    have hi := congrArg Complex.im hh
    simp only [Complex.conj_im] at hi
    linarith
  have hqim (y : ℝ) : (L.derivWeierstrassP y).im = 0 := by
    have hh : L.derivWeierstrassP (conj (y : ℂ)) = conj (L.derivWeierstrassP (y : ℂ)) := hreal.2.1 _
    rw [Complex.conj_ofReal] at hh
    have hi := congrArg Complex.im hh
    simp only [Complex.conj_im] at hi
    linarith
  have hpD (y : ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 2) : HasDerivAt P (Q y) y := by
    have hh := ((L.differentiableOn_weierstrassP y (hnot y hy)).differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds (hnot y hy))).hasDerivAt
    rw [L.deriv_weierstrassP] at hh
    exact hh.real_of_complex
  have hqD (y : ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 2) :
      HasDerivAt Q (6 * P y ^ 2 - L.g₂.re / 2) y := by
    have hh := ((L.differentiableOn_derivWeierstrassP y (hnot y hy)).differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds (hnot y hy))).hasDerivAt
    rw [square_second y (hnot y hy)] at hh
    have hhReal : HasDerivAt Q ((6 * L.weierstrassP y ^ 2 - L.g₂ / 2).re) y := hh.real_of_complex
    convert hhReal using 1
    simp [P, Complex.mul_re, Complex.sub_re, pow_two, hpim]
  have hmono : StrictMonoOn Q (Set.Ioo (0 : ℝ) 2) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo 0 2)
    · intro y hy
      exact (hqD y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [(hqD y (interior_subset hy)).deriv]
      nlinarith [sq_nonneg (P y)]
  have hx2 : x ∈ Set.Ioo (0 : ℝ) 2 := ⟨hx.1, by linarith [hx.2]⟩
  have h1 : (1 : ℝ) ∈ Set.Ioo (0 : ℝ) 2 := by norm_num
  have hq1 : Q 1 = 0 := by simp only [Q, Complex.ofReal_one, hrot.2.2.2.2, Complex.zero_re]
  have hqx : Q x < 0 := by simpa only [hq1] using hmono hx2 h1 hx.2
  have hp : L.weierstrassP x = (P x : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hpim x
  have hq : L.derivWeierstrassP x = (Q x : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hqim x
  have hg : L.g₂ = (L.g₂.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hreal.2.2
  have hc := L.derivWeierstrassP_sq x (hnot x hx2)
  rw [hp,hq,hg,hrot.2.2.1] at hc
  have hcu : Q x ^ 2 = 4 * P x ^ 3 - L.g₂.re * P x := by
    have hh : Q x ^ 2 = 4 * P x ^ 3 - L.g₂.re * P x - 0 := by exact_mod_cast hc
    simpa only [sub_zero] using hh
  have hcoef : 0 < 4 * P x ^ 2 - L.g₂.re := by nlinarith [sq_nonneg (P x)]
  have hmul : 0 < P x * (4 * P x ^ 2 - L.g₂.re) := by
    nlinarith [sq_pos_of_ne_zero hqx.ne]
  have hpx : 0 < P x := (mul_pos_iff_of_pos_right hcoef).mp hmul
  exact ⟨hnot x hx2, hpim x, hqim x, hpx, hqx, hpD x hx2, hqD x hx2⟩


private theorem square_sqrt_branch :
  let L := CothSums.lemniscaticPeriodPair
  let μ := Real.sqrt (Real.sqrt (-L.g₂.re) / 2)
  let R : ℝ → ℝ := fun x => μ / Real.sqrt (L.weierstrassP x).re
  0 < μ ∧ μ ^ 4 = -L.g₂.re / 4 ∧
  ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 →
    0 < R x ∧ HasDerivAt R (μ * Real.sqrt (1 + R x ^ 4)) x := by
  let L := CothSums.lemniscaticPeriodPair
  let μ := Real.sqrt (Real.sqrt (-L.g₂.re) / 2)
  let R : ℝ → ℝ := fun x => μ / Real.sqrt (L.weierstrassP x).re
  have hneg : L.g₂.re < 0 := square_negative
  have hκ : 0 < -L.g₂.re := by linarith
  have hμ : 0 < μ := Real.sqrt_pos.mpr (div_pos (Real.sqrt_pos.mpr hκ) (by norm_num))
  have hμ2 : μ ^ 2 = Real.sqrt (-L.g₂.re) / 2 := Real.sq_sqrt (by positivity)
  have hμ4 : μ ^ 4 = -L.g₂.re / 4 := by
    rw [show μ ^ 4 = (μ ^ 2) ^ 2 by ring, hμ2, div_pow, Real.sq_sqrt hκ.le]
    norm_num
  refine ⟨hμ,hμ4,?_⟩
  intro x hx
  rcases square_real_branch x hx with ⟨hn,hpi,hqi,hp,hq,hpd,hqd⟩
  change (x : ℂ) ∉ L.lattice at hn
  change 0 < (L.weierstrassP x).re at hp
  change (L.derivWeierstrassP x).re < 0 at hq
  let s := Real.sqrt (L.weierstrassP x).re
  have hs : 0 < s := Real.sqrt_pos.mpr hp
  have hs2 : s ^ 2 = (L.weierstrassP x).re := Real.sq_sqrt hp.le
  have hR : 0 < R x := div_pos hμ hs
  refine ⟨hR,?_⟩
  have hd : HasDerivAt R ((-μ * (L.derivWeierstrassP x).re) / (2 * s ^ 3)) x := by
    have hh := (hasDerivAt_const x μ).div (hpd.sqrt hp.ne') hs.ne'
    apply hh.congr_deriv
    change (0 * s - μ * ((L.derivWeierstrassP x).re / (2 * s))) / s ^ 2 =
      (-μ * (L.derivWeierstrassP x).re) / (2 * s ^ 3)
    field_simp [hs.ne']
    <;> ring
  have hpC : L.weierstrassP x = ((L.weierstrassP x).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hpi
  have hqC : L.derivWeierstrassP x = ((L.derivWeierstrassP x).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hqi
  have hgC : L.g₂ = (L.g₂.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using square_reality.2.2
  have hc := L.derivWeierstrassP_sq x hn
  rw [hpC,hqC,hgC,square_rotation.2.2.1] at hc
  have hcu : (L.derivWeierstrassP x).re ^ 2 =
      4 * (L.weierstrassP x).re ^ 3 - L.g₂.re * (L.weierstrassP x).re := by
    have hh : (L.derivWeierstrassP x).re ^ 2 =
        4 * (L.weierstrassP x).re ^ 3 - L.g₂.re * (L.weierstrassP x).re - 0 := by exact_mod_cast hc
    simpa only [sub_zero] using hh
  have hce : (L.derivWeierstrassP x).re ^ 2 = 4 * s ^ 6 + 4 * μ ^ 4 * s ^ 2 := by
    rw [hμ4, hs2, show s ^ 6 = (s ^ 2) ^ 3 by ring, hs2]
    nlinarith [hcu]
  have hD : 0 < (-μ * (L.derivWeierstrassP x).re) / (2 * s ^ 3) := by
    have hu : 0 < -μ * (L.derivWeierstrassP x).re := mul_pos_of_neg_of_neg (neg_neg_of_pos hμ) hq
    exact div_pos hu (by positivity)
  have hsq : ((-μ * (L.derivWeierstrassP x).re) / (2 * s ^ 3)) ^ 2 =
      (μ * Real.sqrt (1 + R x ^ 4)) ^ 2 := by
    have hsqroot : Real.sqrt (1 + R x ^ 4) ^ 2 = 1 + R x ^ 4 := Real.sq_sqrt (by positivity)
    rw [mul_pow, hsqroot]
    dsimp only [R]
    change ((-μ * (L.derivWeierstrassP x).re) / (2 * s ^ 3)) ^ 2 =
      μ ^ 2 * (1 + (μ / s) ^ 4)
    field_simp
    linear_combination hce
  have heq : (-μ * (L.derivWeierstrassP x).re) / (2 * s ^ 3) =
      μ * Real.sqrt (1 + R x ^ 4) := by
    have hnon : 0 ≤ μ * Real.sqrt (1 + R x ^ 4) := by positivity
    nlinarith
  exact hd.congr_deriv heq


private theorem square_branch_endpoints :
  let L := CothSums.lemniscaticPeriodPair
  let μ := Real.sqrt (Real.sqrt (-L.g₂.re) / 2)
  let R : ℝ → ℝ := fun x => μ / Real.sqrt (L.weierstrassP x).re
  Filter.Tendsto R (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
  Filter.Tendsto R (nhdsWithin 1 (Set.Iio 1)) Filter.atTop := by
  let L := CothSums.lemniscaticPeriodPair
  let μ := Real.sqrt (Real.sqrt (-L.g₂.re) / 2)
  let R : ℝ → ℝ := fun x => μ / Real.sqrt (L.weierstrassP x).re
  let E : ℝ → ℝ := fun x => (L.weierstrassPExcept 0 x).re
  have hμ : 0 < μ := square_sqrt_branch.1
  have hE : ContinuousAt E 0 := by
    have hc : ContinuousAt (L.weierstrassPExcept 0) (0 : ℂ) := (L.analyticAt_weierstrassPExcept 0).continuousAt
    have ho : ContinuousAt (fun x : ℝ => (x : ℂ)) 0 := Complex.continuous_ofReal.continuousAt
    have hcomp := hc.comp_of_eq ho (by simp : ((0 : ℝ) : ℂ) = 0)
    simpa only [Function.comp_def] using Complex.continuous_re.continuousAt.comp hcomp
  have hexact (x : ℝ) : (L.weierstrassP x).re = E x + 1 / x ^ 2 := by
    have hh := L.weierstrassPExcept_add ⟨0,zero_mem L.lattice⟩ (x : ℂ)
    have hc : L.weierstrassPExcept 0 x + ((1 / x ^ 2 : ℝ) : ℂ) = L.weierstrassP x := by
      simpa only [sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), div_zero,
        Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow] using hh
    simpa only [Complex.add_re, Complex.ofReal_re, E] using (congrArg Complex.re hc).symm
  have hRrewrite (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
      R x = μ * x / Real.sqrt (1 + x ^ 2 * E x) := by
    have hp : 0 < (L.weierstrassP x).re := (square_real_branch x hx).2.2.2.1
    have hxne : x ≠ 0 := hx.1.ne'
    have hsne : Real.sqrt (L.weierstrassP x).re ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    have he : 1 + x ^ 2 * E x = x ^ 2 * (L.weierstrassP x).re := by
      rw [hexact x]
      field_simp
      <;> ring
    rw [he, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx.1.le]
    dsimp only [R]
    field_simp
  have hB : Tendsto (fun x : ℝ => 1 + x ^ 2 * E x) (𝓝 0) (𝓝 (1 : ℝ)) := by
    have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝 0) (𝓝 1) := tendsto_const_nhds
    have hi : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0) := tendsto_id
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, add_zero] using
      hc.add ((hi.pow 2).mul hE.tendsto)
  have hden : Tendsto (fun x : ℝ => Real.sqrt (1 + x ^ 2 * E x)) (𝓝 0) (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_one] using (Real.continuous_sqrt.tendsto 1).comp hB
  have hleft : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hh : Tendsto (fun x : ℝ => μ * x / Real.sqrt (1 + x ^ 2 * E x))
        (𝓝 0) (𝓝 0) := by
      have hc : Tendsto (fun _ : ℝ => μ) (𝓝 0) (𝓝 μ) := tendsto_const_nhds
      have hi : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0) := tendsto_id
      convert! (hc.mul hi).div hden (by norm_num : (1 : ℝ) ≠ 0) using 1 <;>
        norm_num [Pi.div_apply, Pi.mul_apply]
    apply hh.mono_left nhdsWithin_le_nhds |>.congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact (hRrewrite x hx).symm
  have hnot1 : (1 : ℂ) ∉ L.lattice := by
    intro hm
    obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp hm
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    dsimp [L, CothSums.lemniscaticPeriodPair] at hr hi
    have hr' : (1 : ℝ) = (m : ℝ) + (n : ℝ) := by simpa using hr.symm
    have hi' : (0 : ℝ) = (m : ℝ) - (n : ℝ) := by simpa [sub_eq_add_neg] using hi.symm
    have hri : (1 : ℤ) = m + n := by exact_mod_cast hr'
    have hii : (0 : ℤ) = m - n := by exact_mod_cast hi'
    omega
  have hPzero : L.weierstrassP 1 = 0 := square_rotation.2.2.2.1
  have hPcont : ContinuousAt (fun x : ℝ => (L.weierstrassP x).re) 1 := by
    have hc : ContinuousAt L.weierstrassP (1 : ℂ) :=
      ((L.differentiableOn_weierstrassP 1 hnot1).differentiableAt
        (L.isClosed_lattice.isOpen_compl.mem_nhds hnot1)).continuousAt
    have ho : ContinuousAt (fun x : ℝ => (x : ℂ)) 1 := Complex.continuous_ofReal.continuousAt
    have hcomp := hc.comp_of_eq ho (by simp : ((1 : ℝ) : ℂ) = 1)
    simpa only [Function.comp_def] using Complex.continuous_re.continuousAt.comp hcomp
  have hP1 : Tendsto (fun x : ℝ => (L.weierstrassP x).re) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    simpa only [Complex.ofReal_one, hPzero, Complex.zero_re] using
      hPcont.tendsto.mono_left nhdsWithin_le_nhds
  have hs1 : Tendsto (fun x : ℝ => Real.sqrt (L.weierstrassP x).re)
      (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hP1
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
      exact Real.sqrt_pos.mpr (square_real_branch x hx).2.2.2.1
  have hright : Tendsto R (𝓝[<] (1 : ℝ)) atTop := by
    simpa only [R,div_eq_mul_inv, Function.comp_def] using
      (tendsto_inv_nhdsGT_zero.comp hs1).const_mul_atTop hμ
  exact ⟨hleft,hright⟩


open MeasureTheory Set


open Asymptotics


open Filter


private theorem chi_reciprocal (r : ℝ) (hr : 0 < r) : CothSums.chi r⁻¹ = 1 - CothSums.chi r := by
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  let H : ℝ → ℝ := fun t => CothSums.chi t⁻¹ + CothSums.chi t
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt H 0 t := by
    have hs : Real.sqrt (1 + (t⁻¹) ^ 4) = Real.sqrt (1 + t ^ 4) / t ^ 2 := by
      have he : 1 + (t⁻¹) ^ 4 = (1 + t ^ 4) / (t ^ 2) ^ 2 := by
        field_simp
        <;> ring
      rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq (sq_nonneg t)]
    have hh := ((CothSums.chi_hasDerivAt t⁻¹).comp t (hasDerivAt_inv ht.ne')).add
      (CothSums.chi_hasDerivAt t)
    apply hh.congr_deriv
    rw [hs]
    have hp : Real.sqrt (1 + t ^ 4) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    field_simp [ht.ne', hp]
    <;> ring
  have hconst (t : ℝ) (ht : 0 < t) : H t = H r := by
    apply isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
      (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hd t ht).deriv) ht hr
  have hz : CothSums.chi 0 = 0 := by simp [CothSums.chi]
  have hlim : Tendsto H atTop (nhds (1 : ℝ)) := by
    have hc := (CothSums.chi_hasDerivAt 0).continuousAt.tendsto.comp
      (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0))
    simpa only [H, Function.comp_def, hz, zero_add] using hc.add chi_limit
  have hlim' : Tendsto H atTop (nhds (H r)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (hconst t ht).symm
  have he : H r = 1 := (tendsto_nhds_unique hlim hlim').symm
  dsimp [H] at he
  linarith


private theorem square_actual_inverse :
  let L := CothSums.lemniscaticPeriodPair
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  let μ := Real.sqrt (Real.sqrt (-L.g₂.re) / 2)
  let R : ℝ → ℝ := fun x => μ / Real.sqrt (L.weierstrassP x).re
  C * μ = 1 ∧ Set.EqOn R (Function.invFun CothSums.chi) (Set.Ioo (0 : ℝ) 1) := by
  let L := CothSums.lemniscaticPeriodPair
  let C : ℝ := 4 * Real.sqrt Real.pi / Real.Gamma (1 / 4) ^ 2
  let μ := Real.sqrt (Real.sqrt (-L.g₂.re) / 2)
  let R : ℝ → ℝ := fun x => μ / Real.sqrt (L.weierstrassP x).re
  let H : ℝ → ℝ := fun x => CothSums.chi (R x) - C * μ * x
  have hode (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
      HasDerivAt R (μ * Real.sqrt (1 + R x ^ 4)) x := (square_sqrt_branch.2.2 x hx).2
  have hd (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) : HasDerivAt H 0 x := by
    have hh := ((CothSums.chi_hasDerivAt (R x)).comp x (hode x hx)).sub
      ((hasDerivAt_id x).const_mul (C * μ))
    apply hh.congr_deriv
    have hs : Real.sqrt (1 + R x ^ 4) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    dsimp only [C]
    field_simp
    <;> ring
  have hconst (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) : H x = H (1 / 2) := by
    apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0 : ℝ) 1).isPreconnected
      (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hd x hx).deriv) hx
    norm_num
  have hz : CothSums.chi 0 = 0 := by simp [CothSums.chi]
  have hzero : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hchi := (CothSums.chi_hasDerivAt 0).continuousAt.tendsto.comp square_branch_endpoints.1
    have hlin : Tendsto (fun x : ℝ => C * μ * x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hi : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [mul_zero] using hi.const_mul (C * μ)
    simpa only [H,Function.comp_def,hz,sub_zero] using hchi.sub hlin
  have hmid : H (1 / 2) = 0 := by
    have hm : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 (H (1 / 2))) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
      exact (hconst x hx).symm
    exact tendsto_nhds_unique hm hzero
  have hchiR (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) : CothSums.chi (R x) = C * μ * x := by
    have hh := (hconst x hx).trans hmid
    exact sub_eq_zero.mp hh
  have hscale : C * μ = 1 := by
    have hchi1 : Tendsto (fun x : ℝ => CothSums.chi (R x)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
      exact chi_limit.comp square_branch_endpoints.2
    have hlin : Tendsto (fun x : ℝ => C * μ * x) (𝓝[<] (1 : ℝ)) (𝓝 (C * μ)) := by
      have hi : Tendsto (fun x : ℝ => x) (𝓝[<] (1 : ℝ)) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [mul_one] using hi.const_mul (C * μ)
    have hh : Tendsto (fun x : ℝ => CothSums.chi (R x)) (𝓝[<] (1 : ℝ)) (𝓝 (C * μ)) := by
      apply hlin.congr'
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
      exact (hchiR x hx).symm
    exact (tendsto_nhds_unique hchi1 hh).symm
  refine ⟨hscale,?_⟩
  intro x hx
  have he : CothSums.chi (R x) = x := by simpa only [hscale,one_mul] using hchiR x hx
  calc
    R x = Function.invFun CothSums.chi (CothSums.chi (R x)) :=
      (Function.leftInverse_invFun chi_strict.injective (R x)).symm
    _ = Function.invFun CothSums.chi x := congrArg (Function.invFun CothSums.chi) he


theorem CothSums.lemniscatic_square_lattice_actual_log_derivative (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
  let L := CothSums.lemniscaticPeriodPair
  let U : ℂ := -L.derivWeierstrassP x / (2 * L.weierstrassP x)
  U = (deriv (fun y : ℝ => Real.log (Function.invFun CothSums.chi y)) x : ℂ) ∧
  HasDerivAt (fun y : ℝ => (Real.log (Function.invFun CothSums.chi y) : ℂ)) U x := by
  let L := CothSums.lemniscaticPeriodPair
  let μ := Real.sqrt (Real.sqrt (-L.g₂.re) / 2)
  let R : ℝ → ℝ := fun x => μ / Real.sqrt (L.weierstrassP x).re
  let p := (L.weierstrassP x).re
  let q := (L.derivWeierstrassP x).re
  let s := Real.sqrt p
  have hμ : 0 < μ := square_sqrt_branch.1
  rcases square_real_branch x hx with ⟨hn,hpi,hqi,hp,hq,hpd,hqd⟩
  change 0 < p at hp
  have hs : 0 < s := Real.sqrt_pos.mpr hp
  have hs2 : s ^ 2 = p := Real.sq_sqrt hp.le
  have hR : 0 < R x := div_pos hμ hs
  have hRD := (hasDerivAt_const x μ).div (hpd.sqrt hp.ne') hs.ne'
  have hlogR : HasDerivAt (fun y => Real.log (R y)) (-q / (2 * p)) x := by
    apply (hRD.log hR.ne').congr_deriv
    change ((0 * s - μ * (q / (2 * s))) / s ^ 2) / (μ / s) = -q / (2 * p)
    rw [← hs2]
    field_simp [hμ.ne',hs.ne']
    <;> ring
  have hident : Set.EqOn R (Function.invFun CothSums.chi) (Set.Ioo (0 : ℝ) 1) := square_actual_inverse.2
  have he : (fun y : ℝ => Real.log (Function.invFun CothSums.chi y)) =ᶠ[𝓝 x]
      (fun y => Real.log (R y)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact congrArg Real.log (hident hy).symm
  have hlog : HasDerivAt (fun y : ℝ => Real.log (Function.invFun CothSums.chi y))
      (-q / (2 * p)) x := hlogR.congr_of_eventuallyEq he
  have hpC : L.weierstrassP x = (p : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hpi
  have hqC : L.derivWeierstrassP x = (q : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hqi
  have hU : -L.derivWeierstrassP x / (2 * L.weierstrassP x) = ((-q / (2 * p) : ℝ) : ℂ) := by
    rw [hpC,hqC]
    push_cast
    rfl
  constructor
  · change -L.derivWeierstrassP x / (2 * L.weierstrassP x) = _
    exact hU.trans hlog.ofReal_comp.deriv.symm
  · change HasDerivAt (fun y : ℝ => (Real.log (Function.invFun CothSums.chi y) : ℂ))
      (-L.derivWeierstrassP x / (2 * L.weierstrassP x)) x
    rw [hU]
    exact hlog.ofReal_comp


theorem CothSums.polynomial_fourier_test_moment : ∀ P : Polynomial ℝ, P.eval 0 = 0 → P.eval 1 = 0 → CothSums.testMoment P = 2 * ∑' n : ℕ, (Real.tanh (Real.pi * (2 * (n : ℝ) + 1) / 2) / (2 * (n : ℝ) + 1)) * CothSums.cosineTest P n := by
  let L := CothSums.lemniscaticPeriodPair
  let U : ℂ → ℂ := fun z => -L.derivWeierstrassP z / (2 * L.weierstrassP z)
  obtain ⟨q, hq, hq0, hqu⟩ := CothSums.square_lattice_log_derivative_regularized_square
  have ha := CothSums.square_lattice_log_derivative_antiperiodic
  exact CothSums.polynomial_fourier_from_complex_data U q ha.1 ha.2
    hq.differentiableOn hqu hq0
    (fun x hx => (CothSums.lemniscatic_square_lattice_actual_log_derivative x hx).1)

theorem CothSums.fifth_power_evaluation :
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
  exact CothSums.evaluation_of_fourier_identity CothSums.polynomial_fourier_test_moment
