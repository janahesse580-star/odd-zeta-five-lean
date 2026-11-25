import OddZetaSix.B40a.Arithmetic.MiddleBandRate
import OddZetaSix.B40a.Arithmetic.OuterBandsRate
import Mathlib.Order.Filter.ENNReal

noncomputable section
namespace OddZetaSix.B40a
open Filter

/-- All three prime bands for the true rational polynomial content, at the
unrounded certificate constant. The arbitrary positive margin accounts for PNT. -/
theorem content_arithmetic_rate (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ n : ℕ in atTop,(-Real.log |(content n:ℝ)|)/normalizer n ≤
      6140423661027/1000000000000+δ := by
  filter_upwards [content_cost_outside_middle (δ/2) (by positivity),
    middle_prime_cost_rate (δ/2) (by positivity)] with n ha hb
  rw [sub_div] at ha
  linarith only [ha,hb]

/-- Strict rounding slack makes the exact requested bound eventual. -/
theorem content_arithmetic_eventually :
    ∀ᶠ n : ℕ in atTop,(-Real.log |(content n:ℝ)|)/normalizer n ≤ 61405/10000 := by
  filter_upwards [content_arithmetic_rate (1/100000) (by norm_num)] with n h
  linarith only [h]

theorem content_arithmetic_limsup :
    limsup (fun n : ℕ=>(-Real.log |(content n:ℝ)|)/normalizer n) atTop ≤ 61405/10000 := by
  by_cases hc : atTop.IsCoboundedUnder (·≤·) (fun n : ℕ=>(-Real.log |(content n:ℝ)|)/normalizer n)
  · exact limsup_le_of_le hc content_arithmetic_eventually
  · rw [Real.limsup_of_not_isCoboundedUnder hc]; norm_num

theorem content_arithmetic_exp :
    ∀ᶠ n : ℕ in atTop, |(content n:ℝ)|⁻¹ ≤ Real.exp ((61405/10000:ℝ)*normalizer n) := by
  filter_upwards [content_arithmetic_eventually,eventually_gt_atTop (0:ℕ)] with n h hn
  have hN : 0<normalizer n := by unfold normalizer; positivity
  have hpos : 0 < |(content n:ℝ)| := abs_pos.mpr (by exact_mod_cast content_ne_zero n)
  rw [←Real.log_inv] at h
  simpa only [Real.exp_log (inv_pos.mpr hpos)] using Real.exp_le_exp.mpr ((div_le_iff₀ hN).mp h)
end OddZetaSix.B40a
