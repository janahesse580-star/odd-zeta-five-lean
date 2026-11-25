import OddZetaSix.B40a.Arithmetic.HighTailBounds
import OddZetaSix.B40a.Arithmetic.WeightedPNT
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The high-prime part of the genuine B40a prime cost has rate at most 1671/2000. -/
noncomputable section
namespace OddZetaSix.B40a
open Finset Filter
open scoped BigOperators Topology Interval

private theorem basis_correction_le (n p : ℕ) :
    2*((40*n-(p+1)/2 : ℕ) : ℤ) ≤ max 0 (80*(n : ℤ)-(p : ℤ)) := by
  by_cases h : (p+1)/2 ≤ 40*n
  · rw [Nat.cast_sub h]
    have hceil : p ≤ 2*((p+1)/2) := by omega
    have hceilZ : (p : ℤ) ≤ 2*(((p+1)/2 : ℕ) : ℤ) := by exact_mod_cast hceil
    exact (by push_cast; omega : 2*((40*n : ℕ) - (((p+1)/2 : ℕ) : ℤ)) ≤ 80*(n : ℤ) - p).trans
      (le_max_right _ _)
  · rw [Nat.sub_eq_zero_of_le (by omega : 40*n ≤ (p+1)/2),Nat.cast_zero,mul_zero]
    exact le_max_left _ _

private def highLo : Fin 4 → ℝ := ![50,51,59,80]
private def highHi : Fin 4 → ℝ := ![51,59,80,84]
private def highIntercept : Fin 4 → ℝ := ![2462,1850,80,0]
private def highSlope : Fin 4 → ℝ := ![43,31,1,0]

def highBandWeight (i : Fin 4) (x : ℝ) : ℝ := highIntercept i-highSlope i*x

private theorem highIntegral_eval (a b c d : ℝ) :
    (∫ x in a..b, c-d*x) = (b-a)*c-d*((b^2-a^2)/2) := by
  have hc : IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume a b :=
    continuous_const.intervalIntegrable _ _
  have hd : IntervalIntegrable (fun x : ℝ => d*x) MeasureTheory.volume a b :=
    (show Continuous (fun x : ℝ => d*x) from continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hc hd,intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,integral_id,smul_eq_mul]

theorem highBandWeight_integral :
    (∑ i : Fin 4, ∫ x in highLo i..highHi i, highBandWeight i x)/2000 =
      1671/2000 := by
  simp only [highBandWeight,highIntegral_eval,Fin.sum_univ_succ,Fin.sum_univ_zero,
    highLo,highHi,highIntercept,highSlope,Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num

private theorem highBandWeight_nonneg (i : Fin 4) (x : ℝ)
    (hx : x ∈ Set.Icc (highLo i) (highHi i)) : 0 ≤ highBandWeight i x := by
  have h := hx.2
  fin_cases i <;> norm_num [highBandWeight,highHi,highIntercept,highSlope,Matrix.cons_val_zero,
    Matrix.cons_val_succ] at h ⊢ <;> linarith

private theorem highWeight1 (n p : ℕ) [Fact p.Prime] (h50 : 50*n < p) (h51 : p ≤ 51*n) :
    primeExponent n p ≤ (n : ℝ) * highBandWeight 0 ((p : ℝ)/(n : ℝ))+42 := by
  have h := content_high_capacity_bound n p h50
  have hL := highLayerCost_le_band1 n p h50 h51
  have hB := basis_correction_le n p
  have h0 : 0 ≤ 80*(n : ℤ) - (p : ℤ) := by omega
  rw [max_eq_right h0] at hB
  have h1 : max 0 (-padicValRat p (content n)) ≤ 2462*(n : ℤ)-43*(p : ℤ)+42 := by
    apply max_le (by omega)
    omega
  have hR : primeExponent n p ≤ 2462*(n : ℝ)-43*(p : ℝ)+42 := by unfold primeExponent; exact_mod_cast h1
  have hn : (n : ℝ) ≠ 0 := by
    have hp := (Fact.out : p.Prime).two_le
    by_cases h : n=0
    · subst n
      omega
    · exact_mod_cast h
  have he : (n : ℝ) * highBandWeight 0 ((p : ℝ)/(n : ℝ))+42 =
      2462*(n : ℝ)-43*(p : ℝ)+42 := by
    change (n : ℝ)*(2462-43*((p : ℝ)/(n : ℝ)))+42 = _
    field_simp <;> ring
  rw [he]
  exact (by simpa using hR)


private theorem highWeight2 (n p : ℕ) [Fact p.Prime] (h51 : 51*n < p) (h59 : p ≤ 59*n) :
    primeExponent n p ≤ (n : ℝ) * highBandWeight 1 ((p : ℝ)/(n : ℝ))+42 := by
  have h := content_high_capacity_bound n p (by omega)
  have hL := highLayerCost_le_band2 n p h51 h59
  have hB := basis_correction_le n p
  have h0 : 0 ≤ 80*(n : ℤ) - (p : ℤ) := by omega
  rw [max_eq_right h0] at hB
  have h1 : max 0 (-padicValRat p (content n)) ≤ 1850*(n : ℤ)-31*(p : ℤ)+42 := by
    apply max_le (by omega)
    omega
  have hR : primeExponent n p ≤ 1850*(n : ℝ)-31*(p : ℝ)+42 := by unfold primeExponent; exact_mod_cast h1
  have hn : (n : ℝ) ≠ 0 := by
    have hp := (Fact.out : p.Prime).two_le
    by_cases h : n=0
    · subst n
      omega
    · exact_mod_cast h
  have he : (n : ℝ) * highBandWeight 1 ((p : ℝ)/(n : ℝ))+42 =
      1850*(n : ℝ)-31*(p : ℝ)+42 := by
    change (n : ℝ)*(1850-31*((p : ℝ)/(n : ℝ)))+42 = _
    field_simp <;> ring
  rw [he]
  exact (by simpa using hR)


private theorem highWeight3 (n p : ℕ) [Fact p.Prime] (h59 : 59*n < p) (h80 : p ≤ 80*n) :
    primeExponent n p ≤ (n : ℝ) * highBandWeight 2 ((p : ℝ)/(n : ℝ))+42 := by
  have h := content_high_regular_bound n p h59
  have hB := basis_correction_le n p
  have h0 : 0 ≤ 80*(n : ℤ) - (p : ℤ) := by omega
  rw [max_eq_right h0] at hB
  have h1 : max 0 (-padicValRat p (content n)) ≤ 80*(n : ℤ)-(p : ℤ)+42 := by
    apply max_le (by omega)
    omega
  have hR : primeExponent n p ≤ 80*(n : ℝ)-(p : ℝ)+42 := by unfold primeExponent; exact_mod_cast h1
  have hn : (n : ℝ) ≠ 0 := by
    have hp := (Fact.out : p.Prime).two_le
    by_cases h : n=0
    · subst n
      omega
    · exact_mod_cast h
  have he : (n : ℝ) * highBandWeight 2 ((p : ℝ)/(n : ℝ))+42 =
      80*(n : ℝ)-1*(p : ℝ)+42 := by
    change (n : ℝ)*(80-1*((p : ℝ)/(n : ℝ)))+42 = _
    field_simp <;> ring
  rw [he]
  exact (by simpa using hR)


private theorem highWeight4 (n p : ℕ) [Fact p.Prime] (h80 : 80*n < p) :
    primeExponent n p ≤ (n : ℝ) * highBandWeight 3 ((p : ℝ)/(n : ℝ))+42 := by
  have h := content_high_regular_bound n p (by omega)
  have hB := basis_correction_le n p
  have h0 : 80*(n : ℤ) - (p : ℤ) ≤ 0 := by omega
  rw [max_eq_left h0] at hB
  have hz : max 0 (-padicValRat p (content n)) ≤ 0 := max_le le_rfl (h.trans hB)
  have hR : primeExponent n p ≤ 0 := by unfold primeExponent; exact_mod_cast hz
  simpa [highBandWeight,highIntercept,highSlope,Matrix.cons_val_zero,Matrix.cons_val_succ] using
    hR.trans (show (0 : ℝ) ≤ 42 by norm_num)

theorem high_prime_cost_rate (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ n : ℕ in atTop, bandPrimeCost n 50 84 / normalizer n ≤ 1671/2000+δ := by
  have h := bandPrimeCost_rate_of_piecewise_majorant (univ : Finset (Fin 4)) 50 84
    (by norm_num) (by norm_num) highLo highHi highBandWeight
    (fun i _ => by fin_cases i <;> norm_num [highLo])
    (fun i _ => by fin_cases i <;> norm_num [highLo,highHi])
    (fun i _ => by fin_cases i <;> norm_num [highHi])
    (fun i _ => (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn)
    (fun i _ x hx => highBandWeight_nonneg i x hx) 42 (by norm_num)
    (fun _ => ∅) 0 (fun _ => empty_subset _) (by simp) ?_ δ hδ
  · rw [highBandWeight_integral] at h
    exact h
  · filter_upwards with n p hp _
    have hpm := mem_filter.mp hp
    have hpr := (Nat.mem_primesLE.mp hpm.1).2
    have hp50 : 50*n < p := by exact_mod_cast hpm.2
    have hp84 : (p : ℝ) ≤ 84*(n : ℝ) :=
      (Nat.le_floor_iff (by positivity)).mp (Nat.mem_primesLE.mp hpm.1).1
    letI : Fact p.Prime := ⟨hpr⟩
    by_cases h51 : p ≤ 51*n
    · exact ⟨0,mem_univ _,by change (50 : ℝ)*(n : ℝ) < (p : ℝ); exact_mod_cast hp50,by change (p : ℝ) ≤ (51 : ℝ)*(n : ℝ); exact_mod_cast h51,highWeight1 n p hp50 h51⟩
    · have h51' : 51*n < p := by omega
      by_cases h59 : p ≤ 59*n
      · exact ⟨1,mem_univ _,by change (51 : ℝ)*(n : ℝ) < (p : ℝ); exact_mod_cast h51',by change (p : ℝ) ≤ (59 : ℝ)*(n : ℝ); exact_mod_cast h59,highWeight2 n p h51' h59⟩
      · have h59' : 59*n < p := by omega
        by_cases h80 : p ≤ 80*n
        · exact ⟨2,mem_univ _,by change (59 : ℝ)*(n : ℝ) < (p : ℝ); exact_mod_cast h59',by change (p : ℝ) ≤ (80 : ℝ)*(n : ℝ); exact_mod_cast h80,highWeight3 n p h59' h80⟩
        · have h80' : 80*n < p := by omega
          exact ⟨3,mem_univ _,by change (80 : ℝ)*(n : ℝ) < (p : ℝ); exact_mod_cast h80',hp84,highWeight4 n p h80'⟩

end OddZetaSix.B40a
