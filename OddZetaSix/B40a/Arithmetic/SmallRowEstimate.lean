import OddZetaSix.B40a.Arithmetic.ReciprocalTile
import OddZetaSix.B40a.Arithmetic.ReciprocalBudget

namespace OddZetaSix.B40a.Cert
open Finset MeasureTheory
open PeriodAffine
set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def inBand (r : ArithRow) := decide (0≤r.left ∧ r.left<r.right ∧ r.right≤1 ∧
  (9/11≤r.left ∨ r.right≤9/11))
private theorem allInBand : smallRows.all inBand = true := by decide +kernel
theorem smallRow_bounds (r : ArithRow) (hr : r ∈ smallRows) :
    0≤r.left ∧ r.left<r.right ∧ r.right≤1 ∧ (9/11≤r.left ∨ r.right≤9/11) :=
  of_decide_eq_true (List.all_eq_true.mp allInBand _ hr)

theorem smallRow_budget_checked (r : ArithRow) (hr : r ∈ smallRows) (hcheck : PeriodAffine.check r = true) (N : ℕ) :
    (∑ k ∈ Ico (periodStart r.left) N,
      ∫ P in 1/((k:ℝ)+r.right)..1/((k:ℝ)+r.left),smallTileWeight r k P) ≤
        2000*(rowValue true r:ℝ) := by
  have hb := smallRow_bounds r hr
  let a : ℝ := r.left
  let b : ℝ := r.right
  let F : ℝ := (periodScores (mid r)).1
  let G : ℝ := (periodScores (mid r)).2
  let s := periodStart r.left
  have hpos : 0<s := by dsimp [s,periodStart]; split <;> decide
  have ha : 0≤a := by dsimp [a]; exact_mod_cast hb.1
  have hab : 0≤b-a := sub_nonneg.mpr (by dsimp [a,b]; exact_mod_cast hb.2.1.le)
  obtain ⟨hF,hG⟩ := smallRows_midpoint_integrals r hr
  have F0 : 0≤F := by
    dsimp [F,mid]; rw [hF]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => by exact_mod_cast (periodicScore_bounds _ u).1)
  have G0 : 0≤G := by
    dsimp [G,mid]; rw [hG]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => by
      exact_mod_cast Int.ediv_nonneg (sq_nonneg _) (by decide : (0:ℤ)≤4))
  have hsum :
      (∑ k ∈ Ico s N,∫ P in 1/((k:ℝ)+b)..1/((k:ℝ)+a),smallTileWeight r k P) ≤
      (b-a)*((40*F)*(∑ k ∈ Ico s N,1/((k:ℝ)+a)^2) +
        ((F+G)/2)*(∑ k ∈ Ico s N,1/((k:ℝ)+a)^3)) := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply sum_le_sum
    intro k hk
    have hkr : (0:ℝ)<k := by exact_mod_cast hpos.trans_le (mem_Ico.mp hk).1
    apply (reciprocal_tile_integral r hr hcheck k (by change 0<(k:ℝ)+a; linarith)).trans
    change (b-a)*(40*F/((k:ℝ)+a)^2+(F+G)/(2*((k:ℝ)+a)^3)) ≤ _
    apply le_of_eq
    simp only [div_eq_mul_inv,mul_inv_rev]; ring
  have h₂ := reciprocalSum_majorant r.left hb.1 2 N (Or.inl rfl)
  have h₃ := reciprocalSum_majorant r.left hb.1 3 N (Or.inr rfl)
  have hcost := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 40*F by positivity))
      (mul_le_mul_of_nonneg_left h₃ (show 0 ≤ (F+G)/2 by positivity))) hab
  apply (hsum.trans hcost).trans
  apply le_of_eq
  simp only [rowValue,ite_true,smallValue,mid,F,G,a,b]
  push_cast
  ring

theorem small_rows_total : arithTotal smallRows = 60166783595 := by decide +kernel

end OddZetaSix.B40a.Cert
