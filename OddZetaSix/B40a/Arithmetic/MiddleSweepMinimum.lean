import OddZetaSix.B40a.Arithmetic.MiddleSweepRanks
import OddZetaSix.B40a.Arithmetic.MiddleCapLayers
import Mathlib.Data.List.OfFn

namespace OddZetaSix.B40a.Cert.Sweep
open Finset

theorem population_eq_card (bag : Array ℤ) (q j : ℕ) (hbag : ∀ r<bag.size,bag[r]!≤16) :
    population bag q j = (((range bag.size).filter (fun r=>(j:ℤ)≤adjusted bag q r)).card:ℤ) := by
  unfold population
  have hcard := Finset.card_filter (s:=range bag.size) (fun r=>(j:ℤ)≤adjusted bag q r)
  push_cast [hcard]
  apply sum_congr rfl
  intro r hr
  have h := hbag r (mem_range.mp hr)
  have hw : adjusted bag q r≤16 := by unfold adjusted; omega
  simp only [eligible,hw,and_true] <;> split <;> rfl

theorem book_cap (d : ℤ) (es : List Event) :
    cappedLayers d (book es blank)=∑ j ∈ Ico 1 17,min (40*d) (level es j) := by
  rw [cappedLayers_eq_levels]
  apply sum_congr rfl
  intro j hj
  congr 1
  rw [←sum_bin_eq_level es j (by have := mem_Ico.mp hj; omega)]
  apply sum_congr rfl
  intro i hi
  obtain ⟨h₁,h₂⟩ := mem_Ico.mp hi
  exact book_blank_bin es i (by have := mem_Ico.mp hj; omega) h₂

theorem allAt_level (b : ℤ × Array ℤ) (j : ℕ) :
    level (allAt b) j=b.1*∑ r ∈ range b.2.size,eligible j b.2[r]! := by
  let F := fun w : ℤ=>b.1*eligible j w
  have H : level (allAt b) j=(b.2.toList.map F).sum := by
    unfold level allAt; rw [List.map_map]
    apply congrArg List.sum; apply List.map_congr_left
    intro w _; dsimp [F,eligible]; split <;> simp
  rw [H,mul_sum,←listRangeSum]
  apply congrArg List.sum
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have his : i<b.2.size := by simpa using hi
    simp [F,his,getElem!_pos b.2 i his]

theorem folded_le_all (bs : Classes) (q j : ℕ) (hj : 0<j)
    (hb : ∀ b∈bs,0≤b.1 ∧ ∀ r<b.2.size,b.2[r]!≤16) :
    level (folded bs q) j ≤ level (bs.flatMap allAt) j := by
  rw [folded_population _ _ _ hj (fun b h=>(hb b h).2),level_flatMap]
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have hh := hb b List.mem_cons_self
    have ht := ih (fun z hz => hb z (List.mem_cons_of_mem _ hz))
    simp only [List.map_cons,List.sum_cons]
    apply add_le_add _ ht
    rw [allAt_level]
    apply mul_le_mul_of_nonneg_left _ hh.1
    apply sum_le_sum; intro r hr
    have h := hh.2 r (mem_range.mp hr)
    unfold adjusted eligible
    split_ifs <;> omega

private theorem below_min_fold {α : Type} (xs : List α) (f : α→ℤ) (v target : ℤ)
    (hv : target≤v) (hf : ∀ x∈xs,target≤f x) :
    target≤xs.foldl (fun s x=>min s (f x)) v := by
  induction xs generalizing v with
  | nil => exact hv
  | cons a xs ih =>
    exact ih _ (le_min hv (hf a List.mem_cons_self)) (fun z hz=>hf z (List.mem_cons_of_mem _ hz))

/-- At the last row index the correction vanishes and the clipped folded
cost can only improve the unfolded one. Hence all admissible row bounds
suffice, including when the checker returns its initial unfolded value. -/
theorem le_best_of_all_rows (bs : Classes) (p d : ℤ) (K : ℕ) (target : ℤ)
    (hb : ∀ b∈bs,0≤b.1 ∧ ∀ r<b.2.size,b.2[r]!≤16)
    (h : ∀ q≤K,target≤score bs p d K q) : target≤best bs p d K (K+1) := by
  apply below_min_fold
  · have hl := h K le_rfl
    simp only [score,rowCharge,Nat.sub_self,Nat.cast_zero,mul_zero,
      Nat.zero_div,sub_zero,zero_add] at hl
    apply hl.trans
    rw [book_cap,book_cap]
    apply sum_le_sum; intro j hj
    exact min_le_min_left _ (folded_le_all _ _ _ (by have := mem_Ico.mp hj; omega) hb)
  · intro q hq; exact h q (by have := List.mem_range.mp hq; omega)

end OddZetaSix.B40a.Cert.Sweep
