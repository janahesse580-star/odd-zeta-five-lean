import OddZetaSix.B40a.Arithmetic.MiddleSweepBins
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OddZetaSix.B40a.Cert.Sweep
open Finset

def eligible (j : ℕ) (z : ℤ) : ℤ := if (j:ℤ)≤z ∧ z≤16 then 1 else 0
def adjusted (bag : Array ℤ) (q r : ℕ) : ℤ := bag[r]! - 2*((r-q:ℕ):ℤ)
def population (bag : Array ℤ) (q j : ℕ) : ℤ :=
  ∑ r ∈ range bag.size,eligible j (adjusted bag q r)

theorem level_flatMap {α : Type} (xs : List α) (f : α → List Event) (j : ℕ) :
    level (xs.flatMap f) j=(xs.map (fun x=>level (f x) j)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,level_append,ih,List.map_cons,List.sum_cons]

theorem listRangeSum (n : ℕ) (f : ℕ → ℤ) :
    ((List.range n).map f).sum=∑ a ∈ range n,f a := by
  induction n with
  | zero => simp
  | succ m ih => simp [List.range_succ,ih,sum_range_succ]

theorem nrangeSum (a b : ℕ) (f : ℕ → ℤ) :
    ((nrange a b).map f).sum=∑ i ∈ Ico a b,f i := by
  rw [nrange,List.map_map,listRangeSum,sum_Ico_eq_sum_range]
  apply sum_congr rfl
  intro i _
  simp only [Function.comp_apply]

private theorem level_one (z v : ℤ) (j : ℕ) : level [(z,v)] j=v*eligible j z := by
  simp only [level,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,eligible]
  split <;> simp_all

theorem head_level (b : ℤ × Array ℤ) (q j : ℕ) :
    level (headAt q b) j= b.1*(if q<b.2.size then eligible j b.2[q]! else 0) := by
  unfold headAt
  split
  · exact level_one _ _ _
  · simp [level]

theorem tail_level (b : ℤ × Array ℤ) (q j : ℕ) (hj : 0<j) :
    level (tailAt q b) j = b.1 * ∑ r ∈ Ico (q+1) (min (q+8) b.2.size),eligible j (adjusted b.2 q r) := by
  unfold tailAt
  rw [level_flatMap,nrangeSum,mul_sum]
  apply sum_congr rfl
  intro r _
  change level (if 0<adjusted b.2 q r then [(adjusted b.2 q r,b.1)] else []) j = _
  split_ifs with h
  · exact level_one _ _ _
  · have : ¬((j:ℤ)≤adjusted b.2 q r ∧ adjusted b.2 q r≤16) := by omega
    simp [eligible,this,level]

private theorem commute_sum {α : Type} (bs : List α) (K : ℕ) (F : ℕ → α → ℤ) :
    (∑ i ∈ range K,(bs.map (F i)).sum) = (bs.map (fun b=>∑ i ∈ range K,F i b)).sum := by
  induction bs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,sum_add_distrib,ih]

private theorem sum_map_add {α : Type} (bs : List α) (f g : α→ℤ) :
    (bs.map f).sum+(bs.map g).sum=(bs.map (fun b=>f b+g b)).sum := by
  induction bs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons]; rw [←ih]; omega

private theorem split_population (bag : Array ℤ) (q j : ℕ) (hj : 0<j)
    (hbag : ∀ r<bag.size,bag[r]!≤16) :
    (∑ r ∈ range (q+1),if r<bag.size then eligible j bag[r]! else 0)+
    (∑ r ∈ Ico (q+1) (min (q+8) bag.size),eligible j (adjusted bag q r)) = population bag q j := by
  let f (r : ℕ) := eligible j (adjusted bag q r)
  let first := (range bag.size).filter (fun r => r≤q)
  let last := (range bag.size).filter (fun r => q<r)
  have he : (range (q+1)).filter (fun r=>r<bag.size)=first := by ext r; simp [first]; omega
  have hf : (∑ r ∈ range (q+1),if r<bag.size then eligible j bag[r]! else 0) = ∑ r ∈ first,f r := by
    rw [←sum_filter,he]
    apply sum_congr rfl; intro r hr
    have h := (mem_filter.mp hr).2
    change r≤q at h
    simp [f,adjusted,Nat.sub_eq_zero_of_le h]
  have hs : Ico (q+1) (min (q+8) bag.size) ⊆ last := by
    intro r hr; obtain ⟨h₁,h₂⟩ := mem_Ico.mp hr
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),by omega⟩
  have ht : (∑ r ∈ Ico (q+1) (min (q+8) bag.size),f r) = ∑ r ∈ last,f r := by
    apply sum_subset hs
    intro r hr hn
    have h₁ := mem_range.mp (mem_filter.mp hr).1
    have h₂ := (mem_filter.mp hr).2
    have h₃ : q+8≤r := by
      by_contra! hf; exact hn (mem_Ico.mpr ⟨by omega,by omega⟩)
    have hv := hbag r h₁
    have hz : ¬ ((j:ℤ)≤adjusted bag q r ∧ adjusted bag q r≤16) := by unfold adjusted; omega
    simp [f,eligible,hz]
  rw [hf,show (∑ r ∈ Ico (q+1) (min (q+8) bag.size),eligible j (adjusted bag q r))=_ from ht]
  change (∑ r ∈ (range bag.size).filter (fun r=>r≤q),f r)+
    (∑ r ∈ (range bag.size).filter (fun r=>q<r),f r)=∑ r ∈ range bag.size,f r
  simpa only [not_le] using sum_filter_add_sum_filter_not (range bag.size) (fun r=>r≤q) f

/-- The executable prefix/suffix sweep counts exactly the weighted population
of all ranks above each positive threshold after subtracting twice the rank excess. -/
theorem folded_population (bs : Classes) (q j : ℕ) (hj : 0<j)
    (hb : ∀ b∈bs,∀ r<b.2.size,b.2[r]!≤16) :
    level (folded bs q) j=(bs.map (fun b=>b.1*population b.2 q j)).sum := by
  rw [folded,level_append,heads,level_flatMap,listRangeSum,level_flatMap]
  simp_rw [level_flatMap,head_level,tail_level _ _ _ hj]
  rw [commute_sum,sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b h
  rw [←mul_sum,←mul_add,split_population _ _ _ hj (hb b h)]

end OddZetaSix.B40a.Cert.Sweep
