import OddZetaSix.B40a.Arithmetic.HighCounts

/-! Explicit layer counts and linear upper bounds in the high-prime band. -/
noncomputable section
namespace OddZetaSix.B40a
open Finset
open scoped BigOperators

def slotsAtLevel (m : ℕ) (s : ℤ) : ℕ :=
  ((univ : Finset (Fin 12)).filter (fun a => a.val < m ∧ s ≤ ((m+4-2*a.val : ℕ) : ℤ))).card

def highLevelCard (n p : ℕ) (s : ℤ) : ℕ :=
  ((univ : Finset (HighColumn n)).filter (fun u => s ≤ (highColumnCapacity n p u : ℤ))).card

theorem highLevelCard_eq (n p : ℕ) (hp : 50*n < p) (s : ℤ) (hs : 1 ≤ s) :
    highLevelCard n p s =
      (highTenSites n p).card * slotsAtLevel 10 s + (highSixSites n p).card * slotsAtLevel 6 s := by
  unfold highLevelCard
  rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_sum_type,Fintype.sum_prod_type]
  have hns : ¬ s ≤ (0 : ℤ) := by omega
  simp only [highColumnCapacity,Nat.cast_zero,ite_eq_right hns,Finset.sum_const_zero,zero_add]
  let f := fun k : ℕ => if k ∈ highTenSites n p then slotsAtLevel 10 s else 0
  let g := fun k : ℕ => if k ∈ highSixSites n p then slotsAtLevel 6 s else 0
  have hsite (k : {k // k ∈ kernelPoleSet n}) :
      (∑ a : Fin 12, if s ≤ (highSiteCapacity n p k.val a.val : ℤ) then 1 else 0) =
      f k.val + g k.val := by
    have hh := high_active_iff n p k.val hp
    by_cases hactive : p ≤ k.val-25*n-1
    · have hm := high_active_order n p k.val hp k.property hactive
      by_cases h10 : k.val ≤ 76*n+1
      · have hf : k.val ∈ highTenSites n p := by
          rw [highTenSites,mem_Icc]
          exact ⟨by omega,h10⟩
        have hg : k.val ∉ highSixSites n p := by
          simp only [highSixSites,mem_Icc,max_le_iff]
          omega
        rw [ite_eq_left h10] at hm
        simp only [f,g,hf,hg,ite_true,ite_false,add_zero,slotsAtLevel,Finset.card_eq_sum_ones,
          Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a _
        simp only [highSiteCapacity,hactive,hm,true_and]
        by_cases ha : a.val < 10 <;> simp [ha,hns]
      · have hf : k.val ∉ highTenSites n p := fun h => h10 (mem_Icc.mp h).2
        have hg := (hh.mp ⟨k.property,hactive⟩).resolve_left hf
        rw [ite_eq_right h10] at hm
        simp only [f,g,hf,hg,ite_true,ite_false,zero_add,slotsAtLevel,Finset.card_eq_sum_ones,
          Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a _
        simp only [highSiteCapacity,hactive,hm,true_and]
        by_cases ha : a.val < 6 <;> simp [ha,hns]
    · have h0 : ¬ (k.val ∈ highTenSites n p ∨ k.val ∈ highSixSites n p) :=
        fun h => hactive (hh.mpr h).2
      have hT : k.val ∉ highTenSites n p := fun h => h0 (Or.inl h)
      have hS : k.val ∉ highSixSites n p := fun h => h0 (Or.inr h)
      simp [highSiteCapacity,hactive,hns,f,g,hT,hS]
  change (∑ k : {k // k ∈ kernelPoleSet n}, ∑ a : Fin 12,
    if s ≤ (highSiteCapacity n p k.val a.val : ℤ) then 1 else 0) = _
  simp_rw [hsite]
  have hu : (univ : Finset {k // k ∈ kernelPoleSet n}) = (kernelPoleSet n).attach := by
    ext x
    simp
  rw [hu,Finset.sum_attach (kernelPoleSet n) (fun k => f k + g k),Finset.sum_add_distrib]
  simp only [f,g,← Finset.sum_filter]
  have hT : (kernelPoleSet n).filter (fun k => k ∈ highTenSites n p) = highTenSites n p := by
    ext k
    rw [mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨((high_active_iff n p k hp).mpr (Or.inl h)).1,h⟩⟩
  have hS : (kernelPoleSet n).filter (fun k => k ∈ highSixSites n p) = highSixSites n p := by
    ext k
    rw [mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨((high_active_iff n p k hp).mpr (Or.inr h)).1,h⟩⟩
  rw [hT,hS]
  simp

theorem highLayerCost_le_band1 (n p : ℕ) (hp : 50*n < p) (h51 : p ≤ 51*n) :
    highLayerCost n p ≤ 240*(n : ℤ)+42*(51*(n : ℤ)-p)+42 := by
  change ∑ s ∈ Icc (1 : ℤ) 18, (min (fiveRank n) (highLevelCard n p s) : ℤ) ≤ _
  have hs : Icc (1 : ℤ) 18 = Icc 1 2 ∪ Icc 3 18 := by decide
  have hd : Disjoint (Icc (1 : ℤ) 2) (Icc 3 18) := by decide
  rw [hs,Finset.sum_union hd]
  have hleft : (∑ s ∈ Icc (1 : ℤ) 2, (min (fiveRank n) (highLevelCard n p s) : ℤ)) ≤
      2*(fiveRank n : ℤ) := by
    calc
      _ ≤ ∑ _s ∈ Icc (1 : ℤ) 2, (fiveRank n : ℤ) :=
        Finset.sum_le_sum (fun _ _ => by exact_mod_cast min_le_left _ _)
      _ = _ := by simp [Finset.sum_const]
  have hright : (∑ s ∈ Icc (3 : ℤ) 18, (min (fiveRank n) (highLevelCard n p s) : ℤ)) ≤
      ((highTenSites n p).card : ℤ)*42 + ((highSixSites n p).card : ℤ)*20 := by
    calc
      _ ≤ ∑ s ∈ Icc (3 : ℤ) 18, (highLevelCard n p s : ℤ) :=
        Finset.sum_le_sum (fun _ _ => by exact_mod_cast min_le_right _ _)
      _ = _ := by
        have h10 : (∑ s ∈ Icc (3 : ℤ) 18, (slotsAtLevel 10 s : ℤ)) = 42 := by decide
        have h6 : (∑ s ∈ Icc (3 : ℤ) 18, (slotsAtLevel 6 s : ℤ)) = 20 := by decide
        rw [← h10,← h6,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro s hs
        rw [highLevelCard_eq n p hp s (by have := (mem_Icc.mp hs).1; omega)]
        norm_cast
  rw [highTenSites_card,highSixSites_card] at hright
  have h8 : 84*n+2-max (76*n+2) (p+25*n+1) ≤ 8*n := by
    have := le_max_left (76*n+2) (p+25*n+1)
    omega
  have h8z : ((84*n+2-max (76*n+2) (p+25*n+1) : ℕ) : ℤ) ≤ 8*(n : ℤ) := by exact_mod_cast h8
  rw [Nat.cast_sub (by omega : p ≤ 51*n+1)] at hright
  push_cast at hright
  have hRank : (fiveRank n : ℤ) = 40*(n : ℤ) := by unfold fiveRank; push_cast; ring
  rw [hRank] at hleft hright ⊢
  linarith

theorem highLayerCost_le_band2 (n p : ℕ) (hp : 51*n < p) (h59 : p ≤ 59*n) :
    highLayerCost n p ≤ 30*(59*(n : ℤ)-p)+30 := by
  change ∑ s ∈ Icc (1 : ℤ) 18, (min (fiveRank n) (highLevelCard n p s) : ℤ) ≤ _
  have h10 : (highTenSites n p).card = 0 := by rw [highTenSites_card]; omega
  have h6 : (highSixSites n p).card = 59*n+1-p := by
    rw [highSixSites_card,max_eq_right (by omega)]
    omega
  calc
    _ ≤ ∑ s ∈ Icc (1 : ℤ) 18, (highLevelCard n p s : ℤ) :=
      Finset.sum_le_sum (fun _ _ => by exact_mod_cast min_le_right _ _)
    _ = (((59*n+1-p : ℕ) : ℤ) * 30) := by
      have hcount : (∑ s ∈ Icc (1 : ℤ) 18, (slotsAtLevel 6 s : ℤ)) = 30 := by decide
      rw [← hcount,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [highLevelCard_eq n p (by omega) s (mem_Icc.mp hs).1,h10,h6,zero_mul,zero_add,Nat.cast_mul]
    _ = _ := by
      rw [Nat.cast_sub (by omega : p ≤ 59*n+1)]
      push_cast
      ring

end OddZetaSix.B40a
