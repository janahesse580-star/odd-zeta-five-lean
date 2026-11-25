import OddZetaSix.B40a.Arithmetic.HighCapacity

/-! Finite endpoint counts for the high-prime capacity. -/
noncomputable section
namespace OddZetaSix.B40a
open Finset

theorem kernelPoleSet_eq_outer (n : ℕ) : kernelPoleSet n = Icc (34*n+1) (84*n+1) := by
  apply Finset.ext
  intro k
  rw [Finset.mem_Icc]
  constructor
  · exact kernel_pole_address_bounds n k
  · intro h
    simp only [kernelPoleSet, List.mem_toFinset, kernelPoleList, List.mem_flatMap,
      List.mem_finRange, true_and, List.mem_map, List.mem_range]
    refine ⟨0,k-(34*n+1),?_,?_⟩ <;>
      simp only [show offsets (0 : Fin 12) = 0 by decide,add_zero,mul_zero,Nat.sub_zero] <;> omega

theorem high_active_order (n p k : ℕ) (hp : 50*n < p) (hk : k ∈ kernelPoleSet n)
    (hx : p ≤ k-25*n-1) :
    poleOrder n k = if k ≤ 76*n+1 then 10 else 6 := by
  have hb := kernel_pole_address_bounds n k hk
  have hn : 0 < n := by omega
  rw [← kernelPoleOrder_eq_poleOrder, ← kernelPoleOrder_eq_block_count]
  have h0 (b : Fin 12) :
      ((if blockStart n b ≤ k ∧ k ≤ blockStart n b + blockLen n b then 1 else 0) : ℕ) =
        if b.val < 6 then 1 else if b.val < 10 ∧ k ≤ 76*n+1 then 1 else 0 := by
    fin_cases b <;>
      simp only [blockStart,blockLen,offsets] <;>
      norm_num <;> (first | omega | split_ifs <;> omega)
  simp_rw [h0]
  by_cases h : k ≤ 76*n+1
  · simp only [h,and_true,ite_true]
    decide
  · simp only [h,and_false,ite_false]
    decide

def highTenSites (n p : ℕ) : Finset ℕ := Icc (p+25*n+1) (76*n+1)
def highSixSites (n p : ℕ) : Finset ℕ := Icc (max (76*n+2) (p+25*n+1)) (84*n+1)

theorem high_active_iff (n p k : ℕ) (hp : 50*n < p) :
    (k ∈ kernelPoleSet n ∧ p ≤ k-25*n-1) ↔
      k ∈ highTenSites n p ∨ k ∈ highSixSites n p := by
  rw [kernelPoleSet_eq_outer]
  simp only [highTenSites,highSixSites,Finset.mem_Icc,max_le_iff]
  omega

theorem highTenSites_card (n p : ℕ) : (highTenSites n p).card = 51*n+1-p := by
  rw [highTenSites,Nat.card_Icc]
  omega

theorem highSixSites_card (n p : ℕ) : (highSixSites n p).card =
    84*n+2-max (76*n+2) (p+25*n+1) := by
  rw [highSixSites,Nat.card_Icc]

end OddZetaSix.B40a
