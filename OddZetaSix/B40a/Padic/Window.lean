import OddZetaSix.B40a.Padic.HighPrimeSplit
import OddZetaSix.B40a.Padic.Hermite

/-! The support and multiplicity of the harmonic window at 51n+1. -/
namespace OddZetaSix.B40a
open Finset

def gateWindow (n : ℕ) : Finset ℕ := Icc (76*n+2) (84*n+1)

theorem gateWindow_card (n : ℕ) : (gateWindow n).card = 8*n := by
  rw [gateWindow, Nat.card_Icc]
  omega

theorem gateWindow_eq_filter (n : ℕ) :
    gateWindow n = (kernelPoleSet n).filter (fun k => primeIndex n ≤ k-25*n-1) := by
  apply Finset.ext
  intro k
  rw [Finset.mem_filter, gateWindow, Finset.mem_Icc]
  simp only [primeIndex]
  constructor
  · intro h
    refine ⟨?_, by omega⟩
    simp only [kernelPoleSet, List.mem_toFinset, kernelPoleList, List.mem_flatMap,
      List.mem_finRange, true_and, List.mem_map, List.mem_range]
    refine ⟨0, k-(34*n+1), ?_, ?_⟩ <;>
      simp only [show offsets (0 : Fin 12) = 0 by decide, add_zero, mul_zero, Nat.sub_zero] <;> omega
  · rintro ⟨hk,h⟩
    exact ⟨by omega, (kernel_pole_address_bounds n k hk).2⟩

private theorem count_gate_block (n k : ℕ) (hk : k ∈ gateWindow n) (b : Fin 12) :
    (((List.range ((50-2*offsets b)*n+1)).map fun j => (34+offsets b)*n+1+j).count k) =
      if b.val < 6 then 1 else 0 := by
  have h := mem_Icc.mp hk
  let l := (List.range ((50-2*offsets b)*n+1)).map fun j => (34+offsets b)*n+1+j
  change l.count k = _
  have hl : l.Nodup := (List.nodup_map_iff (fun _ _ hab => Nat.add_left_cancel hab)).mpr List.nodup_range
  have hm : k ∈ l ↔ b.val < 6 := by
    have hm' : k ∈ l ↔ (34+offsets b)*n+1 ≤ k ∧
        k < (34+offsets b)*n+1 + ((50-2*offsets b)*n+1) := by
      simp only [l,List.mem_map,List.mem_range]
      constructor
      · rintro ⟨j,hj,rfl⟩
        omega
      · rintro ⟨ha,hb⟩
        exact ⟨k-((34+offsets b)*n+1),by omega,by omega⟩
    rw [hm']
    fin_cases b <;> norm_num [offsets,Matrix.cons_val_zero,Matrix.cons_val_succ] <;> omega
  split_ifs with hb
  · have hpos := List.count_pos_iff.mpr (hm.mpr hb)
    have hle := List.nodup_iff_count_le_one.mp hl k
    omega
  · exact List.count_eq_zero.mpr (mt hm.mp hb)

theorem gateWindow_order (n k : ℕ) (hk : k ∈ gateWindow n) : kernelPoleOrder n k = 6 := by
  unfold kernelPoleOrder kernelPoleList
  rw [list_count_flatMap]
  calc
    _ = ((List.finRange 12).map fun b => if b.val < 6 then 1 else 0).sum := by
      congr 1
      apply List.map_congr_left
      intro b _
      exact count_gate_block n k hk b
    _ = 6 := by decide

/-- The doubled centered address is a strict positive representative below p. -/
theorem gateWindow_doubled_address (n k : ℕ) (hk : k ∈ gateWindow n) :
    0 < 2*(k-center n) ∧ 2*(k-center n) < primeIndex n := by
  have hh := mem_Icc.mp hk
  have hn : 0 < n := by omega
  unfold center primeIndex
  omega

theorem singularHigh_gate_window (n : ℕ) (i j : Fin (fiveRank n)) :
    singularHigh n (primeIndex n) i j =
    -(∑ k ∈ gateWindow n, ∑ ℓ ∈ Finset.Icc 1 6,
      ((ℓ+3).choose 4 : ℚ) * localPrincipal n k ℓ (Polynomial.X^(2*i.val)) (Polynomial.X^(2*j.val)) *
        (1/(primeIndex n : ℚ)^(ℓ+4))) := by
  unfold singularHigh harmonicSingular
  rw [gateWindow_eq_filter, ← kernelPoleSet_eq_poleList, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases hp : primeIndex n ≤ k-25*n-1
  · have hkw : k ∈ gateWindow n := by
      rw [gateWindow_eq_filter, Finset.mem_filter]
      exact ⟨hk,hp⟩
    have h6 : poleOrder n k = 6 := by
      rw [← kernelPoleOrder_eq_poleOrder]
      exact gateWindow_order n k hkw
    simp [hp,h6]
  · simp [hp]

end OddZetaSix.B40a
