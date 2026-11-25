import OddZetaSix.B40a.Arithmetic.MiddleSweep
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace OddZetaSix.B40a.Cert.Sweep
open Finset

def bin (es : List Event) (i : ℕ) : ℤ :=
  (es.map fun e => if e.1=(i:ℤ) then e.2 else 0).sum

def level (es : List Event) (j : ℕ) : ℤ :=
  (es.map fun e => if (j:ℤ)≤e.1 ∧ e.1≤16 then e.2 else 0).sum

theorem book_size (es : List Event) (h : Array ℤ) : (book es h).size=h.size := by
  induction es generalizing h with
  | nil => rfl
  | cons e es ih =>
    change (book es (post h e)).size=h.size
    rw [ih]; exact Array.size_modify

theorem book_bin (es : List Event) (h : Array ℤ) (i : ℕ) (hi : 0<i) (hb : i<h.size) :
    (book es h)[i]! = h[i]!+bin es i := by
  induction es generalizing h with
  | nil => simp [book,bin]
  | cons e es ih =>
    change (book es (post h e))[i]! = _
    have hsz : i<(post h e).size := by simpa [post,bump] using hb
    rw [ih _ hsz,getElem!_pos (post h e) i hsz,getElem!_pos h i hb]
    simp only [post,bump,Array.getElem_modify,bin,List.map_cons,List.sum_cons]
    have hiff : e.1.toNat=i ↔ e.1=(i:ℤ) := by omega
    simp only [hiff]
    split_ifs <;> omega

theorem book_blank_bin (es : List Event) (i : ℕ) (hi : 0<i) (hb : i<17) :
    (book es blank)[i]! = bin es i := by
  have hs : i<blank.size := by simpa [blank] using hb
  rw [book_bin _ _ _ hi hs,getElem!_pos blank i hs]
  simp [blank]

theorem sum_bin_eq_level (es : List Event) (j : ℕ) (hj : 0<j) :
    (∑ i ∈ Ico j 17,bin es i)=level es j := by
  induction es with
  | nil => simp [bin,level]
  | cons e es ih =>
    have hcons (i : ℕ) : bin (e::es) i=(if e.1=(i:ℤ) then e.2 else 0)+bin es i := by
      simp [bin]
    simp only [hcons,sum_add_distrib,ih,level,List.map_cons,List.sum_cons]
    congr 1
    by_cases h : (j:ℤ)≤e.1 ∧ e.1≤16
    · rw [ite_eq_left h]
      have hz : 0≤e.1 := by omega
      have hi : e.1.toNat ∈ Ico j 17 := mem_Ico.mpr ⟨by omega,by omega⟩
      rw [Finset.sum_eq_single_of_mem e.1.toNat hi]
      · simp [Int.toNat_of_nonneg hz]
      · intro i _ hn; simp only [ite_eq_right_iff]; intro hh; exfalso; omega
    · rw [ite_eq_right h]
      apply sum_eq_zero
      intro i hi
      have := mem_Ico.mp hi
      rw [ite_eq_right (by omega)]

theorem level_append (a b : List Event) (j : ℕ) :
    level (a++b) j=level a j+level b j := by simp [level]

end OddZetaSix.B40a.Cert.Sweep
