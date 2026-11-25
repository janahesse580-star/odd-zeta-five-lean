import OddZetaSix.B40a.Arithmetic.Periodic
import OddZetaSix.B40a.Arithmetic.CertificateRows

namespace OddZetaSix.B40a.Cert
open Finset

private theorem cube_tail (a : ℝ) (ha : 0≤a) (N : ℕ) :
    (∑ j ∈ Ico 17 N, 1/((j:ℝ)+a)^3) ≤ 1/(2*(16+a)^2) := by
  by_cases hN : 17 ≤ N
  · have H : (∑ j ∈ Ico 17 N,(1/(2*((j:ℝ)+a-1)^2)-1/(2*((j:ℝ)+a)^2))) =
        1/(2*(16+a)^2)-1/(2*((N:ℝ)+a-1)^2) := by
      induction N,hN using Nat.le_induction with
      | base => simp; ring
      | succ N hN ih => rw [sum_Ico_succ_top hN,ih]; push_cast; ring
    calc
      _ ≤ ∑ j ∈ Ico 17 N,(1/(2*((j:ℝ)+a-1)^2)-1/(2*((j:ℝ)+a)^2)) := by
        apply sum_le_sum
        intro j hj
        have hj' : (17:ℝ)≤j := by exact_mod_cast (mem_Ico.mp hj).1
        exact tail_cube_term (by linarith)
      _ ≤ _ := by rw [H]; apply sub_le_self; positivity
  · simp [Ico_eq_empty (by omega : ¬(17:ℕ)<N)]; positivity

def periodStart (a : ℚ) : ℕ := if 9/11 ≤ a then 1 else 2

/-- The checked rounded reciprocal sum bounds every truncation; the proof
also covers truncations ending before the finite head of the certificate. -/
theorem reciprocalSum_majorant (a : ℚ) (ha : 0≤a) (k N : ℕ) (hk : k=2 ∨ k=3) :
    (∑ j ∈ Ico (periodStart a) N, (1:ℝ)/((j:ℝ)+a)^k) ≤ (reciprocalSum a k:ℝ) := by
  let s := periodStart a
  have hs : s ≤ 17 := by dsimp [s,periodStart]; split <;> decide
  have htail (m : ℕ) : (∑ j ∈ Ico 17 m, (1:ℝ)/((j:ℝ)+a)^k) ≤
      ((1/(((k-1:ℕ):ℚ)*(16+a)^(k-1)):ℚ):ℝ) := by
    have haR : (0:ℝ)≤a := by exact_mod_cast ha
    rcases hk with rfl|rfl
    · simpa using tail_period_square haR m
    · simpa using cube_tail a haR m
  let f (j : ℕ) := (1:ℝ)/((j:ℝ)+a)^k
  let F (j : ℕ) := roundUp (1/((j:ℚ)+a)^k)
  have head : (∑ j ∈ Ico s 17,f j) ≤ (((nrange s 17).map F).sum:ℝ) := by
    calc
      _ ≤ ∑ j ∈ Ico s 17, (F j:ℝ) := by
        apply sum_le_sum
        intro j _
        have h := (Rat.cast_le (K:=ℝ)).mpr (le_roundUp (1/((j:ℚ)+a)^k))
        simpa [f,F] using h
      _ = _ := by
        rw [sum_Ico_eq_sum_range]
        have hh (m : ℕ) (g : ℕ → ℝ) :
            (∑ j ∈ range m,g j) = ((List.range m).map g).sum := by
          induction m with
          | zero => simp
          | succ m ih => rw [Finset.sum_range_succ,List.range_succ,List.map_append,List.sum_append,ih]; simp
        rw [hh]
        simp [nrange,Function.comp_def]
  have htail' := htail (max N 17)
  have hceil := (Rat.cast_le (K:=ℝ)).mpr (le_roundUp (1/(((k-1:ℕ):ℚ)*(16+a)^(k-1))))
  have haR : (0:ℝ)≤a := by exact_mod_cast ha
  have hpad : (∑ j ∈ Ico s N,f j) ≤ ∑ j ∈ Ico s (max N 17),f j :=
    sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right (le_max_left _ _)) (fun j _ _ => by dsimp [f]; positivity)
  rw [←sum_Ico_consecutive f hs (le_max_right N 17)] at hpad
  change (∑ j ∈ Ico s N,f j) ≤ (( ((nrange s 17).map F).sum + roundUp (1/(((k-1:ℕ):ℚ)*(16+a)^(k-1))) : ℚ):ℝ)
  rw [Rat.cast_add]
  exact hpad.trans (add_le_add head (htail'.trans hceil))

end OddZetaSix.B40a.Cert
