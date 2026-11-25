import OddZetaSix.B40a.Arithmetic.MiddleLayerCompare
import OddZetaSix.B40a.Arithmetic.MiddleSweepMinimum
import OddZetaSix.B40a.Arithmetic.MiddleRowPenalty
import OddZetaSix.B40a.Arithmetic.PrimeSums

namespace OddZetaSix.B40a.MiddleGrid
open Finset Cert.Sweep
noncomputable section

def actualCount (n p q j : ℕ) [Fact p.Prime] : ℕ :=
  ∑ c : Fin (p/2+1),(classRows n p c q j).card

private theorem true_cap_bound (n p : ℕ) [Fact p.Prime] (hn : 0<n) (hsq : 84*n<p^2) (q : ℕ) :
    -padicValRat p (content n) ≤ 2*(OddZetaSix.sixRowPenalty (fiveRank n) p q:ℤ)+
      ∑ j ∈ Ico 1 17,(min (fiveRank n) (actualCount n p q j):ℤ) := by
  let S := middleSlotClass n p (Fact.out : p.Prime).pos
  let pair := fun (c : Fin (p/2+1)) (r : Fin (slotCount n)) => r.val<(S c).card
  let cost := fun (c : Fin (p/2+1)) (r : Fin (slotCount n)) =>
    (OddZetaSix.nthDescWeight (S c) (slotCost n p) r.val:ℤ) - 2*((r.val-q:ℕ):ℤ)
  have H := content_folded_capacity n p hn hsq q
  let pairs := univ.filter (fun cr : Fin (p/2+1) × Fin (slotCount n) => pair cr.1 cr.2)
  let B (j : ℕ) := (pairs.filter (fun cr=>(j:ℤ)≤cost cr.1 cr.2)).card
  change _ ≤ _ + ∑ j ∈ Icc 1 18,(min (fiveRank n) (B j):ℤ) at H
  have HC (j : ℕ) : B j=actualCount n p q j := by
    unfold B pairs
    rw [filter_filter,card_filter,←univ_product_univ,sum_product]
    unfold actualCount
    apply sum_congr rfl; intro c _
    rw [classRows,card_filter]
  simp_rw [HC] at H
  have he : ∑ j ∈ Ico 1 17,(min (fiveRank n) (actualCount n p q j):ℤ) =
      ∑ j ∈ Icc 1 18,(min (fiveRank n) (actualCount n p q j):ℤ) := by
    apply sum_subset (by intro j h; obtain ⟨h1,h2⟩ := mem_Ico.mp h; exact mem_Icc.mpr ⟨h1,by omega⟩)
    intro j hj hnot
    have h1 := (mem_Icc.mp hj).1
    have hmax : 16<j := by by_contra! hh; exact hnot (mem_Ico.mpr ⟨h1,by omega⟩)
    have hnul (c : Fin (p/2+1)) : classRows n p c q j = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr; intro r hr
      have h := (mem_filter.mp hr).2.2
      have hw := OddZetaSix.nthDescWeight_le_bound (S c) (slotCost n p) 16
        (fun u _=>slotCost_le_16 n p hn hsq u) r.val
      change (j:ℤ)≤(OddZetaSix.nthDescWeight (S c) (slotCost n p) r.val:ℤ)-2*((r.val-q:ℕ):ℤ) at h
      omega
    simp [actualCount,hnul]
  rw [he]; exact H

private theorem row_scaled (n p q : ℕ) (hn : 0<n) (hp : 0<p) (hq : q≤80*n/p) :
    4*(2*(OddZetaSix.sixRowPenalty (fiveRank n) p q:ℤ))≤
      rowCharge (4*p) (4*n) (80*n/p) q := by
  let K := 80*n/p
  have H := middle_certificate_row_penalty n p q K hn hp hq rfl
  have hz : 2*(OddZetaSix.sixRowPenalty (fiveRank n) p q:ℤ) ≤
      80*(n:ℤ)*(K-q:ℕ)-(p:ℤ)*((K+q+1)*(K-q)/2:ℕ) := by exact_mod_cast H
  have he : rowCharge (4*p) (4*n) K q =
      4*(80*(n:ℤ)*(K-q:ℕ)-(p:ℤ)*((K+q+1)*(K-q)/2:ℕ)) := by unfold rowCharge; ring
  change _≤rowCharge _ _ K q
  rw [he]; omega

/-- At native fourfold scale, all q options and the unfolded option control
the actual content. The sole additive allowance counts the seven walls. -/
theorem content_le_middle_best (n p : ℕ) [Fact p.Prime] (hn : 0<n) (hp : 2<p)
    (hsq : 84*n<p^2) (hband : 11*n≤20*p) :
    4*max 0 (-padicValRat p (content n))-494592 ≤
      best (classes n p) (4*p) (4*n) (80*n/p) (80*n/p+1) := by
  have hp' : 0<p := by omega
  let bs := classes n p
  apply le_best_of_all_rows _ _ _ _ _ (classes_valid n p hp')
  intro q hq
  let K := 80*n/p
  have hrow := row_scaled n p q hn hp' hq
  have H := true_cap_bound n p hn hsq q
  let f := fun j : ℕ => (min (fiveRank n) (actualCount n p q j):ℤ)
  let g := fun j : ℕ => min (40*(4*(n:ℤ))) (level (folded bs q) j)
  have per (j : ℕ) (hj : j∈Ico 1 17) : 4*f j≤g j+30912 := by
    have hl := folded_layer_grid n p hn hp hsq hband q j (mem_Ico.mp hj).1
    change 4*(∑ c : Fin (p/2+1),((classRows n p c q j).card:ℤ))≤_ at hl
    have hc : (actualCount n p q j:ℤ)=∑ c : Fin (p/2+1),((classRows n p c q j).card:ℤ) := by
      unfold actualCount; push_cast; rfl
    rw [←hc] at hl
    unfold f g fiveRank
    change _ ≤ min _ (level (folded (classes n p) q) j)+30912
    omega
  have hsum := sum_le_sum per
  rw [←mul_sum,sum_add_distrib] at hsum
  have hsize : ∑ _j ∈ Ico 1 17,(30912:ℤ)=494592 := by decide
  rw [hsize] at hsum
  change _≤_+ ∑ j ∈ Ico 1 17,f j at H
  have hz : 0≤2*(OddZetaSix.sixRowPenalty (fiveRank n) p q:ℤ)+ ∑ j ∈ Ico 1 17,f j :=
    add_nonneg (by positivity) (sum_nonneg (fun j _ => (by dsimp [f]; positivity)))
  have H' := max_le hz H
  change _≤score bs _ _ K q
  unfold score
  rw [book_cap]
  change _ ≤ rowCharge _ _ K q + ∑ j ∈ Ico 1 17,g j
  change _ ≤ rowCharge _ _ K q at hrow
  omega

/-- First-layer upper bound on the true prime exponent on the whole middle
band, away from the single diagonal prime p=n. No row oracle is assumed. -/
theorem primeExponent_le_middleValue (n p : ℕ) [Fact p.Prime] (hn : 0<n) (hp : 2<p)
    (hsq : 84*n<p^2) (hband : 11*n≤20*p) (hne : p≠n) :
    primeExponent n p ≤ 2000*(n:ℝ)*(Cert.middleValue ((p:ℚ)/n):ℝ)+123648 := by
  have hp' := (Fact.out : p.Prime)
  have hcop : p.Coprime n := hp'.coprime_iff_not_dvd.mpr (by
    rintro ⟨k,hk⟩
    have hk0 : k≠0 := by rintro rfl; simp_all
    have hk1 : k≠1 := by rintro rfl; simp_all
    have hle := Nat.mul_le_mul_left p (show 2≤k by omega)
    omega)
  have hnum : ((p:ℚ)/n).num=p := by
    simpa using Rat.num_div_eq_of_coprime (a:=(p:ℤ)) (b:=(n:ℤ)) (by omega) (by simpa using hcop)
  have hden : (((p:ℚ)/n).den:ℤ)=n := by
    simpa using Rat.den_div_eq_of_coprime (a:=(p:ℤ)) (b:=(n:ℤ)) (by omega) (by simpa using hcop)
  have hK : ((80*(4*(n:ℤ)))/(4*(p:ℤ))).toNat=80*n/p := by
    rw [show (80*(4*(n:ℤ)))=4*(80*(n:ℤ)) by ring,Int.mul_ediv_mul_of_pos _ _ (by decide : (0:ℤ)<4)]
    exact_mod_cast (rfl : (80*n/p:ℕ)=_)
  have H := content_le_middle_best n p hn hp hsq hband
  let v := best (classes n p) (4*p) (4*n) (80*n/p) (80*n/p+1)
  have Hr : 4*primeExponent n p-494592≤(v:ℝ) := by unfold primeExponent; exact_mod_cast H
  rw [middleValue_eq_best]
  rw [hnum,hden,hK]
  change _ ≤ 2000*(n:ℝ)*(((v:ℚ)/(2000*(4*(n:ℤ)):ℤ):ℚ):ℝ)+123648
  push_cast
  have hz : (n:ℝ)≠0 := by positivity
  field_simp [hz]
  <;> nlinarith

end
end OddZetaSix.B40a.MiddleGrid
