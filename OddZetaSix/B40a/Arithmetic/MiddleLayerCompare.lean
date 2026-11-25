import OddZetaSix.B40a.Arithmetic.MiddleSampleGrid
import OddZetaSix.B40a.Arithmetic.MiddleGridSum
import OddZetaSix.B40a.Arithmetic.MiddleSweepRanks

namespace OddZetaSix.B40a.MiddleGrid
open Finset Cert.StripGrid Cert.Sweep
noncomputable section
set_option maxHeartbeats 1200000

def classes (n p : ℕ) := Cert.middleClasses (4*(p:ℤ)) (4*(n:ℤ))
theorem classes_eq (n p : ℕ) : classes n p =
    (stripSet n p).map (fun v=>(v.2-v.1,(sampleBag n p v).toArray)) := rfl

theorem sample_range (n p : ℕ) (v : ℤ×ℤ) (r : ℕ) :
    (sampleBag n p v).getD r 0≤16 := by
  by_cases hr : r<(sampleBag n p v).length
  · rw [List.getD_eq_getElem _ _ hr]
    have hm := List.getElem_mem (l:=sampleBag n p v) hr
    unfold sampleBag middleSortedSlots at hm
    obtain ⟨k,hk,hw⟩ := List.mem_flatMap.mp hm
    have heq := List.eq_of_mem_replicate hw
    change (sampleBag n p v)[r] = (k:ℤ) at heq
    have hk16 : k<17 := by
      simp only [List.mem_reverse,Cert.nrange,List.mem_map,List.mem_range] at hk
      obtain ⟨a,ha,rfl⟩ := hk; omega
    omega
  · rw [List.getD_eq_default _ _ (by omega : (sampleBag n p v).length≤r)]; decide

theorem classes_valid (n p : ℕ) (hp : 0<p) : ∀ B∈classes n p,0≤B.1 ∧ ∀ r<B.2.size,B.2[r]!≤16 := by
  rw [classes_eq]; intro B h
  obtain ⟨⟨a,b⟩,hv,rfl⟩ := List.mem_map.mp h
  have hs := strip_window p n _ _ (by exact_mod_cast hp) hv
  refine ⟨by dsimp; omega,?_⟩
  intro r hr
  have hlen : r<(sampleBag n p (a,b)).length := by simpa using hr
  change (sampleBag n p (a,b)).toArray[r]!≤16
  rw [getElem!_pos (sampleBag n p (a,b)).toArray r (by simpa using hlen),List.getElem_toArray]
  have H := sample_range n p (a,b) r
  rwa [List.getD_eq_getElem _ _ hlen] at H

def classRows (n p : ℕ) [Fact p.Prime] (c : Fin (p/2+1)) (q j : ℕ) :=
  let S := middleSlotClass n p (Fact.out : p.Prime).pos c
  univ.filter (fun r : Fin (slotCount n) => r.val<S.card ∧
      (j:ℤ)≤(OddZetaSix.nthDescWeight S (slotCost n p) r.val:ℤ)-2*((r.val-q:ℕ):ℤ))

private theorem le_population (n p : ℕ) [Fact p.Prime] (hn : 0<n) (hp : 2<p) (hsq : 84*n<p^2)
    (v : ℤ×ℤ) (hv : v∈stripSet n p) (c : Fin (p/2+1)) (hc : c∈interior p v)
    (q j : ℕ) (hj : 0<j) :
    ((classRows n p c q j).card:ℤ)≤population (sampleBag n p v).toArray q j := by
  let xs := sampleBag n p v
  let I := (range xs.length).filter (fun r=>(j:ℤ)≤adjusted xs.toArray q r)
  have hcnt := card_le_card_of_injOn (s:=classRows n p c q j) (t:=I) Fin.val (by
    intro r hr
    obtain ⟨_,hcost⟩ := (mem_filter.mp hr).2
    rw [←sample_rank n p hn hp hsq v hv c hc r.val] at hcost
    have hin : r.val<xs.length := by
      by_contra! he
      change (j:ℤ)≤xs.getD r.val 0-2*((r.val-q:ℕ):ℤ) at hcost
      rw [List.getD_eq_default xs 0 he] at hcost; omega
    refine mem_filter.mpr ⟨mem_range.mpr hin,?_⟩
    change (j:ℤ)≤xs.getD r.val 0 - 2*((r.val-q:ℕ):ℤ) at hcost
    rw [List.getD_eq_getElem _ _ hin] at hcost
    simpa only [adjusted,getElem!_pos xs.toArray r.val (by simpa using hin),List.getElem_toArray] using hcost)
    (fun _ _ _ _ h => Fin.ext h)
  have hcR : (I.card:ℤ)=∑ r ∈ range xs.length,eligible j (adjusted xs.toArray q r) := by
    dsimp [I]
    rw [card_filter]; push_cast
    apply sum_congr rfl; intro r hr
    have hi := mem_range.mp hr
    have hw := sample_range n p v r
    change xs.getD r 0≤16 at hw
    have h' : adjusted xs.toArray q r≤16 := by
      unfold adjusted
      rw [List.getD_eq_getElem _ _ hi] at hw
      simp only [getElem!_pos xs.toArray r (by simpa using hi),List.getElem_toArray]
      omega
    simp only [eligible,h',and_true] <;> split <;> rfl
  calc _ ≤ (I.card:ℤ) := by exact_mod_cast hcnt
       _ = _ := hcR

private theorem classRows_card_le (n p : ℕ) [Fact p.Prime] (hband : 11*n≤20*p)
    (c : Fin (p/2+1)) (q j : ℕ) : (classRows n p c q j).card≤1104 := by
  let S := middleSlotClass n p (Fact.out : p.Prime).pos c
  have h := card_le_card_of_injOn (s:=classRows n p c q j) (t:=range S.card) Fin.val
    (fun r hr => mem_range.mpr (mem_filter.mp hr).2.1) (fun _ _ _ _ h=>Fin.ext h)
  rw [card_range] at h
  have ht := middleSlotClass_card n p (Fact.out : p.Prime).pos c
  change S.card≤_ at ht
  have hp0 := (Fact.out : p.Prime).pos
  have hq : 25*n/p<46 := (Nat.div_lt_iff_lt_mul (Fact.out : p.Prime).pos).mpr (by omega)
  omega

theorem folded_layer_grid (n p : ℕ) [Fact p.Prime] (hn : 0<n) (hp : 2<p) (hsq : 84*n<p^2)
    (hband : 11*n≤20*p) (q j : ℕ) (hj : 0<j) :
    4*(∑ c : Fin (p/2+1),((classRows n p c q j).card:ℤ)) ≤
      level (folded (classes n p) q) j + 30912 := by
  let f := fun c : Fin (p/2+1) => ((classRows n p c q j).card:ℤ)
  let g := fun v => population (sampleBag n p v).toArray q j
  have hp0 : 0<p := by omega
  have H := upper_grid_sum p n hp0 (interior p) (wallClasses n p) f g
    (fun v _ => sum_nonneg (fun r _ => by dsimp [eligible]; split <;> decide))
    (fun _ _ => rfl) (fun c hc => by
      obtain ⟨v,hv,hcv⟩ := offWall_cover n p c hc
      exact ⟨v,hv,hcv,le_population n p hn hp hsq v hv c hcv q j hj⟩)
  have hw : (∑ c ∈ wallClasses n p,f c)≤7728 := by
    calc
      _ ≤ ∑ _c ∈ wallClasses n p,(1104:ℤ) := sum_le_sum (fun c _ => by
        change ((classRows n p c q j).card:ℤ)≤1104
        exact_mod_cast classRows_card_le n p hband c q j)
      _ ≤ _ := by
        simp only [sum_const,nsmul_eq_mul]
        have := wallClasses_card n p; omega
  rw [folded_population _ _ _ hj (fun b h=>(classes_valid n p hp0 b h).2),classes_eq,List.map_map]
  change 4*(∑ c,f c)≤((stripSet n p).map (fun v=>(v.2-v.1)*g v)).sum+30912
  change _ ≤ _+((stripSet n p).map (fun v=>(v.2-v.1)*g v)).sum at H
  omega

end
end OddZetaSix.B40a.MiddleGrid
