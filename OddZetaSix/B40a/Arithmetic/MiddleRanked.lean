import OddZetaSix.B40a.Arithmetic.MiddleHistogram

namespace OddZetaSix.B40a
open Finset
noncomputable section

private theorem sorted_threshold {α : Type} [LinearOrder α] (xs : List α) (hd : xs.Pairwise (·≥·))
    (r : ℕ) (d v : α) (hv : d<v) :
    v≤xs.getD r d ↔ r<xs.countP (fun z=>decide (v≤z)) := by
  induction xs generalizing r with
  | nil => simp [hv.not_ge]
  | cons x xs ih =>
    obtain ⟨hx,ht⟩ := List.pairwise_cons.mp hd
    by_cases h : v≤x
    · cases r with
      | zero => simp [h]
      | succ r => simpa [h,List.countP_cons] using ih ht r
    · have hz : xs.countP (fun z=>decide (v≤z))=0 := List.countP_eq_zero.mpr (by
        intro a ha; simp only [decide_eq_true_eq]; exact fun H=>h (H.trans (hx a ha)))
      cases r with
      | zero => simp [h,hz]
      | succ r => simpa [h,List.countP_cons,hz] using ih ht r

private theorem desc_count {α : Type} (s : Finset α) (f : α→ℕ) (w : ℕ) :
    (OddZetaSix.descWeights s f).countP (fun k=>decide (w≤k)) =
      (s.filter (fun u=>w≤f u)).card := by
  classical
  unfold OddZetaSix.descWeights
  rw [(List.mergeSort_perm (s.toList.map f) _).countP_eq (fun k=>decide (w≤k)),List.countP_map,
    List.countP_eq_length_filter]
  change (s.toList.filter (fun u=>decide (w≤f u))).length=_
  rw [←Finset.length_toList (s.filter (fun u=>w≤f u))]
  exact List.Perm.length_eq (by
    apply (List.perm_ext_iff_of_nodup (List.Nodup.filter _ s.nodup_toList) (Finset.nodup_toList _)).mpr
    intro a; simp)

theorem middleRankedSlot_eq (n p : ℕ) [Fact p.Prime] (hn : 0<n) (hp : 2<p)
    (hsq : 84*n<p^2) (c : Fin (p/2+1)) (hc : 0<(c.val:ℤ)) (hc2 : 2*(c.val:ℤ)<p)
    (hopen : middleOpenClass p n c.val) (r : ℕ) :
    (middleSortedSlots ((middleClassSites p n c.val).flatMap (Cert.middleSite p n))).getD r 0 =
      (OddZetaSix.nthDescWeight (middleSlotClass n p (Fact.out : p.Prime).pos c)
        (slotCost n p) r:ℤ) := by
  let raw := (middleClassSites p n c.val).flatMap (Cert.middleSite p n)
  let zs := middleSortedSlots raw
  let S := middleSlotClass n p (Fact.out : p.Prime).pos c
  let ts := OddZetaSix.descWeights S (slotCost n p)
  change zs.getD r 0=(ts.getD r 0:ℤ)
  have hperm := middleSortedSlots_perm raw (middleRawBag_range n p hn hp hsq _ hc hc2 hopen)
  have ht : ts.Pairwise (·≥·) := by
    have hh := List.pairwise_mergeSort (le:=fun a b : ℕ => decide (b≤a))
      (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega) (fun a b => by simp; omega) (S.toList.map (slotCost n p))
    simpa [ts,OddZetaSix.descWeights] using hh
  have hpos : 0≤zs.getD r 0 := by
    by_cases hr : r<zs.length
    · rw [List.getD_eq_getElem _ _ hr]
      have hmem := hperm.mem_iff.mp (List.getElem_mem (l:=zs) hr)
      exact (middleRawBag_range n p hn hp hsq _ hc hc2 hopen _ hmem).1.le
    · rw [List.getD_eq_default zs (0:ℤ) (by omega : zs.length≤r)]
  have eqv (j : ℕ) (hj : 0<j) : (j:ℤ)≤zs.getD r 0 ↔ j≤ts.getD r 0 := by
    rw [sorted_threshold zs (middleSortedSlots_decreasing raw) _ _ _ (by exact_mod_cast hj),
      sorted_threshold ts ht _ _ _ hj,hperm.countP_eq,desc_count]
    rw [middle_actual_layer_count n p hn hp hsq c hc hc2 hopen j hj]
  have H := eqv ((zs.getD r 0).toNat+1) (by omega)
  have H' := eqv (ts.getD r 0+1) (by omega)
  omega

end
end OddZetaSix.B40a
