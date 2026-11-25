import OddZetaSix.B40a.Arithmetic.MiddleBoundary

namespace OddZetaSix.B40a
open Finset
noncomputable section

private theorem mapped_sum_nodup {α : Type} [DecidableEq α] (xs : List α) (h : xs.Nodup)
    (f : α → ℕ) : (xs.map f).sum = ∑ t ∈ xs.toFinset,f t := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hh := List.nodup_cons.mp h
    simp [ih hh.2,hh.1]

private theorem count_nodup {α : Type} [DecidableEq α] (xs : List α) (h : xs.Nodup)
    (f : α → Bool) : xs.countP f=(xs.toFinset.filter (fun t => f t=true)).card := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨hnot,ht⟩ := List.nodup_cons.mp h
    cases he : f a <;> simp [he,ih ht,hnot,Finset.filter_insert]

private theorem siteLayerCount (n p : ℕ) [Fact p.Prime] (hn : 0<n) (hp : 2<p)
    (hsq : 84*n<p^2) (c t : ℤ) (hc : 0<c) (hc2 : 2*c<p) (hopen : middleOpenClass p n c)
    (ht : t ∈ middleClassSites p n c) (j : ℕ) (hj : 0<j) :
    (Cert.middleSite p n t).countP (fun z=>decide ((j:ℤ)≤z)) =
      ((range 12).filter (fun a => j≤refinedSlotCost n p (center n+t.toNat) a)).card := by
  obtain ⟨h0,h25,h16,h17,hw⟩ := openClass_site_conditions _ _ _ _ hc hc2 hopen ht
  have ht' := Int.toNat_of_nonneg h0
  have h1 : t.toNat≤25*n := by omega
  have h2 : t.toNat≠16*n := by omega
  have h3 : t.toNat≠17*n := by omega
  let m := middleMultiplicity n t.toNat
  let F (a : ℕ) := refinedSlotCost n p (center n+t.toNat) a
  have hm12 : m≤12 := by dsimp [m,middleMultiplicity]; split_ifs <;> decide
  have H := middleSite_matches_slots n p t.toNat hn hp hsq h1 h2 h3 (by rwa [ht'])
  rw [ht'] at H
  rw [H,List.countP_filter,List.countP_map,count_nodup _ List.nodup_range]
  apply congrArg Finset.card
  ext a
  simp only [mem_filter,List.mem_toFinset,List.mem_range,mem_range,Function.comp_apply,
    Bool.and_eq_true,decide_eq_true_eq,Nat.cast_le,Int.natCast_pos]
  change (a<m ∧ j≤F a ∧ 0<F a) ↔ a<12 ∧ j≤F a
  by_cases ha : a<m
  · omega
  · have hzero : F a=0 := refinedSlotCost_zero_of_inactive _ _ _ _
        (by rw [middle_order_open _ _ h1 h2 h3]; omega)
    omega

/-- Exact equality with the population of the true matrix columns at every
positive threshold, before the rank truncation and row correction. -/
theorem middle_actual_layer_count (n p : ℕ) [Fact p.Prime] (hn : 0<n) (hp : 2<p)
    (hsq : 84*n<p^2) (c : Fin (p/2+1)) (hc : 0<(c.val:ℤ)) (hc2 : 2*(c.val:ℤ)<p)
    (hopen : middleOpenClass p n c.val) (j : ℕ) (hj : 0<j) :
    ((middleClassSites p n c.val).flatMap (Cert.middleSite p n)).countP (fun z=>decide ((j:ℤ)≤z)) =
      ((middleSlotClass n p (Fact.out : p.Prime).pos c).filter (fun u=>j≤slotCost n p u)).card := by
  let S := middleClassSites p n (c.val:ℤ)
  let F (t : ℤ) (a : ℕ) := refinedSlotCost n p (center n+t.toNat) a
  let A := (S.toFinset ×ˢ range 12).filter (fun z=>j≤F z.1 z.2)
  let C := (middleSlotClass n p (Fact.out : p.Prime).pos c).filter (fun u=>j≤slotCost n p u)
  have hs := (middleClassSites_spec p n c.val hc hc2).1
  rw [List.countP_flatMap,mapped_sum_nodup _ hs]
  change (∑ t ∈ S.toFinset,(Cert.middleSite p n t).countP _) = C.card
  calc
    _ = ∑ t ∈ S.toFinset, ((range 12).filter (fun a=>j≤F t a)).card := by
      apply sum_congr rfl; intro t ht
      exact siteLayerCount n p hn hp hsq c.val t hc hc2 hopen (List.mem_toFinset.mp ht) j hj
    _ = A.card := by
      dsimp [A]
      rw [Finset.card_filter,Finset.sum_product]
      simp only [Finset.card_filter]
    _ = C.card := by
      symm
      apply Finset.card_bij (fun u _ =>
        ((((slotEquiv n).symm u).1.val:ℤ),((slotEquiv n).symm u).2.val))
      · intro u hu
        obtain ⟨hcl,hv⟩ := mem_filter.mp hu
        have hc' := (mem_filter.mp hcl).2
        have hs' := (middleClassSites_iff_slot n p (Fact.out : p.Prime).pos c.val hc hc2 hopen u).mpr
          (by rw [hc'])
        exact mem_filter.mpr ⟨mem_product.mpr ⟨List.mem_toFinset.mpr hs',mem_range.mpr
          ((slotEquiv n).symm u).2.isLt⟩,by simpa [slotCost,halfPole,F] using hv⟩
      · intro u hu v hv h
        apply (slotEquiv n).symm.injective
        have haddr := congrArg Prod.fst h
        change (((slotEquiv n).symm u).1.val:ℤ)=(((slotEquiv n).symm v).1.val:ℤ) at haddr
        exact Prod.ext (Fin.ext (by exact_mod_cast haddr))
          (Fin.ext (congrArg Prod.snd h))
      · rintro ⟨t,a⟩ hta
        obtain ⟨hpair,hval⟩ := mem_filter.mp hta
        obtain ⟨htS,ha⟩ := mem_product.mp hpair
        have ht := List.mem_toFinset.mp htS
        obtain ⟨h0,hl,_⟩ := ((middleClassSites_spec p n c.val hc hc2).2 t).mp ht
        have ht' := Int.toNat_of_nonneg h0
        let u := slotEquiv n (⟨t.toNat,by omega⟩,⟨a,mem_range.mp ha⟩)
        have hpair' : (slotEquiv n).symm u=(⟨t.toNat,by omega⟩,⟨a,mem_range.mp ha⟩) :=
          (slotEquiv n).symm_apply_apply _
        have hc' := (middleClassSites_iff_slot n p (Fact.out : p.Prime).pos c.val hc hc2 hopen u).mp
          (by simpa only [hpair',ht'] using ht)
        refine ⟨u,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,Fin.ext (by exact_mod_cast hc')⟩,?_⟩,?_⟩
        · simpa only [slotCost,hpair',halfPole] using hval
        · simp only [hpair',ht']

end
end OddZetaSix.B40a
