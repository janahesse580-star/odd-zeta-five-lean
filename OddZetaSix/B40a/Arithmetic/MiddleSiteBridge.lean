import OddZetaSix.B40a.Arithmetic.MiddleSuffix

namespace OddZetaSix.B40a
open Finset

theorem kernelDenomAliases_nonnegative (n p k : ℕ) : 0 ≤ kernelDenomAliases n p k := by
  unfold kernelDenomAliases kernelPoleAliasCount
  rw [sub_nonneg, Nat.cast_le,←kernelPoleOrder_eq_block_count]
  apply sum_le_sum
  intro b _
  split_ifs with h
  · apply Finset.card_pos.mpr
    refine ⟨k-blockStart n b,mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩⟩
    rw [Nat.cast_sub h.1]
    have he : (blockStart n b:ℤ)-center n+(k-blockStart n b)-((k:ℤ)-center n)=0 := by ring
    rw [he]; exact dvd_zero _
  · omega

private theorem middle_atom_matches (n p t a l : ℕ) (hn : 0<n) (hp : 0<p)
    (ht : t≤25*n) (h16 : t≠16*n) (h17 : t≠17*n) (hw : middleAway n p t) :
    (certificateAtom p n t a (l+1)).toNat = middleOrderTerm n p t a l := by
  let m := middleMultiplicity n t
  let d := middlePoleAliases n p t-(m:ℤ)
  let z := middleZeroAliases n p t
  have hm : (6+(if (t:ℤ)<17*n then 4 else 0)+(if (t:ℤ)<16*n then 2 else 0):ℕ) = m := by
    have h1 : ((t:ℤ)<17*n) ↔ t<17*n := by omega
    have h2 : ((t:ℤ)<16*n) ↔ t<16*n := by omega
    simp only [h1,h2]; rfl
  obtain ⟨hP,hZ⟩ := middle_kernel_aliases n p hn hp t hw
  have zd : 0≤z := by dsimp [z]; rw [←hZ]; positivity
  have dd : 0≤d := by
    have h := kernelDenomAliases_nonnegative n p (center n+t)
    simpa only [kernelDenomAliases,Nat.cast_add,add_sub_cancel_left,hP,middle_order_open _ _ ht h16 h17] using h
  have ht34 : t ≤ 34*n := by omega
  have hlo : (34*n-t)/p ≤ (34*n+t)/p := Nat.div_le_div_right (by omega)
  have hodd : ((l+1)%2=1) ↔ Even l := by rw [Nat.even_iff]; omega
  have hdiff : ((34*n-t)/p ≠ (34*n+t)/p) ↔ (34*n-t)/p < (34*n+t)/p := by omega
  have hsub : m-(l+1)-a=m-1-l-a := by omega
  let v := z-d+6*((50*n/p:ℕ):ℤ)+4*((34*n/p:ℕ):ℤ)+2*((32*n/p:ℕ):ℤ)-10*((25*n/p:ℕ):ℤ)
  let L := (34*n-t)/p
  let R := (34*n+t)/p
  have Hleft : ((34*(n:ℤ)-t)/(p:ℤ))=(L:ℤ) := by dsimp [L]; simp [Nat.cast_sub ht34]
  have Hright : ((34*(n:ℤ)+t)/(p:ℤ))=(R:ℤ) := by simp [R]
  have castFact (b : ℕ) : (((b*n/p:ℕ):ℤ)) = (b:ℤ)*n/(p:ℤ) := by simp
  unfold certificateAtom
  dsimp only
  simp only [hm,hodd]
  change ((a:ℤ)-(z-d+6*(50*n/(p:ℤ))+4*(34*n/(p:ℤ))+2*(32*n/(p:ℤ))-10*(25*n/(p:ℤ)))+
    (if 0<d then ((m-(l+1)-a:ℕ):ℤ) else min ((m-(l+1)-a:ℕ):ℤ) z)+
    (if (if Even l then 0<(34*(n:ℤ)+t)/(p:ℤ) else (34*(n:ℤ)-t)/(p:ℤ)≠(34*(n:ℤ)+t)/(p:ℤ)) then ((l+1:ℕ):ℤ)+4 else 0)).toNat = _
  change _ = ((a:ℤ)-v+((if d=0 then min (m-1-l-a) z.toNat else m-1-l-a : ℕ):ℤ)+
    ((l+5:ℕ):ℤ)*((if Even l then (if 0<R then 1 else 0) else (if L<R then 1 else 0) : ℕ):ℤ)).toNat
  have vf : z-d+6*(50*n/(p:ℤ))+4*(34*n/(p:ℤ))+2*(32*n/(p:ℤ))-10*(25*n/(p:ℤ))=v := by
    dsimp [v]
  rw [vf,hsub]
  have hlr : (L≠R) ↔ L<R := hdiff
  have hzCast := Int.toNat_of_nonneg zd
  simp only [Hleft,Hright,Int.natCast_pos]
  split_ifs <;> push_cast <;> omega

private theorem nrange_mem (m a e : ℕ) :
    e ∈ Cert.nrange 1 (m-a+1) ↔ 0<e ∧ e≤m-a := by
  simp only [Cert.nrange,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨j,hj,rfl⟩; omega
  · rintro ⟨he,hm⟩; exact ⟨e-1,by omega,by omega⟩

/-- On open middle-band classes, the original rational checker's site bag
is exactly the positive costs of the actual slots, with multiplicities. -/
theorem middleSite_matches_slots (n p t : ℕ) [Fact p.Prime] (hn : 0<n)
    (hp : 2<p) (hsq : 84*n<p^2) (ht : t≤25*n) (h16 : t≠16*n) (h17 : t≠17*n)
    (hw : middleAway n p t) :
    Cert.middleSite p n t =
      ((List.range (middleMultiplicity n t)).map (fun a => (refinedSlotCost n p (center n+t) a:ℤ))).filter
        (fun z => decide (0<z)) := by
  let m := middleMultiplicity n t
  let φ := certificateAtom (p:ℤ) n t
  have hm : (6+(if (t:ℤ)<17*n then 4 else 0)+(if (t:ℤ)<16*n then 2 else 0):ℕ)=m := by
    have h1 : ((t:ℤ)<17*n) ↔ t<17*n := by omega
    have h2 : ((t:ℤ)<16*n) ↔ t<16*n := by omega
    simp only [h1,h2]; rfl
  rw [middleSite_eq_suffix]
  simp only [hm]
  have ho (a : ℕ) (ha : a<m) : siteOrder m φ a =
      ((range m).filter (fun l=>a≤m-1-l)).sup (middleOrderTerm n p t a) := by
    unfold siteOrder
    apply le_antisymm
    · apply Finset.sup_le; intro e he
      have H := (nrange_mem m a e).mp (List.mem_toFinset.mp he)
      obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero H.1.ne'
      rw [show (φ a (l+1)).toNat=middleOrderTerm n p t a l from
        middle_atom_matches n p t a l hn (by omega) ht h16 h17 hw]
      exact Finset.le_sup (f:=middleOrderTerm n p t a) (mem_filter.mpr ⟨mem_range.mpr (by omega),by omega⟩)
    · apply Finset.sup_le; intro l hl
      have hl' := mem_filter.mp hl
      have hlt := mem_range.mp hl'.1
      rw [←middle_atom_matches n p t a l hn (by omega) ht h16 h17 hw]
      exact Finset.le_sup (f:=fun e => (φ a e).toNat) (List.mem_toFinset.mpr ((nrange_mem _ _ _).mpr ⟨by omega,by omega⟩))
  have H (a : ℕ) : suffixSlot m φ a = refinedSlotCost n p (center n+t) a := by
    rw [middle_refined_slot n p t a hn hp hsq ht h16 h17 hw]
    unfold suffixSlot middleSlot
    apply Finset.sup_congr rfl
    intro j hj
    exact ho j (mem_range.mp (mem_filter.mp hj).1)
  simp only [←H]
  rfl

end OddZetaSix.B40a
