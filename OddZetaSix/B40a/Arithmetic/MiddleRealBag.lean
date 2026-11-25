import OddZetaSix.B40a.Arithmetic.MiddleClassSites

namespace OddZetaSix.B40a
open Finset

def middleOpenClass (p d c : ℤ) :=
  ∀ e ∈ ([16,17,25,34,59]: List ℤ), c ≠ middleFoldWall p (e*d)

theorem openClass_site_conditions (n p : ℕ) (c t : ℤ) (hc : 0<c) (hc2 : 2*c<p)
    (hopen : middleOpenClass p n c) (ht : t ∈ middleClassSites p n c) :
    0≤t ∧ t<25*n ∧ t ≠ 16*n ∧ t ≠ 17*n ∧ middleAway n p t := by
  obtain ⟨h0,h25,hr⟩ := ((middleClassSites_spec p n c hc hc2).2 t).mp ht
  have hp : 0<(p:ℤ) := by omega
  have hf : middleFoldWall p t=c := by unfold middleFoldWall; rcases hr with h|h <;> rw [h] <;> omega
  have hd (a : ℤ) (ha : a ∈ ([16,17,25,34,59] : List ℤ)) : t≠a*n := by
    intro he
    exact hopen a ha (hf.symm.trans (congrArg _ he))
  refine ⟨h0,h25,hd 16 (by decide),hd 17 (by decide),?_⟩
  intro a ha hdiv
  have hres : t%(p:ℤ)=(a*n)%(p:ℤ) := Int.modEq_iff_dvd.mpr hdiv
  have hfold : middleFoldWall p t=middleFoldWall p (a*n) := by unfold middleFoldWall; rw [hres]
  have ha' : -a ∈ ([16,17,25,34,59]: List ℤ) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha ⊢; omega
  apply hopen (-a) ha'
  rw [neg_mul,middleFoldWall_neg _ _ hp,←hfold,hf]

/-- A true slot is enumerated in an open class exactly when the actual
confluent Vandermonde matrix assigns it that folded address. -/
theorem middleClassSites_iff_slot (n p : ℕ) (hp : 0<p) (c : ℤ)
    (hc : 0<c) (hc2 : 2*c<p) (hopen : middleOpenClass p n c) (u : Fin (slotCount n)) :
    (((slotEquiv n).symm u).1.val:ℤ) ∈ middleClassSites p n c ↔
      ((OddZetaSix.foldMod p hp (slotCenter n u)).val:ℤ)=c := by
  let t := ((slotEquiv n).symm u).1.val
  have ht : t≤25*n := by have := ((slotEquiv n).symm u).1.isLt; dsimp [t]; omega
  have hpz : 0<(p:ℤ) := by exact_mod_cast hp
  rw [foldMod_val_eq_middleFoldWall]
  change (t:ℤ) ∈ middleClassSites p n c ↔ middleFoldWall p (-(t:ℤ))=c
  rw [middleFoldWall_neg _ _ hpz]
  rw [(middleClassSites_spec p n c hc hc2).2]
  have hres : middleFoldWall p t=c ↔ (t:ℤ)%p=c ∨ (t:ℤ)%p=p-c := by
    unfold middleFoldWall; omega
  constructor
  · exact fun h => hres.mpr h.2.2
  · intro h
    have he : (t:ℤ)≠25*n := by
      intro he; exact hopen 25 (by decide) (h.symm.trans (congrArg _ he))
    exact ⟨by positivity,by omega,hres.mp h⟩

/-- The certifier lists positive slots only. All indices up to 11 are present
in the determinant, and inactive indices really have zero cost. -/
theorem refinedSlotCost_zero_of_inactive (n p k a : ℕ) [Fact p.Prime]
    (ha : kernelPoleOrder n k≤a) : refinedSlotCost n p k a=0 := by
  unfold refinedSlotCost
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro r hr
  have h1 := mem_range.mp (mem_filter.mp hr).1
  have h2 := (mem_filter.mp hr).2
  omega

/-- On the exact, duplicate-free list of all the poles of this class, the
certificate's raw bag equals the list of actual positive refined slot costs. -/
theorem middleRawBag_eq_actual (n p : ℕ) [Fact p.Prime] (hn : 0<n) (hp : 2<p)
    (hsq : 84*n<p^2) (c : ℤ) (hc : 0<c) (hc2 : 2*c<p) (hopen : middleOpenClass p n c) :
    (middleClassSites p n c).flatMap (Cert.middleSite p n) =
    (middleClassSites p n c).flatMap (fun t =>
      ((List.range (kernelPoleOrder n (center n+t.toNat))).map
        (fun a => (refinedSlotCost n p (center n+t.toNat) a:ℤ))).filter (fun z => decide (0<z))) := by
  apply List.flatMap_congr
  intro t ht
  obtain ⟨h0,h25,h16,h17,hw⟩ := openClass_site_conditions _ _ _ _ hc hc2 hopen ht
  have ht' := Int.toNat_of_nonneg h0
  have h1 : t.toNat≤25*n := by omega
  have h2 : t.toNat≠16*n := by omega
  have h3 : t.toNat≠17*n := by omega
  rw [middle_order_open _ _ h1 h2 h3]
  simpa only [ht'] using middleSite_matches_slots n p t.toNat hn hp hsq h1 h2 h3 (by rwa [ht'])

end OddZetaSix.B40a
