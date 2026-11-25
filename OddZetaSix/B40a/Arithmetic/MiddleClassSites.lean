import OddZetaSix.B40a.Arithmetic.MiddleStripBag

namespace OddZetaSix.B40a

theorem middle_range_index (a b p : ℤ) (i : ℕ) (hp : 0<p) :
    i < ((b-a+p-1)/p).toNat ↔ a+(i:ℤ)*p<b := by
  have h : i < ((b-a+p-1)/p).toNat ↔ (i:ℤ)+1 ≤ (b-a+p-1)/p := by omega
  rw [h,Int.le_ediv_iff_mul_le hp,add_mul,one_mul]; omega

theorem mem_middle_progression (p a b t : ℤ) (hp : 0<p) (ha : 0≤a) (hap : a<p) :
    t ∈ Cert.iRange a b p ↔ 0≤t ∧ t<b ∧ t%p=a := by
  unfold Cert.iRange
  simp only [ite_eq_right (by omega : ¬p≤0),List.mem_map,List.mem_range,middle_range_index _ _ _ _ hp]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨add_nonneg ha (mul_nonneg (by positivity) hp.le),hi,by
      rw [Int.add_mul_emod_self_right,Int.emod_eq_of_lt ha hap]⟩
  · rintro ⟨ht,hb,hm⟩
    have hq : 0≤t/p := Int.ediv_nonneg ht hp.le
    have he := Int.emod_add_mul_ediv t p
    rw [hm,mul_comm p] at he
    exact ⟨(t/p).toNat,by rwa [Int.toNat_of_nonneg hq,he],by rwa [Int.toNat_of_nonneg hq]⟩

theorem middle_progression_nodup (p a b : ℤ) (hp : 0<p) : (Cert.iRange a b p).Nodup := by
  unfold Cert.iRange
  rw [ite_eq_right (by omega : ¬p≤0)]
  apply List.Nodup.map _ List.nodup_range
  intro i j h
  have h' : (i:ℤ)*p=(j:ℤ)*p := add_left_cancel h
  have := mul_right_cancel₀ hp.ne' h'
  exact_mod_cast this

def middleClassSites (p d c : ℤ) := Cert.iRange c (25*d) p ++ Cert.iRange (p-c) (25*d) p

/-- Positive and negative lifts, with exactly one occurrence per pole. -/
theorem middleClassSites_spec (p d c : ℤ) (hc : 0<c) (hc2 : 2*c<p) :
    (middleClassSites p d c).Nodup ∧ ∀ t : ℤ,
    t ∈ middleClassSites p d c ↔ 0≤t ∧ t<25*d ∧ (t%p=c ∨ t%p=p-c) := by
  have hp : 0<p := by omega
  have h₁ := fun t => mem_middle_progression p c (25*d) t hp hc.le (by omega)
  have h₂ := fun t => mem_middle_progression p (p-c) (25*d) t hp (by omega) (by omega)
  unfold middleClassSites
  refine ⟨List.nodup_append.mpr ⟨middle_progression_nodup _ _ _ hp,
    middle_progression_nodup _ _ _ hp,?_⟩,?_⟩
  · rintro t ht s hs rfl
    have := (h₁ _).mp ht
    have := (h₂ _).mp hs
    omega
  · intro t; rw [List.mem_append,h₁,h₂]; tauto

/-- The certificate's folded address agrees with the formal determinant's
folded slot index, including negative centers. -/
theorem foldMod_val_eq_middleFoldWall (p : ℕ) (hp : 0<p) (t : ℤ) :
    ((OddZetaSix.foldMod p hp t).val:ℤ) = middleFoldWall p t := by
  have hpz : 0<(p:ℤ) := by exact_mod_cast hp
  have h0 := Int.emod_nonneg t hpz.ne'
  have h1 := Int.emod_lt_of_pos t hpz
  unfold OddZetaSix.foldMod middleFoldWall
  dsimp only
  split_ifs <;> dsimp only <;> omega

end OddZetaSix.B40a
