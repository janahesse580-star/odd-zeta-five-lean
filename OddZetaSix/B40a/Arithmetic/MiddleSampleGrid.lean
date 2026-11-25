import OddZetaSix.B40a.Arithmetic.MiddleStripGrid
import OddZetaSix.B40a.Arithmetic.MiddleScaling
import OddZetaSix.B40a.Arithmetic.MiddleBoundary

namespace OddZetaSix.B40a
namespace MiddleGrid
open Finset Cert.StripGrid

abbrev wallSet (n p : ℕ) := walls (4*(p:ℤ)) (4*(n:ℤ))
abbrev stripSet (n p : ℕ) := strips (4*(p:ℤ)) (4*(n:ℤ))
def interior (p : ℕ) (v : ℤ×ℤ) := univ.filter
  (fun c : Fin (p/2+1) => v.1<4*(c.val:ℤ) ∧ 4*(c.val:ℤ)<v.2)
def wallClasses (n p : ℕ) := univ.filter
  (fun c : Fin (p/2+1) => 4*(c.val:ℤ)∈wallSet n p)
def sampleBag (n p : ℕ) (v : ℤ×ℤ) :=
  middleSortedSlots ((middleClassSites (4*(p:ℤ)) (4*(n:ℤ)) ((v.1+v.2)/2)).flatMap
    (Cert.middleSite (4*(p:ℤ)) (4*(n:ℤ))))

private theorem mem_folded_wall (n p : ℕ) (e : ℤ) (he : e∈([16,17,25,34,59]:List ℤ)) :
    middleFoldWall (4*p) (e*(4*n)) ∈ wallSet n p := by
  apply ((increasing_spec _).2.2 _).mpr
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e,he,rfl⟩))

theorem wallClasses_card (n p : ℕ) : (wallClasses n p).card≤7 := by
  have h := Finset.card_le_card_of_injOn (s:=wallClasses n p) (t:=(wallSet n p).toFinset)
    (fun c : Fin (p/2+1) => 4*(c.val:ℤ)) (fun _ h=>List.mem_toFinset.mpr (mem_filter.mp h).2)
    (by intro a ha b hb he; change 4*(a.val:ℤ)=4*(b.val:ℤ) at he; apply Fin.ext; omega)
  have hl := (increasing_spec (0::(4*(p:ℤ))/2::([16,17,25,34,59]:List ℤ).map
    (fun e => foldAddr (4*(p:ℤ)) (e*(4*n))))).2.1
  exact h.trans ((List.toFinset_card_le _).trans hl)

theorem offWall_cover (n p : ℕ) (c : Fin (p/2+1)) (hc : c∉wallClasses n p) :
    ∃ v ∈ stripSet n p,c∈interior p v := by
  have hw : 4*(c.val:ℤ)∉wallSet n p := fun h=>hc (mem_filter.mpr ⟨mem_univ _,h⟩)
  have h0 : (0:ℤ)∈wallSet n p := ((increasing_spec _).2.2 _).mpr List.mem_cons_self
  have he : 2*(p:ℤ)∈wallSet n p := by
    rw [show 2*(p:ℤ)=4*(p:ℤ)/2 by omega]
    exact ((increasing_spec _).2.2 _).mpr (List.mem_cons_of_mem _ List.mem_cons_self)
  have hc0 : 4*(c.val:ℤ)≠0 := fun h=>hw (h ▸ h0)
  have hce : 4*(c.val:ℤ)≠2*(p:ℤ) := fun h=>hw (h ▸ he)
  have := c.isLt
  obtain ⟨v,hv,hlo,hhi⟩ := cover_adjacent _ (increasing_spec _).1 hw ⟨0,h0,by omega⟩
    ⟨2*(p:ℤ),he,by omega⟩
  exact ⟨v,hv,mem_filter.mpr ⟨mem_univ _,hlo,hhi⟩⟩

/-- The literal midpoint sampled in middleClasses at four times the
integer scale has exactly the same ranked entries as each true class. -/
theorem sample_rank (n p : ℕ) [Fact p.Prime] (hn : 0<n) (hp : 2<p) (hsq : 84*n<p^2)
    (v : ℤ×ℤ) (hv : v∈stripSet n p) (c : Fin (p/2+1)) (hc : c∈interior p v) (r : ℕ) :
    (sampleBag n p v).getD r 0 =
      (OddZetaSix.nthDescWeight (middleSlotClass n p (Fact.out : p.Prime).pos c) (slotCost n p) r:ℤ) := by
  obtain ⟨a,b⟩ := v
  have hnz : 0<(p:ℤ) := by omega
  obtain ⟨h0,hab,hmax,_,hm1,hm2⟩ := strip_window p n a b hnz hv
  obtain ⟨h₁,h₂⟩ := (mem_filter.mp hc).2
  change a<4*(c.val:ℤ) at h₁; change 4*(c.val:ℤ)<b at h₂
  have hno := (adjacent_gap _ (increasing_spec _).1 hv).2.2.2
  have H (x y : ℤ) (hx : a<x) (hy : y<b) (hle : x≤y) :
      (middleClassSites (4*p) (4*n) x).flatMap (Cert.middleSite (4*p) (4*n)) =
        (middleClassSites (4*p) (4*n) y).flatMap (Cert.middleSite (4*p) (4*n)) := by
    apply middle_strip_bag_constant _ _ _ _ (by omega) (by omega) hle (by omega)
    intro e he hs
    exact hno _ (mem_folded_wall n p e he) ⟨hx.trans_le hs.1,hs.2.trans_lt hy⟩
  have hsite : (middleClassSites (4*p) (4*n) ((a+b)/2)).flatMap (Cert.middleSite (4*p) (4*n)) =
      (middleClassSites (4*p) (4*n) (4*(c.val:ℤ))).flatMap (Cert.middleSite (4*p) (4*n)) := by
    rcases le_total ((a+b)/2) (4*(c.val:ℤ)) with he|he
    · exact H _ _ hm1 h₂ he
    · exact (H _ _ h₁ hm2 he).symm
  have hopen : middleOpenClass p n c.val := by
    intro e he eq
    have hw := mem_folded_wall n p e he
    change foldAddr (4*(p:ℤ)) (e*(4*n)) ∈ wallSet n p at hw
    rw [show e*(4*(n:ℤ))=4*(e*n) by ring,foldAddr_scale_four] at hw
    change (c.val:ℤ)=foldAddr p (e*n) at eq
    rw [←eq] at hw
    exact hno _ hw ⟨h₁,h₂⟩
  unfold sampleBag
  rw [hsite,middleRawBag_scale _ _ _ _ hnz (by decide)]
  exact middleRankedSlot_eq _ _ hn hp hsq c (by omega) (by omega) hopen r

theorem boundary_total (n p : ℕ) [Fact p.Prime] (hn : 0<n) (hsq : 84*n<p^2)
    (hband : 11*n≤20*p) :
    ∑ c ∈ wallClasses n p, ∑ u ∈ middleSlotClass n p (Fact.out : p.Prime).pos c,slotCost n p u ≤ 123648 := by
  calc
    _ ≤ ∑ _c ∈ wallClasses n p,17664 := sum_le_sum (fun c _ => middle_boundary_class_cost _ _ hn hsq hband c)
    _ ≤ _ := by
      simp only [sum_const,nsmul_eq_mul]
      change (wallClasses n p).card*17664≤123648
      have := wallClasses_card n p; omega

end MiddleGrid
end OddZetaSix.B40a
