import OddZetaSix.B40a.Arithmetic.MiddleActualLayers

namespace OddZetaSix.B40a
open Finset
noncomputable section

def middleUpdateHist (xs : List ℤ) (H : Array ℕ) :=
  xs.foldl (fun (h : Array ℕ) v => h.modify v.toNat (·+1)) H

def middleSortedSlots (xs : List ℤ) : List ℤ :=
  let hist := middleUpdateHist xs (Array.replicate 17 0)
  (Cert.nrange 1 17).reverse.flatMap (fun (k : ℕ) => List.replicate hist[k]! (k:ℤ))

theorem middleUpdateHist_bin (xs : List ℤ) (H : Array ℕ) {k : ℕ} (hk : 0<k) (hsize : k<H.size) :
    (middleUpdateHist xs H)[k]! = H[k]!+xs.count (k:ℤ) := by
  induction xs generalizing H with
  | nil => simp [middleUpdateHist]
  | cons v xs ih =>
    change (middleUpdateHist xs (H.modify v.toNat (·+1)))[k]! = _
    have hs : k<(H.modify v.toNat (·+1)).size := by simpa using hsize
    rw [ih _ hs,getElem!_pos (H.modify v.toNat (·+1)) k hs,Array.getElem_modify,getElem!_pos H k hsize,List.count_cons]
    by_cases he : v=(k:ℤ)
    · subst v; simp; omega
    · have hne : v.toNat≠k := by omega
      simp [hne,he]

private theorem expanded_count (keys : List ℕ) (hd : keys.Nodup) (f : ℕ → ℕ) (z : ℤ) :
    (keys.flatMap (fun k => List.replicate (f k) (k:ℤ))).count z =
      if 0≤z ∧ z.toNat∈keys then f z.toNat else 0 := by
  induction keys with
  | nil => simp
  | cons a keys ih =>
    obtain ⟨hnot,ht⟩ := List.nodup_cons.mp hd
    rw [List.flatMap_cons,List.count_append,List.count_replicate,ih ht]
    by_cases he : (a:ℤ)=z
    · subst z; simp [hnot]
    · have H : 0≤z → z.toNat≠a := by omega
      by_cases hz : 0≤z <;> simp [he,hz,H]

private theorem keys_spec (k : ℕ) : k∈(Cert.nrange 1 17).reverse ↔ 0<k ∧ k<17 := by
  simp only [List.mem_reverse,Cert.nrange,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩; omega
  · rintro ⟨h₁,h₂⟩; exact ⟨k-1,by omega,by omega⟩

theorem middleSortedSlots_perm (xs : List ℤ) (hr : ∀ z∈xs, 0<z ∧ z≤16) :
    (middleSortedSlots xs).Perm xs := by
  apply List.perm_iff_count.mpr
  intro z
  unfold middleSortedSlots
  rw [expanded_count _ (by decide)]
  simp only [keys_spec]
  split_ifs with h
  · have hi := middleUpdateHist_bin xs (Array.replicate 17 0) h.2.1 (by simpa using h.2.2)
    rw [Int.toNat_of_nonneg h.1] at hi
    simpa [getElem!_pos (Array.replicate 17 (0:ℕ)) z.toNat (by simpa using h.2.2 : z.toNat<(Array.replicate 17 (0:ℕ)).size)] using hi
  · have hn : z∉xs := by intro hm; have := hr z hm; omega
    exact (List.count_eq_zero_of_not_mem hn).symm

theorem middleSortedSlots_decreasing (xs : List ℤ) : (middleSortedSlots xs).Pairwise (·≥·) := by
  unfold middleSortedSlots
  rw [List.pairwise_flatMap]
  constructor
  · intro k _; exact List.pairwise_replicate.mpr (Or.inr le_rfl)
  · have h : (Cert.nrange 1 17).reverse.Pairwise (·≥·) := by decide
    apply h.imp
    intro a b hab z hz w hw
    have hz' := List.eq_of_mem_replicate hz
    have hw' := List.eq_of_mem_replicate hw
    subst z; subst w; exact_mod_cast hab

theorem middleRawBag_range (n p : ℕ) [Fact p.Prime] (hn : 0<n) (hp : 2<p)
    (hsq : 84*n<p^2) (c : ℤ) (hc : 0<c) (hc2 : 2*c<p) (hopen : middleOpenClass p n c) :
    ∀ z ∈ (middleClassSites p n c).flatMap (Cert.middleSite p n), 0<z ∧ z≤16 := by
  rw [middleRawBag_eq_actual n p hn hp hsq c hc hc2 hopen]
  intro z hz
  obtain ⟨t,ht,hm⟩ := List.mem_flatMap.mp hz
  obtain ⟨hma,hz⟩ := List.mem_filter.mp hm
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hma
  refine ⟨of_decide_eq_true hz,?_⟩
  have h := refinedSlotCost_le_finitePeriodic n p hn hsq (center n+t.toNat) a
  have h' := finitePeriodicRaw_le_16 n p hn (by omega) ((center n+t.toNat:ℕ)- (center n:ℤ))
  omega

end
end OddZetaSix.B40a
