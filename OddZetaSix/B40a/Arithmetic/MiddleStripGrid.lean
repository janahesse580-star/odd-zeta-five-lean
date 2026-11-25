import OddZetaSix.B40a.Arithmetic.MiddleSweepBins
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Card

namespace OddZetaSix.B40a.Cert
namespace StripGrid
open Finset

theorem mem_insertZ (z x : ℤ) (xs : List ℤ) : z ∈ insertZ x xs ↔ z=x ∨ z∈xs := by
  induction xs with
  | nil => simp [insertZ]
  | cons y ys ih => unfold insertZ; split_ifs <;> simp_all [or_left_comm]

private theorem sorted_insertZ (x : ℤ) (xs : List ℤ) (hx : xs.Pairwise (·<·)) :
    (insertZ x xs).Pairwise (·<·) := by
  induction xs with
  | nil => simp [insertZ]
  | cons y ys ih =>
    obtain ⟨hall,ht⟩ := List.pairwise_cons.mp hx
    unfold insertZ; split_ifs with h h'
    · apply List.pairwise_cons.mpr
      exact ⟨fun z hz => (List.mem_cons.mp hz).elim (fun he=>he ▸ h) (fun he=>h.trans (hall z he)),hx⟩
    · exact hx
    · refine List.pairwise_cons.mpr ⟨?_,ih ht⟩
      intro z hz
      rcases (mem_insertZ _ _ _).mp hz with rfl|hz
      · omega
      · exact hall _ hz

private theorem insertZ_length (x : ℤ) (xs : List ℤ) : (insertZ x xs).length ≤ xs.length+1 := by
  induction xs with
  | nil => simp [insertZ]
  | cons y ys ih => unfold insertZ; split_ifs <;> simp_all

private theorem increasing_spec_aux (xs acc : List ℤ) (h : acc.Pairwise (·<·)) :
    let ys := xs.foldl (fun s x=>insertZ x s) acc
    ys.Pairwise (·<·) ∧ ys.length≤xs.length+acc.length ∧ ∀ z, z∈ys ↔ z∈acc ∨ z∈xs := by
  induction xs generalizing acc with
  | nil => simpa using h
  | cons u us ih =>
    dsimp only [List.foldl_cons,List.length_cons]
    have ⟨hs,hl,hm⟩ := ih (insertZ u acc) (sorted_insertZ _ _ h)
    refine ⟨hs,by have := insertZ_length u acc; omega,?_⟩
    intro z; rw [hm,mem_insertZ,List.mem_cons]; tauto

theorem increasing_spec (xs : List ℤ) :
    (increasingZ xs).Pairwise (·<·) ∧ (increasingZ xs).length≤xs.length ∧
    ∀ z, z∈increasingZ xs ↔ z∈xs := by
  simpa [increasingZ] using increasing_spec_aux xs [] (by simp)

theorem adj_cons (a b : ℤ) (xs : List ℤ) :
    adjacent (a::b::xs)=(a,b)::adjacent (b::xs) := rfl

theorem adjacent_gap (xs : List ℤ) (hs : xs.Pairwise (·<·)) {a b : ℤ}
    (hab : (a,b)∈adjacent xs) :
    a∈xs ∧ b∈xs ∧ a<b ∧ ∀ z∈xs, ¬(a<z ∧ z<b) := by
  induction xs with
  | nil => simp [adjacent] at hab
  | cons x xs ih =>
    cases xs with
    | nil => simp [adjacent] at hab
    | cons y ys =>
      obtain ⟨hx,hs'⟩ := List.pairwise_cons.mp hs
      rw [adj_cons,List.mem_cons] at hab
      rcases hab with h|h
      · have ha := congrArg Prod.fst h; have hb := congrArg Prod.snd h
        change a=x at ha; change b=y at hb; subst a; subst b
        refine ⟨by simp,by simp,hx _ (by simp),?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl|hz
        · omega
        rcases List.mem_cons.mp hz with rfl|hz
        · omega
        have := (List.pairwise_cons.mp hs').1 _ hz; omega
      · obtain ⟨ha,hb,hh,hz⟩ := ih hs' h
        refine ⟨List.mem_cons_of_mem _ ha,List.mem_cons_of_mem _ hb,hh,?_⟩
        intro z hm
        rcases List.mem_cons.mp hm with rfl|hm
        · have := hx a ha; omega
        · exact hz z hm

/-- Every interior address off the wall set falls in an adjacent open strip. -/
theorem cover_adjacent (xs : List ℤ) (hs : xs.Pairwise (·<·)) {z : ℤ} (hz : z∉xs)
    (hl : ∃ a∈xs,a<z) (hr : ∃ b∈xs,z<b) :
    ∃ v∈adjacent xs,v.1<z ∧ z<v.2 := by
  induction xs with
  | nil => simp at hl
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [List.mem_singleton] at hl hr; omega
    | cons y ys =>
      have ⟨hx,hs'⟩ := List.pairwise_cons.mp hs
      have hz' : z∉y::ys := fun h=>hz (List.mem_cons_of_mem _ h)
      have xz : x<z := by
        obtain ⟨a,ha,hh⟩ := hl
        rcases List.mem_cons.mp ha with rfl|ha
        · exact hh
        · exact (hx _ ha).trans hh
      by_cases h : z<y
      · exact ⟨(x,y),by rw [adj_cons]; simp, xz,h⟩
      · have he : z≠y := fun e=>hz' (e ▸ List.mem_cons_self)
        obtain ⟨b,hb,hzB⟩ := hr
        have hb' : b∈y::ys := (List.mem_cons.mp hb).resolve_left (by omega)
        obtain ⟨v,hv,hh⟩ := ih hs' hz' ⟨y,List.mem_cons_self,by omega⟩ ⟨b,hb',hzB⟩
        exact ⟨v,by rw [adj_cons]; exact List.mem_cons_of_mem _ hv,hh⟩

def foldAddr (p u : ℤ) := min (u%p) (p-u%p)
def walls (p d : ℤ) := increasingZ (0::p/2::([16,17,25,34,59]:List ℤ).map (fun e=>foldAddr p (e*d)))
def strips (p d : ℤ) := adjacent (walls p d)

theorem foldAddr_scale_four (p u : ℤ) : foldAddr (4*p) (4*u)=4*foldAddr p u := by
  unfold foldAddr
  rw [Int.mul_emod_mul_of_pos _ _ (by decide : (0:ℤ)<4),←mul_sub]
  omega

private theorem scaled_wall (p d z : ℤ) (hp : 0<p) (h : z∈walls (4*p) (4*d)) :
    0≤z ∧ z≤2*p ∧ (z=2*p ∨ 4∣z) := by
  have hm := ((increasing_spec _).2.2 _).mp h
  simp only [List.mem_cons,List.mem_map] at hm
  rcases hm with rfl|rfl|⟨e,he,rfl⟩
  · exact ⟨le_rfl,by omega,Or.inr (dvd_zero _)⟩
  · exact ⟨by omega,by omega,Or.inl (by omega)⟩
  · rw [show e*(4*d)=4*(e*d) by ring,foldAddr_scale_four]
    unfold foldAddr
    have h₁ := Int.emod_nonneg (e*d) hp.ne'
    have h₂ := Int.emod_lt_of_pos (e*d) hp
    exact ⟨by omega,by omega,Or.inr (dvd_mul_right _ _)⟩

theorem strip_window (p d a b : ℤ) (hp : 0<p) (hab : (a,b)∈strips (4*p) (4*d)) :
    0≤a ∧ a<b ∧ b≤2*p ∧ 4∣a ∧ a<(a+b)/2 ∧ (a+b)/2<b := by
  have H := adjacent_gap _ (increasing_spec _).1 hab
  have ha := scaled_wall p d _ hp H.1
  have hb := scaled_wall p d _ hp H.2.1
  have hm : 4∣a := ha.2.2.resolve_left (by omega)
  obtain ⟨k,hk⟩ := hm
  rcases hb.2.2 with he|⟨j,hj⟩ <;> exact ⟨ha.1,H.2.2.1,hb.2.1,⟨k,hk⟩,by omega,by omega⟩

/-- No positive quadrature penalty for open strips on the fourfold lattice:
the left wall is a multiple of four; the upper endpoint can be a half period. -/
theorem four_times_class_card_le_width (p : ℕ) (d a b : ℤ) (hp : 0<p)
    (hab : (a,b)∈strips (4*(p:ℤ)) (4*d)) :
    4*((univ.filter (fun c : Fin (p/2+1) => a<4*(c.val:ℤ) ∧ 4*(c.val:ℤ)<b)).card:ℤ) ≤ b-a := by
  obtain ⟨h0,hlt,_,⟨m,hm⟩,_⟩ := strip_window p d a b (by exact_mod_cast hp) hab
  let S := univ.filter (fun c : Fin (p/2+1) => a<4*(c.val:ℤ) ∧ 4*(c.val:ℤ)<b)
  have hc := card_le_card_of_injOn (s:=S) (t:=Icc (m+1) ((b-1)/4))
    (fun c : Fin (p/2+1) => (c.val:ℤ)) (by
      intro c hc; obtain ⟨hl,hr⟩ := (mem_filter.mp hc).2
      change (c.val:ℤ) ∈ Icc (m+1) ((b-1)/4)
      exact mem_Icc.mpr ⟨by omega,by omega⟩) (by
        intro i hi j hj he; change (i.val:ℤ) = j.val at he; exact Fin.ext (by exact_mod_cast he))
  rw [Int.card_Icc] at hc
  change 4*(S.card:ℤ)≤b-a
  omega

end StripGrid
end OddZetaSix.B40a.Cert
