import OddZetaSix.B40a.Arithmetic.SmallRowEstimate
import OddZetaSix.B40a.Arithmetic.WeightedPNT
noncomputable section
namespace OddZetaSix.B40a.Cert
open Finset Filter Set
open PeriodAffine
set_option maxRecDepth 32768
attribute [local irreducible] smallRows

abbrev SmallIndex := Fin smallRows.length
def smallRow (i : SmallIndex) := smallRows.get i
theorem smallRow_mem (i : SmallIndex) : smallRow i ∈ smallRows := List.get_mem _ _
abbrev SmallTile := Σ _ : SmallIndex, ℕ
def smallTiles (K : ℕ) : Finset SmallTile :=
  univ.sigma (fun i => Finset.Ico (periodStart (smallRow i).left) K)
def tileLo (i : SmallTile) : ℝ := 1/((i.2:ℝ)+(smallRow i.1).right)
def tileHi (i : SmallTile) : ℝ := 1/((i.2:ℝ)+(smallRow i.1).left)
def tileW (i : SmallTile) := smallTileWeight (smallRow i.1) i.2

private theorem chain_contains {xs : List ArithRow} {a b : ℚ} {t : ℝ}
    (hc : arithChain a b xs = true) (ht : (a:ℝ)≤t ∧ t<b) :
    ∃ r ∈ xs,(r.left:ℝ)≤t ∧ t<r.right := by
  induction xs generalizing a with
  | nil => simp only [arithChain,decide_eq_true_eq] at hc; subst a; linarith [ht.1,ht.2]
  | cons r xs ih =>
    simp only [arithChain,Bool.and_eq_true,decide_eq_true_eq] at hc
    by_cases hr : t<(r.right:ℝ)
    · exact ⟨r,List.mem_cons_self, hc.1 ▸ ht.1,hr⟩
    · obtain ⟨q,hq,hh⟩ := ih hc.2 ⟨le_of_not_gt hr,ht.2⟩
      exact ⟨q,List.mem_cons_of_mem _ hq,hh⟩

theorem tile_positive {K : ℕ} {i : SmallTile} (hi : i ∈ smallTiles K) :
    0 < (i.2:ℝ)+(smallRow i.1).left := by
  have hk := (Finset.mem_Ico.mp (mem_sigma.mp hi).2).1
  have hs : 0 < periodStart (smallRow i.1).left := by unfold periodStart; split <;> decide
  have hkR : (0:ℝ) < i.2 := by exact_mod_cast hs.trans_le hk
  have ha : (0:ℝ)≤(smallRow i.1).left := by exact_mod_cast (smallRow_bounds _ (smallRow_mem _)).1
  linarith

theorem tile_endpoints {K : ℕ} {i : SmallTile} (hi : i ∈ smallTiles K) :
    0<tileLo i ∧ tileLo i≤tileHi i ∧ tileHi i≤84 := by
  have hp := tile_positive hi
  have hr := smallRow_bounds _ (smallRow_mem i.1)
  have hab : ((smallRow i.1).left:ℝ)<(smallRow i.1).right := by exact_mod_cast hr.2.1
  have hb : 0<(i.2:ℝ)+(smallRow i.1).right := by linarith
  have hj := (Finset.mem_Ico.mp (mem_sigma.mp hi).2).1
  have hstart : 1 ≤ periodStart (smallRow i.1).left := by unfold periodStart; split <;> decide
  have h1 : (1:ℝ) ≤ i.2 := by exact_mod_cast hstart.trans hj
  have ha : (0:ℝ)≤(smallRow i.1).left := by exact_mod_cast hr.1
  exact ⟨one_div_pos.mpr hb,one_div_le_one_div_of_le hp (by linarith),
    (div_le_iff₀ hp).mpr (by linarith)⟩

theorem tile_bounds_inverse {K : ℕ} {i : SmallTile} (hi : i ∈ smallTiles K) {P : ℝ}
    (hP : P ∈ Icc (tileLo i) (tileHi i)) :
    1/P-i.2 ∈ Icc ((smallRow i.1).left:ℝ) (smallRow i.1).right := by
  have hp := (tile_endpoints hi).1.trans_le hP.1
  have h1 := one_div_le_one_div_of_le hp hP.2
  have h2 := one_div_le_one_div_of_le (tile_endpoints hi).1 hP.1
  simp only [tileLo,tileHi,one_div_one_div] at h1 h2
  exact ⟨by linarith,by linarith⟩

def smallExceptional (K n : ℕ) : Finset ℕ :=
  ((smallTiles K).image (fun i => ⌊tileHi i*(n:ℝ)⌋₊)) ∩ cutoffPrimes n

theorem small_band_cover {K n p : ℕ} (hK : 17≤K) (hn : 0<n) (hp : p.Prime)
    (hP : 1/(K:ℝ)*(n:ℝ) < p) (hmax : (p:ℝ) ≤ 11/20*(n:ℝ))
    (hE : p ∉ smallExceptional K n) :
    ∃ i ∈ smallTiles K, tileLo i*(n:ℝ)<p ∧ (p:ℝ)≤tileHi i*n ∧
      (n:ℝ)/p-i.2 ∈ Ioo ((smallRow i.1).left:ℝ) (smallRow i.1).right := by
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have hpR : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have hKR : 0<(K:ℝ) := by exact_mod_cast (show 0<K by omega)
  let τ : ℝ := (n:ℝ)/p
  have ht0 : 0<τ := div_pos hnR hpR
  have ht20 : 20/11 ≤ τ := (le_div_iff₀ hpR).mpr (by linarith)
  have htK : τ<K := (div_lt_iff₀ hpR).mpr (by
    have := (div_lt_iff₀ hKR).mp (by simpa [div_eq_inv_mul] using hP : (n:ℝ)/K < p)
    linarith)
  let k := ⌊τ⌋₊
  have hk0 : (k:ℝ) ≤ τ := Nat.floor_le ht0.le
  have hk1 : τ < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have hkK : k<K := by exact_mod_cast hk0.trans_lt htK
  have ht : 0≤τ-k ∧ τ-k<1 := ⟨by linarith,by linarith⟩
  obtain ⟨r,hr,hl,hh⟩ := chain_contains small_chain (t:=τ-k) (by simpa only [Rat.cast_zero,Rat.cast_one] using ht)
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hr
  have heqr : smallRow j = r := hj
  let i : SmallTile := ⟨j,k⟩
  have hk : periodStart r.left ≤ k := by
    have hone : 1≤k := by
      by_contra h
      have h0 : k=0 := by omega
      rw [h0] at hk1
      norm_num at hk1
      linarith only [hk1,ht20]
    unfold periodStart
    split
    · exact hone
    · rename_i hleft
      have hright := (smallRow_bounds r hr).2.2.2.resolve_left hleft
      have hrr : (r.right:ℝ) ≤ 9/11 := by simpa using (Rat.cast_le (K:=ℝ)).mpr hright
      by_contra h
      have he : k=1 := by omega
      rw [he] at hh
      push_cast at hh
      linarith
  have him : i ∈ smallTiles K := mem_sigma.mpr ⟨mem_univ _,Finset.mem_Ico.mpr
    ⟨(by simpa [i,heqr] using hk),hkK⟩⟩
  have hbelow : (k:ℝ)+r.left ≤ τ := by linarith
  have habove : τ < (k:ℝ)+r.right := by linarith
  have hpos : 0<(k:ℝ)+r.left := by simpa [i,heqr] using tile_positive him
  have hpos2 := ht0.trans habove
  have up : (p:ℝ)≤tileHi i*n := by
    dsimp [tileHi,i]; rw [heqr]
    rw [one_div_mul_eq_div,le_div_iff₀ hpos,mul_comm]
    exact (le_div_iff₀ hpR).mp hbelow
  have low : tileLo i*n < (p:ℝ) := by
    dsimp [tileLo,i]; rw [heqr]
    rw [one_div_mul_eq_div,div_lt_iff₀ hpos2,mul_comm]
    exact (div_lt_iff₀ hpR).mp habove
  have hne : (r.left:ℝ)≠τ-k := by
    intro h
    apply hE
    have hnum : (k:ℝ)+r.left=τ := by linarith
    have hiEq : tileHi i*(n:ℝ)=p := by
      dsimp [tileHi,i]; rw [heqr,hnum]; dsimp [τ]; field_simp
    have hpn : p≤84*n := by exact_mod_cast (show (p:ℝ)≤84*n by linarith)
    exact mem_inter.mpr ⟨mem_image.mpr ⟨i,him,by rw [hiEq,Nat.floor_natCast]⟩,
      Nat.mem_primesLE.mpr ⟨hpn,hp⟩⟩
  refine ⟨i,him,low,up,?_⟩
  simpa [i,heqr,τ] using (show τ-k ∈ Ioo (r.left:ℝ) r.right from ⟨lt_of_le_of_ne hl hne,hh⟩)

end OddZetaSix.B40a.Cert
