import OddZetaSix.B40a.Arithmetic.PeriodicSlots
import Mathlib.Data.Rat.Floor

/-! Discrete residue counts, their continuous floor model, and the exact
single-endpoint correction for a closed interval. -/
namespace OddZetaSix.B40a
open Finset

def residueCount (p : ℕ) (a b c : ℤ) : ℕ :=
  ((Icc a b).filter (fun k => (p : ℤ) ∣ k-c)).card

theorem residueCount_eq_ediv (p : ℕ) (hp : 0<p) (a b c : ℤ) (hab : a≤b) :
    (residueCount p a b c : ℤ) = (b-c)/(p : ℤ)-(a-c-1)/(p : ℤ) := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hpne : (p : ℤ) ≠ 0 := hpz.ne'
  let L := (a-c-1)/(p : ℤ)+1
  let U := (b-c)/(p : ℤ)
  have he : residueCount p a b c = (Icc L U).card := by
    unfold residueCount
    apply Finset.card_bij (fun k _ => (k-c)/(p : ℤ))
    · intro k hk
      have h := mem_filter.mp hk
      obtain ⟨z,hz⟩ := h.2
      rw [hz,Int.mul_ediv_cancel_left _ hpne,mem_Icc]
      have hk' := mem_Icc.mp h.1
      exact ⟨by
        apply Int.add_one_le_iff.mpr
        apply (Int.ediv_lt_iff_lt_mul hpz).mpr
        rw [mul_comm,← hz]
        omega,
        by
          apply (Int.le_ediv_iff_mul_le hpz).mpr
          rw [mul_comm,← hz]
          omega⟩
    · intro k hk l hl h
      obtain ⟨z,hz⟩ := (mem_filter.mp hk).2
      obtain ⟨w,hw⟩ := (mem_filter.mp hl).2
      rw [hz,hw,Int.mul_ediv_cancel_left _ hpne,Int.mul_ediv_cancel_left _ hpne] at h
      rw [h] at hz
      omega
    · intro z hz
      have hz' := mem_Icc.mp hz
      refine ⟨z*(p : ℤ)+c,mem_filter.mpr ⟨mem_Icc.mpr ⟨?_,?_⟩,?_⟩,?_⟩
      · have h := (Int.ediv_lt_iff_lt_mul hpz).mp (show (a-c-1)/(p : ℤ) < z by
          have hl := hz'.1
          unfold L at hl
          omega)
        omega
      · have h := (Int.le_ediv_iff_mul_le hpz).mp hz'.2
        omega
      · exact ⟨z,by ring⟩
      · rw [add_sub_cancel_right,Int.mul_ediv_cancel _ hpne]
  have hnonneg : 0 ≤ U+1-L := by
    have h := Int.ediv_le_ediv hpz (show a-c-1 ≤ b-c by omega)
    dsimp [U,L]
    omega
  rw [he,Int.card_Icc,Int.toNat_of_nonneg hnonneg]
  dsimp [L,U]
  omega

private theorem floor_div_nat (x : ℤ) (p : ℕ) :
    ⌊(x : ℝ)/(p : ℝ)⌋ = x/(p : ℤ) := by
  rw [← Rat.cast_intCast (α := ℝ) x,← Rat.cast_natCast (α := ℝ) p,← Rat.cast_div,
    Rat.floor_cast,Rat.floor_intCast_div_natCast]

theorem periodicCount_rational (a b c : ℤ) (n p : ℕ) (hp : 0<p) :
    periodicCount a b ((n : ℝ)/p) ((c : ℝ)/p) =
      (b*(n : ℤ)-c)/(p : ℤ)-(a*(n : ℤ)-c)/(p : ℤ)-(b-a)*(n : ℤ)/(p : ℤ) := by
  have hr : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hh (d : ℤ) : (d : ℝ)*((n : ℝ)/p)-(c : ℝ)/p =
      ((d*(n : ℤ)-c : ℤ) : ℝ)/(p : ℝ) := by
    push_cast
    field_simp
  have hL : (((b-a : ℤ) : ℝ))*((n : ℝ)/p) =
      (((b-a)*(n : ℤ) : ℤ) : ℝ)/(p : ℝ) := by push_cast; ring
  unfold periodicCount
  rw [hh a,hh b,hL,floor_div_nat,floor_div_nat,floor_div_nat]

theorem residue_closed_normalized (a b c : ℤ) (n p : ℕ) (hp : 0<p) (hab : a≤b) :
    (residueCount p (a*n) (b*n) c : ℤ) - (b-a)*(n : ℤ)/(p : ℤ) =
      periodicCount a b ((n : ℝ)/p) ((c : ℝ)/p) +
        (if (p : ℤ) ∣ a*(n : ℤ)-c then (1 : ℤ) else 0) := by
  have hAB : a*(n : ℤ) ≤ b*(n : ℤ) := mul_le_mul_of_nonneg_right hab (Int.natCast_nonneg n)
  rw [residueCount_eq_ediv p hp _ _ _ hAB,periodicCount_rational a b c n p hp]
  have hx := residueCount_eq_ediv p hp (a*n) (a*n) c le_rfl
  have hy : (residueCount p (a*n) (a*n) c : ℤ) =
      (if (p : ℤ) ∣ a*(n : ℤ)-c then (1 : ℤ) else 0) := by
    unfold residueCount
    rw [Icc_self]
    split_ifs with hh
    · have hs : (({a*(n : ℤ)} : Finset ℤ).filter (fun k => (p : ℤ) ∣ k-c)) =
          {a*(n : ℤ)} := by
        apply Finset.filter_eq_self.mpr
        intro k hk
        rw [Finset.mem_singleton.mp hk]
        exact hh
      rw [hs,Finset.card_singleton,Nat.cast_one]
    · simp [hh]
  rw [hy] at hx
  linarith only [hx]

def endpointAlias (p : ℕ) (x c : ℤ) : ℤ :=
  if (p : ℤ) ∣ x-c then 1 else 0

theorem residue_right_closed_normalized (a b c : ℤ) (n p : ℕ) (hp : 0<p) (hn : 0<n)
    (hab : a<b) :
    (residueCount p (a*n+1) (b*n) c : ℤ) - (b-a)*(n : ℤ)/(p : ℤ) =
      periodicCount a b ((n : ℝ)/p) ((c : ℝ)/p) := by
  have ht : a*(n : ℤ) < b*(n : ℤ) := mul_lt_mul_of_pos_right hab (by exact_mod_cast hn)
  rw [residueCount_eq_ediv p hp _ _ _ (by omega),periodicCount_rational a b c n p hp]
  congr 2
  ring

theorem residue_left_closed_normalized (a b c : ℤ) (n p : ℕ) (hp : 0<p) (hn : 0<n)
    (hab : a<b) :
    (residueCount p (a*n) (b*n-1) c : ℤ) - (b-a)*(n : ℤ)/(p : ℤ) =
      periodicCount a b ((n : ℝ)/p) ((c : ℝ)/p) +
        endpointAlias p (a*n) c - endpointAlias p (b*n) c := by
  have ht : a*(n : ℤ) < b*(n : ℤ) := mul_lt_mul_of_pos_right hab (by exact_mod_cast hn)
  have H := residue_closed_normalized b b c n p hp le_rfl
  have he := periodicCount_rational b b c n p hp
  have hh : periodicCount b b ((n : ℝ)/p) ((c : ℝ)/p) = 0 := by
    rw [he]
    simp
  rw [hh,sub_self,zero_mul,Int.zero_ediv,sub_zero,zero_add] at H
  rw [residueCount_eq_ediv p hp _ _ _ le_rfl] at H
  change (b*(n : ℤ)-c)/(p : ℤ)-(b*(n : ℤ)-c-1)/(p : ℤ) = endpointAlias p (b*n) c at H
  have hc := residue_closed_normalized a b c n p hp hab.le
  rw [residueCount_eq_ediv p hp _ _ _ ht.le] at hc
  rw [residueCount_eq_ediv p hp _ _ _ (by omega)]
  have hcon : b*(n : ℤ)-1-c = b*(n : ℤ)-c-1 := by ring
  rw [hcon]
  change _ = _ + endpointAlias p (a*n) c - endpointAlias p (b*n) c
  change _ = _ + endpointAlias p (a*n) c at hc
  linarith only [H,hc]

def finitePeriodicRaw (n p : ℕ) (c : ℤ) : ℤ :=
  4 + 6*((residueCount p (-25*n) (25*n) c : ℤ) - 50*n/p) +
    4*((residueCount p (-17*n) (17*n) c : ℤ) - 34*n/p) +
    2*((residueCount p (-16*n) (16*n) c : ℤ) - 32*n/p) -
    5*((residueCount p (-59*n) (-34*n-1) c : ℤ) - 25*n/p) -
    5*((residueCount p (34*n+1) (59*n) c : ℤ) - 25*n/p)

noncomputable def continuousPeriodicRaw (τ u : ℝ) : ℤ :=
  4 + 6*periodicCount (-25) 25 τ u + 4*periodicCount (-17) 17 τ u +
    2*periodicCount (-16) 16 τ u - 5*periodicCount (-59) (-34) τ u -
    5*periodicCount 34 59 τ u

theorem finitePeriodicRaw_eq (n p : ℕ) (hn : 0<n) (hp : 0<p) (c : ℤ) :
    finitePeriodicRaw n p c =
      continuousPeriodicRaw ((n : ℝ)/p) ((c : ℝ)/p) +
        (6*endpointAlias p (-25*n) c + 4*endpointAlias p (-17*n) c +
          2*endpointAlias p (-16*n) c - 5*endpointAlias p (-59*n) c +
          5*endpointAlias p (-34*n) c) := by
  have h1 := residue_closed_normalized (-25) 25 c n p hp (by decide)
  have h2 := residue_closed_normalized (-17) 17 c n p hp (by decide)
  have h3 := residue_closed_normalized (-16) 16 c n p hp (by decide)
  have h4 := residue_left_closed_normalized (-59) (-34) c n p hp hn (by decide)
  have h5 := residue_right_closed_normalized 34 59 c n p hp hn (by decide)
  norm_num only [sub_neg_eq_add,Int.reduceAdd,Int.reduceSub] at h1 h2 h3 h4 h5
  unfold finitePeriodicRaw continuousPeriodicRaw endpointAlias
  unfold endpointAlias at h4
  linarith only [h1,h2,h3,h4,h5]

theorem finitePeriodicScore_eq_off_walls (n p : ℕ) (hn : 0<n) (hp : 0<p) (c : ℤ)
    (h : ∀ e : ℤ, e ∈ ([-25,-17,-16,-59,-34] : List ℤ) → ¬ (p : ℤ) ∣ e*n-c) :
    max 0 (finitePeriodicRaw n p c) = periodicScore ((n : ℝ)/p) ((c : ℝ)/p) := by
  rw [finitePeriodicRaw_eq n p hn hp]
  have he (e : ℤ) (he : e ∈ ([-25,-17,-16,-59,-34] : List ℤ)) :
      endpointAlias p (e*n) c = 0 := ite_eq_right (h e he)
  rw [he (-25) (by decide),he (-17) (by decide),he (-16) (by decide),
    he (-59) (by decide),he (-34) (by decide)]
  simp [continuousPeriodicRaw,periodicScore]

end OddZetaSix.B40a
