import OddZetaSix.B40a.Arithmetic.FoldedPackets
import OddZetaSix.B40a.Arithmetic.Valuation

/-! The one-layer folded prime bounds on the actual rational content. -/
noncomputable section
namespace OddZetaSix.B40a
open Finset
open scoped BigOperators

private theorem ediv_add_plus_one_le (p x d : ℤ) (hp : 0 < p) :
    (x+d+1)/p-x/p-d/p ≤ 1 := by
  have hx := (Int.ediv_lt_iff_lt_mul hp).mp (show x/p < x/p+1 by omega)
  have hd := (Int.ediv_lt_iff_lt_mul hp).mp (show d/p < d/p+1 by omega)
  have h : x+d+1 < (x/p+d/p+2)*p := by
    rw [show (x/p+d/p+2)*p = (x/p+1)*p+(d/p+1)*p by ring]
    omega
  have hh := (Int.ediv_lt_iff_lt_mul hp).mpr h
  omega

private theorem ediv_add_ge (p x d : ℤ) (hp : 0 < p) :
    0 ≤ (x+d)/p-x/p-d/p := by
  have hx := (Int.le_ediv_iff_mul_le hp).mp (le_refl (x/p))
  have hd := (Int.le_ediv_iff_mul_le hp).mp (le_refl (d/p))
  have h : (x/p+d/p)*p ≤ x+d := by rw [add_mul]; omega
  have hh := (Int.le_ediv_iff_mul_le hp).mpr h
  omega

private theorem residueCount_closed_upper (p : ℕ) (a b c : ℤ) (hp : 0 < p) (hab : a ≤ b) :
    (residueCount p a b c : ℤ)-(b-a)/p ≤ 1 := by
  rw [residueCount_eq_ediv p hp _ _ _ hab]
  have hh : a-c-1+(b-a)+1 = b-c := by ring
  simpa only [hh] using ediv_add_plus_one_le p (a-c-1) (b-a) (by exact_mod_cast hp)

private theorem residueCount_lower (p : ℕ) (a b c : ℤ) (hp : 0 < p) (hab : a ≤ b) :
    0 ≤ (residueCount p a b c : ℤ)-(b-a+1)/p := by
  rw [residueCount_eq_ediv p hp _ _ _ hab]
  have hh : a-c-1+(b-a+1) = b-c := by ring
  simpa only [hh] using ediv_add_ge p (a-c-1) (b-a+1) (by exact_mod_cast hp)

theorem finitePeriodicRaw_le_16 (n p : ℕ) (hn : 0 < n) (hp : 0 < p) (c : ℤ) :
    finitePeriodicRaw n p c ≤ 16 := by
  have h1 := residueCount_closed_upper p (-25*n) (25*n) c hp (by omega)
  have h2 := residueCount_closed_upper p (-17*n) (17*n) c hp (by omega)
  have h3 := residueCount_closed_upper p (-16*n) (16*n) c hp (by omega)
  have h4 := residueCount_lower p (-59*n) (-34*n-1) c hp (by omega)
  have h5 := residueCount_lower p (34*n+1) (59*n) c hp (by omega)
  rw [show (25*(n:ℤ))-(-25*n)=50*n by ring] at h1
  rw [show (17*(n:ℤ))-(-17*n)=34*n by ring] at h2
  rw [show (16*(n:ℤ))-(-16*n)=32*n by ring] at h3
  rw [show (-34*(n:ℤ)-1)-(-59*n)+1=25*n by ring] at h4
  rw [show (59*(n:ℤ))-(34*n+1)+1=25*n by ring] at h5
  unfold finitePeriodicRaw
  linarith only [h1,h2,h3,h4,h5]

theorem refinedSlotCost_le_finitePeriodic (n p : ℕ) [Fact p.Prime] (hn : 0<n)
    (hsq : 84*n < p^2) (k a : ℕ) :
    refinedSlotCost n p k a ≤ (finitePeriodicRaw n p ((k : ℤ)-center n)).toNat := by
  have hp2 : 2 < p := by
    have hp := (Fact.out : p.Prime).two_le
    by_contra! h
    obtain rfl : p=2 := by omega
    omega
  have hBase := finitePeriodicRaw_eq_kernel_counts n p hn hp2 hsq ((k : ℤ)-center n)
  change finitePeriodicRaw n p ((k : ℤ)-center n) =
    4 + (kernelPoleAliasCount n p ((k : ℤ)-center n) : ℤ) -
      (kernelZeroAliasCount n p ((k : ℤ)-center n) : ℤ) - factVal n p at hBase
  unfold refinedSlotCost
  apply Finset.sup_le
  intro r hr
  unfold refinedOrderCost
  apply Finset.sup_le
  intro l hl
  apply Int.toNat_le_toNat
  have hrm := mem_range.mp (mem_filter.mp hr).1
  have hlm := mem_range.mp (mem_filter.mp hl).1
  have hrl := (mem_filter.mp hl).2
  let m := kernelPoleOrder n k
  let d := m-1-l-r
  have hD : effectiveOrderLoss n p k d ≤ d := by
    unfold effectiveOrderLoss
    split_ifs <;> omega
  have hI : harmonicIndicator n p k l ≤ 1 := by
    unfold harmonicIndicator
    split_ifs <;> decide
  have hIz : (harmonicIndicator n p k l : ℤ) ≤ 1 := by exact_mod_cast hI
  have hmul := mul_le_mul_of_nonneg_left hIz
    (show (0 : ℤ) ≤ ((l+5 : ℕ) : ℤ) by positivity)
  rw [mul_one] at hmul
  change ((r : ℤ)-siteBaseVal n p k+(effectiveOrderLoss n p k d : ℤ)+
    ((l+5 : ℕ) : ℤ)*(harmonicIndicator n p k l : ℤ)) ≤ _
  have hh : (r : ℤ)+(d : ℤ)+(l : ℤ)+5 = (m : ℤ)+4 := by
    have hrl' : r ≤ m-1-l := hrl
    have hlm' : l<m := hlm
    unfold d
    omega
  have hDz : (effectiveOrderLoss n p k d : ℤ) ≤ d := by exact_mod_cast hD
  unfold siteBaseVal numAliasCount kernelDenomAliases
  push_cast at hmul ⊢
  dsimp [m] at hh
  linarith only [hBase,hh,hDz,hmul]

theorem slotCost_le_16 (n p : ℕ) [Fact p.Prime] (hn : 0<n)
    (hsq : 84*n < p^2) (u : Fin (slotCount n)) :
    slotCost n p u ≤ 16 := by
  unfold slotCost
  apply (refinedSlotCost_le_finitePeriodic n p hn hsq _ _).trans
  exact (Int.toNat_le_toNat (finitePeriodicRaw_le_16 n p hn (Fact.out : p.Prime).pos _))

/-- Refined Cauchy–Binet bound including the exact residue classes and row penalty. -/
theorem content_folded_capacity (n p : ℕ) [Fact p.Prime]
    (hn : 0 < n) (hsq : 84 * n < p ^ 2) (q : ℕ) :
    let hp := (Fact.out : p.Prime).pos
    let clsSet : Fin (p / 2 + 1) → Finset (Fin (slotCount n)) :=
      fun c => Finset.univ.filter (fun u => foldMod p hp (slotCenter n u) = c)
    let slotPairs : Finset (Fin (p / 2 + 1) × Fin (slotCount n)) :=
      Finset.univ.filter (fun cr => cr.2.val < (clsSet cr.1).card)
    let inc : Fin (p / 2 + 1) × Fin (slotCount n) → ℤ := fun cr =>
      (nthDescWeight (clsSet cr.1) (slotCost n p) cr.2.val : ℤ) -
        2 * ((cr.2.val - q : ℕ) : ℤ);
    -padicValRat p (content n) ≤
      2 * (sixRowPenalty (fiveRank n) p q : ℤ) +
        ∑ j ∈ Finset.Icc 1 18,
          (min (fiveRank n) (slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card : ℤ) := by
  intro hp clsSet slotPairs inc
  have h2h : 2 * fiveRank n < p ^ 2 := by unfold fiveRank; omega
  have hformal := folded_joint_formalValAtLeast (p := p) h2h
    (slotCenter n) (slotDeg n) (slotWeightMatrix n p) (slotCost n p)
    (fun u => (slotCost_le_16 n p hn hsq u).trans (by decide))
    (slotWeightMatrix_doubled_bound n p hn hsq) q
  rw [← Hpoly_eq_evalJet_mul_weight n p hn hp] at hformal
  have hnonpos : -(2 * (sixRowPenalty (fiveRank n) p q : ℤ) +
      ∑ j ∈ Finset.Icc 1 18,
        (min (fiveRank n) (slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card : ℤ)) ≤ 0 := by
    have h1 : (0 : ℤ) ≤ 2 * (sixRowPenalty (fiveRank n) p q : ℤ) := by positivity
    have h2 : (0 : ℤ) ≤ ∑ j ∈ Finset.Icc 1 18,
        (min (fiveRank n) (slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card : ℤ) :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    linarith
  have hge := content_padicValRat_ge_of_formal_nonpos n p _ hnonpos hformal
  linarith

/-- Unfolded option in the arithmetic certificate, on the same true content. -/
theorem content_unfolded_capacity (n p : ℕ) [Fact p.Prime]
    (hn : 0 < n) (hsq : 84 * n < p ^ 2) (q : ℕ) :
    let inc : Fin (slotCount n) → ℤ := fun u =>
      (slotCost n p u : ℤ) - 2*((slotDeg n u - q : ℕ) : ℤ);
    -padicValRat p (content n) ≤
      2*(sixRowPenalty (fiveRank n) p q : ℤ) +
        ∑ j ∈ Finset.Icc 1 18, (min (fiveRank n)
          (Finset.univ.filter (fun u => (j : ℤ) ≤ inc u)).card : ℤ) := by
  intro inc
  have hp := (Fact.out : p.Prime).pos
  have h2h : 2*fiveRank n < p^2 := by unfold fiveRank; omega
  have hformal := unfolded_formalValAtLeast (p := p) h2h
    (slotCenter n) (slotDeg n) (slotWeightMatrix n p) (slotCost n p)
    (fun u => (slotCost_le_16 n p hn hsq u).trans (by decide))
    (slotWeightMatrix_doubled_bound n p hn hsq) q
  rw [← Hpoly_eq_evalJet_mul_weight n p hn hp] at hformal
  have hnonpos : -(2*(sixRowPenalty (fiveRank n) p q : ℤ) +
      ∑ j ∈ Finset.Icc 1 18, (min (fiveRank n)
        (Finset.univ.filter (fun u => (j : ℤ) ≤ inc u)).card : ℤ)) ≤ 0 := by
    apply neg_nonpos.mpr
    exact add_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => by positivity))
  have hge := content_padicValRat_ge_of_formal_nonpos n p _ hnonpos hformal
  linarith

/-- Exact periodic-envelope sum on the true content, for any dominating folded class costs. -/
theorem content_folded_periodic (n p : ℕ) [Fact p.Prime]
    (hn : 0<n) (hsq : 84*n < p^2) (B : Fin (p/2+1) → ℕ)
    (hB_dom : ∀ u, slotCost n p u ≤ B (foldMod p (Fact.out : p.Prime).pos (slotCenter n u)))
    (hB16 : ∀ c, B c ≤ 16) :
    -padicValRat p (content n) ≤ ∑ c : Fin (p/2+1), (slotEnvelope (2*fiveRank n/p) (B c) : ℤ) := by
  have hp := (Fact.out : p.Prime).pos
  have h2h : 2*fiveRank n < p^2 := by unfold fiveRank; omega
  have hformal := folded_periodic_exact_formalValAtLeast (p := p) h2h
    (slotCenter n) (slotDeg n) (slotWeightMatrix n p) (slotCost n p) B
    hB_dom hB16 (slotWeightMatrix_doubled_bound n p hn hsq)
  rw [← Hpoly_eq_evalJet_mul_weight n p hn hp] at hformal
  have hnonpos :
      -(∑ c : Fin (p/2+1), (slotEnvelope (2*fiveRank n/p) (B c) : ℤ)) ≤ 0 := by
    apply neg_nonpos.mpr
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hge := content_padicValRat_ge_of_formal_nonpos n p _ hnonpos hformal
  linarith

private theorem residueCount_mod (p : ℕ) (a b c d : ℤ) (h : (p : ℤ) ∣ c-d) :
    residueCount p a b c = residueCount p a b d := by
  unfold residueCount
  congr 1
  ext k
  rw [mem_filter,mem_filter]
  apply and_congr_right
  intro _
  constructor
  · intro hk
    have hh := dvd_add hk h
    rwa [show k-c+(c-d)=k-d by ring] at hh
  · intro hk
    have hh := dvd_sub hk h
    rwa [show k-d-(c-d)=k-c by ring] at hh

private theorem residueCount_reflect (p : ℕ) (a b c : ℤ) :
    residueCount p a b (-c) = residueCount p (-b) (-a) c := by
  unfold residueCount
  apply Finset.card_bij (fun j _ => -j)
  · intro j hj
    have h := mem_filter.mp hj
    have hI := mem_Icc.mp h.1
    exact mem_filter.mpr ⟨mem_Icc.mpr (by omega),
      by have hh := Int.dvd_neg.mpr h.2; rwa [show -(j-(-c))=-j-c by ring] at hh⟩
  · intro j _ k _ h
    omega
  · intro j hj
    have h := mem_filter.mp hj
    have hI := mem_Icc.mp h.1
    refine ⟨-j,mem_filter.mpr ⟨mem_Icc.mpr (by omega),?_⟩,by omega⟩
    have hh := Int.dvd_neg.mpr h.2
    rwa [show -(j-c)=-j-(-c) by ring] at hh

theorem finitePeriodicRaw_neg (n p : ℕ) (c : ℤ) :
    finitePeriodicRaw n p (-c) = finitePeriodicRaw n p c := by
  unfold finitePeriodicRaw
  simp only [residueCount_reflect]
  have h1 : -(25*(n:ℤ))=-25*n := by ring
  have h2 : -(17*(n:ℤ))=-17*n := by ring
  have h3 : -(16*(n:ℤ))=-16*n := by ring
  have h4 : -(-34*(n:ℤ)-1)=34*n+1 := by ring
  have h5 : -(59*(n:ℤ))=-59*n := by ring
  have h6 : -(34*(n:ℤ)+1)=-34*n-1 := by ring
  simp only [h1,h2,h3,h4,h5,h6]
  have h7 (a : ℤ) : -(-a*(n:ℤ))=a*n := by ring
  simp only [h7]
  ring

theorem finitePeriodicRaw_foldMod (n p : ℕ) (hp : 0<p) (c : ℤ) :
    finitePeriodicRaw n p c = finitePeriodicRaw n p (foldMod p hp c).val := by
  have hd := foldMod_congruence p hp c
  have hmod : finitePeriodicRaw n p (foldSign p c*c) =
      finitePeriodicRaw n p (foldMod p hp c).val := by
    unfold finitePeriodicRaw
    simp only [residueCount_mod p _ _ _ _ hd]
  unfold foldSign at hmod
  split_ifs at hmod
  · simpa using hmod
  · simpa [finitePeriodicRaw_neg] using hmod

/-- The first-layer periodic bound, expressed using the explicit centered
residue counts, with all closed-endpoint corrections retained. -/
theorem content_finite_periodic (n p : ℕ) [Fact p.Prime]
    (hn : 0<n) (hsq : 84*n < p^2) :
    -padicValRat p (content n) ≤ ∑ c : Fin (p/2+1),
      (slotEnvelope (2*fiveRank n/p) (finitePeriodicRaw n p c.val).toNat : ℤ) := by
  have hp := (Fact.out : p.Prime).pos
  apply content_folded_periodic n p hn hsq
  · intro u
    have h := refinedSlotCost_le_finitePeriodic n p hn hsq
      (halfPole n ((slotEquiv n).symm u).1) (slotDeg n u)
    have he : (halfPole n ((slotEquiv n).symm u).1 : ℤ)-center n = -(slotCenter n u) := by
      simp [halfPole,slotCenter]
    rw [he,finitePeriodicRaw_neg,finitePeriodicRaw_foldMod n p hp] at h
    exact h
  · intro c
    exact Int.toNat_le_toNat (finitePeriodicRaw_le_16 n p hn hp c.val)

end OddZetaSix.B40a
