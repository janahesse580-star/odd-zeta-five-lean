import OddZetaSix.B40a.Arithmetic.HighBand
import OddZetaSix.B40a.Arithmetic.FoldedCapacity

/-! Local Taylor weights of the actual singular terms at every prime p > 50n. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset
open scoped BigOperators

def highUnitSeries (n k : ℕ) : ℚ[X] :=
  truncatedQuotient (taylor (-(k : ℚ)) (C (normalization n) * numerator n))
    (taylor (-(k : ℚ)) (regularDenominator n k)) (poleOrder n k)

theorem highUnitSeries_mem (n p k : ℕ) [Fact p.Prime] (hp : 50*n < p)
    (hk : k ∈ kernelPoleSet n) :
    PolyInSubring (sixGateIntegralRing p) (highUnitSeries n k) := by
  let S := sixGateIntegralRing p
  unfold highUnitSeries
  apply truncatedQuotient_in_subring
  · apply polyInSubring_taylor _ (S.neg_mem (natCast_mem S k))
    exact polyInSubring_mul (polyInSubring_C (normalization_integral n p hp))
      (numerator_integral n S)
  · exact cofactor_integral n p k hk
  · exact cofactor_inv_coeff_mem n p k hp hk

theorem high_principal_eq_jet_coeff (n k ℓ : ℕ) (f g : ℚ[X])
    (hk : k ∈ kernelPoleSet n) (hℓ : 1 ≤ ℓ ∧ ℓ ≤ poleOrder n k) :
    localPrincipal n k ℓ f g =
      (highUnitSeries n k *
        (taylor ((center n : ℚ)-k) f * taylor ((center n : ℚ)-k) g)).coeff (poleOrder n k-ℓ) := by
  let A := taylor (-(k : ℚ)) (C (normalization n) * numerator n)
  let D := taylor (-(k : ℚ)) (regularDenominator n k)
  let J := taylor ((center n : ℚ)-k) f * taylor ((center n : ℚ)-k) g
  have hD : D.coeff 0 ≠ 0 := by
    dsimp [D]
    rw [regularDenominator_eq_erase n k hk]
    exact kernelLocalCofactor_ne_zero_coeff n k
  have hj : taylor (-(k : ℚ)) ((f*g).comp (X+C (center n : ℚ))) = J := by
    simp only [J, taylor_apply,comp_assoc,add_comp,X_comp,C_comp,mul_comp]
    congr 1 <;> congr 1 <;> rw [add_assoc,← C_add] <;> congr 2 <;> ring
  unfold localPrincipal
  rw [taylor_mul,hj]
  change localQuotient (A*J) D (poleOrder n k-ℓ) = _
  apply localQuotient_eq_coeff_of_congruence _ _ _ hD (poleOrder n k)
  · have h := truncatedQuotient_dvd A D hD (poleOrder n k)
    change X^poleOrder n k ∣ A - D * highUnitSeries n k at h
    change X^poleOrder n k ∣ A*J-D*(highUnitSeries n k*J)
    rw [show A*J-D*(highUnitSeries n k*J) = (A-D*highUnitSeries n k)*J by ring]
    exact dvd_mul_of_dvd_left h J
  · omega

def highSiteWeight (n p k a b : ℕ) : ℚ :=
  if p ≤ k-25*n-1 then
    -(∑ ℓ ∈ Icc 1 (poleOrder n k-(a+b)),
      ((ℓ+3).choose 4 : ℚ) * (highUnitSeries n k).coeff (poleOrder n k-ℓ-(a+b)) *
        (1/(p : ℚ)^(ℓ+4)))
  else 0

def highSiteCapacity (n p k a : ℕ) : ℕ :=
  if p ≤ k-25*n-1 ∧ a < poleOrder n k then poleOrder n k+4-2*a else 0

theorem high_site_weight_bound (n p k a b : ℕ) [Fact p.Prime] (hp : 50*n < p)
    (hk : k ∈ kernelPoleSet n) :
    DoubledValAtLeast p (-(highSiteCapacity n p k a + highSiteCapacity n p k b : ℕ)) 
      (highSiteWeight n p k a b) := by
  unfold highSiteWeight
  split_ifs with hsing
  · apply doubledValAtLeast_neg
    apply doubledValAtLeast_sum
    intro ℓ hℓ
    have hℓ' := mem_Icc.mp hℓ
    have hval : ValAtLeast p (-((ℓ+4 : ℕ) : ℤ)) (1/(p : ℚ)^(ℓ+4)) := by
      right
      rw [one_div,padicValRat.inv,padicValRat.pow,padicValRat.self (Fact.out : p.Prime).one_lt,mul_one]
    have hm0 := highUnitSeries_mem n p k hp hk (poleOrder n k-ℓ-(a+b))
    have hm1 : ValAtLeast p 0 ((highUnitSeries n k).coeff (poleOrder n k-ℓ-(a+b))) :=
      Or.inr ((sixGateIntegralRing_mem_iff p _).mp hm0)
    have hx := doubledValAtLeast_of_valAtLeast (valAtLeast_mul
      (valAtLeast_mul (valAtLeast_natCast p ((ℓ+3).choose 4)) hm1) hval)
    apply doubledValAtLeast_mono hx
    have ha : a < poleOrder n k := by omega
    have hb : b < poleOrder n k := by omega
    simp only [highSiteCapacity,hsing,ha,hb,and_self,ite_true]
    omega
  · exact doubledValAtLeast_zero p _

theorem coeff_mul3_fin12 (U f g : ℚ[X]) (d : ℕ) (hd : d<12) :
    (U*(f*g)).coeff d = ∑ a : Fin 12, ∑ b : Fin 12,
      if a.val+b.val ≤ d then U.coeff (d-a.val-b.val) * f.coeff a.val * g.coeff b.val else 0 := by
  rw [show U*(f*g) = f*(g*U) by ring,coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => f.coeff a*(g*U).coeff b)]
  let F : ℕ → ℕ → ℚ := fun a b =>
    if a+b ≤ d then U.coeff (d-a-b) * f.coeff a * g.coeff b else 0
  change _ = ∑ a : Fin 12, ∑ b : Fin 12, F a.val b.val
  have hs : (∑ a : Fin 12, ∑ b : Fin 12, F a.val b.val) = ∑ a ∈ range 12, ∑ b ∈ range 12, F a b := by
    calc
      _ = ∑ a : Fin 12, ∑ b ∈ range 12, F a.val b := by
        apply Finset.sum_congr rfl
        intro a _
        exact Fin.sum_univ_eq_sum_range (F a.val) 12
      _ = _ := Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range 12, F a b) 12
  rw [hs]
  dsimp only [F]
  symm
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : d+1 ≤ 12))]
  · apply Finset.sum_congr rfl
    intro a ha
    have ha' := mem_range.mp ha
    rw [coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun b c => g.coeff b*U.coeff c),
      Finset.mul_sum]
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : d-a+1 ≤ 12))]
    · apply Finset.sum_congr rfl
      intro b hb
      have hh := mem_range.mp hb
      rw [ite_eq_left (by omega)]
      ring
    · intro b hb hn
      have hh : ¬ a+b ≤ d := by
        intro h
        exact hn (mem_range.mpr (by omega))
      simp [hh]
  · intro a ha hn
    apply Finset.sum_eq_zero
    intro b _
    have hh : ¬ a+b ≤ d := by
      intro h
      exact hn (mem_range.mpr (by omega))
    simp [hh]

def highJet (n k : ℕ) (i : Fin (fiveRank n)) (a : Fin 12) : ℚ :=
  (taylor ((center n : ℚ)-k) (X^(2*i.val))).coeff a.val

theorem highJet_integral (n p k : ℕ) [Fact p.Prime] (i : Fin (fiveRank n)) (a : Fin 12) :
    highJet n k i a ∈ sixGateIntegralRing p := by
  let S := sixGateIntegralRing p
  unfold highJet
  apply (polyInSubring_taylor (polyInSubring_pow polyInSubring_X _)
    (S.sub_mem (natCast_mem S _) (natCast_mem S _))) _

theorem high_singular_site_eq (n p k : ℕ) (i j : Fin (fiveRank n)) (hk : k ∈ kernelPoleSet n) :
    -(∑ ℓ ∈ Icc 1 (poleOrder n k),
      ((ℓ+3).choose 4 : ℚ)*localPrincipal n k ℓ (X^(2*i.val)) (X^(2*j.val))*
        harmonicSingular p (ℓ+4) (k-25*n-1)) =
    ∑ a : Fin 12, ∑ b : Fin 12, highJet n k i a * highSiteWeight n p k a.val b.val * highJet n k j b := by
  let U := highUnitSeries n k
  let f := taylor ((center n : ℚ)-k) (X^(2*i.val))
  let g := taylor ((center n : ℚ)-k) (X^(2*j.val))
  let m := poleOrder n k
  have h12 : m ≤ 12 := by
    change poleOrder n k ≤ 12
    rw [← kernelPoleOrder_eq_poleOrder]
    exact kernel_pole_order_le n k
  unfold harmonicSingular highSiteWeight
  by_cases hsing : p ≤ k-25*n-1
  · simp only [hsing,ite_true,Finset.sum_neg_distrib, mul_neg, neg_mul]
    apply congrArg (fun x : ℚ => -x)
    let c : ℕ → Fin 12 → Fin 12 → ℚ := fun ℓ a b =>
      if a.val+b.val ≤ m-ℓ then
        ((ℓ+3).choose 4 : ℚ) * U.coeff (m-ℓ-a.val-b.val) * f.coeff a.val * g.coeff b.val *
          (1/(p : ℚ)^(ℓ+4)) else 0
    calc
      _ = ∑ ℓ ∈ Icc 1 m, ∑ a : Fin 12, ∑ b : Fin 12, c ℓ a b := by
        apply Finset.sum_congr rfl
        intro ℓ hℓ
        have hℓ' := mem_Icc.mp hℓ
        rw [high_principal_eq_jet_coeff n k ℓ _ _ hk hℓ']
        change ((ℓ+3).choose 4 : ℚ)*(U*(f*g)).coeff (m-ℓ)*_ = _
        rw [coeff_mul3_fin12 U f g (m-ℓ) (by omega), Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        dsimp [c]
        split_ifs <;> ring
      _ = ∑ a : Fin 12, ∑ b : Fin 12, ∑ ℓ ∈ Icc 1 m, c ℓ a b := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        change _ = f.coeff a.val * _ * g.coeff b.val
        rw [Finset.mul_sum,Finset.sum_mul]
        have hs : Icc 1 (m-(a.val+b.val)) ⊆ Icc 1 m := by
          intro ℓ hℓ
          have hh := mem_Icc.mp hℓ
          exact mem_Icc.mpr ⟨hh.1,by omega⟩
        rw [← Finset.sum_subset hs]
        · apply Finset.sum_congr rfl
          intro ℓ hℓ
          have hh := mem_Icc.mp hℓ
          simp only [c,ite_eq_left (by omega : a.val+b.val ≤ m-ℓ)]
          rw [show m-ℓ-a.val-b.val = m-ℓ-(a.val+b.val) by omega]
          ring
        · intro ℓ hℓ hnot
          have hh := mem_Icc.mp hℓ
          have hlt : ¬ a.val+b.val ≤ m-ℓ := by
            intro h
            exact hnot (mem_Icc.mpr ⟨hh.1,by omega⟩)
          simp [c,hlt]
  · simp [hsing]

end OddZetaSix.B40a
