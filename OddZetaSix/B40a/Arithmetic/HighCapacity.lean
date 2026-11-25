import OddZetaSix.B40a.Arithmetic.HighSingular

/-! Singular-column truncation for the true symbolic B40a determinant. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset
open scoped BigOperators

abbrev HighColumn (n : ℕ) := Fin (fiveRank n) ⊕ ({k // k ∈ kernelPoleSet n} × Fin 12)

def highY (n : ℕ) : Matrix (Fin (fiveRank n)) (HighColumn n) ℚ :=
  fun i u => match u with
  | Sum.inl j => if i=j then 1 else 0
  | Sum.inr (k,a) => highJet n k.val i a

def highW (n p : ℕ) : Matrix (HighColumn n) (HighColumn n) FivePolynomial :=
  fun u v => match u,v with
  | Sum.inl i, Sum.inl j => regularHighFormal n p i j
  | Sum.inr (k,a), Sum.inr (l,b) =>
    if k=l then MvPolynomial.C (highSiteWeight n p k.val a.val b.val) else 0
  | _,_ => 0

def highColumnCapacity (n p : ℕ) (u : HighColumn n) : ℕ := match u with
  | Sum.inl _ => 0
  | Sum.inr (k,a) => highSiteCapacity n p k.val a.val

theorem Hpow_high_factorization (n p : ℕ) (hp : 0 < p) :
    Hpow n = (highY n).map MvPolynomial.C * highW n p * ((highY n).map MvPolynomial.C).transpose := by
  apply Matrix.ext
  intro i j
  rw [Hpow_formal_high_split n p hp,Matrix.mul_assoc]
  simp only [Matrix.mul_apply,Matrix.map_apply,Matrix.transpose_apply]
  rw [Fintype.sum_sum_type]
  have hreg : (∑ a : Fin (fiveRank n), MvPolynomial.C (highY n i (Sum.inl a)) *
      ∑ x : HighColumn n, highW n p (Sum.inl a) x * MvPolynomial.C (highY n j x)) =
        regularHighFormal n p i j := by
    simp only [Fintype.sum_sum_type, highY,highW,zero_mul,Finset.sum_const_zero,add_zero,
      apply_ite,map_one,map_zero,ite_mul,one_mul,mul_one,mul_zero]
    simp
  rw [hreg]
  congr 1
  symm
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, highY,highW,zero_mul,
    Finset.sum_const_zero,zero_add]
  have hs (k : {k // k ∈ kernelPoleSet n}) (a : Fin 12) :
      (∑ l : {k // k ∈ kernelPoleSet n}, ∑ b : Fin 12,
        (if k=l then (MvPolynomial.C (highSiteWeight n p k.val a.val b.val) : FivePolynomial) else 0) *
          MvPolynomial.C (highJet n l.val j b)) =
        ∑ b : Fin 12, (MvPolynomial.C (highSiteWeight n p k.val a.val b.val) : FivePolynomial) *
          MvPolynomial.C (highJet n k.val j b) := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ h
      simp [Ne.symm h]
    · simp
  simp_rw [hs]
  simp only [Finset.mul_sum, ← map_mul, ← map_sum]
  congr 1
  simp only [singularHigh, ← kernelPoleSet_eq_poleList, ← Finset.sum_neg_distrib]
  rw [← Finset.sum_attach (kernelPoleSet n)]
  have hs' (k : {k // k ∈ kernelPoleSet n}) :
      (∑ a : Fin 12, ∑ b : Fin 12,
        highJet n k.val i a * (highSiteWeight n p k.val a.val b.val * highJet n k.val j b)) =
      -(∑ ℓ ∈ Icc 1 (poleOrder n k.val),
        ((ℓ+3).choose 4 : ℚ)*localPrincipal n k.val ℓ (X^(2*i.val)) (X^(2*j.val))*
          harmonicSingular p (ℓ+4) (k.val-25*n-1)) := by
    simpa only [mul_assoc] using (high_singular_site_eq n p k.val i j k.property).symm
  simp_rw [hs']
  have hu : (univ : Finset {k // k ∈ kernelPoleSet n}) = (kernelPoleSet n).attach := by
    ext x
    simp
  simp only [hu,← Finset.sum_neg_distrib]

theorem highY_integral (n p : ℕ) [Fact p.Prime] (i : Fin (fiveRank n)) (u : HighColumn n) :
    ValAtLeast p 0 (highY n i u) := by
  cases u with
  | inl j =>
    change ValAtLeast p 0 (if i=j then (1 : ℚ) else 0)
    split_ifs
    · exact valAtLeast_one p
    · exact valAtLeast_zero p 0
  | inr t =>
    exact Or.inr ((sixGateIntegralRing_mem_iff p _).mp (highJet_integral n p t.1.val i t.2))

theorem highW_weight (n p : ℕ) [Fact p.Prime] (hp : 50*n < p) (u v : HighColumn n) :
    DoubledFormalValAtLeast p (-((highColumnCapacity n p u+highColumnCapacity n p v : ℕ) : ℤ))
      (highW n p u v) := by
  cases u with
  | inl i =>
    cases v with
    | inl j =>
      simpa [highW,highColumnCapacity] using
        doubledFormalValAtLeast_of_formal (regularHighFormal_integral n p hp i j)
    | inr v => exact doubledFormalValAtLeast_zero p _
  | inr u =>
    cases v with
    | inl j => exact doubledFormalValAtLeast_zero p _
    | inr v =>
      rcases u with ⟨k,a⟩
      rcases v with ⟨l,b⟩
      by_cases h : k=l
      · subst l
        intro s
        simp only [highColumnCapacity,highW,ite_true,MvPolynomial.coeff_C]
        split_ifs
        · exact high_site_weight_bound n p k.val a.val b.val hp k.property
        · exact doubledValAtLeast_zero p _
      · simpa only [highW,ite_eq_right h] using
          doubledFormalValAtLeast_zero p
            (-((highColumnCapacity n p (Sum.inr (k,a))+highColumnCapacity n p (Sum.inr (l,b)) : ℕ) : ℤ))

def highLayerCost (n p : ℕ) : ℤ :=
  ∑ s ∈ Icc (1 : ℤ) 18, (min (fiveRank n)
    ((univ : Finset (HighColumn n)).filter (fun u => s ≤ (highColumnCapacity n p u : ℤ))).card : ℤ)

private theorem rat_det_integral {h p : ℕ} [Fact p.Prime] (A : Matrix (Fin h) (Fin h) ℚ)
    (hA : ∀ i j, ValAtLeast p 0 (A i j)) : ValAtLeast p 0 A.det := by
  rw [Matrix.det_apply']
  apply valAtLeast_sum
  intro σ _
  apply valAtLeast_mono
    (valAtLeast_mul (valAtLeast_intCast p _) (valAtLeast_prod _ _ _ (fun i _ => hA (σ i) i)))
  simp

theorem Hpow_high_capacity_bound (n p : ℕ) [Fact p.Prime] (hp : 50*n < p) :
    FormalValAtLeast p (-highLayerCost n p) (Hpow n).det := by
  let m := Fintype.card (HighColumn n)
  let e : Fin m ≃ HighColumn n := (Fintype.equivFin _).symm
  let Y : Matrix (Fin (fiveRank n)) (Fin m) ℚ := (highY n).submatrix id e
  let W : Matrix (Fin m) (Fin m) FivePolynomial := (highW n p).submatrix e e
  let B : Fin m → ℕ := fun u => highColumnCapacity n p (e u)
  have hrep : Hpow n = Y.map MvPolynomial.C * W * (Y.map MvPolynomial.C).transpose := by
    rw [Hpow_high_factorization n p (Fact.out : p.Prime).pos,Matrix.mul_assoc,Matrix.mul_assoc]
    apply Matrix.ext
    intro i j
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.map_apply,Matrix.submatrix_apply,Y,W,id_eq]
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro a _
    rw [← e.sum_comp]
  have hW (u v : Fin m) :
      DoubledFormalValAtLeast p (-((B u+B v : ℕ) : ℤ)) (W u v) :=
    highW_weight n p hp (e u) (e v)
  have hB (u : Fin m) : B u ≤ 18 := by
    simp only [B]
    cases e u with
    | inl j => simp [highColumnCapacity]
    | inr ka =>
      have hk := kernel_pole_order_le n ka.1.val
      rw [kernelPoleOrder_eq_poleOrder] at hk
      simp only [highColumnCapacity,highSiteCapacity]
      split_ifs <;> omega
  have hcap (I : Finset (Fin m)) (hI : I.card = fiveRank n) :
      (∑ u ∈ I, (B u : ℤ)) ≤ highLayerCost n p := by
    have hh := sum_subset_le_layer_cap (univ : Finset (Fin m)) I (subset_univ I)
      (fiveRank n) hI.le (fun u => (B u : ℤ)) (fun u _ => by exact_mod_cast hB u)
    refine hh.trans_eq ?_
    unfold highLayerCost
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    apply Finset.card_bij (fun u _ => e u)
    · intro u h
      have hh := (mem_filter.mp h).2
      exact mem_filter.mpr ⟨mem_univ _,hh⟩
    · intro u _ v _ h
      exact e.injective h
    · intro v hv
      refine ⟨e.symm v,mem_filter.mpr ⟨mem_univ _,?_⟩,e.apply_symm_apply _⟩
      have hh := (mem_filter.mp hv).2
      simpa [B] using hh
  rw [hrep]
  apply doubled_cauchy_binet_formalValAtLeast Y W B _ hW
  intro I hI hne
  have hi := rat_det_integral (p := p) (Y.submatrix id (subsetEmb I hI))
    (fun i j => highY_integral n p i (e (subsetEmb I hI j)))
  have hv := valAtLeast_of_ne_zero hi hne
  linarith only [hv,hcap I hI]

theorem content_high_capacity_bound (n p : ℕ) [Fact p.Prime] (hp : 50*n < p) :
    -padicValRat p (content n) ≤
      highLayerCost n p + 2*((40*n-(p+1)/2 : ℕ) : ℤ) := by
  let L := highLayerCost n p
  let v : ℤ := -2*((40*n-(p+1)/2 : ℕ) : ℤ)
  have hv : ValAtLeast p v (basisFactor n) := Or.inr (high_basis_factor_valuation n p hp).ge
  have hd : FormalValAtLeast p (v-L) (Hpoly n).det := by
    rw [Hpoly_det_basis_change,sub_eq_add_neg]
    exact formalValAtLeast_C_mul hv (Hpow_high_capacity_bound n p hp)
  have hL : 0 ≤ L := by
    unfold L highLayerCost
    apply Finset.sum_nonneg
    intro s _
    positivity
  have hv0 : v ≤ 0 := by
    unfold v
    exact mul_nonpos_of_nonpos_of_nonneg (by decide) (Int.natCast_nonneg _)
  have hh := content_padicValRat_ge_of_formal_nonpos n p _ (sub_nonpos.mpr (hv0.trans hL)) hd
  dsimp [v,L] at hh
  linarith

end OddZetaSix.B40a
