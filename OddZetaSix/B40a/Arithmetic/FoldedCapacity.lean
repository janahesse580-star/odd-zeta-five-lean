import OddZetaSix.B40a.Arithmetic.Valuation
import OddZetaSix.SixFolded

/-! The folded and unfolded determinant capacity lemmas for five-variable
polynomials. The matrix estimates and the sorting by valuation layers use the
MIT-licensed upstream SixFolded development. -/
noncomputable section
namespace OddZetaSix.B40a
open Finset Polynomial
open scoped BigOperators

/-- Coefficientwise doubled Gauss valuation floor on `FivePolynomial`. -/
def DoubledFormalValAtLeast (p : ℕ) (a : ℤ) (F : FivePolynomial) : Prop :=
  ∀ m : Fin 5 →₀ ℕ, DoubledValAtLeast p a (F.coeff m)

theorem doubledFormalValAtLeast_zero (p : ℕ) (a : ℤ) : DoubledFormalValAtLeast p a 0 :=
  fun m => by simp [doubledValAtLeast_zero]

theorem doubledFormalValAtLeast_one (p : ℕ) [Fact p.Prime] : DoubledFormalValAtLeast p 0 1 := by
  intro m
  exact doubledValAtLeast_of_valAtLeast (formalValAtLeast_one p m)

theorem doubledFormalValAtLeast_mono {p : ℕ} {a b : ℤ} {F : FivePolynomial}
    (h : DoubledFormalValAtLeast p a F) (hab : b ≤ a) : DoubledFormalValAtLeast p b F :=
  fun m => doubledValAtLeast_mono (h m) hab

theorem doubledFormalValAtLeast_neg {p : ℕ} {a : ℤ} {F : FivePolynomial}
    (h : DoubledFormalValAtLeast p a F) : DoubledFormalValAtLeast p a (-F) := by
  intro m; rw [MvPolynomial.coeff_neg]; exact doubledValAtLeast_neg (h m)

theorem doubledFormalValAtLeast_add {p : ℕ} [Fact p.Prime] {a : ℤ} {F G : FivePolynomial}
    (hF : DoubledFormalValAtLeast p a F) (hG : DoubledFormalValAtLeast p a G) :
    DoubledFormalValAtLeast p a (F + G) := by
  intro m
  have h : (F + G).coeff m = F.coeff m + G.coeff m := by simp
  rw [h]
  exact doubledValAtLeast_add (hF m) (hG m)

theorem doubledFormalValAtLeast_mul {p : ℕ} [Fact p.Prime] {a b : ℤ} {F G : FivePolynomial}
    (hF : DoubledFormalValAtLeast p a F) (hG : DoubledFormalValAtLeast p b G) :
    DoubledFormalValAtLeast p (a + b) (F * G) := by
  intro m
  rw [MvPolynomial.coeff_mul]
  exact doubledValAtLeast_sum _ _ _ (fun x _ => doubledValAtLeast_mul (hF x.1) (hG x.2))

theorem doubledFormalValAtLeast_C_mul {p : ℕ} [Fact p.Prime] {a b : ℤ} {c : ℚ}
    {F : FivePolynomial} (hc : DoubledValAtLeast p a c) (hF : DoubledFormalValAtLeast p b F) :
    DoubledFormalValAtLeast p (a + b) (MvPolynomial.C c * F) := by
  intro m
  rw [MvPolynomial.coeff_C_mul]
  exact doubledValAtLeast_mul hc (hF m)

theorem doubledFormalValAtLeast_sum {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → FivePolynomial) (a : ℤ) (hf : ∀ i ∈ s, DoubledFormalValAtLeast p a (f i)) :
    DoubledFormalValAtLeast p a (∑ i ∈ s, f i) := by
  intro m
  rw [MvPolynomial.coeff_sum]
  exact doubledValAtLeast_sum s (fun i => (f i).coeff m) a (fun i hi => hf i hi m)

theorem doubledFormalValAtLeast_prod {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → FivePolynomial) (a : ι → ℤ) (hf : ∀ i ∈ s, DoubledFormalValAtLeast p (a i) (f i)) :
    DoubledFormalValAtLeast p (∑ i ∈ s, a i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using doubledFormalValAtLeast_one p
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact doubledFormalValAtLeast_mul (hf i (mem_insert_self _ _))
      (ih (fun j hj => hf j (mem_insert_of_mem hj)))

theorem formalValAtLeast_of_doubled_two_mul {p : ℕ} {a : ℤ} {F : FivePolynomial}
    (h : DoubledFormalValAtLeast p (2 * a) F) : FormalValAtLeast p a F :=
  fun m => valAtLeast_of_doubled_two_mul (h m)

theorem doubledFormalValAtLeast_of_formal {p : ℕ} {a : ℤ} {F : FivePolynomial}
    (h : FormalValAtLeast p a F) : DoubledFormalValAtLeast p (2 * a) F :=
  fun m => doubledValAtLeast_of_valAtLeast (h m)

theorem doubled_cauchy_binet_formalValAtLeast {p h m : ℕ} [Fact p.Prime]
    (Y : Matrix (Fin h) (Fin m) ℚ)
    (W : Matrix (Fin m) (Fin m) FivePolynomial)
    (B : Fin m → ℕ) (U : ℤ)
    (hW : ∀ u v : Fin m, DoubledFormalValAtLeast p (-((B u + B v : ℕ) : ℤ)) (W u v))
    (hY : ∀ (I : Finset (Fin m)) (hI : I.card = h),
      (Y.submatrix id (subsetEmb I hI)).det ≠ 0 →
      -U ≤ 2 * padicValRat p (Y.submatrix id (subsetEmb I hI)).det -
        ∑ u ∈ I, (B u : ℤ)) :
    FormalValAtLeast p (-U)
      (Y.map MvPolynomial.C * W * (Y.map MvPolynomial.C).transpose).det := by
  apply formalValAtLeast_of_doubled_two_mul
  have hexp : (Y.map MvPolynomial.C * W * (Y.map MvPolynomial.C).transpose).det =
      ∑ I ∈ ((Finset.univ : Finset (Fin m)).powersetCard h).attach,
        ∑ J ∈ ((Finset.univ : Finset (Fin m)).powersetCard h).attach,
          MvPolynomial.C
            ((Y.submatrix id (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2)).det *
             (Y.submatrix id (subsetEmb J.1 (Finset.mem_powersetCard.mp J.2).2)).det) *
          (W.submatrix (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2)
            (subsetEmb J.1 (Finset.mem_powersetCard.mp J.2).2)).det := by
    rw [Matrix.mul_assoc, cauchy_binet_det_mul]
    apply Finset.sum_congr rfl; intro I _
    have hright : ((W * (Y.map MvPolynomial.C).transpose).submatrix
        (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2) id).det =
        ∑ J ∈ ((Finset.univ : Finset (Fin m)).powersetCard h).attach,
          (W.submatrix (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2)
            (subsetEmb J.1 (Finset.mem_powersetCard.mp J.2).2)).det *
          ((Y.map MvPolynomial.C).submatrix id
            (subsetEmb J.1 (Finset.mem_powersetCard.mp J.2).2)).det := by
      have hsub : (W * (Y.map MvPolynomial.C).transpose).submatrix
          (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2) id =
          W.submatrix (subsetEmb I.1 (Finset.mem_powersetCard.mp I.2).2) id *
            (Y.map MvPolynomial.C).transpose := by
        ext i j; rfl
      rw [hsub, cauchy_binet_det_mul]
      apply Finset.sum_congr rfl; intro J _
      congr 1
      rw [← Matrix.det_transpose]
      congr 1
    rw [hright, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro J _
    have hYC : ∀ K : {x // x ∈ (Finset.univ : Finset (Fin m)).powersetCard h},
        ((Y.map (MvPolynomial.C : ℚ →+* FivePolynomial)).submatrix id
          (subsetEmb K.1 (Finset.mem_powersetCard.mp K.2).2)).det =
        (MvPolynomial.C : ℚ →+* FivePolynomial) (Y.submatrix id
          (subsetEmb K.1 (Finset.mem_powersetCard.mp K.2).2)).det := by
      intro K
      have hmap : (Y.map (MvPolynomial.C : ℚ →+* FivePolynomial)).submatrix id
          (subsetEmb K.1 (Finset.mem_powersetCard.mp K.2).2) =
          (MvPolynomial.C : ℚ →+* FivePolynomial).mapMatrix
            (Y.submatrix id (subsetEmb K.1 (Finset.mem_powersetCard.mp K.2).2)) := by
        ext i j; rfl
      rw [hmap, ← RingHom.map_det]
    rw [hYC I, hYC J, map_mul]
    ring
  rw [hexp]
  apply doubledFormalValAtLeast_sum; intro I _
  apply doubledFormalValAtLeast_sum; intro J _
  have hIcard : I.1.card = h := (Finset.mem_powersetCard.mp I.2).2
  have hJcard : J.1.card = h := (Finset.mem_powersetCard.mp J.2).2
  let dI := (Y.submatrix id (subsetEmb I.1 hIcard)).det
  let dJ := (Y.submatrix id (subsetEmb J.1 hJcard)).det
  by_cases hdI : dI = 0
  · simp [dI, hdI, doubledFormalValAtLeast_zero]
  by_cases hdJ : dJ = 0
  · simp [dJ, hdJ, doubledFormalValAtLeast_zero]
  have hWsub : DoubledFormalValAtLeast p
      (-(∑ u ∈ I.1, (B u : ℤ)) - ∑ v ∈ J.1, (B v : ℤ))
      (W.submatrix (subsetEmb I.1 hIcard) (subsetEmb J.1 hJcard)).det := by
    rw [Matrix.det_apply]
    apply doubledFormalValAtLeast_sum; intro σ _
    have hprod := doubledFormalValAtLeast_prod (Finset.univ : Finset (Fin h))
      (fun i => W (subsetEmb I.1 hIcard (σ i)) (subsetEmb J.1 hJcard i))
      (fun i => -((B (subsetEmb I.1 hIcard (σ i)) + B (subsetEmb J.1 hJcard i) : ℕ) : ℤ))
      (fun i _ => hW _ _)
    have hsum_eq : (∑ i : Fin h,
        -((B (subsetEmb I.1 hIcard (σ i)) + B (subsetEmb J.1 hJcard i) : ℕ) : ℤ)) =
        -(∑ u ∈ I.1, (B u : ℤ)) - ∑ v ∈ J.1, (B v : ℤ) := by
      have hI_sum : (∑ i : Fin h, (B (subsetEmb I.1 hIcard (σ i)) : ℤ)) =
          ∑ u ∈ I.1, (B u : ℤ) := by
        rw [Equiv.sum_comp σ (fun i => (B (subsetEmb I.1 hIcard i) : ℤ))]
        have himg : Finset.univ.image (subsetEmb I.1 hIcard) = I.1 := by
          ext u
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
          · intro hu
            have hmem : u ∈ Set.range (subsetEmb I.1 hIcard) := by
              rw [subsetEmb, Finset.range_orderEmbOfFin]; exact hu
            exact hmem
        conv_rhs => rw [← himg]
        rw [Finset.sum_image (fun _ _ _ _ h => (subsetEmb I.1 hIcard).injective h)]
      have hJ_sum : (∑ i : Fin h, (B (subsetEmb J.1 hJcard i) : ℤ)) =
          ∑ v ∈ J.1, (B v : ℤ) := by
        have himg : Finset.univ.image (subsetEmb J.1 hJcard) = J.1 := by
          ext u
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
          · intro hu
            have hmem : u ∈ Set.range (subsetEmb J.1 hJcard) := by
              rw [subsetEmb, Finset.range_orderEmbOfFin]; exact hu
            exact hmem
        conv_rhs => rw [← himg]
        rw [Finset.sum_image (fun _ _ _ _ h => (subsetEmb J.1 hJcard).injective h)]
      push_cast
      simp only [neg_add, Finset.sum_add_distrib, Finset.sum_neg_distrib, hI_sum, hJ_sum]
      ring
    rw [hsum_eq] at hprod
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul]; exact hprod
    · rw [hs, Units.neg_smul, one_smul]; exact doubledFormalValAtLeast_neg hprod
  have hY_I := hY I.1 hIcard hdI
  have hY_J := hY J.1 hJcard hdJ
  have hdIJ : DoubledValAtLeast p (2 * padicValRat p dI + 2 * padicValRat p dJ) (dI * dJ) := by
    right
    rw [padicValRat.mul hdI hdJ]
    ring_nf; exact le_rfl
  have hcomb := doubledFormalValAtLeast_C_mul hdIJ hWsub
  exact doubledFormalValAtLeast_mono hcomb (by linarith)

/-- **Standard Form 1: Folded joint capacity bound (with layer cap `min h`)**. -/
theorem folded_joint_formalValAtLeast {p h m : ℕ} [Fact p.Prime]
    (hsq : 2 * h < p ^ 2)
    (x : Fin m → ℤ) (a : Fin m → ℕ)
    (W : Matrix (Fin m) (Fin m) FivePolynomial)
    (B : Fin m → ℕ) (hB18 : ∀ u : Fin m, B u ≤ 18)
    (hW : ∀ u v : Fin m, DoubledFormalValAtLeast p (-((B u + B v : ℕ) : ℤ)) (W u v))
    (q : ℕ) :
    let hp := (Fact.out : p.Prime).pos
    let clsSet : Fin (p / 2 + 1) → Finset (Fin m) :=
      fun c => Finset.univ.filter (fun u => foldMod p hp (x u) = c)
    let slotPairs : Finset (Fin (p / 2 + 1) × Fin m) :=
      Finset.univ.filter (fun cr => cr.2.val < (clsSet cr.1).card)
    let inc : Fin (p / 2 + 1) × Fin m → ℤ := fun cr =>
      (nthDescWeight (clsSet cr.1) B cr.2.val : ℤ) - 2 * ((cr.2.val - q : ℕ) : ℤ)
    let U : ℤ := 2 * (sixRowPenalty h p q : ℤ) +
      ∑ j ∈ Finset.Icc 1 18, (min h (slotPairs.filter (fun cr => (j : ℤ) ≤ inc cr)).card : ℤ)
    FormalValAtLeast p (-U)
      ((evalJetMatrix p h m x a).map MvPolynomial.C * W *
        ((evalJetMatrix p h m x a).map MvPolynomial.C).transpose).det := by
  intro hp clsSet slotPairs inc U
  apply doubled_cauchy_binet_formalValAtLeast (evalJetMatrix p h m x a) W B U hW
  intro I hI hne
  have hscaled_val := valAtLeast_folded_scaledJetMinor (p := p) (q := q) hsq x a I hI
  have hscaled_ne : ((scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI)).det ≠ 0 := by
    have hsub : (scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI) =
        Matrix.diagonal (fun i : Fin h => (p : ℚ) ^ (2 * i.val / p - q)) *
          (evalJetMatrix p h m x a).submatrix id (subsetEmb I hI) := by
      ext i j; simp [scaledJetMatrix, Matrix.diagonal_mul]
    rw [hsub, Matrix.det_mul, Matrix.det_diagonal]
    have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ hpne)) hne
  have hval_ge := valAtLeast_of_ne_zero hscaled_val hscaled_ne
  rw [padicValRat_scaledJetMinor x a I hI hne] at hval_ge
  let I_c : Fin (p / 2 + 1) → Finset (Fin m) :=
    fun c => I.filter (fun u => foldMod p hp (x u) = c)
  have hI_part : (∑ u ∈ I, (B u : ℤ)) = ∑ c : Fin (p / 2 + 1), ∑ u ∈ I_c c, (B u : ℤ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun u => foldMod p hp (x u))
      (fun _ _ => Finset.mem_univ _)]
  -- Bound each class sum by the sorted prefix of `clsSet c`
  have hB_le : (∑ u ∈ I, (B u : ℤ)) ≤
      ∑ c : Fin (p / 2 + 1), ∑ r ∈ range (I_c c).card,
        (nthDescWeight (clsSet c) B r : ℤ) := by
    rw [hI_part]
    apply Finset.sum_le_sum; intro c _
    have hsub : I_c c ⊆ clsSet c := Finset.filter_subset_filter _ (Finset.subset_univ _)
    exact_mod_cast sum_subset_le_descWeights_prefix (clsSet c) (I_c c) hsub B
  -- Combine into subset `A ⊆ slotPairs` of cardinality `h`
  let A : Finset (Fin (p / 2 + 1) × Fin m) :=
    Finset.univ.filter (fun cr => cr.2.val < (I_c cr.1).card)
  have hAS : A ⊆ slotPairs := by
    intro cr hcr
    rw [Finset.mem_filter] at hcr ⊢
    refine ⟨Finset.mem_univ _, hcr.2.trans_le ?_⟩
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  have hI_c_le : ∀ c : Fin (p / 2 + 1), (I_c c).card ≤ m := fun c =>
    (Finset.card_le_univ _).trans (by simp)
  have hA_card : A.card = h := by
    have hfib : A.card = ∑ c : Fin (p / 2 + 1),
        ((Finset.univ : Finset (Fin m)).filter (fun r => r.val < (I_c c).card)).card := by
      dsimp [A]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro c _
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hcard_c : ∀ c : Fin (p / 2 + 1),
        ((Finset.univ : Finset (Fin m)).filter (fun r => r.val < (I_c c).card)).card = (I_c c).card := by
      intro c
      have himg : ((Finset.univ : Finset (Fin m)).filter (fun r => r.val < (I_c c).card)).image Fin.val =
          range (I_c c).card := by
        ext k
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
        constructor
        · rintro ⟨r, hr, rfl⟩; exact hr
        · intro hk; exact ⟨⟨k, hk.trans_le (hI_c_le c)⟩, hk, rfl⟩
      rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Finset.card_range]
    rw [hfib]
    simp_rw [hcard_c]
    have hpartI : (∑ c : Fin (p / 2 + 1), (I_c c).card) = I.card := by
      simpa only [Finset.card_eq_sum_ones] using
        Finset.sum_fiberwise_of_maps_to (s := I) (t := Finset.univ)
          (g := fun u => foldMod p hp (x u)) (f := fun _ => 1) (fun _ _ => Finset.mem_univ _)
    rw [hpartI, hI]
  have hsum_A : (∑ cr ∈ A, inc cr) =
      ∑ c : Fin (p / 2 + 1), ∑ r ∈ range (I_c c).card,
        ((nthDescWeight (clsSet c) B r : ℤ) - 2 * ((r - q : ℕ) : ℤ)) := by
    dsimp [A, inc]
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro c _
    rw [← Finset.sum_filter]
    apply Finset.sum_bij (fun r _ => r.val)
    · intro r hr; exact mem_range.mpr (Finset.mem_filter.mp hr).2
    · intro r₁ _ r₂ _ h; exact Fin.ext h
    · intro k hk
      have hklt := mem_range.mp hk
      exact ⟨⟨k, hklt.trans_le (hI_c_le c)⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hklt⟩, rfl⟩
    · intro r _; rfl
  have hinc_le : ∀ cr ∈ slotPairs, inc cr ≤ 18 := by
    intro cr _
    dsimp [inc]
    have h18 := nthDescWeight_le_bound (clsSet cr.1) B 18 (fun u _ => hB18 u) cr.2.val
    omega
  have hlayer := sum_subset_le_layer_cap slotPairs A hAS h hA_card.le inc hinc_le
  rw [hsum_A] at hlayer
  have hsub_sum : (∑ c : Fin (p / 2 + 1), ∑ r ∈ range (I_c c).card,
      ((nthDescWeight (clsSet c) B r : ℤ) - 2 * ((r - q : ℕ) : ℤ))) =
      (∑ c : Fin (p / 2 + 1), ∑ r ∈ range (I_c c).card, (nthDescWeight (clsSet c) B r : ℤ)) -
      2 * (∑ c : Fin (p / 2 + 1), ∑ r ∈ range (I_c c).card, ((r - q : ℕ) : ℤ)) := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsub_sum] at hlayer
  dsimp only [U]
  linarith

/-- **Standard Form 2: Unfolded direct capacity bound (with layer cap `min h`)**. -/
theorem unfolded_formalValAtLeast {p h m : ℕ} [Fact p.Prime]
    (hsq : 2 * h < p ^ 2)
    (x : Fin m → ℤ) (a : Fin m → ℕ)
    (W : Matrix (Fin m) (Fin m) FivePolynomial)
    (B : Fin m → ℕ) (hB18 : ∀ u : Fin m, B u ≤ 18)
    (hW : ∀ u v : Fin m, DoubledFormalValAtLeast p (-((B u + B v : ℕ) : ℤ)) (W u v))
    (q : ℕ) :
    let inc : Fin m → ℤ := fun u => (B u : ℤ) - 2 * ((a u - q : ℕ) : ℤ)
    let U : ℤ := 2 * (sixRowPenalty h p q : ℤ) +
      ∑ j ∈ Finset.Icc 1 18,
        (min h ((Finset.univ : Finset (Fin m)).filter (fun u => (j : ℤ) ≤ inc u)).card : ℤ)
    FormalValAtLeast p (-U)
      ((evalJetMatrix p h m x a).map MvPolynomial.C * W *
        ((evalJetMatrix p h m x a).map MvPolynomial.C).transpose).det := by
  intro inc U
  apply doubled_cauchy_binet_formalValAtLeast (evalJetMatrix p h m x a) W B U hW
  intro I hI hne
  have hscaled_val := valAtLeast_unfolded_scaledJetMinor (p := p) (q := q) hsq x a I hI
  have hscaled_ne : ((scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI)).det ≠ 0 := by
    have hsub : (scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI) =
        Matrix.diagonal (fun i : Fin h => (p : ℚ) ^ (2 * i.val / p - q)) *
          (evalJetMatrix p h m x a).submatrix id (subsetEmb I hI) := by
      ext i j; simp [scaledJetMatrix, Matrix.diagonal_mul]
    rw [hsub, Matrix.det_mul, Matrix.det_diagonal]
    have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ hpne)) hne
  have hval_ge := valAtLeast_of_ne_zero hscaled_val hscaled_ne
  rw [padicValRat_scaledJetMinor x a I hI hne] at hval_ge
  have hlayer := sum_subset_le_layer_cap (Finset.univ : Finset (Fin m)) I (Finset.subset_univ I)
    h hI.le inc (fun u _ => by dsimp [inc]; have := hB18 u; omega)
  have hinc_sum : (∑ u ∈ I, inc u) =
      (∑ u ∈ I, (B u : ℤ)) - 2 * ∑ u ∈ I, ((a u - q : ℕ) : ℤ) := by
    simp only [inc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hinc_sum] at hlayer
  dsimp only [U]
  linarith


end OddZetaSix.B40a
