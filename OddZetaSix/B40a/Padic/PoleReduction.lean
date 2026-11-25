import OddZetaSix.B40a.Padic.GateReduction

/-! Entrywise reduction of a single pole in the normalized Hermite coordinates. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset

def scaledPole (n : ℕ) (i j : Fin (fiveRank n)) (t : Fin (8*n)) : ℚ :=
  let a := ((jetIndex n).symm i).2.val
  let b := ((jetIndex n).symm j).2.val
  let p := primeIndex n
  ∑ ℓ ∈ Icc 1 (6-(a+b)), (p : ℚ)^(6-ℓ-(a+b)) * ((ℓ+3).choose 4 : ℚ) *
    (windowSeries n (gatePole n t) * (normalizedJet n i t * normalizedJet n j t)).coeff (6-ℓ-(a+b))

theorem scaledPole_eq (n : ℕ) [Fact (primeIndex n).Prime]
    (i j : Fin (fiveRank n)) (t : Fin (8*n)) :
    scaledPole n i j t =
      ∑ ℓ ∈ Icc 1 6,
        (primeIndex n : ℚ)^(10-(((jetIndex n).symm i).2.val+((jetIndex n).symm j).2.val)) *
          ((ℓ+3).choose 4 : ℚ) *
          localPrincipal n (gatePole n t) ℓ (interpolatingEven n i) (interpolatingEven n j) *
          (1/(primeIndex n : ℚ)^(ℓ+4)) := by
  let a := ((jetIndex n).symm i).2.val
  let b := ((jetIndex n).symm j).2.val
  let p := primeIndex n
  let U := windowSeries n (gatePole n t) * (normalizedJet n i t * normalizedJet n j t)
  let Q := fun ℓ : ℕ => (p : ℚ)^(10-(a+b)) * ((ℓ+3).choose 4 : ℚ) *
    localPrincipal n (gatePole n t) ℓ (interpolatingEven n i) (interpolatingEven n j) *
    (1/(p : ℚ)^(ℓ+4))
  have hpa : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have ha : a < 5 := ((jetIndex n).symm i).2.isLt
  have hb : b < 5 := ((jetIndex n).symm j).2.isLt
  have hlocal (ℓ : ℕ) (hℓ : ℓ ∈ Icc 1 6) :
      localPrincipal n (gatePole n t) ℓ (interpolatingEven n i) (interpolatingEven n j) =
      (X^(a+b) * U).coeff (6-ℓ) := by
    rw [window_principal_eq_jet_coeff _ _ _ _ _ (gatePole_mem n t) (mem_Icc.mp hℓ),
      gatePole_center,← normalizedJet_restore n i t,← normalizedJet_restore n j t]
    congr 1
    dsimp [U,a,b]
    rw [pow_add]
    ring
  change (∑ ℓ ∈ Icc 1 (6-(a+b)), (p : ℚ)^(6-ℓ-(a+b)) *
    ((ℓ+3).choose 4 : ℚ) * U.coeff (6-ℓ-(a+b))) = ∑ ℓ ∈ Icc 1 6, Q ℓ
  have hsub : Icc 1 (6-(a+b)) ⊆ Icc 1 6 := by
    intro ℓ h
    have h' := mem_Icc.mp h
    exact mem_Icc.mpr ⟨h'.1,by omega⟩
  have hcut : (∑ ℓ ∈ Icc 1 (6-(a+b)), Q ℓ) = ∑ ℓ ∈ Icc 1 6, Q ℓ := by
    apply Finset.sum_subset hsub
    intro ℓ hℓ hnot
    have hh := mem_Icc.mp hℓ
    have hlt : ¬ a+b ≤ 6-ℓ := by
      intro hab
      exact hnot (mem_Icc.mpr ⟨hh.1,by omega⟩)
    dsimp [Q]
    rw [hlocal ℓ hℓ,coeff_X_pow_mul',ite_eq_right hlt]
    ring
  rw [← hcut]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  have hh := mem_Icc.mp hℓ
  have hle : a+b ≤ 6-ℓ := by omega
  dsimp [Q]
  rw [hlocal ℓ (hsub hℓ),coeff_X_pow_mul',ite_eq_left hle]
  rw [show 10-(a+b) = (6-ℓ-(a+b))+(ℓ+4) by omega,pow_add]
  field_simp

theorem scaledPole_mem (n : ℕ) [Fact (primeIndex n).Prime]
    (i j : Fin (fiveRank n)) (t : Fin (8*n)) :
    scaledPole n i j t ∈ sixGateIntegralRing (primeIndex n) := by
  let S := sixGateIntegralRing (primeIndex n)
  unfold scaledPole
  apply S.sum_mem
  intro ℓ _
  apply S.mul_mem (S.mul_mem (S.pow_mem (natCast_mem S _) _) (natCast_mem S _))
  exact (polyInSubring_mul (windowSeries_mem n _ (gatePole_mem n t))
    (polyInSubring_mul (normalizedJet_mem n i t) (normalizedJet_mem n j t))) _

theorem scaledPole_cast (n : ℕ) [Fact (primeIndex n).Prime]
    (i j : Fin (fiveRank n)) (t : Fin (8*n)) :
    ((scaledPole n i j t : ℚ) : ZMod (primeIndex n)) =
      if ((jetIndex n).symm i).1 = t ∧ ((jetIndex n).symm j).1 = t then
        windowJetBlock n (gatePole n t) ((jetIndex n).symm i).2 ((jetIndex n).symm j).2
      else 0 := by
  let p := primeIndex n
  let a := ((jetIndex n).symm i).2.val
  let b := ((jetIndex n).symm j).2.val
  let U := windowSeries n (gatePole n t) * (normalizedJet n i t * normalizedJet n j t)
  let S := sixGateIntegralRing p
  have hU := polyInSubring_mul (windowSeries_mem n _ (gatePole_mem n t))
    (polyInSubring_mul (normalizedJet_mem n i t) (normalizedJet_mem n j t))
  let g := fun ℓ : ℕ => ((ℓ+3).choose 4 : ℚ) * U.coeff (6-ℓ-(a+b))
  let f := fun ℓ : ℕ => (p : ℚ)^(6-ℓ-(a+b)) * g ℓ
  have hg (ℓ : ℕ) : g ℓ ∈ S := S.mul_mem (natCast_mem S _) (hU _)
  have hf (ℓ : ℕ) : f ℓ ∈ S := S.mul_mem (S.pow_mem (natCast_mem S _) _) (hg ℓ)
  have hblock := jetWeight_cast n (gatePole n t) a b (gatePole_mem n t)
  have heq : scaledPole n i j t = ∑ ℓ ∈ Icc 1 (6-(a+b)), f ℓ := by
    simp only [scaledPole,f,g,a,b,U,p,mul_assoc]
  rw [heq]
  rw [sixGateIntegralRing_cast_sum p _ f (fun ℓ _ => hf ℓ)]
  by_cases hab : a+b < 6
  · rw [Finset.sum_eq_single (6-(a+b))]
    · have he : 6-(6-(a+b))-(a+b) = 0 := by omega
      have hh : 6-(a+b)+3 = 9-(a+b) := by omega
      simp only [f,g,he,hh,pow_zero,one_mul]
      rw [sixGateIntegralRing_cast_mul p (natCast_mem S _) (hU 0),Rat.cast_natCast]
      simp only [mul_coeff_zero,normalizedJet_coeff_zero,windowJetBlock]
      rw [hblock]
      by_cases hi : ((jetIndex n).symm i).1 = t <;>
        by_cases hj : ((jetIndex n).symm j).1 = t <;> simp [hi,hj]
    · intro ℓ hℓ hne
      have hh := mem_Icc.mp hℓ
      exact sixGateReduction_p_pow_mul_eq_zero p (by omega) _ (hg ℓ)
    · intro hn
      exact (hn (mem_Icc.mpr ⟨by omega,le_rfl⟩)).elim
  · have he : 6-(a+b)=0 := by omega
    have hh : 9-(a+b)<4 := by omega
    simp only [he,Icc_eq_empty_of_lt (by decide : 0 < 1),sum_empty,windowJetBlock]
    rw [hblock,Nat.choose_eq_zero_of_lt hh,Nat.cast_zero,zero_mul]
    split_ifs <;> rfl

end OddZetaSix.B40a
