import OddZetaSix.B40a.Padic.WindowJets

/-! The monomial five-jet evaluation matrix at the actual signed pole nodes. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset

def gatePole (n : ℕ) (t : Fin (8*n)) : ℕ := 76*n+2+t.val

theorem gatePole_mem (n : ℕ) (t : Fin (8*n)) : gatePole n t ∈ gateWindow n := by
  have ht := t.isLt
  rw [gateWindow, Finset.mem_Icc]
  unfold gatePole
  omega

theorem gatePole_center (n : ℕ) (t : Fin (8*n)) :
    (center n : ℚ) - gatePole n t = -(absNode n t : ℚ) := by
  unfold center gatePole absNode
  push_cast
  ring

def jetIndex (n : ℕ) : (Fin (8*n) × Fin 5) ≃ Fin (fiveRank n) :=
  finProdFinEquiv.trans (finCongr (by unfold fiveRank; omega))

def monomialJets {K : Type*} [CommRing K] (n : ℕ) :
    Matrix (Fin (fiveRank n)) (Fin (fiveRank n)) K := fun i j =>
  let (t,a) := (jetIndex n).symm j
  (taylor (-(absNode n t : K)) (X^(2*i.val))).coeff a.val

private theorem poly_zero_of_signed_jets (n : ℕ) [Fact (primeIndex n).Prime]
    (P : (ZMod (primeIndex n))[X]) (hd : P.natDegree < fiveRank n)
    (h : ∀ t : Fin (8*n), ∀ a < 5,
      (taylor (-(absNode n t : ZMod (primeIndex n))) (P.comp (X^2))).coeff a = 0) :
    P = 0 := by
  by_contra hP
  have hcop : Set.Pairwise ((univ : Finset (Fin (8*n))) : Set (Fin (8*n)))
      (fun t s => IsCoprime ((X-C (squareNode n t))^5) ((X-C (squareNode n s))^5)) := by
    intro t _ s _ hne
    exact (Polynomial.pairwise_coprime_X_sub_C (squareNode_injective n) hne).pow
  have hdiv : (∏ t : Fin (8*n), (X-C (squareNode n t))^5) ∣ P := by
    apply Finset.prod_dvd_of_coprime hcop
    intro t _
    have h2 : 2 * (-(absNode n t : ZMod (primeIndex n))) ≠ 0 := by
      simpa only [mul_neg,neg_ne_zero] using two_mul_node_ne_zero n t
    simpa only [neg_sq,squareNode] using pow_dvd_of_square_jets P h2 5 (h t)
  have hprod : (∏ t : Fin (8*n), (X-C (squareNode n t))^5).natDegree = fiveRank n := by
    rw [natDegree_prod_of_monic _ _ (fun t _ => (monic_X_sub_C _).pow 5)]
    simp_rw [(monic_X_sub_C _).natDegree_pow,natDegree_X_sub_C,mul_one]
    simp [fiveRank]
    ring
  exact (not_le_of_gt hd) (hprod ▸ Polynomial.natDegree_le_of_dvd hdiv hP)

theorem monomialJets_det_mod_ne_zero (n : ℕ) [Fact (primeIndex n).Prime] :
    (monomialJets (K := ZMod (primeIndex n)) n).det ≠ 0 := by
  let V := monomialJets (K := ZMod (primeIndex n)) n
  intro hV
  have hVT : V.transpose.det = 0 := by rw [Matrix.det_transpose]; exact hV
  obtain ⟨c,hc,hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hVT
  let P : (ZMod (primeIndex n))[X] := ∑ i : Fin (fiveRank n), C (c i) * X^i.val
  have hn : 0 < fiveRank n := by
    have hp := (Fact.out : (primeIndex n).Prime).two_le
    unfold fiveRank primeIndex at *
    omega
  have hPdeg : P.natDegree < fiveRank n := by
    refine (Polynomial.natDegree_sum_le _ _).trans_lt ?_
    rw [Finset.fold_max_lt]
    refine ⟨hn, ?_⟩
    intro i _
    exact (natDegree_C_mul_le _ _).trans_lt (by simpa using i.isLt)
  have hPjets (t : Fin (8*n)) (a : ℕ) (ha : a < 5) :
      (taylor (-(absNode n t : ZMod (primeIndex n))) (P.comp (X^2))).coeff a = 0 := by
    have hrow := congrFun hker (jetIndex n (t,⟨a,ha⟩))
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply,
      V,monomialJets,Equiv.symm_apply_apply] at hrow
    simp only [P,Polynomial.sum_comp,mul_comp,C_comp,pow_comp,X_comp,← pow_mul,
      map_sum,taylor_mul,taylor_C,finsetSum_coeff,coeff_C_mul]
    simpa only [mul_comm] using hrow
  have hzero := poly_zero_of_signed_jets n P hPdeg hPjets
  apply hc
  funext i
  have hi := congrArg (fun p : (ZMod (primeIndex n))[X] => p.coeff i.val) hzero
  simp only [P,finsetSum_coeff,coeff_C_mul,coeff_X_pow,Polynomial.coeff_zero] at hi
  rw [Finset.sum_eq_single i] at hi
  · simpa using hi
  · intro b _ hb
    have hne : i.val ≠ b.val := fun h => hb (Fin.ext h.symm)
    simp [hne]
  · simp

theorem monomialJets_rat_mem (n : ℕ) [Fact (primeIndex n).Prime] (i j : Fin (fiveRank n)) :
    monomialJets (K := ℚ) n i j ∈ sixGateIntegralRing (primeIndex n) := by
  unfold monomialJets
  let S := sixGateIntegralRing (primeIndex n)
  exact (polyInSubring_taylor (polyInSubring_pow polyInSubring_X _)
    (S.neg_mem (natCast_mem S _))) _

theorem monomialJets_rat_cast (n : ℕ) [Fact (primeIndex n).Prime] (i j : Fin (fiveRank n)) :
    ((monomialJets (K := ℚ) n i j : ℚ) : ZMod (primeIndex n)) = monomialJets n i j := by
  generalize he : (jetIndex n).symm j = ta
  rcases ta with ⟨t,a⟩
  simp only [monomialJets,he,taylor_X_pow,coeff_X_add_C_pow]
  exact_mod_cast rfl

theorem monomialJets_det_unit (n : ℕ) [Fact (primeIndex n).Prime] :
    let d := (monomialJets (K := ℚ) n).det
    d ≠ 0 ∧ padicValRat (primeIndex n) d = 0 := by
  let S := sixGateIntegralRing (primeIndex n)
  let V : Matrix (Fin (fiveRank n)) (Fin (fiveRank n)) S :=
    fun i j => ⟨monomialJets n i j, monomialJets_rat_mem n i j⟩
  have hsub : S.subtype.mapMatrix V = monomialJets (K := ℚ) n := rfl
  have hred : (sixGateReduction (primeIndex n)).mapMatrix V =
      monomialJets (K := ZMod (primeIndex n)) n := by
    apply Matrix.ext
    exact monomialJets_rat_cast n
  have hu : sixGateReduction (primeIndex n) V.det ≠ 0 := by
    rw [RingHom.map_det,hred]
    exact monomialJets_det_mod_ne_zero n
  have hunit := (sixGateReduction_ne_zero_iff _ _).mp hu
  change S.subtype V.det ≠ 0 ∧ padicValRat (primeIndex n) (S.subtype V.det) = 0 at hunit
  rwa [RingHom.map_det,hsub] at hunit

end OddZetaSix.B40a
