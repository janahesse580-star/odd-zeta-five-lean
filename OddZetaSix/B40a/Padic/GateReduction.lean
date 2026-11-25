import OddZetaSix.B40a.Padic.GateScaling

/-! Reduction in the rational Hermite interpolation basis. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset

theorem inverseMonomialJets_mem (n : ℕ) [Fact (primeIndex n).Prime] (i j : Fin (fiveRank n)) :
    inverseMonomialJets n i j ∈ sixGateIntegralRing (primeIndex n) := by
  let S := sixGateIntegralRing (primeIndex n)
  let V : Matrix (Fin (fiveRank n)) (Fin (fiveRank n)) S :=
    fun i j => ⟨monomialJets n i j, monomialJets_rat_mem n i j⟩
  have hV : S.subtype.mapMatrix V = monomialJets (K := ℚ) n := rfl
  have hAdj : S.subtype.mapMatrix V.adjugate = (monomialJets (K := ℚ) n).adjugate := by
    rw [← hV]
    exact RingHom.map_adjugate _ _
  have h := monomialJets_det_unit n
  have hentry := congrFun (congrFun hAdj i) j
  change ((V.adjugate i j : S) : ℚ) = _ at hentry
  unfold inverseMonomialJets
  rw [Matrix.smul_apply,smul_eq_mul,← hentry]
  exact S.mul_mem (sixGateIntegralRing_inv_of_unit _ _ h.1 h.2) (V.adjugate i j).property

def interpolatingEven (n : ℕ) (i : Fin (fiveRank n)) : ℚ[X] :=
  ∑ j : Fin (fiveRank n), C (inverseMonomialJets n i j) * X^(2*j.val)

theorem interpolatingEven_mem (n : ℕ) [Fact (primeIndex n).Prime] (i : Fin (fiveRank n)) :
    PolyInSubring (sixGateIntegralRing (primeIndex n)) (interpolatingEven n i) := by
  unfold interpolatingEven
  intro r
  rw [finsetSum_coeff]
  apply (sixGateIntegralRing (primeIndex n)).sum_mem
  intro j _
  exact (polyInSubring_mul (polyInSubring_C (inverseMonomialJets_mem n i j))
    (polyInSubring_pow polyInSubring_X _)) r

theorem interpolation_coeff (n : ℕ) [Fact (primeIndex n).Prime] (i : Fin (fiveRank n))
    (t : Fin (8*n)) (a : Fin 5) :
    (taylor (-(absNode n t : ℚ)) (interpolatingEven n i)).coeff a.val =
      if i = jetIndex n (t,a) then 1 else 0 := by
  have h := congrFun (congrFun (inverseMonomialJets_mul n) i) (jetIndex n (t,a))
  simpa only [interpolatingEven,map_sum,taylor_mul,taylor_C,finsetSum_coeff,coeff_C_mul,
    Matrix.mul_apply,monomialJets,Equiv.symm_apply_apply,Matrix.one_apply] using h

private def dropCoeffs (a : ℕ) (f : ℚ[X]) : ℚ[X] :=
  match a with
  | 0 => f
  | a+1 => (dropCoeffs a f).divX

private theorem coeff_dropCoeffs (a : ℕ) (f : ℚ[X]) (k : ℕ) :
    (dropCoeffs a f).coeff k = f.coeff (k+a) := by
  induction a generalizing k with
  | zero => simp [dropCoeffs]
  | succ a ih => rw [dropCoeffs,coeff_divX,ih]; congr 1; omega

private theorem dropCoeffs_restore (a : ℕ) (f : ℚ[X]) (h : ∀ k<a, f.coeff k = 0) :
    X^a * dropCoeffs a f = f := by
  ext k
  rw [coeff_X_pow_mul']
  by_cases hk : a ≤ k
  · rw [ite_eq_left hk,coeff_dropCoeffs]
    congr 1
    omega
  · rw [ite_eq_right hk,h k (by omega)]

def normalizedJet (n : ℕ) (i : Fin (fiveRank n)) (t : Fin (8*n)) : ℚ[X] :=
  dropCoeffs ((jetIndex n).symm i).2.val (taylor (-(absNode n t : ℚ)) (interpolatingEven n i))

theorem normalizedJet_restore (n : ℕ) [Fact (primeIndex n).Prime] (i : Fin (fiveRank n))
    (t : Fin (8*n)) :
    X^((jetIndex n).symm i).2.val * normalizedJet n i t =
      taylor (-(absNode n t : ℚ)) (interpolatingEven n i) := by
  apply dropCoeffs_restore
  intro k hk
  have ha : k < 5 := hk.trans ((jetIndex n).symm i).2.isLt
  rw [interpolation_coeff n i t ⟨k,ha⟩,ite_eq_right]
  intro he
  have hh := congrArg ((jetIndex n).symm) he
  rw [Equiv.symm_apply_apply] at hh
  exact (Nat.ne_of_lt hk) (congrArg (fun p : Fin (8*n) × Fin 5 => p.2.val) hh).symm

theorem normalizedJet_mem (n : ℕ) [Fact (primeIndex n).Prime] (i : Fin (fiveRank n))
    (t : Fin (8*n)) : PolyInSubring (sixGateIntegralRing (primeIndex n)) (normalizedJet n i t) := by
  intro k
  rw [normalizedJet,coeff_dropCoeffs]
  exact (polyInSubring_taylor (interpolatingEven_mem n i)
    ((sixGateIntegralRing (primeIndex n)).neg_mem (natCast_mem _ _))) _

theorem normalizedJet_coeff_zero (n : ℕ) [Fact (primeIndex n).Prime] (i : Fin (fiveRank n))
    (t : Fin (8*n)) :
    (normalizedJet n i t).coeff 0 = if ((jetIndex n).symm i).1 = t then 1 else 0 := by
  rw [normalizedJet,coeff_dropCoeffs,zero_add,interpolation_coeff]
  congr 1
  apply propext
  constructor
  · intro he
    have h := congrArg (jetIndex n).symm he
    rw [Equiv.symm_apply_apply] at h
    exact congrArg Prod.fst h
  · intro he
    apply (jetIndex n).symm.injective
    rw [Equiv.symm_apply_apply]
    exact Prod.ext he rfl

end OddZetaSix.B40a
