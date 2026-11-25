import OddZetaSix.B40a.Padic.PoleReduction

/-! The scaled rational B40a matrix reduces to the block diagonal matrix
of its actual sixfold poles. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset

private theorem sum_gateWindow (n : ℕ) (f : ℕ → ℚ) :
    ∑ k ∈ gateWindow n, f k = ∑ t : Fin (8*n), f (gatePole n t) := by
  symm
  apply Finset.sum_bij (fun t _ => gatePole n t)
  · intro t _
    exact gatePole_mem n t
  · intro t _ s _ h
    apply Fin.ext
    unfold gatePole at h
    omega
  · intro k hk
    have hh := mem_Icc.mp hk
    refine ⟨⟨k-(76*n+2),by omega⟩,Finset.mem_univ _,?_⟩
    unfold gatePole
    simp only
    omega
  · simp

private def singularLinear (n : ℕ) : ℚ[X] →ₗ[ℚ] ℚ where
  toFun f := ∑ t : Fin (8*n), ∑ ℓ ∈ Icc 1 6,
    ((ℓ+3).choose 4 : ℚ) * localPrincipal n (gatePole n t) ℓ f 1 *
      (1/(primeIndex n : ℚ)^(ℓ+4))
  map_add' f g := by
    simp only [localPrincipal,mul_one,add_comp,mul_add,map_add,localQuotient_add,add_mul,
      Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [RingHom.id_apply,smul_eq_mul,Polynomial.smul_eq_C_mul,localPrincipal,mul_one,
      mul_comp,C_comp]
    have move :
        C (normalization n) * numerator n * (C c * f.comp (X+C (center n : ℚ))) =
          C c * (C (normalization n) * numerator n * f.comp (X+C (center n : ℚ))) := by ring
    simp only [move,taylor_mul,taylor_C,localQuotient_C_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro ℓ _
    ring

private theorem singularLinear_apply (n : ℕ) (f g : ℚ[X]) :
    singularLinear n (f*g) = ∑ t : Fin (8*n), ∑ ℓ ∈ Icc 1 6,
      ((ℓ+3).choose 4 : ℚ) * localPrincipal n (gatePole n t) ℓ f g *
        (1/(primeIndex n : ℚ)^(ℓ+4)) := by
  simp only [singularLinear,LinearMap.coe_mk,AddHom.coe_mk,localPrincipal,mul_one]

private theorem negativeSingular_eval (n : ℕ) (i j : Fin (fiveRank n)) :
    -singularHigh n (primeIndex n) i j = singularLinear n (X^(2*i.val)*X^(2*j.val)) := by
  rw [singularHigh_gate_window,neg_neg,singularLinear_apply,sum_gateWindow]

private theorem interpolatedSingular (n : ℕ) (i j : Fin (fiveRank n)) :
    (∑ v : Fin (fiveRank n), ∑ w : Fin (fiveRank n),
      inverseMonomialJets n i v * singularHigh n (primeIndex n) v w * inverseMonomialJets n j w) =
      -(singularLinear n (interpolatingEven n i * interpolatingEven n j)) := by
  simp only [interpolatingEven,Finset.sum_mul,Finset.mul_sum,map_sum,← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro v _
  let c := inverseMonomialJets n i v
  let d := inverseMonomialJets n j w
  change c * singularHigh n (primeIndex n) v w * d =
    -singularLinear n (C c * X^(2*v.val) * (C d * X^(2*w.val)))
  rw [show C c * (X : ℚ[X])^(2*v.val) * (C d * X^(2*w.val)) =
        c • (d • (X^(2*v.val)*X^(2*w.val) : ℚ[X])) by
          simp only [Polynomial.smul_eq_C_mul]; ring,
    map_smul,map_smul, ← negativeSingular_eval]
  simp only [smul_eq_mul]
  ring

private def regScaled (n : ℕ) (q : Fin 5 → ℚ) (i j : Fin (fiveRank n)) : ℚ :=
  let a := ((jetIndex n).symm i).2.val
  let b := ((jetIndex n).symm j).2.val
  (primeIndex n : ℚ)^(10-(a+b)) *
    ∑ v : Fin (fiveRank n), ∑ w : Fin (fiveRank n),
      inverseMonomialJets n i v * regularHigh n (primeIndex n) q v w * inverseMonomialJets n j w

private theorem scaledWindowMatrix_apply (n : ℕ) [Fact (primeIndex n).Prime]
    (q : Fin 5 → ℚ) (i j : Fin (fiveRank n)) :
    scaledWindowMatrix n q i j = regScaled n q i j - ∑ t : Fin (8*n), scaledPole n i j t := by
  let p := primeIndex n
  let a := ((jetIndex n).symm i).2.val
  let b := ((jetIndex n).symm j).2.val
  let A := (Hpow n).map (MvPolynomial.eval q)
  let W := inverseMonomialJets n
  have ha : a < 5 := ((jetIndex n).symm i).2.isLt
  have hb : b < 5 := ((jetIndex n).symm j).2.isLt
  have hmid : (W * (A * W.transpose)) i j =
      ∑ v : Fin (fiveRank n), ∑ w : Fin (fiveRank n), W i v * A v w * W j w := by
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    ring
  change (jetScale n * W * A * W.transpose * jetScale n) i j = _
  unfold jetScale
  rw [Matrix.mul_diagonal,Matrix.mul_assoc (Matrix.diagonal _),
    Matrix.mul_assoc (Matrix.diagonal _),Matrix.diagonal_mul,Matrix.mul_assoc W,hmid]
  change (p : ℚ)^(5-a)*(∑ v, ∑ w, W i v * A v w * W j w)*(p : ℚ)^(5-b) = _
  have hpow : (p : ℚ)^(5-a)*(p : ℚ)^(5-b) = (p : ℚ)^(10-(a+b)) := by
    rw [← pow_add,show (5-a)+(5-b)=10-(a+b) by omega]
  have heq : A = regularHigh n p q + singularHigh n p :=
    monomial_high_prime_split n p (Fact.out : p.Prime).pos q
  rw [mul_right_comm,hpow,heq]
  simp only [Matrix.add_apply,mul_add,add_mul,Finset.sum_add_distrib]
  change _ * _ + _ *
    (∑ v, ∑ w, inverseMonomialJets n i v * singularHigh n (primeIndex n) v w * inverseMonomialJets n j w) = _
  rw [interpolatedSingular,singularLinear_apply]
  simp only [regScaled,mul_neg,sub_eq_add_neg]
  congr 1
  rw [Finset.mul_sum]
  apply congrArg (fun x : ℚ => -x)
  apply Finset.sum_congr rfl
  intro t _
  rw [scaledPole_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ℓ _
  ring

private theorem regScaled_mem_cast (n : ℕ) [Fact (primeIndex n).Prime] (q : Fin 5 → ℚ)
    (hq : ∀ a, q a ∈ sixGateIntegralRing (primeIndex n)) (i j : Fin (fiveRank n)) :
    regScaled n q i j ∈ sixGateIntegralRing (primeIndex n) ∧
      ((regScaled n q i j : ℚ) : ZMod (primeIndex n)) = 0 := by
  let S := sixGateIntegralRing (primeIndex n)
  have ha := ((jetIndex n).symm i).2.isLt
  have hb := ((jetIndex n).symm j).2.isLt
  have hlarge : 50*n < primeIndex n := by unfold primeIndex; omega
  have hint :
      (∑ v : Fin (fiveRank n), ∑ w : Fin (fiveRank n),
        inverseMonomialJets n i v * regularHigh n (primeIndex n) q v w * inverseMonomialJets n j w) ∈ S := by
    apply S.sum_mem
    intro v _
    apply S.sum_mem
    intro w _
    exact S.mul_mem (S.mul_mem (inverseMonomialJets_mem n i v)
      (regularHigh_mem n _ hlarge q hq v w)) (inverseMonomialJets_mem n j w)
  exact ⟨S.mul_mem (S.pow_mem (natCast_mem S _) _) hint,
    sixGateReduction_p_pow_mul_eq_zero (primeIndex n) (by omega) _ hint⟩

private def reducedWindow (n : ℕ) [Fact (primeIndex n).Prime] :
    Matrix (Fin (fiveRank n)) (Fin (fiveRank n)) (ZMod (primeIndex n)) :=
  fun i j => let (t,a) := (jetIndex n).symm i
             let (s,b) := (jetIndex n).symm j
             if t = s then -windowJetBlock n (gatePole n t) a b else 0

private theorem reducedWindow_det_ne_zero (n : ℕ) [Fact (primeIndex n).Prime] :
    (reducedWindow n).det ≠ 0 := by
  let e : (Fin 5 × Fin (8*n)) ≃ Fin (fiveRank n) :=
    (Equiv.prodComm (Fin 5) (Fin (8*n))).trans (jetIndex n)
  have hreindex : Matrix.reindex e.symm e.symm (reducedWindow n) =
      Matrix.blockDiagonal (fun t => -windowJetBlock n (gatePole n t)) := by
    apply Matrix.ext
    rintro ⟨a,t⟩ ⟨b,s⟩
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,reducedWindow,
      Matrix.blockDiagonal_apply,e,Equiv.trans_apply,Equiv.prodComm_apply,Equiv.symm_apply_apply,
      Prod.swap_prod_mk,Matrix.neg_apply]
  rw [← Matrix.det_reindex_self e.symm (reducedWindow n),hreindex,Matrix.det_blockDiagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro t _
  rw [Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (windowJetBlock_det_ne_zero n _ (gatePole_mem n t))

theorem scaledWindow_mem_cast (n : ℕ) [Fact (primeIndex n).Prime] (q : Fin 5 → ℚ)
    (hq : ∀ a, q a ∈ sixGateIntegralRing (primeIndex n)) (i j : Fin (fiveRank n)) :
    scaledWindowMatrix n q i j ∈ sixGateIntegralRing (primeIndex n) ∧
      ((scaledWindowMatrix n q i j : ℚ) : ZMod (primeIndex n)) = reducedWindow n i j := by
  let p := primeIndex n
  let S := sixGateIntegralRing p
  have hr := regScaled_mem_cast n q hq i j
  have hs : (∑ t : Fin (8*n), scaledPole n i j t) ∈ S :=
    S.sum_mem (fun t _ => scaledPole_mem n i j t)
  rw [scaledWindowMatrix_apply]
  refine ⟨S.sub_mem hr.1 hs,?_⟩
  rw [sub_eq_add_neg,sixGateIntegralRing_cast_add p hr.1 (S.neg_mem hs),
    Rat.cast_neg,hr.2,zero_add,sixGateIntegralRing_cast_sum p _ _ (fun t _ => scaledPole_mem n i j t)]
  have hsum : (∑ t : Fin (8*n), ((scaledPole n i j t : ℚ) : ZMod (primeIndex n))) =
      ∑ t : Fin (8*n), if ((jetIndex n).symm i).1 = t ∧ ((jetIndex n).symm j).1 = t then
        windowJetBlock n (gatePole n t) ((jetIndex n).symm i).2 ((jetIndex n).symm j).2 else 0 := by
    apply Finset.sum_congr rfl
    intro t _
    exact scaledPole_cast n i j t
  change -(∑ t : Fin (8*n), ((scaledPole n i j t : ℚ) : ZMod (primeIndex n))) = _
  rw [hsum,Finset.sum_eq_single ((jetIndex n).symm i).1]
  · simp only [reducedWindow,true_and]
    generalize (jetIndex n).symm i = x
    generalize (jetIndex n).symm j = y
    rcases x with ⟨ti,ai⟩
    rcases y with ⟨tj,aj⟩
    by_cases h : ti = tj
    · subst tj
      simp
    · simp [h,Ne.symm h]
  · intro t _ ht
    simp [Ne.symm ht]
  · simp

theorem rational_det_valuation (n : ℕ) [Fact (primeIndex n).Prime] (q : Fin 5 → ℚ)
    (hq : ∀ a, q a ∈ sixGateIntegralRing (primeIndex n)) :
    ((Hpoly n).map (MvPolynomial.eval q)).det ≠ 0 ∧
      padicValRat (primeIndex n) ((Hpoly n).map (MvPolynomial.eval q)).det = -269*(n : ℤ)+2 := by
  let p := primeIndex n
  let S := sixGateIntegralRing p
  let M : Matrix (Fin (fiveRank n)) (Fin (fiveRank n)) S :=
    fun i j => ⟨_,(scaledWindow_mem_cast n q hq i j).1⟩
  have hsub : S.subtype.mapMatrix M = scaledWindowMatrix n q := rfl
  have hred : (sixGateReduction p).mapMatrix M = reducedWindow n := by
    apply Matrix.ext
    intro i j
    exact (scaledWindow_mem_cast n q hq i j).2
  have hu : sixGateReduction p M.det ≠ 0 := by
    rw [RingHom.map_det,hred]
    exact reducedWindow_det_ne_zero n
  have hh := (sixGateReduction_ne_zero_iff p M.det).mp hu
  change S.subtype M.det ≠ 0 ∧ padicValRat p (S.subtype M.det) = 0 at hh
  rw [RingHom.map_det,hsub] at hh
  exact concrete_valuation_from_scaled_window n q hh.1 hh.2

theorem exists_irrational_riemannZeta_seven_to_fifteen_of_analytic_arithmetic
    (analytic : ∀ᶠ n : ℕ in Filter.atTop,
      |(fiveFunctional n).det| ≤ Real.exp ((-619/100 : ℝ)*normalizer n))
    (arithmetic : ∀ᶠ n : ℕ in Filter.atTop,
      |(content n : ℝ)|⁻¹ ≤ Real.exp ((61405/10000 : ℝ)*normalizer n)) :
    ∃ s ∈ ({7,9,11,13,15} : Finset ℕ), Irrational ((riemannZeta (s : ℂ)).re) :=
  exists_irrational_riemannZeta_seven_to_fifteen_of_gate_and_rates
    (subsequence_of_local_nonzero (fun n _ q hq => (rational_det_valuation n q hq).1))
    analytic arithmetic

end OddZetaSix.B40a
