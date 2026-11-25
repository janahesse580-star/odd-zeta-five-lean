import OddZetaSix.B40a.Model
import OddZetaSix.SixAssembly

noncomputable section

namespace OddZetaSix.B40a

open Filter
open scoped Topology

/-- The two remaining algebraic interfaces and the two rate interfaces for the
actual B40a kernel. Providing this structure is a separate theorem. -/
structure ProofInputs where
  primitive : ℕ → MvPolynomial (Fin 5) ℤ
  content : ℕ → ℚ
  content_nonzero : ∀ n, content n ≠ 0
  degree_bound : ∀ n, (primitive n).totalDegree ≤ fiveRank n
  determinant_identity : ∀ n,
    (content n : ℝ) * (primitive n).eval₂ (Int.castRingHom ℝ) fiveValues =
      (fiveFunctional n).det
  gate : ∀ Q : ℤ, 0 < Q → ∀ N : ℕ, ∃ n ≥ N,
    ∀ q : Fin 5 → ℚ, (∀ k, ∃ z : ℤ, (Q : ℚ)*q k = (z : ℚ)) →
      (primitive n).eval₂ (Int.castRingHom ℚ) q ≠ 0
  analytic : ∀ᶠ n : ℕ in atTop,
    |(fiveFunctional n).det| ≤ Real.exp ((-619/100 : ℝ)*normalizer n)
  arithmetic : ∀ᶠ n : ℕ in atTop,
    |(content n : ℝ)|⁻¹ ≤ Real.exp ((61405/10000 : ℝ)*normalizer n)

private theorem eval_rat_real (P : MvPolynomial (Fin 5) ℤ) (q : Fin 5 → ℚ) :
    ((P.eval₂ (Int.castRingHom ℚ) q : ℚ) : ℝ) =
      P.eval₂ (Int.castRingHom ℝ) (fun k => (q k : ℝ)) := by
  have h := MvPolynomial.hom_eval₂ P (Int.castRingHom ℚ) (Rat.castHom ℝ) q
  have hcomp : (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ :=
    RingHom.ext fun z => by simp
  simpa only [hcomp, Rat.coe_castHom] using h

theorem primitive_exp_bound (data : ProofInputs) : ∀ᶠ n : ℕ in atTop,
    |(data.primitive n).eval₂ (Int.castRingHom ℝ) fiveValues| ≤
      Real.exp ((-495/10000 : ℝ)*normalizer n) := by
  filter_upwards [data.analytic,data.arithmetic] with n ha hc
  have hγ : (data.content n : ℝ) ≠ 0 := by exact_mod_cast data.content_nonzero n
  have he : (data.primitive n).eval₂ (Int.castRingHom ℝ) fiveValues =
      (data.content n : ℝ)⁻¹ * (fiveFunctional n).det := by
    rw [← data.determinant_identity n, inv_mul_cancel_left₀ hγ]
  rw [he,abs_mul,abs_inv]
  refine (mul_le_mul hc ha (abs_nonneg _) (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add]
  apply le_of_eq
  congr 1
  ring

/-- Conditional assembly for the concrete five zeta weights. This declaration
does not itself supply the arithmetic or analytic estimates or the prime gate. -/
theorem exists_irrational_riemannZeta_seven_to_fifteen_of_inputs
    (data : ProofInputs) : FiveZetaIrrational := by
  by_contra hall
  have hrat : ∀ i : Fin 5, ∃ q : ℚ, (q : ℝ) = fiveValues i := by
    intro i
    have hni : ¬ Irrational (fiveValues i) := by
      intro hi
      exact hall ⟨7+2*i.val, fiveWeights_index i, hi⟩
    unfold Irrational at hni
    push Not at hni
    exact hni
  choose q hq using hrat
  obtain ⟨Q,hQ,hInt⟩ := OddZetaSix.common_denominator_exists q
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp (primitive_exp_bound data)
  let δ : ℝ := 495/10000
  have hδ : 0 < δ := by norm_num [δ]
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  obtain ⟨N₂,hN₂⟩ := exists_nat_gt (40*Real.log (Q : ℝ)/(2000*δ))
  let N := max (max N₁ N₂) 1
  obtain ⟨n,hn,hne⟩ := data.gate Q hQ N
  have hn1 : N₁ ≤ n := (le_max_left N₁ N₂).trans ((le_max_left _ 1).trans hn)
  have hn2 : N₂ ≤ n := (le_max_right N₁ N₂).trans ((le_max_left _ 1).trans hn)
  have hnPos : 0 < n := (le_max_right (max N₁ N₂) 1).trans hn
  have hl := OddZetaSix.one_le_abs_cleared_evaluation (data.primitive n) q Q (fiveRank n)
    hQ.ne' (data.degree_bound n) hInt (hne q hInt)
  have hlR : (1 : ℝ) ≤ (Q : ℝ)^(fiveRank n) *
      |(data.primitive n).eval₂ (Int.castRingHom ℝ) fiveValues| := by
    have hcast : (1 : ℝ) ≤
        ((|(Q : ℚ)^fiveRank n * (data.primitive n).eval₂ (Int.castRingHom ℚ) q| : ℚ) : ℝ) := by
      exact_mod_cast hl
    rw [Rat.cast_abs, Rat.cast_mul, Rat.cast_pow, Rat.cast_intCast, eval_rat_real,
      abs_mul, abs_pow, abs_of_pos hQR, funext hq] at hcast
    exact hcast
  have hcomb := hlR.trans (mul_le_mul_of_nonneg_left (hN₁ n hn1) (pow_nonneg hQR.le _))
  have hQpow : (Q : ℝ)^fiveRank n = Real.exp ((fiveRank n : ℝ)*Real.log (Q : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hQR, mul_comm]
  rw [hQpow,← Real.exp_add] at hcomb
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hN : 40*Real.log (Q : ℝ)/(2000*δ) < (n : ℝ) :=
    hN₂.trans_le (by exact_mod_cast hn2)
  have hm := (div_lt_iff₀ (show 0<2000*δ by positivity)).mp hN
  have hmn := mul_lt_mul_of_pos_right hm hnR
  have hneg : (fiveRank n : ℝ)*Real.log (Q : ℝ) +
      (-495/10000 : ℝ)*normalizer n < 0 := by
    unfold fiveRank normalizer
    push_cast
    dsimp [δ] at hmn
    nlinarith only [hmn]
  exact (not_lt_of_ge hcomb) (Real.exp_lt_one_iff.mpr hneg)

end OddZetaSix.B40a
