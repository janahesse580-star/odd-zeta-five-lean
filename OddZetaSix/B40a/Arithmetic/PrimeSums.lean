import OddZetaSix.B40a.Arithmetic.Coarse
import OddZetaSix.B40a.Arithmetic.Periodic

/-! Relate the finite weighted prime sum for the true B40a content to the
logarithmic cost. The factorization argument adapts the MIT-licensed SixPNTBridge. -/
noncomputable section
namespace OddZetaSix.B40a
open Finset Filter
open scoped BigOperators Topology

/-- All primes up to the sharp integrality cutoff `84 * n`. -/
def cutoffPrimes (n : ℕ) : Finset ℕ :=
  Nat.primesLE (84 * n)

/-- Nonnegative `p`-adic denominator exponent `max 0 (-v_p(γ_n))` as a real number. -/
def primeExponent (n p : ℕ) : ℝ :=
  (max (0 : ℤ) (-padicValRat p (content n)) : ℝ)

theorem primeExponent_nonneg (n p : ℕ) : 0 ≤ primeExponent n p := by
  unfold primeExponent
  exact_mod_cast le_max_left (0 : ℤ) (-padicValRat p (content n))

/-- Total logarithmic denominator cost `∑_{p ≤ 84n} max(0, -v_p(γ_n)) log p`. -/
def primeCost (n : ℕ) : ℝ :=
  ∑ p ∈ cutoffPrimes n, primeExponent n p * Real.log (p : ℝ)

/-- Band-restricted prime cost on `a * n < p ≤ b * n`. -/
def bandPrimeCost (n : ℕ) (a b : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ (Nat.primesLE ⌊b * (n : ℝ)⌋₊).filter (fun p : ℕ => a * (n : ℝ) < (p : ℝ)),
    primeExponent n p * Real.log (p : ℝ)

theorem primeCost_nonneg (n : ℕ) : 0 ≤ primeCost n := by
  apply Finset.sum_nonneg
  intro p hp
  have hpr : p.Prime := (Nat.mem_primesLE.mp hp).2
  exact mul_nonneg (primeExponent_nonneg n p)
    (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))

theorem bandPrimeCost_nonneg (n : ℕ) (a b : ℝ) : 0 ≤ bandPrimeCost n a b := by
  classical
  unfold bandPrimeCost
  apply Finset.sum_nonneg
  intro p hp
  have hpr : p.Prime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
  exact mul_nonneg (primeExponent_nonneg n p)
    (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))

/-- For any rational `q ≠ 0` and prime `p ∣ q.den`, `padicValRat p q = -padicValNat p q.den`. -/
private theorem padicValRat_eq_neg_den_of_dvd (q : ℚ) (p : ℕ) [Fact p.Prime]
    (hdvd : p ∣ q.den) :
    padicValRat p q = -(padicValNat p q.den : ℤ) := by
  have hp : p.Prime := Fact.out
  have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
  have hndvd_num : ¬ p ∣ q.num.natAbs := by
    intro hnum
    have h1 : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hnum hdvd
    rw [hcop.gcd_eq_one] at h1
    exact hp.not_dvd_one h1
  have hnum0 : q.num ≠ 0 := by
    intro h0
    rw [h0] at hndvd_num
    exact hndvd_num (dvd_zero p)
  have hq : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
  conv_lhs => rw [hq]
  rw [padicValRat.div (by exact_mod_cast hnum0) (by exact_mod_cast q.den_nz),
    padicValRat.of_int, padicValInt, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd hndvd_num]
  simp

/-- Unconditional exponential bridge: `|γ_n|⁻¹ ≤ exp(primeCost n)` for every `n : ℕ`. -/
theorem content_inv_le_exp_primeCost (n : ℕ) :
    |(content n : ℝ)|⁻¹ ≤ Real.exp (primeCost n) := by
  let q : ℚ := content n
  have hqne : q ≠ 0 := content_ne_zero n
  have hnum_ne : q.num ≠ 0 := Rat.num_ne_zero.mpr hqne
  have hden_pos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have habs_inv : |(q : ℝ)|⁻¹ ≤ (q.den : ℝ) := by
    have hqR : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den q).symm
    rw [hqR, abs_div, inv_div, abs_of_pos hden_pos]
    have h1 : (1 : ℝ) ≤ |(q.num : ℝ)| := by
      have : (1 : ℤ) ≤ |q.num| := by
        have := abs_pos.mpr hnum_ne
        omega
      exact_mod_cast this
    exact div_le_self hden_pos.le h1
  have hlog_den : Real.log (q.den : ℝ) ≤ primeCost n := by
    have hfac : (∏ p ∈ q.den.primeFactors, p ^ q.den.factorization p) = q.den :=
      Nat.prod_factorization_pow_eq_self q.den_nz
    have hlog_eq : Real.log (q.den : ℝ) =
        ∑ p ∈ q.den.primeFactors, (padicValNat p q.den : ℝ) * Real.log (p : ℝ) := by
      conv_lhs => rw [← hfac]
      push_cast
      rw [Real.log_prod (fun p hp => by
        have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
        exact pow_ne_zero _ (by exact_mod_cast hpr.ne_zero))]
      apply Finset.sum_congr rfl
      intro p hp
      have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
      have : Fact p.Prime := ⟨hpr⟩
      rw [Real.log_pow, Nat.factorization_def q.den hpr]
    rw [hlog_eq]
    unfold primeCost
    have hsub : q.den.primeFactors ⊆ cutoffPrimes n := by
      intro p hp
      have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hdvd : p ∣ q.den := Nat.dvd_of_mem_primeFactors hp
      have : Fact p.Prime := ⟨hpr⟩
      have hv_pos : 0 < padicValNat p q.den :=
        lt_of_lt_of_le Nat.zero_lt_one (one_le_padicValNat_of_dvd q.den_nz hdvd)
      have hv_eq : padicValRat p q = -(padicValNat p q.den : ℤ) :=
        padicValRat_eq_neg_den_of_dvd q p hdvd
      have hp84 : p ≤ 84 * n := by
        by_contra hgt
        push Not at hgt
        have hle0 := content_large_prime_support n p hgt
        change 0 ≤ padicValRat p q at hle0
        omega
      exact Nat.mem_primesLE.mpr ⟨hp84, hpr⟩
    refine (Finset.sum_le_sum (fun p hp => ?_)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by
        have hpr : p.Prime := (Nat.mem_primesLE.mp hp).2
        exact mul_nonneg (primeExponent_nonneg n p)
          (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))))
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ q.den := Nat.dvd_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hpr⟩
    have hv_eq : padicValRat p q = -(padicValNat p q.den : ℤ) :=
      padicValRat_eq_neg_den_of_dvd q p hdvd
    apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
    unfold primeExponent
    change (padicValNat p q.den : ℝ) ≤ max ((0 : ℤ) : ℝ) (-((padicValRat p q : ℤ) : ℝ))
    rw [hv_eq, Int.cast_neg, neg_neg, Int.cast_zero, Int.cast_natCast]
    exact le_max_right (0 : ℝ) (padicValNat p q.den : ℝ)
  calc
    |(q : ℝ)|⁻¹ ≤ (q.den : ℝ) := habs_inv
    _ = Real.exp (Real.log (q.den : ℝ)) := (Real.exp_log hden_pos).symm
    _ ≤ Real.exp (primeCost n) := Real.exp_le_exp.mpr hlog_den


theorem content_log_le_primeCost (n : ℕ) :
    -Real.log |(content n : ℝ)| ≤ primeCost n := by
  have h : 0 < |(content n : ℝ)| := abs_pos.mpr (by exact_mod_cast content_ne_zero n)
  have hv := Real.log_le_log (inv_pos.mpr h) (content_inv_le_exp_primeCost n)
  simpa only [Real.log_inv,Real.log_exp] using hv

theorem primeExponent_coarse_bound (n p : ℕ) [Fact p.Prime] :
    primeExponent n p ≤ (640*(n : ℝ)) * (Nat.log p (84*n) : ℝ) := by
  have h := content_coarse_bound n p
  have hi : max 0 (-padicValRat p (content n)) ≤
      640*(n : ℤ)*(Nat.log p (84*n) : ℤ) := by
    apply max_le (by positivity)
    simpa [fiveRank,← mul_assoc] using h
  unfold primeExponent
  exact_mod_cast hi

theorem tinyCost_le_theta_add_higher (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0 ≤ ε) :
    (∑ p ∈ (cutoffPrimes n).filter (fun p : ℕ => (p : ℝ) ≤ ε*(n : ℝ)),
      primeExponent n p * Real.log p) ≤
      640*(n : ℝ) * Chebyshev.theta (ε*(n : ℝ)) + higherPowerCost n := by
  let ps := (cutoffPrimes n).filter (fun p : ℕ => (p : ℝ) ≤ ε*(n : ℝ))
  have hp (p : ℕ) (h : p ∈ ps) : p.Prime := (Nat.mem_primesLE.mp (mem_filter.mp h).1).2
  have hl (p : ℕ) (h : p ∈ ps) : 1 ≤ Nat.log p (84*n) := by
    apply (Nat.le_log_iff_pow_le (hp p h).one_lt (by omega : 84*n ≠ 0)).mpr
    simpa using (Nat.mem_primesLE.mp (mem_filter.mp h).1).1
  have hx (p : ℕ) (h : p ∈ ps) : 0 ≤ Real.log p :=
    Real.log_nonneg (by exact_mod_cast (hp p h).one_lt.le)
  have hsθ : ps ⊆ Nat.primesLE ⌊ε*(n : ℝ)⌋₊ := by
    intro p h
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (by positivity)).mpr (mem_filter.mp h).2, hp p h⟩
  have hsH : ps ⊆ (Finset.range (84*n+1)).filter Nat.Prime := by
    intro p h
    exact mem_filter.mpr ⟨mem_range.mpr (by
      have hh := (Nat.mem_primesLE.mp (mem_filter.mp h).1).1
      omega),hp p h⟩
  change ∑ p ∈ ps, primeExponent n p * Real.log p ≤ _
  calc
    _ ≤ ∑ p ∈ ps, (640*(n : ℝ)) *
        ((1+((Nat.log p (84*n)-1 : ℕ) : ℝ))*Real.log p) := by
      apply sum_le_sum
      intro p hh
      letI : Fact p.Prime := ⟨hp p hh⟩
      have hlog : (Nat.log p (84*n) : ℝ) = 1+((Nat.log p (84*n)-1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (hl p hh),Nat.cast_one]
        ring
      calc
        _ ≤ (640*(n : ℝ)) * (Nat.log p (84*n) : ℝ) * Real.log p :=
          mul_le_mul_of_nonneg_right (primeExponent_coarse_bound n p) (hx p hh)
        _ = _ := by rw [hlog,mul_assoc]
    _ = (640*(n : ℝ)) * (∑ p ∈ ps, Real.log p) +
        (640*(n : ℝ)) * ∑ p ∈ ps, ((Nat.log p (84*n)-1 : ℕ) : ℝ)*Real.log p := by
      simp only [Finset.mul_sum,add_mul,one_mul,mul_add,Finset.sum_add_distrib]
    _ ≤ _ := by
      rw [Chebyshev.theta_eq_sum_primesLE,← higher_power_full_sum_eq n hn]
      gcongr



theorem tiny_cost_rate (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (∑ p ∈ (cutoffPrimes n).filter (fun p : ℕ => (p : ℝ) ≤ ε*(n : ℝ)),
        primeExponent n p * Real.log p) / normalizer n ≤ (8/25 : ℝ)*ε+δ := by
  have hθ := (OddZetaPNT.scaled_theta_div_nat_limit ε hε).const_mul (8/25 : ℝ)
  have hs := hθ.add higherPowerCost_rate_zero
  have he := hs.eventually (gt_mem_nhds (show (8/25 : ℝ)*ε+0 < (8/25 : ℝ)*ε+δ by linarith))
  filter_upwards [he,eventually_gt_atTop (0 : ℕ)] with n ht hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnorm : 0 < normalizer n := by unfold normalizer; positivity
  have heq : 640*(n : ℝ)*Chebyshev.theta (ε*(n : ℝ)) / normalizer n =
      (8/25 : ℝ)*(Chebyshev.theta (ε*(n : ℝ))/(n : ℝ)) := by
    unfold normalizer
    field_simp [hnR.ne']
    ring
  refine (div_le_div_of_nonneg_right (tinyCost_le_theta_add_higher n hn ε hε.le) hnorm.le).trans ?_
  rw [add_div,heq]
  exact ht.le

/-- An unconditional coarse upper bound from all prime powers. The refined
middle and small prime densities are needed for the target rate. -/
theorem content_coarse_rate (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (-Real.log |(content n : ℝ)|) / normalizer n ≤ 672/25+δ := by
  filter_upwards [tiny_cost_rate 84 (by norm_num) δ hδ] with n h
  have he : (cutoffPrimes n).filter (fun p : ℕ => (p : ℝ) ≤ 84*(n : ℝ)) = cutoffPrimes n := by
    apply filter_eq_self.mpr
    intro p hp
    exact_mod_cast (Nat.mem_primesLE.mp hp).1
  rw [he] at h
  have hn : 0 ≤ normalizer n := by unfold normalizer; positivity
  have hc := div_le_div_of_nonneg_right (content_log_le_primeCost n) hn
  apply hc.trans
  change primeCost n / normalizer n ≤ (8/25 : ℝ)*84+δ at h
  rw [show (8/25 : ℝ)*84 = 672/25 by norm_num] at h
  exact h

end OddZetaSix.B40a
