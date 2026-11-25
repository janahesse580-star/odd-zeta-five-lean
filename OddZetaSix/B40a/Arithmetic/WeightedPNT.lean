import OddZetaSix.B40a.Arithmetic.PrimeSums

/-! The PNT summation bridge for B40a's actual prime costs, adapted from the
MIT-licensed upstream SixPNTBridge. -/
noncomputable section
namespace OddZetaSix.B40a
open Finset Filter
open scoped BigOperators Topology Interval

theorem primeExponent_mul_log_coarse (n p : ℕ) [Fact p.Prime] (hn : 0 < n) :
    primeExponent n p * Real.log (p : ℝ) ≤ 640 * (n : ℝ) * Real.log (84 * (n : ℝ)) := by
  have hp : p.Prime := Fact.out
  have hexp_le := primeExponent_coarse_bound n p
  have hpow_le : (p : ℝ) ^ (Nat.log p (84 * n)) ≤ 84 * (n : ℝ) := by
    have hnat : p ^ (Nat.log p (84 * n)) ≤ 84 * n := Nat.pow_log_le_self p (by omega)
    exact_mod_cast hnat
  have hlog_mul : (Nat.log p (84 * n) : ℝ) * Real.log (p : ℝ) ≤ Real.log (84 * (n : ℝ)) := by
    have hppos : (0 : ℝ) < (p : ℝ) ^ (Nat.log p (84 * n)) := by
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
      positivity
    rw [← Real.log_pow]
    exact Real.log_le_log hppos hpow_le
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  calc
    primeExponent n p * Real.log (p : ℝ)
        ≤ (640 * (n : ℝ) * (Nat.log p (84 * n) : ℝ)) * Real.log (p : ℝ) :=
      mul_le_mul_of_nonneg_right hexp_le hlogp
    _ = 640 * (n : ℝ) * ((Nat.log p (84 * n) : ℝ) * Real.log (p : ℝ)) := by ring
    _ ≤ 640 * (n : ℝ) * Real.log (84 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_mul (by positivity)

theorem exceptionalPrimes_rate_zero (E : ℕ → Finset ℕ) (M : ℕ)
    (hsub : ∀ n, E n ⊆ cutoffPrimes n)
    (hcard : ∀ᶠ n : ℕ in atTop, (E n).card ≤ M) :
    Tendsto (fun n : ℕ =>
      (∑ p ∈ E n, primeExponent n p * Real.log (p : ℝ)) / normalizer n) atTop (nhds 0) := by
  have hlog_div : Tendsto (fun n : ℕ =>
      (640 * (M : ℝ) / 2000 : ℝ) * (Real.log (84 * (n : ℝ)) / (n : ℝ))) atTop (nhds 0) := by
    have h84 : Tendsto (fun n : ℕ => 84*(n : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
    have h0 := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp h84
    have h1 : Tendsto (fun n : ℕ => Real.log (84 * (n : ℝ)) / (n : ℝ)) atTop (nhds 0) := by
      have hh := h0.const_mul 84
      simp only [mul_zero,Function.comp_apply,id_eq] at hh
      refine hh.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    simpa using h1.const_mul (640 * (M : ℝ) / 2000 : ℝ)
  refine squeeze_zero' ?_ ?_ hlog_div
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n _
    apply div_nonneg _ (by unfold normalizer; positivity : 0 ≤ normalizer n)
    apply Finset.sum_nonneg
    intro p hp
    have hpr : p.Prime := (Nat.mem_primesLE.mp (hsub n hp)).2
    exact mul_nonneg (primeExponent_nonneg n p)
      (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
  · filter_upwards [hcard, eventually_ge_atTop (1 : ℕ)] with n hc hn
    have hsum : (∑ p ∈ E n, primeExponent n p * Real.log (p : ℝ)) ≤
        (M : ℝ) * (640 * (n : ℝ) * Real.log (84 * (n : ℝ))) := by
      calc
        _ ≤ ∑ _p ∈ E n, (640 * (n : ℝ) * Real.log (84 * (n : ℝ))) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpr : p.Prime := (Nat.mem_primesLE.mp (hsub n hp)).2
          have : Fact p.Prime := ⟨hpr⟩
          exact primeExponent_mul_log_coarse n p hn
        _ = ((E n).card : ℝ) * (640 * (n : ℝ) * Real.log (84 * (n : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (M : ℝ) * (640 * (n : ℝ) * Real.log (84 * (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast hc)
          have : (1 : ℝ) ≤ 84 * (n : ℝ) := by
            have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            linarith
          have := Real.log_nonneg this
          positivity
    unfold normalizer
    have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h2000 : 0 < 2000 * (n : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ h2000]
    calc
      _ ≤ (M : ℝ) * (640 * (n : ℝ) * Real.log (84 * (n : ℝ))) := hsum
      _ = (640 * (M : ℝ) / 2000 : ℝ) * (Real.log (84 * (n : ℝ)) / (n : ℝ)) *
            (2000 * (n : ℝ) ^ 2) := by
        field_simp [hnPos.ne']

/-- Finite piecewise tile sum bound: if `(a, b]` is partitioned by finitely many tiles `i ∈ s`
each admitting a continuous nonnegative majorant `f i`, then `bandPrimeCost n a b / normalizer n`
has asymptotic upper rate `≤ (∑ i ∈ s, ∫ x in a_i..b_i, f_i x) / 2000`. -/
theorem bandPrimeCost_rate_of_piecewise_majorant {ι : Type*} (s : Finset ι)
    (a b : ℝ) (_ha : 0 < a) (_hab : a ≤ b)
    (lo hi : ι → ℝ) (f : ι → ℝ → ℝ)
    (hlo : ∀ i ∈ s, 0 < lo i) (hlohi : ∀ i ∈ s, lo i ≤ hi i) (_hhi55 : ∀ i ∈ s, hi i ≤ 84)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (Set.Icc (lo i) (hi i)))
    (hf0 : ∀ i ∈ s, ∀ x ∈ Set.Icc (lo i) (hi i), 0 ≤ f i x)
    (C : ℝ) (hC0 : 0 ≤ C) (E : ℕ → Finset ℕ) (M : ℕ)
    (hEsub : ∀ n, E n ⊆ cutoffPrimes n)
    (hEcard : ∀ᶠ n : ℕ in atTop, (E n).card ≤ M)
    (hcover : ∀ᶠ n : ℕ in atTop,
      ∀ p ∈ (Nat.primesLE ⌊b * (n : ℝ)⌋₊).filter (fun p : ℕ => a * (n : ℝ) < (p : ℝ)),
        p ∉ E n →
        ∃ i ∈ s, lo i * (n : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ hi i * (n : ℝ) ∧
          primeExponent n p ≤ (n : ℝ) * f i ((p : ℝ) / (n : ℝ)) + C) :
    ∀ δ > 0, ∀ᶠ n : ℕ in atTop,
      bandPrimeCost n a b / normalizer n ≤ (∑ i ∈ s, ∫ x in lo i..hi i, f i x) / 2000 + δ := by
  intro δ hδ
  classical
  let w : ι → ℕ → ℕ → ℝ := fun i n p => (n : ℝ) * f i ((p : ℝ) / (n : ℝ)) + C
  have hsum_lim : Tendsto (fun n : ℕ =>
      (∑ i ∈ s, OddZetaPNT.primeBandCost (w i) n (lo i) (hi i)) / 2000)
      atTop (nhds ((∑ i ∈ s, ∫ x in lo i..hi i, f i x) / 2000)) := by
    apply Tendsto.div_const
    apply tendsto_finsetSum
    intro i hi'
    have hcont := OddZetaPNT.primeWeightedInterval_continuous_limit (f i) (lo i) (hi i)
      (hlo i hi') (hlohi i hi') (hf i hi')
    apply OddZetaPNT.primeBandCost_bounded_perturbation_limit (w i) (f i) (lo i) (hi i) |C| _
      (hlo i hi') (hlohi i hi') hcont
    filter_upwards with n p _
    dsimp [w]; simp
  have hexc_lim := exceptionalPrimes_rate_zero E M hEsub hEcard
  have hw_ev := Metric.tendsto_nhds.mp hsum_lim (δ / 2) (by positivity)
  have hexc_ev := Metric.tendsto_nhds.mp hexc_lim (δ / 2) (by positivity)
  filter_upwards [hcover, hw_ev, hexc_ev, eventually_ge_atTop (1 : ℕ)] with n hcoverN hwe hee hn
  have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnorm_pos : 0 < normalizer n := by unfold normalizer; positivity
  let S := (Nat.primesLE ⌊b * (n : ℝ)⌋₊).filter (fun p : ℕ => a * (n : ℝ) < (p : ℝ))
  let Si : ι → Finset ℕ := fun i =>
    (Nat.primesLE ⌊hi i * (n : ℝ)⌋₊).filter (fun p : ℕ => lo i * (n : ℝ) < (p : ℝ))
  have hw_nonneg : ∀ i ∈ s, ∀ p ∈ Si i, 0 ≤ w i n p * Real.log (p : ℝ) := by
    intro i hi' p hp
    have hmem := Finset.mem_filter.mp hp
    have hpr : p.Prime := (Nat.mem_primesLE.mp hmem.1).2
    have hbp : (p : ℝ) ≤ hi i * (n : ℝ) :=
      (Nat.le_floor_iff (mul_nonneg ((hlo i hi').le.trans (hlohi i hi')) hnPos.le)).mp
        (Nat.mem_primesLE.mp hmem.1).1
    have hx : (p : ℝ) / (n : ℝ) ∈ Set.Icc (lo i) (hi i) :=
      ⟨((lt_div_iff₀ hnPos).mpr hmem.2).le, (div_le_iff₀ hnPos).mpr hbp⟩
    have hfval : 0 ≤ f i ((p : ℝ) / (n : ℝ)) := hf0 i hi' _ hx
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
    dsimp [w]; positivity
  have hsum_le : bandPrimeCost n a b ≤
      (∑ i ∈ s, ∑ p ∈ Si i, w i n p * Real.log (p : ℝ)) +
      (∑ p ∈ E n, primeExponent n p * Real.log (p : ℝ)) := by
    unfold bandPrimeCost
    have hpart := (Finset.sum_filter_add_sum_filter_not S (fun p => p ∈ E n)
      (fun p => primeExponent n p * Real.log (p : ℝ))).symm
    rw [hpart, add_comm]
    apply add_le_add
    · calc
        ∑ p ∈ S.filter (fun p => p ∉ E n), primeExponent n p * Real.log (p : ℝ)
            ≤ ∑ p ∈ S.filter (fun p => p ∉ E n),
                ∑ i ∈ s, if p ∈ Si i then w i n p * Real.log (p : ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro p hp
          have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
          have hpE : p ∉ E n := (Finset.mem_filter.mp hp).2
          have hpr : p.Prime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hpS).1).2
          obtain ⟨i₀, hi₀, hlo', hhi', hdom'⟩ := hcoverN p hpS hpE
          have hpSi : p ∈ Si i₀ := by
            rw [Finset.mem_filter, Nat.mem_primesLE]
            exact ⟨⟨(Nat.le_floor_iff (mul_nonneg ((hlo i₀ hi₀).le.trans (hlohi i₀ hi₀)) hnPos.le)).mpr hhi',
              hpr⟩, hlo'⟩
          have h1 : primeExponent n p * Real.log (p : ℝ) ≤
              (if p ∈ Si i₀ then w i₀ n p * Real.log (p : ℝ) else 0) := by
            simp only [hpSi, ite_true]
            exact mul_le_mul_of_nonneg_right hdom'
              (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
          have h2 : (if p ∈ Si i₀ then w i₀ n p * Real.log (p : ℝ) else 0) ≤
              ∑ i ∈ s, if p ∈ Si i then w i n p * Real.log (p : ℝ) else 0 :=
            Finset.single_le_sum
              (f := fun i => if p ∈ Si i then w i n p * Real.log (p : ℝ) else 0)
              (fun i hi' => by
                split_ifs with hmem
                · exact hw_nonneg i hi' p hmem
                · exact le_rfl)
              hi₀
          exact h1.trans h2
        _ = ∑ i ∈ s, ∑ p ∈ S.filter (fun p => p ∉ E n),
              if p ∈ Si i then w i n p * Real.log (p : ℝ) else 0 := Finset.sum_comm
        _ ≤ ∑ i ∈ s, ∑ p ∈ Si i, w i n p * Real.log (p : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi'
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp; exact (Finset.mem_filter.mp hp).2
          · intro p hp _; exact hw_nonneg i hi' p hp
    · apply Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).2)
      intro p hp _
      have hpr : p.Prime := (Nat.mem_primesLE.mp (hEsub n hp)).2
      exact mul_nonneg (primeExponent_nonneg n p)
        (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
  have hdiv_w : (∑ i ∈ s, ∑ p ∈ Si i, w i n p * Real.log (p : ℝ)) / normalizer n =
      (∑ i ∈ s, OddZetaPNT.primeBandCost (w i) n (lo i) (hi i)) / 2000 := by
    rw [normalizer, Finset.sum_div]
    unfold OddZetaPNT.primeBandCost
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    have hn2 : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hnPos.ne'
    dsimp [Si]
    field_simp [hn2]
  rw [Real.dist_eq] at hwe hee
  rw [sub_zero] at hee
  have hwe' : (∑ i ∈ s, OddZetaPNT.primeBandCost (w i) n (lo i) (hi i)) / 2000 ≤
      (∑ i ∈ s, ∫ x in lo i..hi i, f i x) / 2000 + δ / 2 := by
    have := (le_abs_self _).trans hwe.le
    linarith
  have hee' : (∑ p ∈ E n, primeExponent n p * Real.log (p : ℝ)) / normalizer n ≤ δ / 2 :=
    (le_abs_self _).trans hee.le
  calc
    bandPrimeCost n a b / normalizer n
        ≤ ((∑ i ∈ s, ∑ p ∈ Si i, w i n p * Real.log (p : ℝ)) +
            (∑ p ∈ E n, primeExponent n p * Real.log (p : ℝ))) / normalizer n :=
      div_le_div_of_nonneg_right hsum_le hnorm_pos.le
    _ = (∑ i ∈ s, ∑ p ∈ Si i, w i n p * Real.log (p : ℝ)) / normalizer n +
        (∑ p ∈ E n, primeExponent n p * Real.log (p : ℝ)) / normalizer n := add_div _ _ _
    _ = (∑ i ∈ s, OddZetaPNT.primeBandCost (w i) n (lo i) (hi i)) / 2000 +
        (∑ p ∈ E n, primeExponent n p * Real.log (p : ℝ)) / normalizer n := by rw [hdiv_w]
    _ ≤ (∑ i ∈ s, ∫ x in lo i..hi i, f i x) / 2000 + δ := by linarith


end OddZetaSix.B40a
