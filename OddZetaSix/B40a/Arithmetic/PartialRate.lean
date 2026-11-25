import OddZetaSix.B40a.Arithmetic.HighTailRate

/-! An unconditional rate using the sharp high band and the universal bound
below it. The separate certificate-based middle and small rates are needed
to improve this bound to 61405 / 10000. -/
noncomputable section
namespace OddZetaSix.B40a
open Finset Filter
open scoped BigOperators Topology

theorem primeCost_split_at_50 (n : ℕ) :
    primeCost n =
      (∑ p ∈ (cutoffPrimes n).filter (fun p : ℕ => (p : ℝ) ≤ 50*(n : ℝ)),
        primeExponent n p * Real.log p) + bandPrimeCost n 50 84 := by
  unfold primeCost bandPrimeCost cutoffPrimes
  have hfloor : ⌊84*(n : ℝ)⌋₊ = 84*n := by
    rw [← Nat.cast_ofNat (R := ℝ),← Nat.cast_mul,Nat.floor_natCast]
  rw [hfloor]
  rw [← sum_filter_add_sum_filter_not (Nat.primesLE (84*n))
    (fun p : ℕ => (p : ℝ) ≤ 50*(n : ℝ))]
  simp only [not_le]

theorem content_rate_with_high_tail (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ n : ℕ in atTop,
      (-Real.log |(content n : ℝ)|) / normalizer n ≤ 33671/2000+δ := by
  filter_upwards [tiny_cost_rate 50 (by norm_num) (δ/2) (by positivity),
    high_prime_cost_rate (δ/2) (by positivity)] with n h₁ h₂
  have h0 : 0 ≤ normalizer n := by unfold normalizer; positivity
  have hc := div_le_div_of_nonneg_right (content_log_le_primeCost n) h0
  rw [primeCost_split_at_50,add_div] at hc
  linarith only [hc,h₁,h₂]

end OddZetaSix.B40a
