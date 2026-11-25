import OddZetaSix.B40a.Arithmetic.SmallPrimeRate
import OddZetaSix.B40a.Arithmetic.PartialRate

namespace OddZetaSix.B40a
open Finset Filter

theorem primeCost_three_bands (n : ℕ) :
    primeCost n = (∑ p ∈ (cutoffPrimes n).filter (fun p : ℕ => (p:ℝ)≤11/20*n),
      primeExponent n p * Real.log p) + bandPrimeCost n (11/20) 50 + bandPrimeCost n 50 84 := by
  rw [primeCost_split_at_50]
  congr 1
  let S := (cutoffPrimes n).filter (fun p : ℕ => (p:ℝ)≤50*n)
  let w := fun p : ℕ => primeExponent n p*Real.log p
  have hsplit := sum_filter_add_sum_filter_not S (fun p : ℕ => (p:ℝ)≤11/20*n) w
  have hs : S.filter (fun p : ℕ => (p:ℝ)≤11/20*n) =
      (cutoffPrimes n).filter (fun p : ℕ => (p:ℝ)≤11/20*n) := by
    ext p
    simp only [S,mem_filter]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · exact fun h => ⟨⟨h.1,by linarith [h.2,Nat.cast_nonneg (α:=ℝ) n]⟩,h.2⟩
  have hm : (∑ p ∈ S.filter (fun p : ℕ => ¬(p:ℝ)≤11/20*n),w p) = bandPrimeCost n (11/20) 50 := by
    unfold bandPrimeCost
    congr 1
    ext p
    simp only [S,cutoffPrimes,mem_filter,Nat.mem_primesLE,not_le,
      Nat.le_floor_iff (show (0:ℝ)≤50*n by positivity)]
    constructor
    · exact fun h => ⟨⟨h.1.2,h.1.1.2⟩,h.2⟩
    · intro h
      have hpr : (p:ℝ) ≤ 84*n := by linarith [h.1.1,Nat.cast_nonneg (α:=ℝ) n]
      exact ⟨⟨⟨by exact_mod_cast hpr,h.1.2⟩,h.1.1⟩,h.2⟩
  rw [hs,hm] at hsplit
  exact hsplit.symm

/-- Subtract the explicit, true middle-band cost from the true content cost.
This gives an unconditional bound for the two complementary prime bands. -/
theorem content_cost_outside_middle (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ n : ℕ in atTop, (-Real.log |(content n:ℝ)| - bandPrimeCost n (11/20) 50)/normalizer n
      ≤ 895666783595/1000000000000+δ := by
  filter_upwards [small_prime_cost_rate (δ/2) (by positivity),
    high_prime_cost_rate (δ/2) (by positivity)] with n hs hh
  have hc := div_le_div_of_nonneg_right (content_log_le_primeCost n)
    (show 0≤normalizer n by unfold normalizer; positivity)
  rw [primeCost_three_bands,add_div,add_div] at hc
  rw [sub_div]
  linarith only [hc,hs,hh]

end OddZetaSix.B40a
