import OddZetaSix.B40a.Arithmetic.SmallBandRate

noncomputable section
namespace OddZetaSix.B40a
open Finset Filter

private theorem band_as_cutoff (n : ℕ) (a b : ℝ) (hb : 0≤b) (hmax : b≤84) :
    bandPrimeCost n a b = ∑ p ∈ (cutoffPrimes n).filter
      (fun p : ℕ => a*n < (p:ℝ) ∧ (p:ℝ) ≤ b*n),primeExponent n p * Real.log p := by
  unfold bandPrimeCost cutoffPrimes
  congr 1
  ext p
  simp only [Finset.mem_filter,Nat.mem_primesLE, Nat.le_floor_iff (mul_nonneg hb (Nat.cast_nonneg n))]
  constructor
  · rintro ⟨⟨hl,hp⟩,hlo⟩
    have h : (p:ℝ) ≤ 84*n := hl.trans (mul_le_mul_of_nonneg_right hmax (Nat.cast_nonneg n))
    exact ⟨⟨by exact_mod_cast h,hp⟩,hlo,hl⟩
  · exact fun h => ⟨⟨h.2.2,h.1.2⟩,h.2.1⟩

theorem small_prime_cost_rate (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ n : ℕ in atTop,
      (∑ p ∈ (cutoffPrimes n).filter (fun p : ℕ => (p:ℝ)≤11/20*n),
        primeExponent n p * Real.log p) / normalizer n ≤ 60166783595/1000000000000+δ := by
  let K := max 17 (⌈1/δ⌉₊+1)
  have hK : 17≤K := le_max_left _ _
  have hKr : (17:ℝ)≤K := by exact_mod_cast hK
  have hKpos : (0:ℝ)<K := by linarith
  have hBig : 1/δ < (K:ℝ) := by
    have h := Nat.le_ceil (1/δ)
    have h' : ((⌈1/δ⌉₊:ℝ)+1) ≤ K := by exact_mod_cast (le_max_right 17 (⌈1/δ⌉₊+1))
    linarith only [h,h']
  let ε := 1/(K:ℝ)
  have hε := one_div_pos.mpr hKpos
  have hεδ : ε < δ := (div_lt_iff₀ hKpos).mpr (by
    have := (div_lt_iff₀ hδ).mp hBig; linarith)
  have he := tiny_cost_rate ε hε (δ/4) (by positivity)
  have hc := small_prime_cutoff_rate K hK (δ/4) (by positivity)
  filter_upwards [he,hc] with n he hc
  let S := (cutoffPrimes n).filter (fun p : ℕ => (p:ℝ)≤11/20*n)
  let w := fun p : ℕ => primeExponent n p*Real.log p
  have hsum := Finset.sum_filter_add_sum_filter_not S (fun p : ℕ => (p:ℝ)≤ε*n) w
  have h1 : (∑ p ∈ S.filter (fun p : ℕ => (p:ℝ)≤ε*n),w p) ≤
      ∑ p ∈ (cutoffPrimes n).filter (fun p : ℕ => (p:ℝ)≤ε*n),w p := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩
    · intro p hp _
      have hp' := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
      exact mul_nonneg (primeExponent_nonneg n p) (Real.log_nonneg (by exact_mod_cast hp'.one_lt.le))
  have ht : (∑ p ∈ S.filter (fun p : ℕ => ¬(p:ℝ)≤ε*n),w p) = bandPrimeCost n ε (11/20) := by
    rw [band_as_cutoff _ _ _ (by norm_num) (by norm_num)]
    change (∑ p ∈ S.filter _, w p) = ∑ p ∈ (cutoffPrimes n).filter _,w p
    congr 1
    ext p
    simp [S,and_assoc,and_comm]
  rw [ht] at hsum
  change (∑ p ∈ S,w p) / normalizer n ≤ _
  rw [←hsum,add_div]
  have hnorm : 0≤normalizer n := by unfold normalizer; positivity
  have h1' := (div_le_div_of_nonneg_right h1 hnorm).trans he
  change bandPrimeCost n ε (11/20)/normalizer n ≤ _ at hc
  linarith only [h1',hc,hεδ,hδ]

end OddZetaSix.B40a
