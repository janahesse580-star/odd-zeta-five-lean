import OddZetaSix.SixHighWalls
import OddZetaSix.B40a.Arithmetic.MiddleBoundary

namespace OddZetaSix.B40a
open OddZetaSix.CertCore

/-- Rank-40 specialization of the layer count in SixHighWalls. -/
theorem middle_row_penalty_le (n p q K : ℕ) (hn : 0 < n) (hp : 0 < p)
    (hqk : q ≤ K) (hK : 80 * n / p = K) :
    2 * (sixRowPenalty (fiveRank n) p q : ℝ) ≤
      (n : ℝ) * ((80 * ((K - q : ℕ) : ℝ)) - ((sumRangeIcc q K : ℕ) : ℝ) * ((p : ℝ) / (n : ℝ))) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr : fiveRank n = 40 * n := rfl
  have hsub_sum : ∀ m : ℕ, m ≤ K →
      m - q = ∑ k ∈ Finset.Icc (q + 1) K, if k ≤ m then 1 else 0 := by
    intro m hm
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    have heq : (Finset.Icc (q + 1) K).filter (fun k => k ≤ m) = Finset.Icc (q + 1) m := by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [heq, Nat.card_Icc]; omega
  have hpen_eq : sixRowPenalty (fiveRank n) p q =
      ∑ k ∈ Finset.Icc (q + 1) K,
        ((Finset.range (40 * n)).filter (fun i => k ≤ 2 * i / p)).card := by
    unfold sixRowPenalty
    rw [hr, Fin.sum_univ_eq_sum_range (fun i => 2 * i / p - q)]
    have h1 : (∑ i ∈ Finset.range (40 * n), (2 * i / p - q)) =
        ∑ i ∈ Finset.range (40 * n), ∑ k ∈ Finset.Icc (q + 1) K,
          if k ≤ 2 * i / p then 1 else 0 := by
      apply Finset.sum_congr rfl; intro i hi
      have hilt : i < 40 * n := Finset.mem_range.mp hi
      have hle : 2 * i / p ≤ K := by
        rw [← hK]; exact Nat.div_le_div_right (by omega)
      exact hsub_sum _ hle
    rw [h1, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  have hterm_le : ∀ k ∈ Finset.Icc (q + 1) K,
      2 * (((Finset.range (40 * n)).filter (fun i => k ≤ 2 * i / p)).card : ℝ) ≤
        80 * (n : ℝ) - (k : ℝ) * (p : ℝ) := by
    intro k hk
    have hk_le : k ≤ K := (Finset.mem_Icc.mp hk).2
    have hkp : k * p ≤ 80 * n := by
      calc k * p ≤ K * p := Nat.mul_le_mul_right p hk_le
        _ = (80 * n / p) * p := by rw [hK]
        _ ≤ 80 * n := Nat.div_mul_le_self (80 * n) p
    let a := (k * p + 1) / 2
    have hsub : (Finset.range (40 * n)).filter (fun i => k ≤ 2 * i / p) ⊆
        Finset.Ico a (40 * n) := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      have hmul : k * p ≤ 2 * i := (Nat.le_div_iff_mul_le hp).mp hi.2
      exact Finset.mem_Ico.mpr ⟨by dsimp [a]; omega, hi.1⟩
    have hcard : ((Finset.range (40 * n)).filter (fun i => k ≤ 2 * i / p)).card ≤ 40 * n - a := by
      exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Ico])
    have h2a : k * p ≤ 2 * a := by dsimp [a]; omega
    have h2c : 2 * ((Finset.range (40 * n)).filter (fun i => k ≤ 2 * i / p)).card + k * p ≤ 80 * n := by
      omega
    have h2cR : 2 * (((Finset.range (40 * n)).filter (fun i => k ≤ 2 * i / p)).card : ℝ) +
        (k : ℝ) * (p : ℝ) ≤ 80 * (n : ℝ) := by exact_mod_cast h2c
    linarith
  have hsum : 2 * (sixRowPenalty (fiveRank n) p q : ℝ) ≤
      ∑ k ∈ Finset.Icc (q + 1) K, (80 * (n : ℝ) - (k : ℝ) * (p : ℝ)) := by
    rw [hpen_eq, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum hterm_le
  have hcardIcc : (Finset.Icc (q + 1) K).card = K - q := by rw [Nat.card_Icc]; omega
  have hrhs : (∑ k ∈ Finset.Icc (q + 1) K, (80 * (n : ℝ) - (k : ℝ) * (p : ℝ))) =
      (n : ℝ) * ((80 * ((K - q : ℕ) : ℝ)) - ((sumRangeIcc q K : ℕ) : ℝ) * ((p : ℝ) / (n : ℝ))) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcardIcc,
      ← Finset.sum_mul, ← Nat.cast_sum, ← sumRangeIcc_eq q K hqk]
    field_simp [hnR.ne']
  linarith


/-- The triangular number in Cert.middleValue uses a single division
after multiplication. It agrees exactly with the integer layer sum. -/
theorem middle_sum_range (q K : ℕ) (hk : q≤K) :
    sumRangeIcc q K=(K+q+1)*(K-q)/2 := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left]
  unfold sumRangeIcc
  have hz (k : ℕ) : 2*(k*(k+1)/2)=k*(k+1) := by
    rcases Nat.even_or_odd k with ⟨a,rfl⟩|⟨a,rfl⟩
    · rw [show (a+a)*(a+a+1)=2*(a*(a+a+1)) by ring]; omega
    · rw [show (2*a+1)*(2*a+1+1)=2*((2*a+1)*(a+1)) by ring]; omega
  have he : (q+s)*(q+s+1)=q*(q+1)+(q+s+q+1)*s := by ring
  have h := hz (q+s)
  have hq := hz q
  omega

theorem middle_certificate_row_penalty (n p q K : ℕ) (hn : 0<n) (hp : 0<p)
    (hq : q≤K) (hK : 80*n/p=K) :
    2*(sixRowPenalty (fiveRank n) p q:ℝ) ≤
      80*(n:ℝ)*(K-q:ℕ)-(p:ℝ)*((K+q+1)*(K-q)/2 : ℕ) := by
  have h := middle_row_penalty_le n p q K hn hp hq hK
  rw [middle_sum_range q K hq] at h
  convert h using 1
  field_simp [show (n:ℝ)≠0 by positivity]
  <;> ring

end OddZetaSix.B40a
