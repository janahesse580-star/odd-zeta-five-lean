import OddZetaSix.B40a.Arithmetic.FoldedCapacity
import OddZetaSix.B40a.Arithmetic.Periodic

/-! Exact periodic slot summation for the B40a small-prime majorant. -/
noncomputable section
namespace OddZetaSix.B40a
open Finset
open scoped BigOperators

theorem periodicCount_bounds (a b : ℤ) (τ u : ℝ) : 0 ≤ periodicCount a b τ u ∧ periodicCount a b τ u ≤ 1 := by
  have h : (b : ℝ)*τ-u = (a : ℝ)*τ-u + (((b-a : ℤ) : ℝ)*τ) := by push_cast; ring
  unfold periodicCount
  rw [h]
  have hl := Int.le_floor_add ((a : ℝ)*τ-u) (((b-a : ℤ) : ℝ)*τ)
  have hu := Int.le_floor_add_floor ((a : ℝ)*τ-u) (((b-a : ℤ) : ℝ)*τ)
  omega

theorem periodicScore_bounds (τ u : ℝ) : 0 ≤ periodicScore τ u ∧ periodicScore τ u ≤ 16 := by
  have h1 := periodicCount_bounds (-25) 25 τ u
  have h2 := periodicCount_bounds (-17) 17 τ u
  have h3 := periodicCount_bounds (-16) 16 τ u
  have h4 := periodicCount_bounds (-59) (-34) τ u
  have h5 := periodicCount_bounds 34 59 τ u
  exact ⟨le_max_left _ _,max_le (by decide) (by omega)⟩

def slotEnvelope (q B : ℕ) : ℕ := (q+1)*B + (B-1)^2/4

theorem slotEnvelope_eq_sum (q B : ℕ) (hB : B ≤ 16) :
    ∑ j ∈ range (q+1+8), (B-2*(j-q)) = slotEnvelope q B := by
  rw [Finset.sum_range_add]
  have h1 : (∑ j ∈ range (q+1), (B-2*(j-q))) = (q+1)*B := by
    calc
      _ = ∑ _j ∈ range (q+1), B := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := mem_range.mp hj
        simp [show j-q=0 by omega]
      _ = _ := by simp
  rw [h1]
  simp only [show ∀ k : ℕ, q+1+k-q = k+1 from fun k => by omega]
  unfold slotEnvelope
  congr 1
  interval_cases B <;> decide

theorem slotEnvelope_prefix (q B l : ℕ) (hB : B ≤ 16) :
    (∑ j ∈ range l, ((B : ℤ)-2*((j-q : ℕ) : ℤ))) ≤ (slotEnvelope q B : ℤ) := by
  have ht (j : ℕ) : (B : ℤ)-2*((j-q : ℕ) : ℤ) ≤ ((B-2*(j-q) : ℕ) : ℤ) := by omega
  have hh : (∑ j ∈ range (max l (q+1+8)), ((B-2*(j-q) : ℕ) : ℤ)) = (slotEnvelope q B : ℤ) := by
    rw [← Finset.sum_subset (Finset.range_mono (le_max_right l (q+1+8)))]
    · exact_mod_cast slotEnvelope_eq_sum q B hB
    · intro j _ hnj
      have hj : q+1+8 ≤ j := Nat.not_lt.mp (fun h => hnj (mem_range.mpr h))
      simp [show B-2*(j-q) = 0 by omega]
  calc
    _ ≤ ∑ j ∈ range l, ((B-2*(j-q) : ℕ) : ℤ) := Finset.sum_le_sum (fun j _ => ht j)
    _ ≤ _ := hh ▸ Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left _ _))
      (fun _ _ _ => by positivity)

theorem folded_periodic_exact_formalValAtLeast {p h m : ℕ} [Fact p.Prime]
    (hsq : 2 * h < p ^ 2)
    (x : Fin m → ℤ) (a : Fin m → ℕ)
    (W : Matrix (Fin m) (Fin m) FivePolynomial)
    (B : Fin m → ℕ)
    (B_max : Fin (p / 2 + 1) → ℕ)
    (hB_dom : ∀ u : Fin m, B u ≤ B_max (foldMod p (Fact.out : p.Prime).pos (x u)))
    (hB16 : ∀ c : Fin (p / 2 + 1), B_max c ≤ 16)
    (hW : ∀ u v : Fin m, DoubledFormalValAtLeast p (-((B u + B v : ℕ) : ℤ)) (W u v)) :
    let U : ℤ := ∑ c : Fin (p / 2 + 1), (slotEnvelope (2*h/p) (B_max c) : ℤ)
    FormalValAtLeast p (-U)
      ((evalJetMatrix p h m x a).map MvPolynomial.C * W *
        ((evalJetMatrix p h m x a).map MvPolynomial.C).transpose).det := by
  intro U
  let hp := (Fact.out : p.Prime).pos
  let q := 2 * h / p
  apply doubled_cauchy_binet_formalValAtLeast (evalJetMatrix p h m x a) W B U hW
  intro I hI hne
  have hscaled_val := valAtLeast_folded_scaledJetMinor (p := p) (q := q) hsq x a I hI
  have hscaled_ne : ((scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI)).det ≠ 0 := by
    have hsub : (scaledJetMatrix p h m q x a).submatrix id (subsetEmb I hI) =
        Matrix.diagonal (fun i : Fin h => (p : ℚ) ^ (2 * i.val / p - q)) *
          (evalJetMatrix p h m x a).submatrix id (subsetEmb I hI) := by
      ext i j; simp [scaledJetMatrix, Matrix.diagonal_mul]
    rw [hsub, Matrix.det_mul, Matrix.det_diagonal]
    have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ hpne)) hne
  have hval_ge := valAtLeast_of_ne_zero hscaled_val hscaled_ne
  rw [padicValRat_scaledJetMinor x a I hI hne, sixRowPenalty_eq_zero_of_ge h p q le_rfl,
    Nat.cast_zero, zero_add] at hval_ge
  let I_c : Fin (p / 2 + 1) → Finset (Fin m) :=
    fun c => I.filter (fun u => foldMod p hp (x u) = c)
  have hI_part : (∑ u ∈ I, (B u : ℤ)) = ∑ c : Fin (p / 2 + 1), ∑ u ∈ I_c c, (B u : ℤ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun u => foldMod p hp (x u))
      (fun _ _ => Finset.mem_univ _)]
  have hclass_bound : ∀ c : Fin (p / 2 + 1),
      (∑ u ∈ I_c c, (B u : ℤ)) - 2 * (∑ r ∈ range (I_c c).card, ((r - q : ℕ) : ℤ)) ≤
        (slotEnvelope q (B_max c) : ℤ) := by
    intro c
    have hBsum : (∑ u ∈ I_c c, (B u : ℤ)) ≤ ((I_c c).card : ℤ) * (B_max c : ℤ) := by
      calc
        (∑ u ∈ I_c c, (B u : ℤ))
            ≤ ∑ _u ∈ I_c c, (B_max c : ℤ) := by
              apply Finset.sum_le_sum; intro u hu
              have huc := (Finset.mem_filter.mp hu).2
              exact_mod_cast (huc ▸ hB_dom u)
        _ = ((I_c c).card : ℤ) * (B_max c : ℤ) := by simp
    have hrew : ((I_c c).card : ℤ) * (B_max c : ℤ) -
        2 * (∑ r ∈ range (I_c c).card, ((r - q : ℕ) : ℤ)) =
        ∑ r ∈ range (I_c c).card, ((B_max c : ℤ) - 2 * ((r - q : ℕ) : ℤ)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum]
    have hprefix_le := slotEnvelope_prefix q (B_max c) (I_c c).card (hB16 c)
    linarith
  have hsum_all := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (p / 2 + 1))))
    (fun c _ => hclass_bound c)
  rw [Finset.sum_sub_distrib, ← hI_part, ← Finset.mul_sum] at hsum_all
  dsimp only [U]
  linarith


end OddZetaSix.B40a
