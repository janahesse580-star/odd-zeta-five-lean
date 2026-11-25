import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open scoped BigOperators

set_option linter.style.haveILetI false

namespace OddZetaSix.B40a

def jetBlock : Matrix (Fin 5) (Fin 5) ℤ :=
  fun a b => (Nat.choose (9 - (a.val + b.val)) 4 : ℤ)

theorem jetBlock_det : Matrix.det (jetBlock : Matrix (Fin 5) (Fin 5) ℤ) = 1 := by
  norm_num [Matrix.det_succ_row_zero, Matrix.det_fin_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, jetBlock, Nat.choose] <;> decide +kernel

theorem jetBlock_mod_det (p : ℕ) :
    ((jetBlock : Matrix (Fin 5) (Fin 5) ℤ).map (Int.castRingHom (ZMod p))).det = 1 := by
  change ((Int.castRingHom (ZMod p)).mapMatrix jetBlock).det = 1
  rw [← RingHom.map_det, jetBlock_det, map_one]

/-- Legendre's formula collapses to its first layer below twice the prime. -/
theorem factorial_val_lt_twice (p m : ℕ) [Fact p.Prime] (hm : m < 2 * p) :
    padicValNat p m.factorial = if p ≤ m then 1 else 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [← padicValNat_mul_div_factorial, padicValNat_factorial_mul]
  split_ifs with h
  · have hq : m / p = 1 := by
      apply Nat.le_antisymm
      · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp).2 (by simpa [Nat.mul_comm] using hm))
      · exact (Nat.le_div_iff_mul_le hp).2 (by simpa using h)
    simp [hq]
  · simp [Nat.div_eq_of_lt (lt_of_not_ge h)]

theorem gate_index_even {n : ℕ} (hp : (51*n+1).Prime) : n % 2 = 0 := by
  have hn : n ≠ 0 := by intro h; subst n; norm_num at hp
  have hodd := hp.odd_of_ne_two (by omega)
  obtain ⟨j, hj⟩ := hodd
  omega

theorem gate_factorial_sum {n : ℕ} (hp : (51*n+1).Prime) :
    (∑ i ∈ Finset.Ico 1 (40*n), padicValNat (51*n+1) (2*i).factorial) =
      (29*n-2)/2 := by
  letI : Fact (51*n+1).Prime := ⟨hp⟩
  have hn : n ≠ 0 := by intro h; subst n; norm_num at hp
  have he := gate_index_even hp
  let c : ℕ := (51*n+2)/2
  have hc : 1 ≤ c := by dsimp [c]; omega
  have hcount : 40*n-c = (29*n-2)/2 := by dsimp [c]; omega
  calc
    _ = ∑ i ∈ Finset.Ico 1 (40*n), if c ≤ i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hib := (Finset.mem_Ico.mp hi).2
      rw [factorial_val_lt_twice _ _ (by omega)]
      have hci : 51*n+1 ≤ 2*i ↔ c ≤ i := by dsimp [c]; omega
      simp only [hci]
    _ = ∑ _i ∈ (Finset.Ico 1 (40*n)).filter (fun i => c ≤ i), (1 : ℕ) := by
      rw [Finset.sum_filter]
    _ = (29*n-2)/2 := by
      have hset : (Finset.Ico 1 (40*n)).filter (fun i => c ≤ i) =
          Finset.Ico c (40*n) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_Ico]
        omega
      rw [hset]
      simpa using hcount

def basisFactor (n : ℕ) : ℚ :=
  ∏ i ∈ Finset.Ico 1 (40*n), ((2 : ℚ) / ((2*i).factorial : ℚ)) ^ 2

theorem basisFactor_ne_zero (n : ℕ) : basisFactor n ≠ 0 := by
  unfold basisFactor
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  positivity

private theorem val_prod {ι : Type} {p : ℕ} [Fact p.Prime] (s : Finset ι) (a : ι → ℚ)
    (ha : ∀ i ∈ s, a i ≠ 0) :
    padicValRat p (∏ i ∈ s, a i) = ∑ i ∈ s, padicValRat p (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i t hit ih =>
    have hti := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hit, Finset.sum_insert hit,
      padicValRat.mul (ha i (Finset.mem_insert_self i t)) (Finset.prod_ne_zero_iff.mpr hti),
      ih hti]

theorem basisFactor_val {n : ℕ} (hp : (51*n+1).Prime) :
    padicValRat (51*n+1) (basisFactor n) = -(29 * (n : ℤ)) + 2 := by
  let p := 51*n+1
  letI : Fact p.Prime := ⟨hp⟩
  have hn : n ≠ 0 := by intro h; subst n; norm_num at hp
  have he := gate_index_even hp
  have hp2 : 2 < p := by dsimp [p]; omega
  have h2 : padicValRat p (2 : ℚ) = 0 := by
    have hh : padicValNat p 2 = 0 :=
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by decide) hp2)
    simpa [hh] using (padicValRat_of_nat (p := p) 2).symm
  have hterm (i : ℕ) :
      padicValRat p (((2 : ℚ) / ((2*i).factorial : ℚ)) ^ 2) =
        -2 * (padicValNat p (2*i).factorial : ℤ) := by
    rw [pow_two, padicValRat.mul (by positivity) (by positivity),
      padicValRat.div (by norm_num) (by positivity), h2, ← padicValRat_of_nat]
    ring
  change padicValRat p (basisFactor n) = _
  unfold basisFactor
  rw [val_prod _ _ (fun i _ => by positivity)]
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← Nat.cast_sum]
  dsimp only [p]
  rw [gate_factorial_sum hp]
  omega

/-- The precise valuation transfer. The local reduction must separately establish
the monomial determinant valuation, and the basis identity must hold for the actual matrix. -/
theorem det_valuation_after_basis_change {n : ℕ} (hp : (51*n+1).Prime)
    {dPow dEven : ℚ} (hpow : dPow ≠ 0)
    (hlocal : padicValRat (51*n+1) dPow = -240 * (n : ℤ))
    (hbasis : dEven = basisFactor n * dPow) :
    dEven ≠ 0 ∧ padicValRat (51*n+1) dEven = -269 * (n : ℤ) + 2 := by
  letI : Fact (51*n+1).Prime := ⟨hp⟩
  rw [hbasis]
  refine ⟨mul_ne_zero (basisFactor_ne_zero n) hpow, ?_⟩
  rw [padicValRat.mul (basisFactor_ne_zero n) hpow, basisFactor_val hp, hlocal]
  ring

end OddZetaSix.B40a
