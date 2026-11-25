import OddZetaSix.B40a.Padic.GateTransfer
import OddZetaSix.B40a.PolynomialModel
import Mathlib.NumberTheory.PrimesCongruentOne

namespace OddZetaSix.B40a

theorem prime_above (Q N : ℕ) (hQ : 0<Q) :
    ∃ n ≥ N, (primeIndex n).Prime ∧ ¬ primeIndex n ∣ Q := by
  obtain ⟨p,hp,hgt,hmod⟩ :=
    Nat.exists_prime_gt_modEq_one (max (51*N+1) Q) (by decide : 51 ≠ 0)
  have hN : 51*N+1 < p := lt_of_le_of_lt (le_max_left _ _) hgt
  have hQp : Q < p := lt_of_le_of_lt (le_max_right _ _) hgt
  have hrem : p%51=1 := by simpa [Nat.ModEq] using hmod
  have heq : primeIndex (p/51)=p := by
    unfold primeIndex
    simpa [hrem] using Nat.div_add_mod p 51
  refine ⟨p/51,by omega,by simpa only [heq] using hp,?_⟩
  rw [heq]
  intro hdvd
  exact (not_le_of_gt hQp) (Nat.le_of_dvd hQ hdvd)

/-- The cyclotomic subsequence and denominator-clearing portions of the gate.
The nonzero rational determinant at each admissible prime is an explicit input. -/
theorem subsequence_of_local_nonzero
    (hlocal : ∀ (n : ℕ) [Fact (primeIndex n).Prime] (q : Fin 5 → ℚ),
      (∀ i, q i ∈ sixGateIntegralRing (primeIndex n)) →
      ((Hpoly n).map (MvPolynomial.eval q)).det ≠ 0) :
    ∀ Q : ℤ, 0 < Q → ∀ N : ℕ, ∃ n ≥ N,
      ∀ q : Fin 5 → ℚ, (∀ k, ∃ z : ℤ, (Q : ℚ)*q k = (z : ℚ)) →
        (primitive n).eval₂ (Int.castRingHom ℚ) q ≠ 0 := by
  intro Q hQ N
  obtain ⟨n,hn,hp,hnd⟩ := prime_above Q.natAbs N (Int.natAbs_pos.mpr hQ.ne')
  letI : Fact (primeIndex n).Prime := ⟨hp⟩
  refine ⟨n,hn,?_⟩
  intro q hq
  have hQne : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hint (i : Fin 5) : q i ∈ sixGateIntegralRing (primeIndex n) := by
    obtain ⟨a,ha⟩ := hq i
    have heq : q i = (a : ℚ)*(Q : ℚ)⁻¹ := by
      apply mul_left_cancel₀ hQne
      rw [ha]
      field_simp
    have hQval : padicValRat (primeIndex n) (Q : ℚ) = 0 := by
      have hndZ : ¬ ((primeIndex n : ℤ) ∣ Q) :=
        fun hd => hnd (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd))
      rw [padicValRat.of_int]
      exact_mod_cast padicValInt.eq_zero_of_not_dvd hndZ
    rw [heq]
    exact (sixGateIntegralRing (primeIndex n)).mul_mem (intCast_mem _ a)
      (sixGateIntegralRing_inv_of_unit _ _ hQne hQval)
  have hdet := hlocal n q hint
  intro h0
  apply hdet
  change ((MvPolynomial.eval q).mapMatrix (Hpoly n)).det = _
  rw [← RingHom.map_det, primitive_det_eq n, map_mul,MvPolynomial.eval_C,
    MvPolynomial.eval_map,h0,mul_zero]

end OddZetaSix.B40a
