import OddZetaSix.B40a.Padic.WindowHermite

/-! The concrete local block series and its reduction at order six. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset

def jetWeight (n k a b : ℕ) : ℚ :=
  ∑ r ∈ range (6-(a+b)),
    (primeIndex n : ℚ)^r * ((9-(a+b+r)).choose 4 : ℚ) * (windowSeries n k).coeff r

theorem jetWeight_mem (n k a b : ℕ) [Fact (primeIndex n).Prime] (hk : k ∈ gateWindow n) :
    jetWeight n k a b ∈ sixGateIntegralRing (primeIndex n) := by
  let S := sixGateIntegralRing (primeIndex n)
  apply S.sum_mem
  intro r _
  exact S.mul_mem (S.mul_mem (S.pow_mem (natCast_mem S _) _) (natCast_mem S _))
    (windowSeries_mem n k hk r)

theorem jetWeight_cast (n k a b : ℕ) [Fact (primeIndex n).Prime] (hk : k ∈ gateWindow n) :
    (jetWeight n k a b : ZMod (primeIndex n)) =
      ((9-(a+b)).choose 4 : ZMod (primeIndex n)) *
        ((windowSeries n k).coeff 0 : ZMod (primeIndex n)) := by
  let p := primeIndex n
  let S := sixGateIntegralRing p
  let U := windowSeries n k
  let f := fun r : ℕ => (p : ℚ)^r * ((9-(a+b+r)).choose 4 : ℚ) * U.coeff r
  have hg (r : ℕ) : ((9-(a+b+r)).choose 4 : ℚ) * U.coeff r ∈ S :=
    S.mul_mem (natCast_mem S _) (windowSeries_mem n k hk r)
  have hf (r : ℕ) : f r ∈ S := by
    dsimp [f]
    rw [mul_assoc]
    exact S.mul_mem (S.pow_mem (natCast_mem S p) _) (hg r)
  change ((∑ r ∈ range (6-(a+b)), f r : ℚ) : ZMod p) = _
  rw [sixGateIntegralRing_cast_sum p _ f (fun r _ => hf r)]
  by_cases hab : a+b < 6
  · rw [Finset.sum_eq_single 0]
    · have h : f 0 = ((9-(a+b)).choose 4 : ℚ) * U.coeff 0 := by simp [f]
      rw [h,sixGateIntegralRing_cast_mul p (natCast_mem S _) (windowSeries_mem n k hk 0),
        Rat.cast_natCast]
    · intro r _ hr
      dsimp [f]
      rw [mul_assoc]
      exact sixGateReduction_p_pow_mul_eq_zero p (by omega) _ (hg r)
    · simp [hab]
  · rw [show 6-(a+b) = 0 by omega,range_zero,sum_empty,
      Nat.choose_eq_zero_of_lt (by omega : 9-(a+b) < 4),Nat.cast_zero,zero_mul]

def windowJetBlock (n k : ℕ) [Fact (primeIndex n).Prime] : Matrix (Fin 5) (Fin 5) (ZMod (primeIndex n)) :=
  fun a b => ((jetWeight n k a.val b.val : ℚ) : ZMod (primeIndex n))

theorem windowJetBlock_det_ne_zero (n k : ℕ) [Fact (primeIndex n).Prime] (hk : k ∈ gateWindow n) :
    (windowJetBlock n k).det ≠ 0 := by
  let p := primeIndex n
  let u := ((windowSeries n k).coeff 0 : ZMod p)
  have hu : u ≠ 0 := (sixGateReduction_ne_zero_iff p
    ⟨_,windowSeries_mem n k hk 0⟩).mpr (windowSeries_zero_unit n k hk)
  have hm : windowJetBlock n k = u • jetBlock.map (Int.castRingHom (ZMod p)) := by
    apply Matrix.ext
    intro a b
    change ((jetWeight n k a.val b.val : ℚ) : ZMod p) =
      u * ((Nat.choose (9-(a.val+b.val)) 4 : ℤ) : ZMod p)
    rw [jetWeight_cast n k a.val b.val hk]
    push_cast
    exact mul_comm _ _
  rw [hm,Matrix.det_smul,jetBlock_mod_det,mul_one]
  exact pow_ne_zero _ hu

end OddZetaSix.B40a
