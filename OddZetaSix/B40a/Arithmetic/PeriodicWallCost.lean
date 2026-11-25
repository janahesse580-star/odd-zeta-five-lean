import OddZetaSix.B40a.Arithmetic.FoldedContent
import OddZetaSix.B40a.Arithmetic.PrimeSums

/-! Removing the five closed-endpoint corrections before computing the
periodic small-prime Riemann sums. Colliding endpoint residues count only once. -/
noncomputable section
namespace OddZetaSix.B40a
open Finset

private def wallAddresses (n p : ℕ) : Finset ℤ :=
  ({-25,-17,-16,-59,-34} : Finset ℤ).image (fun e => (e*(n:ℤ))%(p:ℤ))

private def wallClasses (n p : ℕ) : Finset (Fin (p/2+1)) :=
  univ.filter (fun c => (c.val : ℤ) ∈ wallAddresses n p)

private theorem wallClasses_card_le (n p : ℕ) : (wallClasses n p).card ≤ 5 := by
  let f : Fin (p/2+1) → ℤ := fun c => c.val
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    dsimp [f] at h
    exact_mod_cast h
  calc
    _ = ((wallClasses n p).image f).card := (card_image_of_injective _ hf).symm
    _ ≤ (wallAddresses n p).card := card_le_card (by
      intro x hx
      obtain ⟨c,hc,rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hc).2)
    _ ≤ _ := card_image_le.trans (by decide : ({-25,-17,-16,-59,-34} : Finset ℤ).card ≤ 5)

private theorem periodic_toNat_off_wall (n p : ℕ) (hn : 0<n) (hp : 0<p)
    (c : Fin (p/2+1)) (hc : c ∉ wallClasses n p) :
    (finitePeriodicRaw n p c.val).toNat =
    (periodicScore ((n:ℝ)/p) ((c.val:ℝ)/p)).toNat := by
  have h := finitePeriodicScore_eq_off_walls n p hn hp (c.val:ℤ) (by
    intro e he hd
    apply hc
    apply mem_filter.mpr
    refine ⟨mem_univ _,mem_image.mpr ⟨e,?_,?_⟩⟩
    · simpa using he
    · have hmod := Int.modEq_iff_dvd.mpr hd
      have hc0 : (c.val:ℤ) % p = c.val := Int.emod_eq_of_lt (by positivity)
        (by exact_mod_cast (show c.val < p by have := c.isLt; omega))
      change (c.val:ℤ) % p = (e*n) % p at hmod
      exact hmod.symm.trans hc0)
  simpa only [Int.cast_natCast] using (show (finitePeriodicRaw n p c.val).toNat =
      (periodicScore ((n:ℝ)/p) (((c.val:ℤ):ℝ)/p)).toNat by omega)

private theorem slotEnvelope_mono_score (q : ℕ) {x y : ℕ} (h : x ≤ y) :
    slotEnvelope q x ≤ slotEnvelope q y := by
  unfold slotEnvelope
  exact Nat.add_le_add (Nat.mul_le_mul_left _ h)
    (Nat.div_le_div_right (Nat.pow_le_pow_left (Nat.sub_le_sub_right h 1) 2))

/-- For every first-layer prime, replacing the true finite centered residues
by the periodic score costs at most five maximal slots, including all walls. -/
theorem content_periodic_with_five_walls (n p : ℕ) [Fact p.Prime]
    (hn : 0<n) (hsq : 84*n < p^2) :
    -padicValRat p (content n) ≤
      (∑ c : Fin (p/2+1), (slotEnvelope (2*fiveRank n/p)
        (periodicScore ((n:ℝ)/p) ((c.val:ℝ)/p)).toNat : ℤ)) +
        5*(slotEnvelope (2*fiveRank n/p) 16 : ℤ) := by
  classical
  let q := 2*fiveRank n/p
  let W := wallClasses n p
  let G (c : Fin (p/2+1)) := (slotEnvelope q
    (periodicScore ((n:ℝ)/p) ((c.val:ℝ)/p)).toNat : ℤ)
  let E := (slotEnvelope q 16 : ℤ)
  have hp := (Fact.out : p.Prime).pos
  have point (c : Fin (p/2+1)) :
      (slotEnvelope q (finitePeriodicRaw n p c.val).toNat : ℤ) ≤
        G c + (if c ∈ W then E else 0) := by
    by_cases h : c ∈ W
    · rw [ite_eq_left h]
      have hs : (finitePeriodicRaw n p c.val).toNat ≤ 16 :=
        Int.toNat_le.mpr (finitePeriodicRaw_le_16 n p hn hp _)
      have hE : (slotEnvelope q (finitePeriodicRaw n p c.val).toNat : ℤ) ≤ E :=
        by dsimp [E]; exact_mod_cast slotEnvelope_mono_score q hs
      have : 0 ≤ G c := Int.natCast_nonneg _
      omega
    · rw [ite_eq_right h, add_zero, periodic_toNat_off_wall n p hn hp c h]
  have hle := (content_finite_periodic n p hn hsq).trans (sum_le_sum (fun c _ => point c))
  rw [sum_add_distrib] at hle
  have herror : (∑ c : Fin (p/2+1), if c ∈ W then E else 0) ≤ 5*E := by
    rw [←sum_filter]
    simp only [filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast wallClasses_card_le n p) (Int.natCast_nonneg _)
  exact hle.trans (add_le_add_right herror _)


/-- On a band bounded away from zero in p/n, the boundary error is
uniform in n and p. This is a per-prime additive constant of exactly
the type accepted by the weighted prime number theorem. -/
theorem primeExponent_periodic_on_band (n p : ℕ) [Fact p.Prime]
    (hn : 0<n) (hsq : 84*n < p^2) (ε : ℝ) (hε : 0<ε)
    (hband : ε*(n:ℝ) ≤ p) :
    primeExponent n p ≤
      (∑ c : Fin (p/2+1), (slotEnvelope (2*fiveRank n/p)
        (periodicScore ((n:ℝ)/p) ((c.val:ℝ)/p)).toNat : ℝ)) +
        (6400/ε+360) := by
  let q := 2*fiveRank n/p
  let S : ℤ := ∑ c : Fin (p/2+1), (slotEnvelope q
        (periodicScore ((n:ℝ)/p) ((c.val:ℝ)/p)).toNat : ℤ)
  have hp : 0<p := (Fact.out : p.Prime).pos
  have hq : (q:ℝ)*(p:ℝ) ≤ 80*(n:ℝ) := by
    exact_mod_cast (show q*p ≤ 80*n by
      exact (Nat.div_mul_le_self (2*fiveRank n) p).trans (by unfold fiveRank; omega))
  have hq' : (q:ℝ)*ε ≤ 80 := by
    have hb := mul_le_mul_of_nonneg_left hband (Nat.cast_nonneg q)
    have hnR : (0:ℝ)<n := by exact_mod_cast hn
    apply le_of_mul_le_mul_right (a:=(n:ℝ)) _ hnR
    nlinarith only [hb,hq]
  have heq : (slotEnvelope q 16 : ℝ) = 16*(q:ℝ)+72 := by
    simp [slotEnvelope]
    <;> ring
  have hcost : (5:ℝ)*(slotEnvelope q 16 : ℝ) ≤ 6400/ε+360 := by
    rw [heq]
    have hle := (le_div_iff₀ hε).mpr hq'
    rw [show (6400:ℝ)/ε = 80*(80/ε) by ring]
    linarith only [hle]
  have hs : 0 ≤ S := Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  have hval : max 0 (-padicValRat p (content n)) ≤ S + 5*(slotEnvelope q 16 : ℤ) :=
    max_le (by positivity) (content_periodic_with_five_walls n p hn hsq)
  have hreal : primeExponent n p ≤ (S:ℝ) + 5*(slotEnvelope q 16 : ℝ) := by
    unfold primeExponent
    exact_mod_cast hval
  dsimp [S] at hreal
  push_cast at hreal
  exact hreal.trans (add_le_add_right hcost _)

end OddZetaSix.B40a
