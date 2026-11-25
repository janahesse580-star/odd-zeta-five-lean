import OddZetaSix.B40a.Arithmetic.LocalNumerator
import OddZetaSix.B40a.Arithmetic.HighCounts

/-! Reflection-paired harmonic packets and the exact folded factorization.
The packet estimates adapt the MIT-licensed upstream SixLocalSlots module. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial Finset
open scoped BigOperators

def numAliasCount (n p k : ℕ) : ℕ :=
  kernelZeroAliasCount n p ((k : ℤ)-(center n : ℤ))

def factVal (n p : ℕ) [Fact p.Prime] : ℤ := padicValRat p (normalization n)

/-- Constant-term valuation `v = v_fact + N_z - N_d` of the local regular factor (with central
factor estimated conservatively as an integral polynomial). -/
def siteBaseVal (n p k : ℕ) [Fact p.Prime] : ℤ :=
  factVal n p + (numAliasCount n p k : ℤ) - (kernelDenomAliases n p k : ℤ)

/-- Effective derivative-order loss `d'`: `min d N_z` if `N_d = 0`, else `d`. -/
def effectiveOrderLoss (n p k d : ℕ) : ℕ :=
  if kernelDenomAliases n p k = 0 then min d (numAliasCount n p k) else d

/-- Paired harmonic denominator indicator `I_ℓ` (`ℓ = l + 1`):
- for `l` even (`ℓ` odd): `1` iff `p ≤ k - 25n - 1`;
- for `l` odd (`ℓ` even): `1` iff `(k' - 25n - 1) / p < (k - 25n - 1) / p`. -/
def harmonicIndicator (n p k l : ℕ) : ℕ :=
  if Even l then
    if 1 ≤ (k - 25 * n - 1) / p then 1 else 0
  else
    if (kernelReflectedPole n k - 25 * n - 1) / p < (k - 25 * n - 1) / p then 1 else 0

/-- Refined combined-order cost `C_{k, r}` from eq. (6) of `zeta6_irrationality_proof.tex`. -/
def refinedOrderCost (n p k r : ℕ) [Fact p.Prime] : ℕ :=
  ((range (kernelPoleOrder n k)).filter (fun l => r ≤ kernelPoleOrder n k - 1 - l)).sup fun l =>
    let d := kernelPoleOrder n k - 1 - l - r
    let d' := effectiveOrderLoss n p k d
    let I := harmonicIndicator n p k l
    ((r : ℤ) - siteBaseVal n p k + (d' : ℤ) + ((l + 5 : ℕ) : ℤ) * (I : ℤ)).toNat

/-- Refined single-slot cost `B_{k, a} = max_{r ≥ a} C_{k, r}` from eq. (6). -/
def refinedSlotCost (n p k a : ℕ) [Fact p.Prime] : ℕ :=
  ((range (kernelPoleOrder n k)).filter (fun r => a ≤ r)).sup fun r =>
    refinedOrderCost n p k r


abbrev slotLocalSeries := highUnitSeries

theorem slotLocalSeries_coeff_valAtLeast (n p : ℕ) [Fact p.Prime] (hn : 0<n)
    (hsq : 84*n < p^2) (k : ℕ) (hk : k ∈ kernelPoleSet n) (d : ℕ)
    (hd : d < poleOrder n k) :
    ValAtLeast p (siteBaseVal n p k-(effectiveOrderLoss n p k d : ℤ))
      ((slotLocalSeries n k).coeff d) := by
  let A := baseKernelNumerator n k
  let D := kernelLocalCofactor n k
  let Q := slotLocalSeries n k
  have hD0 := kernelLocalCofactor_ne_zero_coeff n k
  have he : D = taylor (-(k : ℚ)) (regularDenominator n k) := by
    unfold D kernelLocalCofactor
    rw [regularDenominator_eq_erase n k hk]
  have hQ : Q = truncatedQuotient A D (poleOrder n k) := by
    unfold Q slotLocalSeries highUnitSeries A baseKernelNumerator
    rw [he]
  have hm : X^poleOrder n k ∣ A-D*Q := by
    rw [hQ]
    exact truncatedQuotient_dvd A D hD0 _
  have hc := localQuotient_eq_coeff_of_congruence A D Q hD0 _ hm d hd
  change ValAtLeast p _ (Q.coeff d)
  rw [← hc]
  exact kernelTaylorQuotient_first_layer n p k hn hsq hk d

/-- Single-pole polynomial packet multiplying `kernelPrincipalCoefficients n i j k l`. -/
def polePacket (n k l : ℕ) : FivePolynomial :=
  MvPolynomial.C (((l + 4).choose 4 : ℚ) * (-harmonicCutoff (l + 5) (k - 25 * n - 1))) +
    ∑ s : Fin 5, if l = 2 + 2 * s.val then
      MvPolynomial.C (((l + 4).choose 4 : ℚ)) * MvPolynomial.X s else 0

/-- Reflection-paired polynomial packet for `k ≥ c_n` (unpaired at the fixed center `k = c_n`). -/
def pairedPacket (n k l : ℕ) : FivePolynomial :=
  if k = center n then
    if Even l then polePacket n k l else 0
  else
    polePacket n k l + MvPolynomial.C ((-1 : ℚ) ^ l) * polePacket n (kernelReflectedPole n k) l

/-- Valuation lower bound on `pairedPacket n k l` matching indicator `harmonicIndicator n p k l`. -/
theorem pairedPacket_formalValAtLeast (n p : ℕ) [Fact p.Prime] (hn : 0 < n)
    (hsq : 84 * n < p ^ 2) (k : ℕ) (hk : k ∈ kernelPoleSet n) (hkc : center n ≤ k) (l : ℕ) :
    FormalValAtLeast p (-(((l + 5 : ℕ) : ℤ) * (harmonicIndicator n p k l : ℤ)))
      (pairedPacket n k l) := by
  have hp : p.Prime := Fact.out
  have hbnd := kernel_pole_address_bounds n k hk
  have hk_ref_le : kernelReflectedPole n k ≤ k := by
    unfold kernelReflectedPole center at *; omega
  have hharm_term : ∀ j : ℕ, 1 ≤ j → j < p ^ 2 →
      ValAtLeast p (if p ∣ j then -((l + 5 : ℕ) : ℤ) else 0) (1 / (j : ℚ) ^ (l + 5)) := by
    intro j hj1 hjlt
    have hjne : (j : ℚ) ≠ 0 := by positivity
    have hpow_val : padicValRat p ((j : ℚ) ^ (l + 5)) =
        ((l + 5 : ℕ) : ℤ) * (padicValNat p j : ℤ) := by
      induction (l + 5) with
      | zero => simp
      | succ m ihm =>
        rw [pow_succ, padicValRat.mul (pow_ne_zero m hjne) hjne, ihm, padicValRat.of_nat]
        push_cast; ring
    right
    rw [one_div, padicValRat.inv, hpow_val]
    split_ifs with hdvd
    · have hlt2 : padicValNat p j < 2 := by
        by_contra hge; push Not at hge
        have := Nat.le_of_dvd (by omega) ((padicValNat_dvd_iff_le (by omega)).mpr hge)
        omega
      have hle1 : (padicValNat p j : ℤ) ≤ 1 := by omega
      nlinarith
    · rw [padicValNat.eq_zero_of_not_dvd hdvd]; simp
  have hharm_le : ∀ N : ℕ, N < p ^ 2 →
      ValAtLeast p (if 1 ≤ N / p then -((l + 5 : ℕ) : ℤ) else 0) (harmonicCutoff (l + 5) N) := by
    intro N hNlt
    unfold harmonicCutoff
    apply valAtLeast_sum; intro j hj
    have hjN : j + 1 ≤ N := by have := mem_range.mp hj; omega
    have h1 := hharm_term (j + 1) (by omega) (hjN.trans_lt hNlt)
    have hcast : ((j : ℚ) + 1) = ((j + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [hcast]
    apply valAtLeast_mono h1
    by_cases hdiv : 1 ≤ N / p
    · by_cases hd : p ∣ j + 1 <;> simp only [hdiv, hd, ite_true, ite_false] <;> omega
    · by_cases hd : p ∣ j + 1
      · exfalso
        have hle : p ≤ j + 1 := Nat.le_of_dvd (by omega) hd
        have : 1 ≤ N / p := Nat.div_pos (hle.trans hjN) hp.pos
        omega
      · simp only [hdiv, hd, ite_false]; exact le_rfl
  unfold pairedPacket harmonicIndicator
  by_cases hkc_eq : k = center n
  · simp only [hkc_eq, ite_true]
    by_cases hev : Even l
    · simp only [hev, ite_true]
      unfold polePacket
      apply formalValAtLeast_add
      · apply formalValAtLeast_C
        have hch := valAtLeast_natCast p ((l + 4).choose 4)
        have hhc := valAtLeast_neg (hharm_le (center n - 25 * n - 1) (by unfold center; omega))
        have hm := valAtLeast_mul hch hhc
        exact valAtLeast_mono hm (by split_ifs <;> simp)
      · apply formalValAtLeast_sum; intro s _
        by_cases hs : l = 2 + 2 * s.val
        · simp only [hs, ite_true]
          exact formalValAtLeast_mono
            (formalValAtLeast_C_mul (valAtLeast_natCast p _) (formalValAtLeast_X p s))
            (by split_ifs <;> omega)
        · simp only [hs, ite_false]
          exact formalValAtLeast_zero p _
    · simp only [hev, ite_false]
      exact formalValAtLeast_zero p _
  · simp only [hkc_eq, ite_false]
    by_cases hev : Even l
    · simp only [hev, ite_true]
      have h1 : FormalValAtLeast p (-(((l + 5 : ℕ) : ℤ) * (if 1 ≤ (k - 25 * n - 1) / p then 1 else 0 : ℕ)))
          (polePacket n k l) := by
        unfold polePacket
        apply formalValAtLeast_add
        · apply formalValAtLeast_C
          have hm := valAtLeast_mul (valAtLeast_natCast p ((l + 4).choose 4))
            (valAtLeast_neg (hharm_le (k - 25 * n - 1) (by omega)))
          exact valAtLeast_mono hm (by split_ifs <;> simp)
        · apply formalValAtLeast_sum; intro s _
          by_cases hs : l = 2 + 2 * s.val
          · simp only [hs, ite_true]
            exact formalValAtLeast_mono
              (formalValAtLeast_C_mul (valAtLeast_natCast p _) (formalValAtLeast_X p s))
              (by split_ifs <;> omega)
          · simp only [hs, ite_false]
            exact formalValAtLeast_zero p _
      have h2 : FormalValAtLeast p (-(((l + 5 : ℕ) : ℤ) * (if 1 ≤ (k - 25 * n - 1) / p then 1 else 0 : ℕ)))
          (polePacket n (kernelReflectedPole n k) l) := by
        unfold polePacket
        apply formalValAtLeast_add
        · apply formalValAtLeast_C
          have hdiv_le : (kernelReflectedPole n k - 25 * n - 1) / p ≤ (k - 25 * n - 1) / p :=
            Nat.div_le_div_right (by omega)
          have hm := valAtLeast_mul (valAtLeast_natCast p ((l + 4).choose 4))
            (valAtLeast_neg (hharm_le (kernelReflectedPole n k - 25 * n - 1) (by omega)))
          exact valAtLeast_mono hm (by split_ifs <;> omega)
        · apply formalValAtLeast_sum; intro s _
          by_cases hs : l = 2 + 2 * s.val
          · simp only [hs, ite_true]
            exact formalValAtLeast_mono
              (formalValAtLeast_C_mul (valAtLeast_natCast p _) (formalValAtLeast_X p s))
              (by split_ifs <;> omega)
          · simp only [hs, ite_false]
            exact formalValAtLeast_zero p _
      rw [hev.neg_one_pow, map_one, one_mul]
      exact formalValAtLeast_add h1 h2
    · simp only [hev, ite_false]
      have hodd : Odd l := Nat.not_even_iff_odd.mp hev
      rw [hodd.neg_one_pow]
      -- When `l` is odd, all `X s` terms vanish (`l ≠ 2 + 2s`), leaving only the harmonic difference!
      have hdiff_eq : polePacket n k l + MvPolynomial.C (-1 : ℚ) * polePacket n (kernelReflectedPole n k) l =
          MvPolynomial.C (-(((l + 4).choose 4 : ℚ) *
            (harmonicCutoff (l + 5) (k - 25 * n - 1) -
              harmonicCutoff (l + 5) (kernelReflectedPole n k - 25 * n - 1)))) := by
        unfold polePacket
        have hnoX : (∑ s : Fin 5, if l = 2 + 2 * s.val then
            MvPolynomial.C (((l + 4).choose 4 : ℚ)) * MvPolynomial.X s else 0) = 0 := by
          apply Finset.sum_eq_zero; intro s _
          have hne : l ≠ 2 + 2 * s.val := by
            obtain ⟨t, rfl⟩ := hodd; omega
          simp [hne]
        rw [hnoX, add_zero, add_zero, ← map_mul, ← map_add]
        congr 1; ring
      rw [hdiff_eq]
      apply formalValAtLeast_C
      apply valAtLeast_neg
      have hch := valAtLeast_natCast p ((l + 4).choose 4)
      have hNle : kernelReflectedPole n k - 25 * n - 1 ≤ k - 25 * n - 1 := by omega
      have hsub_harm : harmonicCutoff (l + 5) (k - 25 * n - 1) -
          harmonicCutoff (l + 5) (kernelReflectedPole n k - 25 * n - 1) =
          ∑ j ∈ Finset.Ico (kernelReflectedPole n k - 25 * n - 1) (k - 25 * n - 1),
            1 / ((j : ℚ) + 1) ^ (l + 5) := by
        unfold harmonicCutoff
        rw [← Nat.Ico_zero_eq_range, ← Nat.Ico_zero_eq_range,
          ← Finset.sum_Ico_consecutive _ (Nat.zero_le _) hNle]
        ring
      rw [hsub_harm]
      have hsum_val : ValAtLeast p
          (-(((l + 5 : ℕ) : ℤ) *
            (if (kernelReflectedPole n k - 25 * n - 1) / p < (k - 25 * n - 1) / p then (1 : ℕ) else 0 : ℤ)))
          (∑ j ∈ Finset.Ico (kernelReflectedPole n k - 25 * n - 1) (k - 25 * n - 1),
            1 / ((j : ℚ) + 1) ^ (l + 5)) := by
        apply valAtLeast_sum; intro j hj
        rw [Finset.mem_Ico] at hj
        have h1 := hharm_term (j + 1) (by omega) (by omega)
        have hcast : ((j : ℚ) + 1) = ((j + 1 : ℕ) : ℚ) := by push_cast; ring
        rw [hcast]
        apply valAtLeast_mono h1
        by_cases hlt : (kernelReflectedPole n k - 25 * n - 1) / p < (k - 25 * n - 1) / p
        · by_cases hd : p ∣ j + 1 <;> simp only [hlt, hd, ite_true, ite_false] <;> omega
        · by_cases hd : p ∣ j + 1
          · exfalso
            obtain ⟨q, hq⟩ := hd
            have hq_gt : (kernelReflectedPole n k - 25 * n - 1) / p < q := by
              have : kernelReflectedPole n k - 25 * n - 1 < q * p := by nlinarith
              exact (Nat.div_lt_iff_lt_mul hp.pos).mpr (by nlinarith)
            have hq_le : q ≤ (k - 25 * n - 1) / p := by
              have : q * p ≤ k - 25 * n - 1 := by nlinarith
              exact (Nat.le_div_iff_mul_le hp.pos).mpr (by nlinarith)
            omega
          · simp only [hlt, hd, ite_false]; exact le_rfl
      simpa using valAtLeast_mul hch hsum_val

/-! ## Exact column indexing `(t, a) ∈ Fin (25n + 1) × Fin 12` and `Y * W * Yᵀ` identity -/

/-- Total number of slot columns across the `25n + 1` upper-half poles (`12` slots each). -/
def slotCount (n : ℕ) : ℕ := (25 * n + 1) * 12

/-- Canonical bijection `Fin (25n + 1) × Fin 12 ≃ Fin (slotCount n)`. -/
def slotEquiv (n : ℕ) : Fin (25 * n + 1) × Fin 12 ≃ Fin (slotCount n) where
  toFun p := ⟨12 * p.1.val + p.2.val, by unfold slotCount; have := p.1.isLt; have := p.2.isLt; omega⟩
  invFun u := (⟨u.val / 12, by unfold slotCount at u; have := u.isLt; omega⟩,
               ⟨u.val % 12, Nat.mod_lt _ (by decide)⟩)
  left_inv p := by ext <;> (dsimp; have := p.2.isLt; omega)
  right_inv u := by ext; dsimp; omega

/-- Pole address `k_t = 59n + 1 + t` for `t : Fin (25n + 1)`. -/
def halfPole (n : ℕ) (t : Fin (25 * n + 1)) : ℕ := center n + t.val

/-- Centered coordinate `x_u = c_n - k_t = -t` for slot `u`. -/
def slotCenter (n : ℕ) (u : Fin (slotCount n)) : ℤ :=
  -((slotEquiv n).symm u).1.val

/-- Jet order `a_u ∈ {0, ..., 11}` for slot `u`. -/
def slotDeg (n : ℕ) (u : Fin (slotCount n)) : ℕ :=
  ((slotEquiv n).symm u).2.val

/-- Refined slot cost `B_u = refinedSlotCost n p k_t a_u`. -/
def slotCost (n p : ℕ) [Fact p.Prime] (u : Fin (slotCount n)) : ℕ :=
  let ta := (slotEquiv n).symm u
  refinedSlotCost n p (halfPole n ta.1) ta.2.val

/-- Block-diagonal paired weight matrix `W` indexed by `Fin (slotCount n)`. -/
def slotWeightMatrix (n p : ℕ) :
    Matrix (Fin (slotCount n)) (Fin (slotCount n)) FivePolynomial :=
  fun u v =>
    let ta := (slotEquiv n).symm u
    let sb := (slotEquiv n).symm v
    if ta.1 = sb.1 then
      let k := halfPole n ta.1
      let m := kernelPoleOrder n k
      let a := ta.2.val
      let b := sb.2.val
      ∑ l : Fin m,
        if a + b ≤ m - 1 - l.val then
          MvPolynomial.C ((slotLocalSeries n k).coeff (m - 1 - l.val - (a + b)) /
            (p : ℚ) ^ (a + b)) * pairedPacket n k l.val
        else 0
    else 0

theorem halfPole_mem (n : ℕ) (_hn : 0<n) (t : Fin (25*n+1)) :
    halfPole n t ∈ kernelPoleSet n := by
  have ht := t.isLt
  rw [kernelPoleSet_eq_outer, Finset.mem_Icc]
  unfold halfPole center
  omega

/-- **Exact `Y * W * Yᵀ` factorization of `Hpoly n`** for any `n ≥ 1` and `p > 0`. -/
theorem Hpoly_eq_evalJet_mul_weight (n p : ℕ) (hn : 0 < n) (hp : 0 < p) :
    Hpoly n =
      (evalJetMatrix p (fiveRank n) (slotCount n) (slotCenter n) (slotDeg n)).map MvPolynomial.C *
      slotWeightMatrix n p *
      ((evalJetMatrix p (fiveRank n) (slotCount n) (slotCenter n) (slotDeg n)).map MvPolynomial.C).transpose := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  -- Step 1: express `Hpoly n i j` as sum of `kernelPrincipalCoefficients * polePacket`
  have hmat_pole : ∀ i j : Fin (fiveRank n),
      Hpoly n i j =
        ∑ k ∈ kernelPoleSet n, ∑ l : Fin (kernelPoleOrder n k),
          MvPolynomial.C (kernelPrincipalCoefficients n i j k l) * polePacket n k l.val := by
    intro i j
    unfold Hpoly fiveEntry
    rw [← kernelPoleSet_eq_poleList]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← kernelPoleOrder_eq_poleOrder, sum_orders]
    apply Finset.sum_congr rfl
    intro l _
    rw [localPrincipal_eq n i j k hk l, harmonic_eq]
    have hv : zetaSymbol (l.val+1) =
        ∑ s : Fin 5, if l.val=2+2*s.val then MvPolynomial.X s else 0 := by
      unfold zetaSymbol
      apply Finset.sum_congr rfl
      intro s _
      simp only [show l.val+1=3+2*s.val ↔ l.val=2+2*s.val by omega]
    have hch : l.val+1+3 = l.val+4 := by omega
    have he : polePacket n k l.val =
        MvPolynomial.C (Nat.choose (l.val+4) 4 : ℚ) *
          (zetaSymbol (l.val+1) - MvPolynomial.C (harmonicCutoff (l.val+5) (k-25*n-1))) := by
      rw [hv]
      unfold polePacket
      simp only [Finset.mul_sum,mul_sub,mul_ite,mul_zero,mul_neg,MvPolynomial.C_neg, ← MvPolynomial.C_mul]
      ring
    rw [hch,he, ← mul_assoc, ← MvPolynomial.C_mul]
    congr 2
    ring
  -- Step 2: fold the pole sum onto `t : Fin (25 * n + 1)` using reflection symmetry
  have hmat_half : ∀ i j : Fin (fiveRank n),
      Hpoly n i j =
        ∑ t : Fin (25 * n + 1), ∑ l : Fin (kernelPoleOrder n (halfPole n t)),
          MvPolynomial.C (kernelPrincipalCoefficients n i j (halfPole n t) l) *
            pairedPacket n (halfPole n t) l.val := by
    intro i j
    rw [hmat_pole i j]
    -- Partition `kernelPoleSet n` into `< c_n`, `= c_n`, `> c_n`
    let S_lt := (kernelPoleSet n).filter (fun k => k < center n)
    let S_ge := (kernelPoleSet n).filter (fun k => center n ≤ k)
    have hsplit : (∑ k ∈ kernelPoleSet n, ∑ l : Fin (kernelPoleOrder n k),
        MvPolynomial.C (kernelPrincipalCoefficients n i j k l) * polePacket n k l.val) =
        (∑ k ∈ S_ge, ∑ l : Fin (kernelPoleOrder n k),
          MvPolynomial.C (kernelPrincipalCoefficients n i j k l) * polePacket n k l.val) +
        (∑ k ∈ S_lt, ∑ l : Fin (kernelPoleOrder n k),
          MvPolynomial.C (kernelPrincipalCoefficients n i j k l) * polePacket n k l.val) := by
      have h := Finset.sum_filter_add_sum_filter_not (kernelPoleSet n) (fun k => center n ≤ k)
        (fun k => ∑ l : Fin (kernelPoleOrder n k),
          MvPolynomial.C (kernelPrincipalCoefficients n i j k l) * polePacket n k l.val)
      simpa only [not_le] using h.symm
    -- Reindex `S_lt` to `S_gt := S_ge.erase (center n)` via `kernelReflectedPole n`
    have hlt_eq : (∑ k ∈ S_lt, ∑ l : Fin (kernelPoleOrder n k),
        MvPolynomial.C (kernelPrincipalCoefficients n i j k l) * polePacket n k l.val) =
        ∑ k ∈ S_ge, if k = center n then 0 else
          ∑ l : Fin (kernelPoleOrder n k),
            MvPolynomial.C (kernelPrincipalCoefficients n i j k l) *
              (MvPolynomial.C ((-1 : ℚ) ^ l.val) * polePacket n (kernelReflectedPole n k) l.val) := by
      symm
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
      apply Finset.sum_bij (fun k _ => kernelReflectedPole n k)
      · intro k hk
        rw [Finset.mem_filter] at hk
        have hkge := Finset.mem_filter.mp hk.1
        rw [Finset.mem_filter]
        refine ⟨(kernel_pole_mem_reflection n k).mpr hkge.1, ?_⟩
        unfold kernelReflectedPole center at *; omega
      · intro k₁ hk₁ k₂ hk₂ heq
        unfold kernelReflectedPole at heq
        have hb1 := kernel_pole_address_bounds n k₁ (Finset.mem_filter.mp (Finset.mem_filter.mp hk₁).1).1
        have hb2 := kernel_pole_address_bounds n k₂ (Finset.mem_filter.mp (Finset.mem_filter.mp hk₂).1).1
        omega
      · intro k hk
        rw [Finset.mem_filter] at hk
        have hb := kernel_pole_address_bounds n k hk.1
        refine ⟨kernelReflectedPole n k, ?_, kernel_pole_reflection_involutive n k hk.1⟩
        rw [Finset.mem_filter, Finset.mem_filter]
        refine ⟨⟨(kernel_pole_mem_reflection n k).mpr hk.1, ?_⟩, ?_⟩
        · unfold kernelReflectedPole center at *; omega
        · unfold kernelReflectedPole center at *; omega
      · intro k hk
        have hkmem : k ∈ kernelPoleSet n := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).1
        have hord := kernel_pole_order_reflection n k
        apply Fintype.sum_equiv (finCongr hord.symm)
        intro l
        have href := kernel_principal_coefficients_reflection n i j k hkmem l
        simp only [finCongr_apply, Fin.val_cast]
        rw [href, map_mul]
        have hsq1 : (MvPolynomial.C ((-1 : ℚ) ^ l.val) : FivePolynomial) *
            MvPolynomial.C ((-1 : ℚ) ^ l.val) = 1 := by
          rw [← map_mul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, map_one]
        calc
          MvPolynomial.C ((-1 : ℚ) ^ l.val) *
              MvPolynomial.C (kernelPrincipalCoefficients n i j (kernelReflectedPole n k) (l.cast hord.symm)) *
              (MvPolynomial.C ((-1 : ℚ) ^ l.val) * polePacket n (kernelReflectedPole n k) l.val)
              = (MvPolynomial.C ((-1 : ℚ) ^ l.val) * MvPolynomial.C ((-1 : ℚ) ^ l.val)) *
                  (MvPolynomial.C (kernelPrincipalCoefficients n i j (kernelReflectedPole n k) (l.cast hord.symm)) *
                    polePacket n (kernelReflectedPole n k) l.val) := by ring
          _ = MvPolynomial.C (kernelPrincipalCoefficients n i j (kernelReflectedPole n k) (l.cast hord.symm)) *
                polePacket n (kernelReflectedPole n k) l.val := by rw [hsq1, one_mul]
    rw [hsplit, hlt_eq, ← Finset.sum_add_distrib]
    -- Reindex `S_ge` by `t : Fin (25 * n + 1)` via `halfPole n t`
    symm
    apply Finset.sum_bij (fun (t : Fin (25 * n + 1)) _ => halfPole n t)
    · intro t _
      rw [Finset.mem_filter]
      exact ⟨halfPole_mem n hn t, by unfold halfPole; omega⟩
    · intro t₁ _ t₂ _ heq
      ext; unfold halfPole at heq; omega
    · intro k hk
      rw [Finset.mem_filter] at hk
      have hb := kernel_pole_address_bounds n k hk.1
      refine ⟨⟨k - center n, by unfold center at *; omega⟩, Finset.mem_univ _, ?_⟩
      unfold halfPole; dsimp; omega
    · intro t _
      by_cases hkc : halfPole n t = center n
      · unfold pairedPacket
        simp only [hkc, ite_true, add_zero]
        apply Finset.sum_congr rfl; intro l _
        by_cases hev : Even l.val
        · simp [hev]
        · simp only [hev, ite_false, mul_zero]
          have hodd : Odd l.val := Nat.not_even_iff_odd.mp hev
          have href := kernel_principal_coefficients_reflection n i j (halfPole n t)
            (halfPole_mem n hn t) l
          have hfix : kernelReflectedPole n (halfPole n t) = halfPole n t := by
            rw [hkc]; unfold kernelReflectedPole center; omega
          have hfix_coef : ∀ (k₁ k₂ : ℕ) (hk : k₁ = k₂)
              (l₁ : Fin (kernelPoleOrder n k₁)) (l₂ : Fin (kernelPoleOrder n k₂)),
              l₁.val = l₂.val →
              kernelPrincipalCoefficients n i j k₁ l₁ = kernelPrincipalCoefficients n i j k₂ l₂ := by
            rintro k₁ _ rfl l₁ l₂ hval; congr 1; exact Fin.ext hval
          have hcoef0 : kernelPrincipalCoefficients n i j (halfPole n t) l = 0 := by
            have h1 : kernelPrincipalCoefficients n i j (halfPole n t) l =
                -kernelPrincipalCoefficients n i j (halfPole n t) l := by
              rw [hodd.neg_one_pow, neg_one_mul,
                hfix_coef _ _ hfix (l.cast _) l (Fin.val_cast _ _)] at href
              exact href
            linarith
          simp [hcoef0]
      · unfold pairedPacket
        simp only [hkc, ite_false]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro l _
        rw [mul_add]
  -- Step 3: express `kernelPrincipalCoefficients n i j k l` via `slotLocalSeries` and `evenBasis` Taylor jets
  have hpc_expand : ∀ (i j : Fin (fiveRank n)) (t : Fin (25 * n + 1))
      (l : Fin (kernelPoleOrder n (halfPole n t))),
      kernelPrincipalCoefficients n i j (halfPole n t) l =
        ∑ a : Fin 12, ∑ b : Fin 12,
          (if a.val + b.val ≤ kernelPoleOrder n (halfPole n t) - 1 - l.val then
            (slotLocalSeries n (halfPole n t)).coeff
              (kernelPoleOrder n (halfPole n t) - 1 - l.val - (a.val + b.val)) /
              (p : ℚ) ^ (a.val + b.val)
          else 0) *
          ((p : ℚ) ^ a.val * taylorCoeff (evenBasis i.val) (-(t.val : ℤ) : ℚ) a.val) *
          ((p : ℚ) ^ b.val * taylorCoeff (evenBasis j.val) (-(t.val : ℤ) : ℚ) b.val) := by
    intro i j t l
    let k := halfPole n t
    let m := kernelPoleOrder n k
    have hk := halfPole_mem n hn t
    have hm14 : m ≤ 12 := kernel_pole_order_le n k
    have hpos : 1 ≤ l.val+1 ∧ l.val+1 ≤ poleOrder n k := by
      rw [← kernelPoleOrder_eq_poleOrder]
      have hh := l.isLt
      change l.val < kernelPoleOrder n k at hh
      omega
    have hprincipal := high_principal_eq_jet_coeff n k (l.val+1)
      (evenBasis i.val) (evenBasis j.val) hk hpos
    rw [localPrincipal_eq n i j k hk l, ← kernelPoleOrder_eq_poleOrder] at hprincipal
    have hx : (center n : ℚ)-(k : ℚ) = (-(t.val : ℤ) : ℚ) := by
      dsimp [k,halfPole]; push_cast; ring
    rw [hx,show kernelPoleOrder n k-(l.val+1) = m-1-l.val by dsimp [m]; omega] at hprincipal
    rw [hprincipal]
    change (slotLocalSeries n k * (taylor (-(t.val : ℤ) : ℚ) (evenBasis i.val) *
      taylor (-(t.val : ℤ) : ℚ) (evenBasis j.val))).coeff (m-1-l.val) = _
    -- Expand triple convolution `(Q * (E_i * E_j)).coeff d`
    let d := m - 1 - l.val
    have hlt_m : l.val < m := l.isLt
    have hd14 : d < 12 := by omega
    have hconv : (slotLocalSeries n k *
        (taylor (-(t.val : ℤ) : ℚ) (evenBasis i.val) *
         taylor (-(t.val : ℤ) : ℚ) (evenBasis j.val))).coeff d =
        ∑ a : Fin 12, ∑ b : Fin 12,
          if a.val+b.val ≤ d then
            (slotLocalSeries n k).coeff (d-(a.val+b.val)) *
              taylorCoeff (evenBasis i.val) (-(t.val : ℤ) : ℚ) a.val *
              taylorCoeff (evenBasis j.val) (-(t.val : ℤ) : ℚ) b.val
          else 0 := by
      simpa only [taylorCoeff,show ∀ a b : ℕ, d-a-b=d-(a+b) from fun _ _ => by omega] using
        coeff_mul3_fin12 (slotLocalSeries n k)
          (taylor (-(t.val : ℤ) : ℚ) (evenBasis i.val))
          (taylor (-(t.val : ℤ) : ℚ) (evenBasis j.val)) d hd14
    rw [hconv]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    split_ifs
    · have hpa : (p : ℚ) ^ a.val ≠ 0 := pow_ne_zero _ hpq
      have hpb : (p : ℚ) ^ b.val ≠ 0 := pow_ne_zero _ hpq
      rw [pow_add]
      field_simp
      dsimp only [d, m, k]
      ring
    · ring
  -- Step 4: assemble into `Y * W * Yᵀ`
  apply Matrix.ext; intro i j
  rw [hmat_half i j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  -- Reindex `u, v : Fin (slotCount n)` by `slotEquiv n`
  have hreindex : (∑ v : Fin (slotCount n), ∑ u : Fin (slotCount n),
      MvPolynomial.C (evalJetMatrix p (fiveRank n) (slotCount n) (slotCenter n) (slotDeg n) i u) *
      slotWeightMatrix n p u v *
      MvPolynomial.C (evalJetMatrix p (fiveRank n) (slotCount n) (slotCenter n) (slotDeg n) j v)) =
      ∑ t : Fin (25 * n + 1), ∑ b : Fin 12, ∑ a : Fin 12,
        MvPolynomial.C (evalJetMatrix p (fiveRank n) (slotCount n) (slotCenter n) (slotDeg n) i
          (slotEquiv n (t, a))) *
        slotWeightMatrix n p (slotEquiv n (t, a)) (slotEquiv n (t, b)) *
        MvPolynomial.C (evalJetMatrix p (fiveRank n) (slotCount n) (slotCenter n) (slotDeg n) j
          (slotEquiv n (t, b))) := by
    rw [← Equiv.sum_comp (slotEquiv n), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro t _
    apply Finset.sum_congr rfl; intro b _
    rw [← Equiv.sum_comp (slotEquiv n), Fintype.sum_prod_type, Finset.sum_eq_single t]
    · intro t' _ hne
      apply Finset.sum_eq_zero; intro a _
      unfold slotWeightMatrix
      simp [Equiv.symm_apply_apply, hne]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [hreindex]
  apply Finset.sum_congr rfl; intro t _
  simp_rw [hpc_expand i j t, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro a _
  unfold slotWeightMatrix evalJetMatrix slotCenter slotDeg
  simp only [Equiv.symm_apply_apply, ite_true, Finset.mul_sum, Finset.sum_mul]
  apply Fintype.sum_equiv (finCongr (by rw [Equiv.symm_apply_apply]))
  intro l
  simp only [finCongr_apply, Fin.val_cast]
  have hcast_t : (((-(t.val : ℤ)) : ℤ) : ℚ) = -(t.val : ℚ) := by push_cast; ring
  have hcast_t' : (-(t.val : ℤ) : ℚ) = -(t.val : ℚ) := by push_cast; ring
  rw [hcast_t, hcast_t']
  split_ifs
  · simp only [map_mul]
    ring
  · simp

/-- Doubled Gauss valuation bound on `slotWeightMatrix n p`:
`2 * v_p^G(W u v) ≥ -(B u + B v)`. -/
theorem slotWeightMatrix_doubled_bound (n p : ℕ) [Fact p.Prime] (hn : 0 < n)
    (hsq : 84 * n < p ^ 2) (u v : Fin (slotCount n)) :
    DoubledFormalValAtLeast p (-((slotCost n p u + slotCost n p v : ℕ) : ℤ))
      (slotWeightMatrix n p u v) := by
  have hp : p.Prime := Fact.out
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold slotWeightMatrix
  dsimp only
  split_ifs with ht
  · let ta := (slotEquiv n).symm u
    let sb := (slotEquiv n).symm v
    let k := halfPole n ta.1
    let m := kernelPoleOrder n k
    let a := ta.2.val
    let b := sb.2.val
    have hk := halfPole_mem n hn ta.1
    have hkc : center n ≤ k := by unfold k halfPole; omega
    -- Show `FormalValAtLeast p (-C_{k, a + b}) (W u v)`, then double!
    have hformal : FormalValAtLeast p (-(refinedOrderCost n p k (a + b) : ℤ))
        (∑ l : Fin m,
          if a + b ≤ m - 1 - l.val then
            MvPolynomial.C ((slotLocalSeries n k).coeff (m - 1 - l.val - (a + b)) /
              (p : ℚ) ^ (a + b)) * pairedPacket n k l.val
          else 0) := by
      apply formalValAtLeast_sum; intro l _
      split_ifs with hle
      · let d := m - 1 - l.val - (a + b)
        have hdm : d < m := by have := l.isLt; omega
        have hQ := slotLocalSeries_coeff_valAtLeast n p hn hsq k hk d (by rw [← kernelPoleOrder_eq_poleOrder]; exact hdm)
        have hpow_val : padicValRat p ((p : ℚ) ^ (a + b)) = ((a + b : ℕ) : ℤ) := by
          induction (a + b) with
          | zero => simp
          | succ r ihr =>
            rw [pow_succ, padicValRat.mul (pow_ne_zero r hpne) hpne, ihr, padicValRat.self hp.one_lt]
            push_cast; ring
        have hdiv : ValAtLeast p
            (siteBaseVal n p k - (effectiveOrderLoss n p k d : ℤ) - ((a + b : ℕ) : ℤ))
            ((slotLocalSeries n k).coeff d / (p : ℚ) ^ (a + b)) := by
          by_cases hq0 : (slotLocalSeries n k).coeff d = 0
          · rw [hq0, zero_div]; exact valAtLeast_zero p _
          · right
            have hval := hQ.resolve_left hq0
            rw [padicValRat.div hq0 (pow_ne_zero _ hpne), hpow_val]
            linarith
        have hpkt := pairedPacket_formalValAtLeast n p hn hsq k hk hkc l.val
        have hprod := formalValAtLeast_C_mul hdiv hpkt
        -- Compare with `refinedOrderCost n p k (a + b)`
        have hle_sup : ((a + b : ℕ) : ℤ) - siteBaseVal n p k +
            (effectiveOrderLoss n p k d : ℤ) +
            ((l.val + 5 : ℕ) : ℤ) * (harmonicIndicator n p k l.val : ℤ) ≤
            (refinedOrderCost n p k (a + b) : ℤ) := by
          have hl_mem : l.val ∈ (range m).filter (fun l' => a + b ≤ m - 1 - l') :=
            Finset.mem_filter.mpr ⟨mem_range.mpr l.isLt, hle⟩
          have hsup := Finset.le_sup (f := fun l' =>
            (((a + b : ℕ) : ℤ) - siteBaseVal n p k +
              (effectiveOrderLoss n p k (m - 1 - l' - (a + b)) : ℤ) +
              ((l' + 5 : ℕ) : ℤ) * (harmonicIndicator n p k l' : ℤ)).toNat) hl_mem
          have hsupZ : ((((a + b : ℕ) : ℤ) - siteBaseVal n p k +
              (effectiveOrderLoss n p k d : ℤ) +
              ((l.val + 5 : ℕ) : ℤ) * (harmonicIndicator n p k l.val : ℤ)).toNat : ℤ) ≤
              (refinedOrderCost n p k (a + b) : ℤ) := by
            exact_mod_cast hsup
          omega
        exact formalValAtLeast_mono hprod (by linarith)
      · exact formalValAtLeast_zero p _
    have hdoub := doubledFormalValAtLeast_of_formal hformal
    apply doubledFormalValAtLeast_mono hdoub
    -- Verify `2 * C_{k, a + b} ≤ B_{k, a} + B_{k, b}` (or `W u v = 0` if `a + b ≥ m`)
    by_cases hab : a + b < m
    · have hle_a : refinedOrderCost n p k (a + b) ≤ slotCost n p u := by
        unfold slotCost refinedSlotCost
        change refinedOrderCost n p k (a + b) ≤
          ((range m).filter (fun r => a ≤ r)).sup (fun r => refinedOrderCost n p k r)
        exact Finset.le_sup (f := fun r => refinedOrderCost n p k r)
          (Finset.mem_filter.mpr ⟨mem_range.mpr hab, by omega⟩)
      have hle_b : refinedOrderCost n p k (a + b) ≤ slotCost n p v := by
        unfold slotCost refinedSlotCost
        change refinedOrderCost n p k (a + b) ≤
          ((range (kernelPoleOrder n (halfPole n sb.1))).filter (fun r => b ≤ r)).sup
            (fun r => refinedOrderCost n p (halfPole n sb.1) r)
        rw [← ht]
        exact Finset.le_sup (f := fun r => refinedOrderCost n p k r)
          (Finset.mem_filter.mpr ⟨mem_range.mpr hab, by omega⟩)
      omega
    · -- When `a + b ≥ m`, every `l : Fin m` fails `a + b ≤ m - 1 - l.val`, so `C_{k, a+b} = 0`!
      have hC0 : refinedOrderCost n p k (a + b) = 0 := by
        unfold refinedOrderCost
        have hemp : (range m).filter (fun l => a + b ≤ m - 1 - l) = ∅ := by
          ext l; simp only [Finset.mem_filter, mem_range, Finset.notMem_empty, iff_false]
          omega
        change ((range m).filter (fun l => a + b ≤ m - 1 - l)).sup _ = 0
        rw [hemp, Finset.sup_empty]; rfl
      rw [hC0]; omega
  · exact doubledFormalValAtLeast_zero p _


end OddZetaSix.B40a
