import OddZetaSix.B40a.Padic.WindowNumerator

/-! Identification of the actual coefficients in the six-term window
with the jets of the monomials and a single scalar unit series. -/
noncomputable section
namespace OddZetaSix.B40a
open Polynomial

def windowNum (n k : ℕ) : ℚ[X] :=
  taylor (-(k : ℚ)) (C (normalization n) * numerator n)

def windowCof (n k : ℕ) : ℚ[X] :=
  taylor (-(k : ℚ)) (regularDenominator n k)

def windowSeries (n k : ℕ) : ℚ[X] :=
  truncatedQuotient (windowNum n k) (windowCof n k) 6

theorem windowSeries_mem (n k : ℕ) [Fact (primeIndex n).Prime] (hk : k ∈ gateWindow n) :
    PolyInSubring (sixGateIntegralRing (primeIndex n)) (windowSeries n k) := by
  have hk' : k ∈ kernelPoleSet n := (Finset.mem_filter.mp (gateWindow_eq_filter n ▸ hk)).1
  have hlarge : 50*n < primeIndex n := by unfold primeIndex; omega
  let S := sixGateIntegralRing (primeIndex n)
  unfold windowSeries windowNum windowCof
  apply truncatedQuotient_in_subring
  · apply polyInSubring_taylor _ (S.neg_mem (natCast_mem S k))
    exact polyInSubring_mul (polyInSubring_C (normalization_integral n _ hlarge))
      (numerator_integral n S)
  · exact cofactor_integral n _ k hk'
  · exact cofactor_inv_coeff_mem n _ k hlarge hk'

theorem windowCof_ne_zero (n k : ℕ) (hk : k ∈ kernelPoleSet n) :
    (windowCof n k).coeff 0 ≠ 0 := by
  rw [windowCof,regularDenominator_eq_erase n k hk]
  exact kernelLocalCofactor_ne_zero_coeff n k

theorem windowSeries_zero_unit (n k : ℕ) [Fact (primeIndex n).Prime] (hk : k ∈ gateWindow n) :
    (windowSeries n k).coeff 0 ≠ 0 ∧
      padicValRat (primeIndex n) ((windowSeries n k).coeff 0) = 0 := by
  have hk' : k ∈ kernelPoleSet n := (Finset.mem_filter.mp (gateWindow_eq_filter n ▸ hk)).1
  have hlarge : 50*n < primeIndex n := by unfold primeIndex; omega
  have hnonzero := windowCof_ne_zero n k hk'
  have hi := cofactor_integral n (primeIndex n) k hk' 0
  have hv := cofactor_inv_coeff_mem n (primeIndex n) k hlarge hk'
  change 0 ≤ padicValRat (primeIndex n) ((windowCof n k).coeff 0) at hi
  change 0 ≤ padicValRat (primeIndex n) ((windowCof n k).coeff 0)⁻¹ at hv
  rw [padicValRat.inv] at hv
  have hval : padicValRat (primeIndex n) ((windowCof n k).coeff 0) = 0 := by omega
  have hn := window_numerator_unit n k hk
  change (windowNum n k).coeff 0 ≠ 0 ∧ padicValRat (primeIndex n) ((windowNum n k).coeff 0)=0 at hn
  rw [windowSeries,truncatedQuotient_coeff_zero _ _ (by decide)]
  exact ⟨div_ne_zero hn.1 hnonzero, by rw [padicValRat.div hn.1 hnonzero,hn.2,hval,sub_zero]⟩

theorem window_principal_eq_jet_coeff (n k l : ℕ) (f g : ℚ[X])
    (hk : k ∈ gateWindow n) (hl : 1 ≤ l ∧ l ≤ 6) :
    localPrincipal n k l f g =
      (windowSeries n k * (taylor ((center n : ℚ)-k) f *
        taylor ((center n : ℚ)-k) g)).coeff (6-l) := by
  have hk' : k ∈ kernelPoleSet n := (Finset.mem_filter.mp (gateWindow_eq_filter n ▸ hk)).1
  have hc := windowCof_ne_zero n k hk'
  have horder : poleOrder n k = 6 := (kernelPoleOrder_eq_poleOrder n k).symm.trans
    (gateWindow_order n k hk)
  let J := taylor ((center n : ℚ)-k) f * taylor ((center n : ℚ)-k) g
  have hj :
      taylor (-(k : ℚ)) ((f*g).comp (X+C (center n : ℚ))) = J := by
    simp only [J, taylor_apply,comp_assoc,add_comp,X_comp,C_comp,mul_comp]
    congr 1 <;> congr 1 <;> rw [add_assoc,← C_add] <;> congr 2 <;> ring
  unfold localPrincipal
  rw [taylor_mul,hj,horder]
  change localQuotient (windowNum n k * J) (windowCof n k) (6-l) =
    (windowSeries n k * J).coeff (6-l)
  apply localQuotient_eq_coeff_of_congruence _ _ _ hc 6
  · have h := truncatedQuotient_dvd (windowNum n k) (windowCof n k) hc 6
    change X^6 ∣ windowNum n k - windowCof n k * windowSeries n k at h
    rw [show windowNum n k * J - windowCof n k * (windowSeries n k * J) =
      (windowNum n k - windowCof n k * windowSeries n k)*J by ring]
    exact dvd_mul_of_dvd_left h J
  · omega

end OddZetaSix.B40a
