import OddZetaSix.B40a.Arithmetic.PeriodicAffine

noncomputable section
namespace OddZetaSix.B40a
open Set MeasureTheory
namespace Cert.PeriodAffine

def linearTerm (b : ℤ) := b
def squareTerm (b : ℤ) := (b-1)^2/4
def linearProfile (r : ArithRow) := realVal (sumLine r linearTerm (adjacent (periodLines r)))
def squareProfile (r : ArithRow) := realVal (sumLine r squareTerm (adjacent (periodLines r)))

private theorem moment_integrable (τ : ℝ) (F : ℤ → ℤ) :
    IntervalIntegrable (fun u => (F (periodicScore τ u):ℝ)) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mpr
  apply Measure.integrableOn_of_bounded (M:=∑ j ∈ Finset.range 17, |(F (j:ℤ):ℝ)|) (measure_Ioc_lt_top.ne)
  · have hm : Measurable (fun u => periodicScore τ u) := by
      unfold periodicScore periodicCount; fun_prop
    exact ((measurable_of_countable (f:=fun b : ℤ => (F b:ℝ))).comp hm).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro u
    let b := periodicScore τ u
    have h := periodicScore_bounds τ u
    have hmem : b.toNat ∈ Finset.range 17 := Finset.mem_range.mpr (by dsimp [b]; omega)
    have H := Finset.single_le_sum (f:=fun j : ℕ => |(F (j:ℤ):ℝ)|)
      (fun j _ => abs_nonneg _) hmem
    simpa only [Int.toNat_of_nonneg h.1,Real.norm_eq_abs,b] using H

/-- Continuous prime-band majorant associated to one row in inverse scale. -/
def smallTileWeight (r : ArithRow) (k : ℕ) (P : ℝ) :=
  let t := 1/P-k
  40*linearProfile r t+P/2*(linearProfile r t+squareProfile r t)

theorem primeExponent_le_small_tile (n p k : ℕ) [Fact p.Prime] (hn : 0<n)
    (hsq : 84*n<p^2) (ε : ℝ) (hε : 0<ε) (hband : ε*(n:ℝ)≤p)
    (r : ArithRow) (ok : check r = true)
    (ht : (n:ℝ)/p-k ∈ Ioo (r.left:ℝ) r.right) :
    primeExponent n p ≤ (n:ℝ)*smallTileWeight r k ((p:ℝ)/n) + (7680/ε+432) := by
  let t := (n:ℝ)/p-k
  let q := 2*fiveRank n/p
  let f := fun u : ℝ => (linearTerm (periodicScore t u):ℝ)
  let g := fun u : ℝ => (squareTerm (periodicScore t u):ℝ)
  have hpR : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have hbase := primeExponent_le_full_period_integral n p hn hsq ε hε hband
  have hshift (u : ℝ) : periodicScore ((n:ℝ)/p) u = periodicScore t u := by
    simpa [t] using periodicScore_add_int (k:ℤ) t u
  have hs (u : ℝ) : (slotEnvelope q (periodicScore ((n:ℝ)/p) u).toNat : ℝ) =
      ((q:ℝ)+1)*f u+g u := by
    rw [hshift]
    let s := periodicScore t u
    have hb : 0 ≤ s ∧ s ≤ 16 := periodicScore_bounds t u
    change (slotEnvelope q s.toNat:ℝ) = ((q:ℝ)+1)*(s:ℝ)+(((s-1)^2/4:ℤ):ℝ)
    obtain ⟨hslo,hshi⟩ := hb
    interval_cases s <;> norm_num [slotEnvelope,Int.toNat] <;> ring
  change primeExponent n p ≤ (p:ℝ)/2 * (∫ u in (0:ℝ)..1, (slotEnvelope q
    (periodicScore ((n:ℝ)/p) u).toNat:ℝ)) + _ at hbase
  simp_rw [hs] at hbase
  have hi := moment_integrable t linearTerm
  have hj := moment_integrable t squareTerm
  rw [intervalIntegral.integral_add (hi.const_mul _) hj,intervalIntegral.integral_const_mul] at hbase
  have hf : (∫ u in (0:ℝ)..1,f u)=linearProfile r t := period_integral_affine r ok linearTerm ht
  have hg : (∫ u in (0:ℝ)..1,g u)=squareProfile r t := period_integral_affine r ok squareTerm ht
  rw [hf,hg] at hbase
  have hf0 : 0 ≤ linearProfile r t := by
    rw [←hf]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => by
      dsimp [f,linearTerm]; exact_mod_cast (periodicScore_bounds t u).1)
  have hqNat : q*p ≤ 80*n := (Nat.div_mul_le_self (2*fiveRank n) p).trans
    (by unfold fiveRank; omega)
  have hq : (q:ℝ)*(p:ℝ) ≤ 80*(n:ℝ) := by exact_mod_cast hqNat
  apply hbase.trans
  unfold smallTileWeight
  rw [show (1:ℝ)/((p:ℝ)/n) - k = t by dsimp [t]; field_simp]
  have hcross : (n:ℝ)*((p:ℝ)/n)=(p:ℝ) := by field_simp
  nlinarith only [mul_le_mul_of_nonneg_right hq hf0,
    congrArg (fun x : ℝ => x*(linearProfile r t+squareProfile r t)) hcross]

end Cert.PeriodAffine
end OddZetaSix.B40a
