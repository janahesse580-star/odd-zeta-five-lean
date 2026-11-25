import OddZetaSix.B40a.Arithmetic.CertificateRows
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OddZetaSix.B40a.Cert

def middleRadii : List ℕ := [16,17,25,34,59]
/-- These positive frequencies include all crossings between signed wall
lines, the half-period boundaries, the normalization floors and the row cap. -/
def middleFrequencies : List ℕ :=
  (([25,32,34,50,80] ++ middleRadii ++ middleRadii.flatMap
    (fun i => middleRadii.flatMap (fun j => [i+j,i-j]))).eraseDups).filter (·>0)

def middleFloor (r : ArithRow) (k : ℕ) : ℤ := ((k:ℤ)*r.right.den)/r.right.num

def checkMiddleFrequencies (r : ArithRow) : Bool :=
  decide (0<r.left ∧ r.left<r.right) && middleFrequencies.all (fun k =>
    let q := middleFloor r k
    decide (0≤q ∧ q*r.right.num≤(k:ℤ)*r.right.den ∧
      (k:ℤ)*r.left.den≤(q+1)*r.left.num))

theorem middle_floor_of_row_check {r : ArithRow} (hc : checkMiddleFrequencies r=true)
    {P : ℝ} (hP : P ∈ Set.Ioo (r.left:ℝ) r.right) {k : ℕ} (hk : k∈middleFrequencies) :
    ⌊(k:ℝ)/P⌋ = middleFloor r k := by
  simp only [checkMiddleFrequencies,Bool.and_eq_true,decide_eq_true_eq] at hc
  have H := of_decide_eq_true (List.all_eq_true.mp hc.2 k hk)
  let q := middleFloor r k
  change 0≤q ∧ q*r.right.num≤(k:ℤ)*r.right.den ∧
    (k:ℤ)*r.left.den≤(q+1)*r.left.num at H
  have hq : (0:ℝ)≤q := by exact_mod_cast H.1
  have hr (z : ℚ) : (z:ℝ)=(z.num:ℝ)/z.den := by
    exact Rat.cast_def z
  have hpos (z : ℚ) : (0:ℝ)<z.den := by exact_mod_cast z.den_pos
  have lo : (q:ℝ)*r.right ≤ k := by
    rw [hr r.right,←mul_div_assoc,div_le_iff₀ (hpos _)]
    exact_mod_cast H.2.1
  have hi : (k:ℝ) ≤ ((q:ℝ)+1)*r.left := by
    rw [hr r.left,←mul_div_assoc,le_div_iff₀ (hpos _)]
    exact_mod_cast H.2.2
  have h0 : 0<P := (show (0:ℝ)<r.left by exact_mod_cast hc.1.1).trans hP.1
  apply Int.floor_eq_iff.mpr
  constructor
  · exact (le_div_iff₀ h0).mpr ((mul_le_mul_of_nonneg_left hP.2.le hq).trans lo)
  · apply (div_lt_iff₀ h0).mpr
    exact hi.trans_lt (mul_lt_mul_of_pos_left hP.1 (by positivity))

end OddZetaSix.B40a.Cert
