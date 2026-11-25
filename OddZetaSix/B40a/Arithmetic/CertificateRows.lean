import OddZetaSix.B40a.Certificate.Generated.All
import Mathlib.Data.Rat.Floor

/-! Soundness of upward rounding for the arithmetic rows. These lemmas
bound the values calculated by the rational checker. -/
namespace OddZetaSix.B40a.Cert

theorem qfloor_eq_floor (q : ℚ) : qfloor q = ⌊q⌋ := Rat.floor_def'.symm

theorem qceil_eq_ceil (q : ℚ) : qceil q = ⌈q⌉ := by
  unfold qceil
  rw [qfloor_eq_floor,← Int.ceil_neg,neg_neg]

theorem mul_bigUnit_le_rounded (q : ℚ) :
    q * bigUnit ≤ (qceil (q * bigUnit) : ℚ) := by
  rw [qceil_eq_ceil]
  exact Int.le_ceil _

theorem le_roundUp (q : ℚ) : q ≤ roundUp q := by
  unfold roundUp
  apply (le_div_iff₀ (by norm_num [bigUnit] : (0 : ℚ) < bigUnit)).mpr
  exact mul_bigUnit_le_rounded q

def rowValue (small : Bool) (r : ArithRow) : ℚ :=
  (r.right-r.left) * (if small then smallValue r.left r.right else middleValue ((r.left+r.right)/2))

theorem checkArithRow_sound (small : Bool) (r : ArithRow) (h : checkArithRow small r = true) :
    r.left < r.right ∧ 0 ≤ r.upper ∧ rowValue small r ≤ (r.upper : ℚ)/bigUnit := by
  unfold checkArithRow at h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at h
  refine ⟨h.1.1,h.1.2,(le_div_iff₀ (by norm_num [bigUnit] : (0 : ℚ) < bigUnit)).mpr ?_⟩
  have hwide := mul_bigUnit_le_rounded (rowValue small r)
  rw [show qceil (rowValue small r * bigUnit) = r.upper from h.2] at hwide
  exact hwide

theorem checkedArithRows_sum_bound (small : Bool) (rs : List ArithRow)
    (h : rs.all (checkArithRow small) = true) :
    (rs.map (rowValue small)).sum ≤ (arithTotal rs : ℚ)/bigUnit := by
  induction rs with
  | nil => simp [arithTotal]
  | cons r rs ih =>
    simp only [List.all_cons,Bool.and_eq_true] at h
    have hr := (checkArithRow_sound small r h.1).2.2
    have ht := ih h.2
    simpa only [arithTotal,List.map_cons,List.sum_cons,Int.cast_add,add_div] using add_le_add hr ht

theorem small_certified_row_sum :
    (smallRows.map (rowValue true)).sum ≤ (arithTotal smallRows : ℚ)/bigUnit :=
  checkedArithRows_sum_bound true _ smallRows_ok

theorem arithmetic_certificate_row_sums
    (hm : middleRows.all (checkArithRow false) = true) :
    (smallRows.map (rowValue true)).sum + (middleRows.map (rowValue false)).sum + highTail ≤
      (61405/10000 : ℚ) := by
  have h := add_le_add_right (add_le_add small_certified_row_sum
    (checkedArithRows_sum_bound false _ hm)) highTail
  have he : (arithTotal smallRows : ℚ)/bigUnit + (arithTotal middleRows : ℚ)/bigUnit + highTail =
      cCert := by
    unfold cCert qfrac bigUnit
    push_cast
    ring
  simp only [add_comm highTail] at h
  rw [he] at h
  exact h.trans numericC_ok

end OddZetaSix.B40a.Cert
