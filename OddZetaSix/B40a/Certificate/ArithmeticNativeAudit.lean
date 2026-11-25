import OddZetaSix.B40a.Arithmetic.CertificateRows

/-! The middle-band budget uses this native row check. The final theorem
therefore carries its compiler-generated computational axiom. -/
namespace OddZetaSix.B40a.Cert.Native
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem middle_rows_checked : middleRows.all (checkArithRow false) = true := by
  native_decide

theorem arithmetic_row_sums_checked :
    (smallRows.map (rowValue true)).sum + (middleRows.map (rowValue false)).sum + highTail ≤
      (61405/10000 : ℚ) :=
  arithmetic_certificate_row_sums middle_rows_checked

#print axioms middle_rows_checked
#print axioms arithmetic_row_sums_checked

end OddZetaSix.B40a.Cert.Native
