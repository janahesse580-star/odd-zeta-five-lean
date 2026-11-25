import OddZetaSix.B40a.Arithmetic.PeriodicAffine
import OddZetaSix.B40a.Arithmetic.SmallAffine018
import OddZetaSix.B40a.Certificate.Generated.Small022

namespace OddZetaSix.B40a.Cert
set_option maxHeartbeats 0
set_option maxRecDepth 32768

private theorem small022_cell_0 : PeriodAffine.check ⟨qfrac 92 93, qfrac 117 118, 165971226⟩=true := by decide +kernel
private theorem small022_cell_1 : PeriodAffine.check ⟨qfrac 117 118, qfrac 1 1, 644042432⟩=true := by decide +kernel

theorem small022_affine_check : small022.all PeriodAffine.check=true := by
  simp only [small022, List.all_cons, List.all_nil, Bool.and_self,
    small022_cell_0,
    small022_cell_1]

end OddZetaSix.B40a.Cert
