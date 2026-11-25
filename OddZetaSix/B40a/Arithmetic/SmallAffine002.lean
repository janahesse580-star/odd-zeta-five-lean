import OddZetaSix.B40a.Arithmetic.PeriodicAffine
import OddZetaSix.B40a.Certificate.Generated.Small002
import OddZetaSix.B40a.Certificate.Generated.Small003

namespace OddZetaSix.B40a.Cert
set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem small002_affine_check : small002.all PeriodAffine.check = true := by decide +kernel

theorem small003_affine_check : small003.all PeriodAffine.check = true := by decide +kernel

end OddZetaSix.B40a.Cert
