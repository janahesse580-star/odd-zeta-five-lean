import OddZetaSix.B40a.Certificate.Generated.All
import OddZetaSix.B40a.Arithmetic.SmallAffine000
import OddZetaSix.B40a.Arithmetic.SmallAffine002
import OddZetaSix.B40a.Arithmetic.SmallAffine004
import OddZetaSix.B40a.Arithmetic.SmallAffine006
import OddZetaSix.B40a.Arithmetic.SmallAffine008
import OddZetaSix.B40a.Arithmetic.SmallAffine010
import OddZetaSix.B40a.Arithmetic.SmallAffine012
import OddZetaSix.B40a.Arithmetic.SmallAffine014
import OddZetaSix.B40a.Arithmetic.SmallAffine016
import OddZetaSix.B40a.Arithmetic.SmallAffine018
import OddZetaSix.B40a.Arithmetic.SmallAffine020
import OddZetaSix.B40a.Arithmetic.SmallAffine022

namespace OddZetaSix.B40a.Cert
set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem smallRows_affine_check : smallRows.all PeriodAffine.check = true := by
  simp only [smallRows,List.all_append,small000_affine_check,
    small001_affine_check,
    small002_affine_check,
    small003_affine_check,
    small004_affine_check,
    small005_affine_check,
    small006_affine_check,
    small007_affine_check,
    small008_affine_check,
    small009_affine_check,
    small010_affine_check,
    small011_affine_check,
    small012_affine_check,
    small013_affine_check,
    small014_affine_check,
    small015_affine_check,
    small016_affine_check,
    small017_affine_check,
    small018_affine_check,
    small019_affine_check,
    small020_affine_check,
    small021_affine_check,
    small022_affine_check,Bool.and_self]


end OddZetaSix.B40a.Cert
