import OddZetaSix.B40a.Arithmetic.PeriodicAffine
import OddZetaSix.B40a.Arithmetic.SmallAffine010
import OddZetaSix.B40a.Certificate.Generated.Small014
import OddZetaSix.B40a.Certificate.Generated.Small015

namespace OddZetaSix.B40a.Cert
set_option maxHeartbeats 0
set_option maxRecDepth 32768

private theorem small014_cell_0 : PeriodAffine.check ⟨qfrac 12 19, qfrac 43 68, 28558786⟩=true := by decide +kernel
private theorem small014_cell_1 : PeriodAffine.check ⟨qfrac 43 68, qfrac 26 41, 63710084⟩=true := by decide +kernel
private theorem small014_cell_2 : PeriodAffine.check ⟨qfrac 26 41, qfrac 59 93, 9077776⟩=true := by decide +kernel
private theorem small014_cell_3 : PeriodAffine.check ⟨qfrac 59 93, qfrac 75 118, 41359467⟩=true := by decide +kernel
private theorem small014_cell_4 : PeriodAffine.check ⟨qfrac 75 118, qfrac 7 11, 27203288⟩=true := by decide +kernel
private theorem small014_cell_5 : PeriodAffine.check ⟨qfrac 7 11, qfrac 16 25, 131979222⟩=true := by decide +kernel
private theorem small014_cell_6 : PeriodAffine.check ⟨qfrac 16 25, qfrac 9 14, 221874730⟩=true := by decide +kernel
private theorem small014_cell_7 : PeriodAffine.check ⟨qfrac 9 14, qfrac 38 59, 99638184⟩=true := by decide +kernel
private theorem small014_cell_8 : PeriodAffine.check ⟨qfrac 38 59, qfrac 49 76, 56510108⟩=true := by decide +kernel
private theorem small014_cell_9 : PeriodAffine.check ⟨qfrac 49 76, qfrac 20 31, 36393384⟩=true := by decide +kernel
private theorem small014_cell_10 : PeriodAffine.check ⟨qfrac 20 31, qfrac 11 17, 167767433⟩=true := by decide +kernel
private theorem small014_cell_11 : PeriodAffine.check ⟨qfrac 11 17, qfrac 28 43, 238609765⟩=true := by decide +kernel
private theorem small014_cell_12 : PeriodAffine.check ⟨qfrac 28 43, qfrac 77 118, 89737317⟩=true := by decide +kernel
private theorem small014_cell_13 : PeriodAffine.check ⟨qfrac 77 118, qfrac 49 75, 55485097⟩=true := by decide +kernel
private theorem small014_cell_14 : PeriodAffine.check ⟨qfrac 49 75, qfrac 55 84, 110658410⟩=true := by decide +kernel
private theorem small014_cell_15 : PeriodAffine.check ⟨qfrac 55 84, qfrac 61 93, 94151742⟩=true := by decide +kernel
private theorem small014_cell_16 : PeriodAffine.check ⟨qfrac 61 93, qfrac 21 32, 27419252⟩=true := by decide +kernel
private theorem small014_cell_17 : PeriodAffine.check ⟨qfrac 21 32, qfrac 25 38, 107860860⟩=true := by decide +kernel
private theorem small014_cell_18 : PeriodAffine.check ⟨qfrac 25 38, qfrac 27 41, 41269015⟩=true := by decide +kernel
private theorem small014_cell_19 : PeriodAffine.check ⟨qfrac 27 41, qfrac 33 50, 93972067⟩=true := by decide +kernel
private theorem small014_cell_20 : PeriodAffine.check ⟨qfrac 33 50, qfrac 39 59, 16560033⟩=true := by decide +kernel
private theorem small014_cell_21 : PeriodAffine.check ⟨qfrac 39 59, qfrac 45 68, 12238189⟩=true := by decide +kernel
private theorem small014_cell_22 : PeriodAffine.check ⟨qfrac 45 68, qfrac 2 3, 134059558⟩=true := by decide +kernel
private theorem small014_cell_23 : PeriodAffine.check ⟨qfrac 2 3, qfrac 79 118, 108045772⟩=true := by decide +kernel
private theorem small014_cell_24 : PeriodAffine.check ⟨qfrac 79 118, qfrac 51 76, 63167638⟩=true := by decide +kernel
private theorem small014_cell_25 : PeriodAffine.check ⟨qfrac 51 76, qfrac 29 43, 144630464⟩=true := by decide +kernel
private theorem small014_cell_26 : PeriodAffine.check ⟨qfrac 29 43, qfrac 23 34, 93700849⟩=true := by decide +kernel
private theorem small014_cell_27 : PeriodAffine.check ⟨qfrac 23 34, qfrac 21 31, 13107718⟩=true := by decide +kernel
private theorem small014_cell_28 : PeriodAffine.check ⟨qfrac 21 31, qfrac 40 59, 8296134⟩=true := by decide +kernel
private theorem small014_cell_29 : PeriodAffine.check ⟨qfrac 40 59, qfrac 19 28, 10092481⟩=true := by decide +kernel
private theorem small014_cell_30 : PeriodAffine.check ⟨qfrac 19 28, qfrac 17 25, 26460393⟩=true := by decide +kernel
private theorem small014_cell_31 : PeriodAffine.check ⟨qfrac 17 25, qfrac 28 41, 169874548⟩=true := by decide +kernel

theorem small014_affine_check : small014.all PeriodAffine.check=true := by
  simp only [small014, List.all_cons, List.all_nil, Bool.and_self,
    small014_cell_0,
    small014_cell_1,
    small014_cell_2,
    small014_cell_3,
    small014_cell_4,
    small014_cell_5,
    small014_cell_6,
    small014_cell_7,
    small014_cell_8,
    small014_cell_9,
    small014_cell_10,
    small014_cell_11,
    small014_cell_12,
    small014_cell_13,
    small014_cell_14,
    small014_cell_15,
    small014_cell_16,
    small014_cell_17,
    small014_cell_18,
    small014_cell_19,
    small014_cell_20,
    small014_cell_21,
    small014_cell_22,
    small014_cell_23,
    small014_cell_24,
    small014_cell_25,
    small014_cell_26,
    small014_cell_27,
    small014_cell_28,
    small014_cell_29,
    small014_cell_30,
    small014_cell_31]

private theorem small015_cell_0 : PeriodAffine.check ⟨qfrac 28 41, qfrac 13 19, 80630325⟩=true := by decide +kernel
private theorem small015_cell_1 : PeriodAffine.check ⟨qfrac 13 19, qfrac 35 51, 137463510⟩=true := by decide +kernel
private theorem small015_cell_2 : PeriodAffine.check ⟨qfrac 35 51, qfrac 81 118, 11477603⟩=true := by decide +kernel
private theorem small015_cell_3 : PeriodAffine.check ⟨qfrac 81 118, qfrac 11 16, 74673381⟩=true := by decide +kernel
private theorem small015_cell_4 : PeriodAffine.check ⟨qfrac 11 16, qfrac 64 93, 38435322⟩=true := by decide +kernel
private theorem small015_cell_5 : PeriodAffine.check ⟨qfrac 64 93, qfrac 29 42, 137947775⟩=true := by decide +kernel
private theorem small015_cell_6 : PeriodAffine.check ⟨qfrac 29 42, qfrac 47 68, 42971272⟩=true := by decide +kernel
private theorem small015_cell_7 : PeriodAffine.check ⟨qfrac 47 68, qfrac 52 75, 138358014⟩=true := by decide +kernel
private theorem small015_cell_8 : PeriodAffine.check ⟨qfrac 52 75, qfrac 41 59, 108057515⟩=true := by decide +kernel
private theorem small015_cell_9 : PeriodAffine.check ⟨qfrac 41 59, qfrac 23 33, 148791586⟩=true := by decide +kernel
private theorem small015_cell_10 : PeriodAffine.check ⟨qfrac 23 33, qfrac 53 76, 29987445⟩=true := by decide +kernel
private theorem small015_cell_11 : PeriodAffine.check ⟨qfrac 53 76, qfrac 30 43, 23258875⟩=true := by decide +kernel
private theorem small015_cell_12 : PeriodAffine.check ⟨qfrac 30 43, qfrac 65 93, 97260486⟩=true := by decide +kernel
private theorem small015_cell_13 : PeriodAffine.check ⟨qfrac 65 93, qfrac 7 10, 86441705⟩=true := by decide +kernel
private theorem small015_cell_14 : PeriodAffine.check ⟨qfrac 7 10, qfrac 59 84, 84707842⟩=true := by decide +kernel
private theorem small015_cell_15 : PeriodAffine.check ⟨qfrac 59 84, qfrac 83 118, 37601208⟩=true := by decide +kernel
private theorem small015_cell_16 : PeriodAffine.check ⟨qfrac 83 118, qfrac 12 17, 97227149⟩=true := by decide +kernel
private theorem small015_cell_17 : PeriodAffine.check ⟨qfrac 12 17, qfrac 53 75, 5553268⟩=true := by decide +kernel
private theorem small015_cell_18 : PeriodAffine.check ⟨qfrac 53 75, qfrac 29 41, 6456726⟩=true := by decide +kernel
private theorem small015_cell_19 : PeriodAffine.check ⟨qfrac 29 41, qfrac 22 31, 39018879⟩=true := by decide +kernel
private theorem small015_cell_20 : PeriodAffine.check ⟨qfrac 22 31, qfrac 27 38, 18009757⟩=true := by decide +kernel
private theorem small015_cell_21 : PeriodAffine.check ⟨qfrac 27 38, qfrac 42 59, 25424848⟩=true := by decide +kernel
private theorem small015_cell_22 : PeriodAffine.check ⟨qfrac 42 59, qfrac 5 7, 49305418⟩=true := by decide +kernel
private theorem small015_cell_23 : PeriodAffine.check ⟨qfrac 5 7, qfrac 23 32, 125299792⟩=true := by decide +kernel
private theorem small015_cell_24 : PeriodAffine.check ⟨qfrac 23 32, qfrac 18 25, 21308895⟩=true := by decide +kernel
private theorem small015_cell_25 : PeriodAffine.check ⟨qfrac 18 25, qfrac 85 118, 18341055⟩=true := by decide +kernel
private theorem small015_cell_26 : PeriodAffine.check ⟨qfrac 85 118, qfrac 67 93, 4991731⟩=true := by decide +kernel
private theorem small015_cell_27 : PeriodAffine.check ⟨qfrac 67 93, qfrac 49 68, 8706537⟩=true := by decide +kernel
private theorem small015_cell_28 : PeriodAffine.check ⟨qfrac 49 68, qfrac 31 43, 18957449⟩=true := by decide +kernel
private theorem small015_cell_29 : PeriodAffine.check ⟨qfrac 31 43, qfrac 13 18, 74650596⟩=true := by decide +kernel
private theorem small015_cell_30 : PeriodAffine.check ⟨qfrac 13 18, qfrac 55 76, 90207842⟩=true := by decide +kernel
private theorem small015_cell_31 : PeriodAffine.check ⟨qfrac 55 76, qfrac 37 51, 117121081⟩=true := by decide +kernel

theorem small015_affine_check : small015.all PeriodAffine.check=true := by
  simp only [small015, List.all_cons, List.all_nil, Bool.and_self,
    small015_cell_0,
    small015_cell_1,
    small015_cell_2,
    small015_cell_3,
    small015_cell_4,
    small015_cell_5,
    small015_cell_6,
    small015_cell_7,
    small015_cell_8,
    small015_cell_9,
    small015_cell_10,
    small015_cell_11,
    small015_cell_12,
    small015_cell_13,
    small015_cell_14,
    small015_cell_15,
    small015_cell_16,
    small015_cell_17,
    small015_cell_18,
    small015_cell_19,
    small015_cell_20,
    small015_cell_21,
    small015_cell_22,
    small015_cell_23,
    small015_cell_24,
    small015_cell_25,
    small015_cell_26,
    small015_cell_27,
    small015_cell_28,
    small015_cell_29,
    small015_cell_30,
    small015_cell_31]

end OddZetaSix.B40a.Cert
