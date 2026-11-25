import OddZetaSix.B40a.Arithmetic.PeriodicAffine
import OddZetaSix.B40a.Arithmetic.SmallAffine008
import OddZetaSix.B40a.Certificate.Generated.Small012
import OddZetaSix.B40a.Certificate.Generated.Small013

namespace OddZetaSix.B40a.Cert
set_option maxHeartbeats 0
set_option maxRecDepth 32768

private theorem small012_cell_0 : PeriodAffine.check ⟨qfrac 41 75, qfrac 23 42, 34862163⟩=true := by decide +kernel
private theorem small012_cell_1 : PeriodAffine.check ⟨qfrac 23 42, qfrac 17 31, 29311165⟩=true := by decide +kernel
private theorem small012_cell_2 : PeriodAffine.check ⟨qfrac 17 31, qfrac 28 51, 24922928⟩=true := by decide +kernel
private theorem small012_cell_3 : PeriodAffine.check ⟨qfrac 28 51, qfrac 65 118, 75996934⟩=true := by decide +kernel
private theorem small012_cell_4 : PeriodAffine.check ⟨qfrac 65 118, qfrac 21 38, 79922426⟩=true := by decide +kernel
private theorem small012_cell_5 : PeriodAffine.check ⟨qfrac 21 38, qfrac 5 9, 143225761⟩=true := by decide +kernel
private theorem small012_cell_6 : PeriodAffine.check ⟨qfrac 5 9, qfrac 24 43, 136678098⟩=true := by decide +kernel
private theorem small012_cell_7 : PeriodAffine.check ⟨qfrac 24 43, qfrac 19 34, 37332757⟩=true := by decide +kernel
private theorem small012_cell_8 : PeriodAffine.check ⟨qfrac 19 34, qfrac 52 93, 5585117⟩=true := by decide +kernel
private theorem small012_cell_9 : PeriodAffine.check ⟨qfrac 52 93, qfrac 33 59, 3305534⟩=true := by decide +kernel
private theorem small012_cell_10 : PeriodAffine.check ⟨qfrac 33 59, qfrac 47 84, 3766108⟩=true := by decide +kernel
private theorem small012_cell_11 : PeriodAffine.check ⟨qfrac 47 84, qfrac 14 25, 9197937⟩=true := by decide +kernel
private theorem small012_cell_12 : PeriodAffine.check ⟨qfrac 14 25, qfrac 23 41, 57494883⟩=true := by decide +kernel
private theorem small012_cell_13 : PeriodAffine.check ⟨qfrac 23 41, qfrac 9 16, 94443383⟩=true := by decide +kernel
private theorem small012_cell_14 : PeriodAffine.check ⟨qfrac 9 16, qfrac 43 76, 166007302⟩=true := by decide +kernel
private theorem small012_cell_15 : PeriodAffine.check ⟨qfrac 43 76, qfrac 67 118, 113605134⟩=true := by decide +kernel
private theorem small012_cell_16 : PeriodAffine.check ⟨qfrac 67 118, qfrac 29 51, 49442976⟩=true := by decide +kernel
private theorem small012_cell_17 : PeriodAffine.check ⟨qfrac 29 51, qfrac 53 93, 80963440⟩=true := by decide +kernel
private theorem small012_cell_18 : PeriodAffine.check ⟨qfrac 53 93, qfrac 4 7, 104118622⟩=true := by decide +kernel
private theorem small012_cell_19 : PeriodAffine.check ⟨qfrac 4 7, qfrac 43 75, 132575791⟩=true := by decide +kernel
private theorem small012_cell_20 : PeriodAffine.check ⟨qfrac 43 75, qfrac 39 68, 13856889⟩=true := by decide +kernel
private theorem small012_cell_21 : PeriodAffine.check ⟨qfrac 39 68, qfrac 19 33, 163570003⟩=true := by decide +kernel
private theorem small012_cell_22 : PeriodAffine.check ⟨qfrac 19 33, qfrac 34 59, 39334592⟩=true := by decide +kernel
private theorem small012_cell_23 : PeriodAffine.check ⟨qfrac 34 59, qfrac 11 19, 215362579⟩=true := by decide +kernel
private theorem small012_cell_24 : PeriodAffine.check ⟨qfrac 11 19, qfrac 29 50, 89410272⟩=true := by decide +kernel
private theorem small012_cell_25 : PeriodAffine.check ⟨qfrac 29 50, qfrac 18 31, 25608905⟩=true := by decide +kernel
private theorem small012_cell_26 : PeriodAffine.check ⟨qfrac 18 31, qfrac 25 43, 30352680⟩=true := by decide +kernel
private theorem small012_cell_27 : PeriodAffine.check ⟨qfrac 25 43, qfrac 7 12, 81236782⟩=true := by decide +kernel
private theorem small012_cell_28 : PeriodAffine.check ⟨qfrac 7 12, qfrac 69 118, 61681326⟩=true := by decide +kernel
private theorem small012_cell_29 : PeriodAffine.check ⟨qfrac 69 118, qfrac 24 41, 27717095⟩=true := by decide +kernel
private theorem small012_cell_30 : PeriodAffine.check ⟨qfrac 24 41, qfrac 44 75, 59471272⟩=true := by decide +kernel
private theorem small012_cell_31 : PeriodAffine.check ⟨qfrac 44 75, qfrac 10 17, 74075677⟩=true := by decide +kernel

theorem small012_affine_check : small012.all PeriodAffine.check=true := by
  simp only [small012, List.all_cons, List.all_nil, Bool.and_self,
    small012_cell_0,
    small012_cell_1,
    small012_cell_2,
    small012_cell_3,
    small012_cell_4,
    small012_cell_5,
    small012_cell_6,
    small012_cell_7,
    small012_cell_8,
    small012_cell_9,
    small012_cell_10,
    small012_cell_11,
    small012_cell_12,
    small012_cell_13,
    small012_cell_14,
    small012_cell_15,
    small012_cell_16,
    small012_cell_17,
    small012_cell_18,
    small012_cell_19,
    small012_cell_20,
    small012_cell_21,
    small012_cell_22,
    small012_cell_23,
    small012_cell_24,
    small012_cell_25,
    small012_cell_26,
    small012_cell_27,
    small012_cell_28,
    small012_cell_29,
    small012_cell_30,
    small012_cell_31]

private theorem small013_cell_0 : PeriodAffine.check ⟨qfrac 10 17, qfrac 55 93, 56551970⟩=true := by decide +kernel
private theorem small013_cell_1 : PeriodAffine.check ⟨qfrac 55 93, qfrac 45 76, 17652839⟩=true := by decide +kernel
private theorem small013_cell_2 : PeriodAffine.check ⟨qfrac 45 76, qfrac 35 59, 25652146⟩=true := by decide +kernel
private theorem small013_cell_3 : PeriodAffine.check ⟨qfrac 35 59, qfrac 19 32, 11879147⟩=true := by decide +kernel
private theorem small013_cell_4 : PeriodAffine.check ⟨qfrac 19 32, qfrac 25 42, 13894760⟩=true := by decide +kernel
private theorem small013_cell_5 : PeriodAffine.check ⟨qfrac 25 42, qfrac 3 5, 73957920⟩=true := by decide +kernel
private theorem small013_cell_6 : PeriodAffine.check ⟨qfrac 3 5, qfrac 71 118, 99539922⟩=true := by decide +kernel
private theorem small013_cell_7 : PeriodAffine.check ⟨qfrac 71 118, qfrac 56 93, 28374831⟩=true := by decide +kernel
private theorem small013_cell_8 : PeriodAffine.check ⟨qfrac 56 93, qfrac 41 68, 50409338⟩=true := by decide +kernel
private theorem small013_cell_9 : PeriodAffine.check ⟨qfrac 41 68, qfrac 26 43, 112371489⟩=true := by decide +kernel
private theorem small013_cell_10 : PeriodAffine.check ⟨qfrac 26 43, qfrac 23 38, 42039763⟩=true := by decide +kernel
private theorem small013_cell_11 : PeriodAffine.check ⟨qfrac 23 38, qfrac 20 33, 56102329⟩=true := by decide +kernel
private theorem small013_cell_12 : PeriodAffine.check ⟨qfrac 20 33, qfrac 17 28, 78252387⟩=true := by decide +kernel
private theorem small013_cell_13 : PeriodAffine.check ⟨qfrac 17 28, qfrac 31 51, 52070948⟩=true := by decide +kernel
private theorem small013_cell_14 : PeriodAffine.check ⟨qfrac 31 51, qfrac 25 41, 147998712⟩=true := by decide +kernel
private theorem small013_cell_15 : PeriodAffine.check ⟨qfrac 25 41, qfrac 36 59, 33074447⟩=true := by decide +kernel
private theorem small013_cell_16 : PeriodAffine.check ⟨qfrac 36 59, qfrac 11 18, 76851944⟩=true := by decide +kernel
private theorem small013_cell_17 : PeriodAffine.check ⟨qfrac 11 18, qfrac 19 31, 152131380⟩=true := by decide +kernel
private theorem small013_cell_18 : PeriodAffine.check ⟨qfrac 19 31, qfrac 46 75, 37630692⟩=true := by decide +kernel
private theorem small013_cell_19 : PeriodAffine.check ⟨qfrac 46 75, qfrac 21 34, 401264245⟩=true := by decide +kernel
private theorem small013_cell_20 : PeriodAffine.check ⟨qfrac 21 34, qfrac 47 76, 47229532⟩=true := by decide +kernel
private theorem small013_cell_21 : PeriodAffine.check ⟨qfrac 47 76, qfrac 73 118, 13866579⟩=true := by decide +kernel
private theorem small013_cell_22 : PeriodAffine.check ⟨qfrac 73 118, qfrac 13 21, 25387371⟩=true := by decide +kernel
private theorem small013_cell_23 : PeriodAffine.check ⟨qfrac 13 21, qfrac 31 50, 61425487⟩=true := by decide +kernel
private theorem small013_cell_24 : PeriodAffine.check ⟨qfrac 31 50, qfrac 58 93, 81765085⟩=true := by decide +kernel
private theorem small013_cell_25 : PeriodAffine.check ⟨qfrac 58 93, qfrac 5 8, 42142836⟩=true := by decide +kernel
private theorem small013_cell_26 : PeriodAffine.check ⟨qfrac 5 8, qfrac 47 75, 27563067⟩=true := by decide +kernel
private theorem small013_cell_27 : PeriodAffine.check ⟨qfrac 47 75, qfrac 37 59, 6112662⟩=true := by decide +kernel
private theorem small013_cell_28 : PeriodAffine.check ⟨qfrac 37 59, qfrac 32 51, 4527146⟩=true := by decide +kernel
private theorem small013_cell_29 : PeriodAffine.check ⟨qfrac 32 51, qfrac 27 43, 7285995⟩=true := by decide +kernel
private theorem small013_cell_30 : PeriodAffine.check ⟨qfrac 27 43, qfrac 53 84, 84307824⟩=true := by decide +kernel
private theorem small013_cell_31 : PeriodAffine.check ⟨qfrac 53 84, qfrac 12 19, 23589573⟩=true := by decide +kernel

theorem small013_affine_check : small013.all PeriodAffine.check=true := by
  simp only [small013, List.all_cons, List.all_nil, Bool.and_self,
    small013_cell_0,
    small013_cell_1,
    small013_cell_2,
    small013_cell_3,
    small013_cell_4,
    small013_cell_5,
    small013_cell_6,
    small013_cell_7,
    small013_cell_8,
    small013_cell_9,
    small013_cell_10,
    small013_cell_11,
    small013_cell_12,
    small013_cell_13,
    small013_cell_14,
    small013_cell_15,
    small013_cell_16,
    small013_cell_17,
    small013_cell_18,
    small013_cell_19,
    small013_cell_20,
    small013_cell_21,
    small013_cell_22,
    small013_cell_23,
    small013_cell_24,
    small013_cell_25,
    small013_cell_26,
    small013_cell_27,
    small013_cell_28,
    small013_cell_29,
    small013_cell_30,
    small013_cell_31]

end OddZetaSix.B40a.Cert
