import OddZetaSix.B40a.Arithmetic.PeriodicAffine
import OddZetaSix.B40a.Arithmetic.SmallAffine000
import OddZetaSix.B40a.Certificate.Generated.Small004
import OddZetaSix.B40a.Certificate.Generated.Small005

namespace OddZetaSix.B40a.Cert
set_option maxHeartbeats 0
set_option maxRecDepth 32768

private theorem small004_cell_0 : PeriodAffine.check ⟨qfrac 2 11, qfrac 17 93, 36202262⟩=true := by decide +kernel
private theorem small004_cell_1 : PeriodAffine.check ⟨qfrac 17 93, qfrac 7 38, 54018635⟩=true := by decide +kernel
private theorem small004_cell_2 : PeriodAffine.check ⟨qfrac 7 38, qfrac 8 43, 62229899⟩=true := by decide +kernel
private theorem small004_cell_3 : PeriodAffine.check ⟨qfrac 8 43, qfrac 11 59, 12186289⟩=true := by decide +kernel
private theorem small004_cell_4 : PeriodAffine.check ⟨qfrac 11 59, qfrac 14 75, 7013863⟩=true := by decide +kernel
private theorem small004_cell_5 : PeriodAffine.check ⟨qfrac 14 75, qfrac 3 16, 27157620⟩=true := by decide +kernel
private theorem small004_cell_6 : PeriodAffine.check ⟨qfrac 3 16, qfrac 4 21, 65092808⟩=true := by decide +kernel
private theorem small004_cell_7 : PeriodAffine.check ⟨qfrac 4 21, qfrac 13 68, 19635943⟩=true := by decide +kernel
private theorem small004_cell_8 : PeriodAffine.check ⟨qfrac 13 68, qfrac 6 31, 70203470⟩=true := by decide +kernel
private theorem small004_cell_9 : PeriodAffine.check ⟨qfrac 6 31, qfrac 23 118, 42943031⟩=true := by decide +kernel
private theorem small004_cell_10 : PeriodAffine.check ⟨qfrac 23 118, qfrac 8 41, 6642348⟩=true := by decide +kernel
private theorem small004_cell_11 : PeriodAffine.check ⟨qfrac 8 41, qfrac 10 51, 32160075⟩=true := by decide +kernel
private theorem small004_cell_12 : PeriodAffine.check ⟨qfrac 10 51, qfrac 15 76, 47589943⟩=true := by decide +kernel
private theorem small004_cell_13 : PeriodAffine.check ⟨qfrac 15 76, qfrac 1 5, 111977858⟩=true := by decide +kernel
private theorem small004_cell_14 : PeriodAffine.check ⟨qfrac 1 5, qfrac 17 84, 229351518⟩=true := by decide +kernel
private theorem small004_cell_15 : PeriodAffine.check ⟨qfrac 17 84, qfrac 12 59, 102035515⟩=true := by decide +kernel
private theorem small004_cell_16 : PeriodAffine.check ⟨qfrac 12 59, qfrac 19 93, 94647667⟩=true := by decide +kernel
private theorem small004_cell_17 : PeriodAffine.check ⟨qfrac 19 93, qfrac 7 34, 169893776⟩=true := by decide +kernel
private theorem small004_cell_18 : PeriodAffine.check ⟨qfrac 7 34, qfrac 9 43, 233028715⟩=true := by decide +kernel
private theorem small004_cell_19 : PeriodAffine.check ⟨qfrac 9 43, qfrac 4 19, 92328593⟩=true := by decide +kernel
private theorem small004_cell_20 : PeriodAffine.check ⟨qfrac 4 19, qfrac 25 118, 105997135⟩=true := by decide +kernel
private theorem small004_cell_21 : PeriodAffine.check ⟨qfrac 25 118, qfrac 7 33, 20855160⟩=true := by decide +kernel
private theorem small004_cell_22 : PeriodAffine.check ⟨qfrac 7 33, qfrac 16 75, 103331068⟩=true := by decide +kernel
private theorem small004_cell_23 : PeriodAffine.check ⟨qfrac 16 75, qfrac 3 14, 85384685⟩=true := by decide +kernel
private theorem small004_cell_24 : PeriodAffine.check ⟨qfrac 3 14, qfrac 20 93, 70260688⟩=true := by decide +kernel
private theorem small004_cell_25 : PeriodAffine.check ⟨qfrac 20 93, qfrac 11 51, 58776914⟩=true := by decide +kernel
private theorem small004_cell_26 : PeriodAffine.check ⟨qfrac 11 51, qfrac 7 32, 296528061⟩=true := by decide +kernel
private theorem small004_cell_27 : PeriodAffine.check ⟨qfrac 7 32, qfrac 9 41, 59868995⟩=true := by decide +kernel
private theorem small004_cell_28 : PeriodAffine.check ⟨qfrac 9 41, qfrac 11 50, 38818161⟩=true := by decide +kernel
private theorem small004_cell_29 : PeriodAffine.check ⟨qfrac 11 50, qfrac 13 59, 5950361⟩=true := by decide +kernel
private theorem small004_cell_30 : PeriodAffine.check ⟨qfrac 13 59, qfrac 15 68, 4824746⟩=true := by decide +kernel
private theorem small004_cell_31 : PeriodAffine.check ⟨qfrac 15 68, qfrac 2 9, 45959251⟩=true := by decide +kernel

theorem small004_affine_check : small004.all PeriodAffine.check=true := by
  simp only [small004, List.all_cons, List.all_nil, Bool.and_self,
    small004_cell_0,
    small004_cell_1,
    small004_cell_2,
    small004_cell_3,
    small004_cell_4,
    small004_cell_5,
    small004_cell_6,
    small004_cell_7,
    small004_cell_8,
    small004_cell_9,
    small004_cell_10,
    small004_cell_11,
    small004_cell_12,
    small004_cell_13,
    small004_cell_14,
    small004_cell_15,
    small004_cell_16,
    small004_cell_17,
    small004_cell_18,
    small004_cell_19,
    small004_cell_20,
    small004_cell_21,
    small004_cell_22,
    small004_cell_23,
    small004_cell_24,
    small004_cell_25,
    small004_cell_26,
    small004_cell_27,
    small004_cell_28,
    small004_cell_29,
    small004_cell_30,
    small004_cell_31]

private theorem small005_cell_0 : PeriodAffine.check ⟨qfrac 2 9, qfrac 17 76, 62136133⟩=true := by decide +kernel
private theorem small005_cell_1 : PeriodAffine.check ⟨qfrac 17 76, qfrac 7 31, 113725735⟩=true := by decide +kernel
private theorem small005_cell_2 : PeriodAffine.check ⟨qfrac 7 31, qfrac 19 84, 22201048⟩=true := by decide +kernel
private theorem small005_cell_3 : PeriodAffine.check ⟨qfrac 19 84, qfrac 17 75, 27466766⟩=true := by decide +kernel
private theorem small005_cell_4 : PeriodAffine.check ⟨qfrac 17 75, qfrac 27 118, 122831202⟩=true := by decide +kernel
private theorem small005_cell_5 : PeriodAffine.check ⟨qfrac 27 118, qfrac 10 43, 210521376⟩=true := by decide +kernel
private theorem small005_cell_6 : PeriodAffine.check ⟨qfrac 10 43, qfrac 4 17, 150961563⟩=true := by decide +kernel
private theorem small005_cell_7 : PeriodAffine.check ⟨qfrac 4 17, qfrac 22 93, 19439216⟩=true := by decide +kernel
private theorem small005_cell_8 : PeriodAffine.check ⟨qfrac 22 93, qfrac 9 38, 5180551⟩=true := by decide +kernel
private theorem small005_cell_9 : PeriodAffine.check ⟨qfrac 9 38, qfrac 14 59, 7489376⟩=true := by decide +kernel
private theorem small005_cell_10 : PeriodAffine.check ⟨qfrac 14 59, qfrac 5 21, 14162148⟩=true := by decide +kernel
private theorem small005_cell_11 : PeriodAffine.check ⟨qfrac 5 21, qfrac 6 25, 39980778⟩=true := by decide +kernel
private theorem small005_cell_12 : PeriodAffine.check ⟨qfrac 6 25, qfrac 8 33, 173184780⟩=true := by decide +kernel
private theorem small005_cell_13 : PeriodAffine.check ⟨qfrac 8 33, qfrac 10 41, 113780234⟩=true := by decide +kernel
private theorem small005_cell_14 : PeriodAffine.check ⟨qfrac 10 41, qfrac 29 118, 152075614⟩=true := by decide +kernel
private theorem small005_cell_15 : PeriodAffine.check ⟨qfrac 29 118, qfrac 23 93, 140581589⟩=true := by decide +kernel
private theorem small005_cell_16 : PeriodAffine.check ⟨qfrac 23 93, qfrac 1 4, 260269497⟩=true := by decide +kernel
private theorem small005_cell_17 : PeriodAffine.check ⟨qfrac 1 4, qfrac 19 75, 272331951⟩=true := by decide +kernel
private theorem small005_cell_18 : PeriodAffine.check ⟨qfrac 19 75, qfrac 15 59, 76401723⟩=true := by decide +kernel
private theorem small005_cell_19 : PeriodAffine.check ⟨qfrac 15 59, qfrac 13 51, 57186041⟩=true := by decide +kernel
private theorem small005_cell_20 : PeriodAffine.check ⟨qfrac 13 51, qfrac 11 43, 80475681⟩=true := by decide +kernel
private theorem small005_cell_21 : PeriodAffine.check ⟨qfrac 11 43, qfrac 8 31, 208684055⟩=true := by decide +kernel
private theorem small005_cell_22 : PeriodAffine.check ⟨qfrac 8 31, qfrac 13 50, 190693824⟩=true := by decide +kernel
private theorem small005_cell_23 : PeriodAffine.check ⟨qfrac 13 50, qfrac 11 42, 69044902⟩=true := by decide +kernel
private theorem small005_cell_24 : PeriodAffine.check ⟨qfrac 11 42, qfrac 31 118, 32280919⟩=true := by decide +kernel
private theorem small005_cell_25 : PeriodAffine.check ⟨qfrac 31 118, qfrac 5 19, 18611747⟩=true := by decide +kernel
private theorem small005_cell_26 : PeriodAffine.check ⟨qfrac 5 19, qfrac 9 34, 68869686⟩=true := by decide +kernel
private theorem small005_cell_27 : PeriodAffine.check ⟨qfrac 9 34, qfrac 4 15, 21177613⟩=true := by decide +kernel
private theorem small005_cell_28 : PeriodAffine.check ⟨qfrac 4 15, qfrac 11 41, 31863717⟩=true := by decide +kernel
private theorem small005_cell_29 : PeriodAffine.check ⟨qfrac 11 41, qfrac 25 93, 12773645⟩=true := by decide +kernel
private theorem small005_cell_30 : PeriodAffine.check ⟨qfrac 25 93, qfrac 16 59, 54307493⟩=true := by decide +kernel
private theorem small005_cell_31 : PeriodAffine.check ⟨qfrac 16 59, qfrac 3 11, 40292739⟩=true := by decide +kernel

theorem small005_affine_check : small005.all PeriodAffine.check=true := by
  simp only [small005, List.all_cons, List.all_nil, Bool.and_self,
    small005_cell_0,
    small005_cell_1,
    small005_cell_2,
    small005_cell_3,
    small005_cell_4,
    small005_cell_5,
    small005_cell_6,
    small005_cell_7,
    small005_cell_8,
    small005_cell_9,
    small005_cell_10,
    small005_cell_11,
    small005_cell_12,
    small005_cell_13,
    small005_cell_14,
    small005_cell_15,
    small005_cell_16,
    small005_cell_17,
    small005_cell_18,
    small005_cell_19,
    small005_cell_20,
    small005_cell_21,
    small005_cell_22,
    small005_cell_23,
    small005_cell_24,
    small005_cell_25,
    small005_cell_26,
    small005_cell_27,
    small005_cell_28,
    small005_cell_29,
    small005_cell_30,
    small005_cell_31]

end OddZetaSix.B40a.Cert
