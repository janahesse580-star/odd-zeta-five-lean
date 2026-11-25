import OddZetaSix.B40a.Arithmetic.PeriodicAffine
import OddZetaSix.B40a.Arithmetic.SmallAffine002
import OddZetaSix.B40a.Certificate.Generated.Small006
import OddZetaSix.B40a.Certificate.Generated.Small007

namespace OddZetaSix.B40a.Cert
set_option maxHeartbeats 0
set_option maxRecDepth 32768

private theorem small006_cell_0 : PeriodAffine.check ⟨qfrac 3 11, qfrac 23 84, 39701895⟩=true := by decide +kernel
private theorem small006_cell_1 : PeriodAffine.check ⟨qfrac 23 84, qfrac 14 51, 28859576⟩=true := by decide +kernel
private theorem small006_cell_2 : PeriodAffine.check ⟨qfrac 14 51, qfrac 21 76, 75703926⟩=true := by decide +kernel
private theorem small006_cell_3 : PeriodAffine.check ⟨qfrac 21 76, qfrac 5 18, 62565356⟩=true := by decide +kernel
private theorem small006_cell_4 : PeriodAffine.check ⟨qfrac 5 18, qfrac 12 43, 56183888⟩=true := by decide +kernel
private theorem small006_cell_5 : PeriodAffine.check ⟨qfrac 12 43, qfrac 19 68, 15008890⟩=true := by decide +kernel
private theorem small006_cell_6 : PeriodAffine.check ⟨qfrac 19 68, qfrac 26 93, 6959992⟩=true := by decide +kernel
private theorem small006_cell_7 : PeriodAffine.check ⟨qfrac 26 93, qfrac 33 118, 4016619⟩=true := by decide +kernel
private theorem small006_cell_8 : PeriodAffine.check ⟨qfrac 33 118, qfrac 7 25, 14979545⟩=true := by decide +kernel
private theorem small006_cell_9 : PeriodAffine.check ⟨qfrac 7 25, qfrac 9 32, 113195060⟩=true := by decide +kernel
private theorem small006_cell_10 : PeriodAffine.check ⟨qfrac 9 32, qfrac 2 7, 340091762⟩=true := by decide +kernel
private theorem small006_cell_11 : PeriodAffine.check ⟨qfrac 2 7, qfrac 17 59, 207169352⟩=true := by decide +kernel
private theorem small006_cell_12 : PeriodAffine.check ⟨qfrac 17 59, qfrac 11 38, 121380993⟩=true := by decide +kernel
private theorem small006_cell_13 : PeriodAffine.check ⟨qfrac 11 38, qfrac 9 31, 79596125⟩=true := by decide +kernel
private theorem small006_cell_14 : PeriodAffine.check ⟨qfrac 9 31, qfrac 12 41, 231652882⟩=true := by decide +kernel
private theorem small006_cell_15 : PeriodAffine.check ⟨qfrac 12 41, qfrac 22 75, 66430026⟩=true := by decide +kernel
private theorem small006_cell_16 : PeriodAffine.check ⟨qfrac 22 75, qfrac 5 17, 81616523⟩=true := by decide +kernel
private theorem small006_cell_17 : PeriodAffine.check ⟨qfrac 5 17, qfrac 35 118, 160197400⟩=true := by decide +kernel
private theorem small006_cell_18 : PeriodAffine.check ⟨qfrac 35 118, qfrac 25 84, 72340368⟩=true := by decide +kernel
private theorem small006_cell_19 : PeriodAffine.check ⟨qfrac 25 84, qfrac 3 10, 181867572⟩=true := by decide +kernel
private theorem small006_cell_20 : PeriodAffine.check ⟨qfrac 3 10, qfrac 28 93, 33962467⟩=true := by decide +kernel
private theorem small006_cell_21 : PeriodAffine.check ⟨qfrac 28 93, qfrac 13 43, 41419478⟩=true := by decide +kernel
private theorem small006_cell_22 : PeriodAffine.check ⟨qfrac 13 43, qfrac 23 76, 9595847⟩=true := by decide +kernel
private theorem small006_cell_23 : PeriodAffine.check ⟨qfrac 23 76, qfrac 10 33, 12158026⟩=true := by decide +kernel
private theorem small006_cell_24 : PeriodAffine.check ⟨qfrac 10 33, qfrac 18 59, 56136019⟩=true := by decide +kernel
private theorem small006_cell_25 : PeriodAffine.check ⟨qfrac 18 59, qfrac 23 75, 45862949⟩=true := by decide +kernel
private theorem small006_cell_26 : PeriodAffine.check ⟨qfrac 23 75, qfrac 21 68, 76345714⟩=true := by decide +kernel
private theorem small006_cell_27 : PeriodAffine.check ⟨qfrac 21 68, qfrac 13 42, 26815408⟩=true := by decide +kernel
private theorem small006_cell_28 : PeriodAffine.check ⟨qfrac 13 42, qfrac 29 93, 95322657⟩=true := by decide +kernel
private theorem small006_cell_29 : PeriodAffine.check ⟨qfrac 29 93, qfrac 5 16, 29800702⟩=true := by decide +kernel
private theorem small006_cell_30 : PeriodAffine.check ⟨qfrac 5 16, qfrac 37 118, 33675655⟩=true := by decide +kernel
private theorem small006_cell_31 : PeriodAffine.check ⟨qfrac 37 118, qfrac 16 51, 5369917⟩=true := by decide +kernel

theorem small006_affine_check : small006.all PeriodAffine.check=true := by
  simp only [small006, List.all_cons, List.all_nil, Bool.and_self,
    small006_cell_0,
    small006_cell_1,
    small006_cell_2,
    small006_cell_3,
    small006_cell_4,
    small006_cell_5,
    small006_cell_6,
    small006_cell_7,
    small006_cell_8,
    small006_cell_9,
    small006_cell_10,
    small006_cell_11,
    small006_cell_12,
    small006_cell_13,
    small006_cell_14,
    small006_cell_15,
    small006_cell_16,
    small006_cell_17,
    small006_cell_18,
    small006_cell_19,
    small006_cell_20,
    small006_cell_21,
    small006_cell_22,
    small006_cell_23,
    small006_cell_24,
    small006_cell_25,
    small006_cell_26,
    small006_cell_27,
    small006_cell_28,
    small006_cell_29,
    small006_cell_30,
    small006_cell_31]

private theorem small007_cell_0 : PeriodAffine.check ⟨qfrac 16 51, qfrac 6 19, 68915193⟩=true := by decide +kernel
private theorem small007_cell_1 : PeriodAffine.check ⟨qfrac 6 19, qfrac 13 41, 44847754⟩=true := by decide +kernel
private theorem small007_cell_2 : PeriodAffine.check ⟨qfrac 13 41, qfrac 8 25, 115457873⟩=true := by decide +kernel
private theorem small007_cell_3 : PeriodAffine.check ⟨qfrac 8 25, qfrac 9 28, 126985179⟩=true := by decide +kernel
private theorem small007_cell_4 : PeriodAffine.check ⟨qfrac 9 28, qfrac 19 59, 55447209⟩=true := by decide +kernel
private theorem small007_cell_5 : PeriodAffine.check ⟨qfrac 19 59, qfrac 10 31, 50921995⟩=true := by decide +kernel
private theorem small007_cell_6 : PeriodAffine.check ⟨qfrac 10 31, qfrac 11 34, 90274717⟩=true := by decide +kernel
private theorem small007_cell_7 : PeriodAffine.check ⟨qfrac 11 34, qfrac 14 43, 114171317⟩=true := by decide +kernel
private theorem small007_cell_8 : PeriodAffine.check ⟨qfrac 14 43, qfrac 25 76, 217489278⟩=true := by decide +kernel
private theorem small007_cell_9 : PeriodAffine.check ⟨qfrac 25 76, qfrac 39 118, 112808163⟩=true := by decide +kernel
private theorem small007_cell_10 : PeriodAffine.check ⟨qfrac 39 118, qfrac 1 3, 226632996⟩=true := by decide +kernel
private theorem small007_cell_11 : PeriodAffine.check ⟨qfrac 1 3, qfrac 23 68, 438690056⟩=true := by decide +kernel
private theorem small007_cell_12 : PeriodAffine.check ⟨qfrac 23 68, qfrac 20 59, 69677829⟩=true := by decide +kernel
private theorem small007_cell_13 : PeriodAffine.check ⟨qfrac 20 59, qfrac 17 50, 97177892⟩=true := by decide +kernel
private theorem small007_cell_14 : PeriodAffine.check ⟨qfrac 17 50, qfrac 14 41, 63014227⟩=true := by decide +kernel
private theorem small007_cell_15 : PeriodAffine.check ⟨qfrac 14 41, qfrac 13 38, 32903423⟩=true := by decide +kernel
private theorem small007_cell_16 : PeriodAffine.check ⟨qfrac 13 38, qfrac 11 32, 90202997⟩=true := by decide +kernel
private theorem small007_cell_17 : PeriodAffine.check ⟨qfrac 11 32, qfrac 32 93, 15803527⟩=true := by decide +kernel
private theorem small007_cell_18 : PeriodAffine.check ⟨qfrac 32 93, qfrac 29 84, 54774845⟩=true := by decide +kernel
private theorem small007_cell_19 : PeriodAffine.check ⟨qfrac 29 84, qfrac 26 75, 67404330⟩=true := by decide +kernel
private theorem small007_cell_20 : PeriodAffine.check ⟨qfrac 26 75, qfrac 41 118, 37023799⟩=true := by decide +kernel
private theorem small007_cell_21 : PeriodAffine.check ⟨qfrac 41 118, qfrac 15 43, 64113882⟩=true := by decide +kernel
private theorem small007_cell_22 : PeriodAffine.check ⟨qfrac 15 43, qfrac 6 17, 187638583⟩=true := by decide +kernel
private theorem small007_cell_23 : PeriodAffine.check ⟨qfrac 6 17, qfrac 11 31, 20916696⟩=true := by decide +kernel
private theorem small007_cell_24 : PeriodAffine.check ⟨qfrac 11 31, qfrac 27 76, 6438430⟩=true := by decide +kernel
private theorem small007_cell_25 : PeriodAffine.check ⟨qfrac 27 76, qfrac 21 59, 8720489⟩=true := by decide +kernel
private theorem small007_cell_26 : PeriodAffine.check ⟨qfrac 21 59, qfrac 5 14, 17070328⟩=true := by decide +kernel
private theorem small007_cell_27 : PeriodAffine.check ⟨qfrac 5 14, qfrac 9 25, 54140785⟩=true := by decide +kernel
private theorem small007_cell_28 : PeriodAffine.check ⟨qfrac 9 25, qfrac 4 11, 249636539⟩=true := by decide +kernel
private theorem small007_cell_29 : PeriodAffine.check ⟨qfrac 4 11, qfrac 43 118, 57372038⟩=true := by decide +kernel
private theorem small007_cell_30 : PeriodAffine.check ⟨qfrac 43 118, qfrac 34 93, 94829914⟩=true := by decide +kernel
private theorem small007_cell_31 : PeriodAffine.check ⟨qfrac 34 93, qfrac 15 41, 22172833⟩=true := by decide +kernel

theorem small007_affine_check : small007.all PeriodAffine.check=true := by
  simp only [small007, List.all_cons, List.all_nil, Bool.and_self,
    small007_cell_0,
    small007_cell_1,
    small007_cell_2,
    small007_cell_3,
    small007_cell_4,
    small007_cell_5,
    small007_cell_6,
    small007_cell_7,
    small007_cell_8,
    small007_cell_9,
    small007_cell_10,
    small007_cell_11,
    small007_cell_12,
    small007_cell_13,
    small007_cell_14,
    small007_cell_15,
    small007_cell_16,
    small007_cell_17,
    small007_cell_18,
    small007_cell_19,
    small007_cell_20,
    small007_cell_21,
    small007_cell_22,
    small007_cell_23,
    small007_cell_24,
    small007_cell_25,
    small007_cell_26,
    small007_cell_27,
    small007_cell_28,
    small007_cell_29,
    small007_cell_30,
    small007_cell_31]

end OddZetaSix.B40a.Cert
