import OddZetaSix.B40a.Arithmetic.PeriodicAffine
import OddZetaSix.B40a.Arithmetic.SmallAffine004
import OddZetaSix.B40a.Certificate.Generated.Small008
import OddZetaSix.B40a.Certificate.Generated.Small009

namespace OddZetaSix.B40a.Cert
set_option maxHeartbeats 0
set_option maxRecDepth 32768

private theorem small008_cell_0 : PeriodAffine.check ⟨qfrac 15 41, qfrac 25 68, 151295780⟩=true := by decide +kernel
private theorem small008_cell_1 : PeriodAffine.check ⟨qfrac 25 68, qfrac 7 19, 65935565⟩=true := by decide +kernel
private theorem small008_cell_2 : PeriodAffine.check ⟨qfrac 7 19, qfrac 31 84, 54536928⟩=true := by decide +kernel
private theorem small008_cell_3 : PeriodAffine.check ⟨qfrac 31 84, qfrac 16 43, 279494844⟩=true := by decide +kernel
private theorem small008_cell_4 : PeriodAffine.check ⟨qfrac 16 43, qfrac 19 51, 43841651⟩=true := by decide +kernel
private theorem small008_cell_5 : PeriodAffine.check ⟨qfrac 19 51, qfrac 22 59, 32286016⟩=true := by decide +kernel
private theorem small008_cell_6 : PeriodAffine.check ⟨qfrac 22 59, qfrac 28 75, 44377351⟩=true := by decide +kernel
private theorem small008_cell_7 : PeriodAffine.check ⟨qfrac 28 75, qfrac 3 8, 168387418⟩=true := by decide +kernel
private theorem small008_cell_8 : PeriodAffine.check ⟨qfrac 3 8, qfrac 35 93, 112549070⟩=true := by decide +kernel
private theorem small008_cell_9 : PeriodAffine.check ⟨qfrac 35 93, qfrac 19 50, 329987211⟩=true := by decide +kernel
private theorem small008_cell_10 : PeriodAffine.check ⟨qfrac 19 50, qfrac 8 21, 31186529⟩=true := by decide +kernel
private theorem small008_cell_11 : PeriodAffine.check ⟨qfrac 8 21, qfrac 45 118, 13925524⟩=true := by decide +kernel
private theorem small008_cell_12 : PeriodAffine.check ⟨qfrac 45 118, qfrac 29 76, 7877315⟩=true := by decide +kernel
private theorem small008_cell_13 : PeriodAffine.check ⟨qfrac 29 76, qfrac 13 34, 28344074⟩=true := by decide +kernel
private theorem small008_cell_14 : PeriodAffine.check ⟨qfrac 13 34, qfrac 29 75, 60233468⟩=true := by decide +kernel
private theorem small008_cell_15 : PeriodAffine.check ⟨qfrac 29 75, qfrac 12 31, 11275397⟩=true := by decide +kernel
private theorem small008_cell_16 : PeriodAffine.check ⟨qfrac 12 31, qfrac 7 18, 41911789⟩=true := by decide +kernel
private theorem small008_cell_17 : PeriodAffine.check ⟨qfrac 7 18, qfrac 23 59, 16625747⟩=true := by decide +kernel
private theorem small008_cell_18 : PeriodAffine.check ⟨qfrac 23 59, qfrac 16 41, 7006875⟩=true := by decide +kernel
private theorem small008_cell_19 : PeriodAffine.check ⟨qfrac 16 41, qfrac 20 51, 48888921⟩=true := by decide +kernel
private theorem small008_cell_20 : PeriodAffine.check ⟨qfrac 20 51, qfrac 11 28, 24795512⟩=true := by decide +kernel
private theorem small008_cell_21 : PeriodAffine.check ⟨qfrac 11 28, qfrac 13 33, 41492784⟩=true := by decide +kernel
private theorem small008_cell_22 : PeriodAffine.check ⟨qfrac 13 33, qfrac 15 38, 30960671⟩=true := by decide +kernel
private theorem small008_cell_23 : PeriodAffine.check ⟨qfrac 15 38, qfrac 17 43, 23976015⟩=true := by decide +kernel
private theorem small008_cell_24 : PeriodAffine.check ⟨qfrac 17 43, qfrac 27 68, 67971695⟩=true := by decide +kernel
private theorem small008_cell_25 : PeriodAffine.check ⟨qfrac 27 68, qfrac 37 93, 31910357⟩=true := by decide +kernel
private theorem small008_cell_26 : PeriodAffine.check ⟨qfrac 37 93, qfrac 47 118, 18525629⟩=true := by decide +kernel
private theorem small008_cell_27 : PeriodAffine.check ⟨qfrac 47 118, qfrac 2 5, 69805658⟩=true := by decide +kernel
private theorem small008_cell_28 : PeriodAffine.check ⟨qfrac 2 5, qfrac 17 42, 426926925⟩=true := by decide +kernel
private theorem small008_cell_29 : PeriodAffine.check ⟨qfrac 17 42, qfrac 13 32, 145268404⟩=true := by decide +kernel
private theorem small008_cell_30 : PeriodAffine.check ⟨qfrac 13 32, qfrac 24 59, 41972715⟩=true := by decide +kernel
private theorem small008_cell_31 : PeriodAffine.check ⟨qfrac 24 59, qfrac 31 76, 90781795⟩=true := by decide +kernel

theorem small008_affine_check : small008.all PeriodAffine.check=true := by
  simp only [small008, List.all_cons, List.all_nil, Bool.and_self,
    small008_cell_0,
    small008_cell_1,
    small008_cell_2,
    small008_cell_3,
    small008_cell_4,
    small008_cell_5,
    small008_cell_6,
    small008_cell_7,
    small008_cell_8,
    small008_cell_9,
    small008_cell_10,
    small008_cell_11,
    small008_cell_12,
    small008_cell_13,
    small008_cell_14,
    small008_cell_15,
    small008_cell_16,
    small008_cell_17,
    small008_cell_18,
    small008_cell_19,
    small008_cell_20,
    small008_cell_21,
    small008_cell_22,
    small008_cell_23,
    small008_cell_24,
    small008_cell_25,
    small008_cell_26,
    small008_cell_27,
    small008_cell_28,
    small008_cell_29,
    small008_cell_30,
    small008_cell_31]

private theorem small009_cell_0 : PeriodAffine.check ⟨qfrac 31 76, qfrac 38 93, 59284906⟩=true := by decide +kernel
private theorem small009_cell_1 : PeriodAffine.check ⟨qfrac 38 93, qfrac 7 17, 280765614⟩=true := by decide +kernel
private theorem small009_cell_2 : PeriodAffine.check ⟨qfrac 7 17, qfrac 31 75, 84223278⟩=true := by decide +kernel
private theorem small009_cell_3 : PeriodAffine.check ⟨qfrac 31 75, qfrac 17 41, 74694770⟩=true := by decide +kernel
private theorem small009_cell_4 : PeriodAffine.check ⟨qfrac 17 41, qfrac 49 118, 36803663⟩=true := by decide +kernel
private theorem small009_cell_5 : PeriodAffine.check ⟨qfrac 49 118, qfrac 5 12, 92446436⟩=true := by decide +kernel
private theorem small009_cell_6 : PeriodAffine.check ⟨qfrac 5 12, qfrac 18 43, 138047490⟩=true := by decide +kernel
private theorem small009_cell_7 : PeriodAffine.check ⟨qfrac 18 43, qfrac 13 31, 53937573⟩=true := by decide +kernel
private theorem small009_cell_8 : PeriodAffine.check ⟨qfrac 13 31, qfrac 21 50, 46604717⟩=true := by decide +kernel
private theorem small009_cell_9 : PeriodAffine.check ⟨qfrac 21 50, qfrac 8 19, 30480777⟩=true := by decide +kernel
private theorem small009_cell_10 : PeriodAffine.check ⟨qfrac 8 19, qfrac 25 59, 64762664⟩=true := by decide +kernel
private theorem small009_cell_11 : PeriodAffine.check ⟨qfrac 25 59, qfrac 14 33, 10928173⟩=true := by decide +kernel
private theorem small009_cell_12 : PeriodAffine.check ⟨qfrac 14 33, qfrac 29 68, 62331506⟩=true := by decide +kernel
private theorem small009_cell_13 : PeriodAffine.check ⟨qfrac 29 68, qfrac 32 75, 6670658⟩=true := by decide +kernel
private theorem small009_cell_14 : PeriodAffine.check ⟨qfrac 32 75, qfrac 3 7, 69276771⟩=true := by decide +kernel
private theorem small009_cell_15 : PeriodAffine.check ⟨qfrac 3 7, qfrac 40 93, 60944792⟩=true := by decide +kernel
private theorem small009_cell_16 : PeriodAffine.check ⟨qfrac 40 93, qfrac 22 51, 53510276⟩=true := by decide +kernel
private theorem small009_cell_17 : PeriodAffine.check ⟨qfrac 22 51, qfrac 51 118, 36749354⟩=true := by decide +kernel
private theorem small009_cell_18 : PeriodAffine.check ⟨qfrac 51 118, qfrac 33 76, 94207630⟩=true := by decide +kernel
private theorem small009_cell_19 : PeriodAffine.check ⟨qfrac 33 76, qfrac 7 16, 170797289⟩=true := by decide +kernel
private theorem small009_cell_20 : PeriodAffine.check ⟨qfrac 7 16, qfrac 18 41, 57401815⟩=true := by decide +kernel
private theorem small009_cell_21 : PeriodAffine.check ⟨qfrac 18 41, qfrac 11 25, 38554504⟩=true := by decide +kernel
private theorem small009_cell_22 : PeriodAffine.check ⟨qfrac 11 25, qfrac 37 84, 39205622⟩=true := by decide +kernel
private theorem small009_cell_23 : PeriodAffine.check ⟨qfrac 37 84, qfrac 26 59, 16784226⟩=true := by decide +kernel
private theorem small009_cell_24 : PeriodAffine.check ⟨qfrac 26 59, qfrac 41 93, 15247978⟩=true := by decide +kernel
private theorem small009_cell_25 : PeriodAffine.check ⟨qfrac 41 93, qfrac 15 34, 26659675⟩=true := by decide +kernel
private theorem small009_cell_26 : PeriodAffine.check ⟨qfrac 15 34, qfrac 19 43, 30505806⟩=true := by decide +kernel
private theorem small009_cell_27 : PeriodAffine.check ⟨qfrac 19 43, qfrac 4 9, 129094500⟩=true := by decide +kernel
private theorem small009_cell_28 : PeriodAffine.check ⟨qfrac 4 9, qfrac 17 38, 172206532⟩=true := by decide +kernel
private theorem small009_cell_29 : PeriodAffine.check ⟨qfrac 17 38, qfrac 53 118, 115357852⟩=true := by decide +kernel
private theorem small009_cell_30 : PeriodAffine.check ⟨qfrac 53 118, qfrac 23 51, 127085549⟩=true := by decide +kernel
private theorem small009_cell_31 : PeriodAffine.check ⟨qfrac 23 51, qfrac 14 31, 47200791⟩=true := by decide +kernel

theorem small009_affine_check : small009.all PeriodAffine.check=true := by
  simp only [small009, List.all_cons, List.all_nil, Bool.and_self,
    small009_cell_0,
    small009_cell_1,
    small009_cell_2,
    small009_cell_3,
    small009_cell_4,
    small009_cell_5,
    small009_cell_6,
    small009_cell_7,
    small009_cell_8,
    small009_cell_9,
    small009_cell_10,
    small009_cell_11,
    small009_cell_12,
    small009_cell_13,
    small009_cell_14,
    small009_cell_15,
    small009_cell_16,
    small009_cell_17,
    small009_cell_18,
    small009_cell_19,
    small009_cell_20,
    small009_cell_21,
    small009_cell_22,
    small009_cell_23,
    small009_cell_24,
    small009_cell_25,
    small009_cell_26,
    small009_cell_27,
    small009_cell_28,
    small009_cell_29,
    small009_cell_30,
    small009_cell_31]

end OddZetaSix.B40a.Cert
