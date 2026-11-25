import OddZetaSix.B40a.Arithmetic.PeriodicAffine
import OddZetaSix.B40a.Arithmetic.SmallAffine016
import OddZetaSix.B40a.Certificate.Generated.Small020
import OddZetaSix.B40a.Certificate.Generated.Small021

namespace OddZetaSix.B40a.Cert
set_option maxHeartbeats 0
set_option maxRecDepth 32768

private theorem small020_cell_0 : PeriodAffine.check ⟨qfrac 19 21, qfrac 29 32, 90564710⟩=true := by decide +kernel
private theorem small020_cell_1 : PeriodAffine.check ⟨qfrac 29 32, qfrac 68 75, 19268996⟩=true := by decide +kernel
private theorem small020_cell_2 : PeriodAffine.check ⟨qfrac 68 75, qfrac 107 118, 5270226⟩=true := by decide +kernel
private theorem small020_cell_3 : PeriodAffine.check ⟨qfrac 107 118, qfrac 39 43, 9239257⟩=true := by decide +kernel
private theorem small020_cell_4 : PeriodAffine.check ⟨qfrac 39 43, qfrac 69 76, 43853958⟩=true := by decide +kernel
private theorem small020_cell_5 : PeriodAffine.check ⟨qfrac 69 76, qfrac 10 11, 59086565⟩=true := by decide +kernel
private theorem small020_cell_6 : PeriodAffine.check ⟨qfrac 10 11, qfrac 31 34, 139919717⟩=true := by decide +kernel
private theorem small020_cell_7 : PeriodAffine.check ⟨qfrac 31 34, qfrac 85 93, 26680426⟩=true := by decide +kernel
private theorem small020_cell_8 : PeriodAffine.check ⟨qfrac 85 93, qfrac 54 59, 21487303⟩=true := by decide +kernel
private theorem small020_cell_9 : PeriodAffine.check ⟨qfrac 54 59, qfrac 11 12, 31250308⟩=true := by decide +kernel
private theorem small020_cell_10 : PeriodAffine.check ⟨qfrac 11 12, qfrac 23 25, 95442438⟩=true := by decide +kernel
private theorem small020_cell_11 : PeriodAffine.check ⟨qfrac 23 25, qfrac 35 38, 88709727⟩=true := by decide +kernel
private theorem small020_cell_12 : PeriodAffine.check ⟨qfrac 35 38, qfrac 47 51, 44852716⟩=true := by decide +kernel
private theorem small020_cell_13 : PeriodAffine.check ⟨qfrac 47 51, qfrac 109 118, 197657974⟩=true := by decide +kernel
private theorem small020_cell_14 : PeriodAffine.check ⟨qfrac 109 118, qfrac 86 93, 97090788⟩=true := by decide +kernel
private theorem small020_cell_15 : PeriodAffine.check ⟨qfrac 86 93, qfrac 63 68, 176585557⟩=true := by decide +kernel
private theorem small020_cell_16 : PeriodAffine.check ⟨qfrac 63 68, qfrac 38 41, 37652474⟩=true := by decide +kernel
private theorem small020_cell_17 : PeriodAffine.check ⟨qfrac 38 41, qfrac 13 14, 189178153⟩=true := by decide +kernel
private theorem small020_cell_18 : PeriodAffine.check ⟨qfrac 13 14, qfrac 40 43, 189912185⟩=true := by decide +kernel
private theorem small020_cell_19 : PeriodAffine.check ⟨qfrac 40 43, qfrac 55 59, 237370176⟩=true := by decide +kernel
private theorem small020_cell_20 : PeriodAffine.check ⟨qfrac 55 59, qfrac 14 15, 142057876⟩=true := by decide +kernel
private theorem small020_cell_21 : PeriodAffine.check ⟨qfrac 14 15, qfrac 71 76, 113365936⟩=true := by decide +kernel
private theorem small020_cell_22 : PeriodAffine.check ⟨qfrac 71 76, qfrac 29 31, 169290565⟩=true := by decide +kernel
private theorem small020_cell_23 : PeriodAffine.check ⟨qfrac 29 31, qfrac 15 16, 279126254⟩=true := by decide +kernel
private theorem small020_cell_24 : PeriodAffine.check ⟨qfrac 15 16, qfrac 31 33, 222227571⟩=true := by decide +kernel
private theorem small020_cell_25 : PeriodAffine.check ⟨qfrac 31 33, qfrac 47 50, 73560522⟩=true := by decide +kernel
private theorem small020_cell_26 : PeriodAffine.check ⟨qfrac 47 50, qfrac 79 84, 20524819⟩=true := by decide +kernel
private theorem small020_cell_27 : PeriodAffine.check ⟨qfrac 79 84, qfrac 111 118, 8798746⟩=true := by decide +kernel
private theorem small020_cell_28 : PeriodAffine.check ⟨qfrac 111 118, qfrac 16 17, 21994595⟩=true := by decide +kernel
private theorem small020_cell_29 : PeriodAffine.check ⟨qfrac 16 17, qfrac 17 18, 42006652⟩=true := by decide +kernel
private theorem small020_cell_30 : PeriodAffine.check ⟨qfrac 17 18, qfrac 88 93, 53397568⟩=true := by decide +kernel
private theorem small020_cell_31 : PeriodAffine.check ⟨qfrac 88 93, qfrac 71 75, 14923798⟩=true := by decide +kernel

theorem small020_affine_check : small020.all PeriodAffine.check=true := by
  simp only [small020, List.all_cons, List.all_nil, Bool.and_self,
    small020_cell_0,
    small020_cell_1,
    small020_cell_2,
    small020_cell_3,
    small020_cell_4,
    small020_cell_5,
    small020_cell_6,
    small020_cell_7,
    small020_cell_8,
    small020_cell_9,
    small020_cell_10,
    small020_cell_11,
    small020_cell_12,
    small020_cell_13,
    small020_cell_14,
    small020_cell_15,
    small020_cell_16,
    small020_cell_17,
    small020_cell_18,
    small020_cell_19,
    small020_cell_20,
    small020_cell_21,
    small020_cell_22,
    small020_cell_23,
    small020_cell_24,
    small020_cell_25,
    small020_cell_26,
    small020_cell_27,
    small020_cell_28,
    small020_cell_29,
    small020_cell_30,
    small020_cell_31]

private theorem small021_cell_0 : PeriodAffine.check ⟨qfrac 71 75, qfrac 18 19, 22395310⟩=true := by decide +kernel
private theorem small021_cell_1 : PeriodAffine.check ⟨qfrac 18 19, qfrac 56 59, 44188495⟩=true := by decide +kernel
private theorem small021_cell_2 : PeriodAffine.check ⟨qfrac 56 59, qfrac 39 41, 45354086⟩=true := by decide +kernel
private theorem small021_cell_3 : PeriodAffine.check ⟨qfrac 39 41, qfrac 20 21, 30438084⟩=true := by decide +kernel
private theorem small021_cell_4 : PeriodAffine.check ⟨qfrac 20 21, qfrac 41 43, 33218367⟩=true := by decide +kernel
private theorem small021_cell_5 : PeriodAffine.check ⟨qfrac 41 43, qfrac 65 68, 85808773⟩=true := by decide +kernel
private theorem small021_cell_6 : PeriodAffine.check ⟨qfrac 65 68, qfrac 89 93, 46139563⟩=true := by decide +kernel
private theorem small021_cell_7 : PeriodAffine.check ⟨qfrac 89 93, qfrac 113 118, 28435136⟩=true := by decide +kernel
private theorem small021_cell_8 : PeriodAffine.check ⟨qfrac 113 118, qfrac 24 25, 117646590⟩=true := by decide +kernel
private theorem small021_cell_9 : PeriodAffine.check ⟨qfrac 24 25, qfrac 73 76, 56936032⟩=true := by decide +kernel
private theorem small021_cell_10 : PeriodAffine.check ⟨qfrac 73 76, qfrac 49 51, 28245658⟩=true := by decide +kernel
private theorem small021_cell_11 : PeriodAffine.check ⟨qfrac 49 51, qfrac 27 28, 405706613⟩=true := by decide +kernel
private theorem small021_cell_12 : PeriodAffine.check ⟨qfrac 27 28, qfrac 57 59, 226160988⟩=true := by decide +kernel
private theorem small021_cell_13 : PeriodAffine.check ⟨qfrac 57 59, qfrac 30 31, 213524071⟩=true := by decide +kernel
private theorem small021_cell_14 : PeriodAffine.check ⟨qfrac 30 31, qfrac 31 32, 135611263⟩=true := by decide +kernel
private theorem small021_cell_15 : PeriodAffine.check ⟨qfrac 31 32, qfrac 32 33, 104883498⟩=true := by decide +kernel
private theorem small021_cell_16 : PeriodAffine.check ⟨qfrac 32 33, qfrac 33 34, 101363282⟩=true := by decide +kernel
private theorem small021_cell_17 : PeriodAffine.check ⟨qfrac 33 34, qfrac 73 75, 185383450⟩=true := by decide +kernel
private theorem small021_cell_18 : PeriodAffine.check ⟨qfrac 73 75, qfrac 37 38, 25857741⟩=true := by decide +kernel
private theorem small021_cell_19 : PeriodAffine.check ⟨qfrac 37 38, qfrac 115 118, 66953734⟩=true := by decide +kernel
private theorem small021_cell_20 : PeriodAffine.check ⟨qfrac 115 118, qfrac 40 41, 79744843⟩=true := by decide +kernel
private theorem small021_cell_21 : PeriodAffine.check ⟨qfrac 40 41, qfrac 41 42, 46026700⟩=true := by decide +kernel
private theorem small021_cell_22 : PeriodAffine.check ⟨qfrac 41 42, qfrac 42 43, 44921377⟩=true := by decide +kernel
private theorem small021_cell_23 : PeriodAffine.check ⟨qfrac 42 43, qfrac 91 93, 148708269⟩=true := by decide +kernel
private theorem small021_cell_24 : PeriodAffine.check ⟨qfrac 91 93, qfrac 49 50, 135820035⟩=true := by decide +kernel
private theorem small021_cell_25 : PeriodAffine.check ⟨qfrac 49 50, qfrac 50 51, 7366912⟩=true := by decide +kernel
private theorem small021_cell_26 : PeriodAffine.check ⟨qfrac 50 51, qfrac 58 59, 65137325⟩=true := by decide +kernel
private theorem small021_cell_27 : PeriodAffine.check ⟨qfrac 58 59, qfrac 67 68, 95088638⟩=true := by decide +kernel
private theorem small021_cell_28 : PeriodAffine.check ⟨qfrac 67 68, qfrac 74 75, 84726778⟩=true := by decide +kernel
private theorem small021_cell_29 : PeriodAffine.check ⟨qfrac 74 75, qfrac 75 76, 12249507⟩=true := by decide +kernel
private theorem small021_cell_30 : PeriodAffine.check ⟨qfrac 75 76, qfrac 83 84, 89074432⟩=true := by decide +kernel
private theorem small021_cell_31 : PeriodAffine.check ⟨qfrac 83 84, qfrac 92 93, 82836759⟩=true := by decide +kernel

theorem small021_affine_check : small021.all PeriodAffine.check=true := by
  simp only [small021, List.all_cons, List.all_nil, Bool.and_self,
    small021_cell_0,
    small021_cell_1,
    small021_cell_2,
    small021_cell_3,
    small021_cell_4,
    small021_cell_5,
    small021_cell_6,
    small021_cell_7,
    small021_cell_8,
    small021_cell_9,
    small021_cell_10,
    small021_cell_11,
    small021_cell_12,
    small021_cell_13,
    small021_cell_14,
    small021_cell_15,
    small021_cell_16,
    small021_cell_17,
    small021_cell_18,
    small021_cell_19,
    small021_cell_20,
    small021_cell_21,
    small021_cell_22,
    small021_cell_23,
    small021_cell_24,
    small021_cell_25,
    small021_cell_26,
    small021_cell_27,
    small021_cell_28,
    small021_cell_29,
    small021_cell_30,
    small021_cell_31]

end OddZetaSix.B40a.Cert
