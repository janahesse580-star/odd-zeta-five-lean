import OddZetaSix.B40a.Arithmetic.PeriodicAffine
import OddZetaSix.B40a.Arithmetic.SmallAffine014
import OddZetaSix.B40a.Certificate.Generated.Small018
import OddZetaSix.B40a.Certificate.Generated.Small019

namespace OddZetaSix.B40a.Cert
set_option maxHeartbeats 0
set_option maxRecDepth 32768

private theorem small018_cell_0 : PeriodAffine.check ⟨qfrac 31 38, qfrac 76 93, 99071152⟩=true := by decide +kernel
private theorem small018_cell_1 : PeriodAffine.check ⟨qfrac 76 93, qfrac 9 11, 70931250⟩=true := by decide +kernel
private theorem small018_cell_2 : PeriodAffine.check ⟨qfrac 9 11, qfrac 41 50, 235923161⟩=true := by decide +kernel
private theorem small018_cell_3 : PeriodAffine.check ⟨qfrac 41 50, qfrac 23 28, 74786484⟩=true := by decide +kernel
private theorem small018_cell_4 : PeriodAffine.check ⟨qfrac 23 28, qfrac 97 118, 32675950⟩=true := by decide +kernel
private theorem small018_cell_5 : PeriodAffine.check ⟨qfrac 97 118, qfrac 14 17, 83216793⟩=true := by decide +kernel
private theorem small018_cell_6 : PeriodAffine.check ⟨qfrac 14 17, qfrac 62 75, 52923306⟩=true := by decide +kernel
private theorem small018_cell_7 : PeriodAffine.check ⟨qfrac 62 75, qfrac 77 93, 41192141⟩=true := by decide +kernel
private theorem small018_cell_8 : PeriodAffine.check ⟨qfrac 77 93, qfrac 63 76, 32190377⟩=true := by decide +kernel
private theorem small018_cell_9 : PeriodAffine.check ⟨qfrac 63 76, qfrac 34 41, 9234842⟩=true := by decide +kernel
private theorem small018_cell_10 : PeriodAffine.check ⟨qfrac 34 41, qfrac 49 59, 31974047⟩=true := by decide +kernel
private theorem small018_cell_11 : PeriodAffine.check ⟨qfrac 49 59, qfrac 5 6, 81594942⟩=true := by decide +kernel
private theorem small018_cell_12 : PeriodAffine.check ⟨qfrac 5 6, qfrac 36 43, 158983449⟩=true := by decide +kernel
private theorem small018_cell_13 : PeriodAffine.check ⟨qfrac 36 43, qfrac 57 68, 51052636⟩=true := by decide +kernel
private theorem small018_cell_14 : PeriodAffine.check ⟨qfrac 57 68, qfrac 26 31, 24885789⟩=true := by decide +kernel
private theorem small018_cell_15 : PeriodAffine.check ⟨qfrac 26 31, qfrac 99 118, 14707157⟩=true := by decide +kernel
private theorem small018_cell_16 : PeriodAffine.check ⟨qfrac 99 118, qfrac 21 25, 57068617⟩=true := by decide +kernel
private theorem small018_cell_17 : PeriodAffine.check ⟨qfrac 21 25, qfrac 16 19, 253029706⟩=true := by decide +kernel
private theorem small018_cell_18 : PeriodAffine.check ⟨qfrac 16 19, qfrac 43 51, 129843178⟩=true := by decide +kernel
private theorem small018_cell_19 : PeriodAffine.check ⟨qfrac 43 51, qfrac 27 32, 78882516⟩=true := by decide +kernel
private theorem small018_cell_20 : PeriodAffine.check ⟨qfrac 27 32, qfrac 71 84, 153788590⟩=true := by decide +kernel
private theorem small018_cell_21 : PeriodAffine.check ⟨qfrac 71 84, qfrac 50 59, 243906742⟩=true := by decide +kernel
private theorem small018_cell_22 : PeriodAffine.check ⟨qfrac 50 59, qfrac 28 33, 118682718⟩=true := by decide +kernel
private theorem small018_cell_23 : PeriodAffine.check ⟨qfrac 28 33, qfrac 79 93, 116506060⟩=true := by decide +kernel
private theorem small018_cell_24 : PeriodAffine.check ⟨qfrac 79 93, qfrac 29 34, 442407815⟩=true := by decide +kernel
private theorem small018_cell_25 : PeriodAffine.check ⟨qfrac 29 34, qfrac 64 75, 29822695⟩=true := by decide +kernel
private theorem small018_cell_26 : PeriodAffine.check ⟨qfrac 64 75, qfrac 35 41, 25151044⟩=true := by decide +kernel
private theorem small018_cell_27 : PeriodAffine.check ⟨qfrac 35 41, qfrac 65 76, 129431088⟩=true := by decide +kernel
private theorem small018_cell_28 : PeriodAffine.check ⟨qfrac 65 76, qfrac 101 118, 56668277⟩=true := by decide +kernel
private theorem small018_cell_29 : PeriodAffine.check ⟨qfrac 101 118, qfrac 6 7, 106613888⟩=true := by decide +kernel
private theorem small018_cell_30 : PeriodAffine.check ⟨qfrac 6 7, qfrac 43 50, 272426935⟩=true := by decide +kernel
private theorem small018_cell_31 : PeriodAffine.check ⟨qfrac 43 50, qfrac 80 93, 6204803⟩=true := by decide +kernel

theorem small018_affine_check : small018.all PeriodAffine.check=true := by
  simp only [small018, List.all_cons, List.all_nil, Bool.and_self,
    small018_cell_0,
    small018_cell_1,
    small018_cell_2,
    small018_cell_3,
    small018_cell_4,
    small018_cell_5,
    small018_cell_6,
    small018_cell_7,
    small018_cell_8,
    small018_cell_9,
    small018_cell_10,
    small018_cell_11,
    small018_cell_12,
    small018_cell_13,
    small018_cell_14,
    small018_cell_15,
    small018_cell_16,
    small018_cell_17,
    small018_cell_18,
    small018_cell_19,
    small018_cell_20,
    small018_cell_21,
    small018_cell_22,
    small018_cell_23,
    small018_cell_24,
    small018_cell_25,
    small018_cell_26,
    small018_cell_27,
    small018_cell_28,
    small018_cell_29,
    small018_cell_30,
    small018_cell_31]

private theorem small019_cell_0 : PeriodAffine.check ⟨qfrac 80 93, qfrac 37 43, 7368558⟩=true := by decide +kernel
private theorem small019_cell_1 : PeriodAffine.check ⟨qfrac 37 43, qfrac 44 51, 63874561⟩=true := by decide +kernel
private theorem small019_cell_2 : PeriodAffine.check ⟨qfrac 44 51, qfrac 51 59, 51178115⟩=true := by decide +kernel
private theorem small019_cell_3 : PeriodAffine.check ⟨qfrac 51 59, qfrac 13 15, 108180450⟩=true := by decide +kernel
private theorem small019_cell_4 : PeriodAffine.check ⟨qfrac 13 15, qfrac 59 68, 64253738⟩=true := by decide +kernel
private theorem small019_cell_5 : PeriodAffine.check ⟨qfrac 59 68, qfrac 33 38, 57132074⟩=true := by decide +kernel
private theorem small019_cell_6 : PeriodAffine.check ⟨qfrac 33 38, qfrac 73 84, 48700770⟩=true := by decide +kernel
private theorem small019_cell_7 : PeriodAffine.check ⟨qfrac 73 84, qfrac 27 31, 151023691⟩=true := by decide +kernel
private theorem small019_cell_8 : PeriodAffine.check ⟨qfrac 27 31, qfrac 103 118, 152696764⟩=true := by decide +kernel
private theorem small019_cell_9 : PeriodAffine.check ⟨qfrac 103 118, qfrac 7 8, 171512915⟩=true := by decide +kernel
private theorem small019_cell_10 : PeriodAffine.check ⟨qfrac 7 8, qfrac 36 41, 175782610⟩=true := by decide +kernel
private theorem small019_cell_11 : PeriodAffine.check ⟨qfrac 36 41, qfrac 29 33, 40860003⟩=true := by decide +kernel
private theorem small019_cell_12 : PeriodAffine.check ⟨qfrac 29 33, qfrac 22 25, 67774937⟩=true := by decide +kernel
private theorem small019_cell_13 : PeriodAffine.check ⟨qfrac 22 25, qfrac 37 42, 109262416⟩=true := by decide +kernel
private theorem small019_cell_14 : PeriodAffine.check ⟨qfrac 37 42, qfrac 52 59, 47242235⟩=true := by decide +kernel
private theorem small019_cell_15 : PeriodAffine.check ⟨qfrac 52 59, qfrac 67 76, 26351911⟩=true := by decide +kernel
private theorem small019_cell_16 : PeriodAffine.check ⟨qfrac 67 76, qfrac 82 93, 16810370⟩=true := by decide +kernel
private theorem small019_cell_17 : PeriodAffine.check ⟨qfrac 82 93, qfrac 15 17, 76007434⟩=true := by decide +kernel
private theorem small019_cell_18 : PeriodAffine.check ⟨qfrac 15 17, qfrac 38 43, 91637028⟩=true := by decide +kernel
private theorem small019_cell_19 : PeriodAffine.check ⟨qfrac 38 43, qfrac 8 9, 423495802⟩=true := by decide +kernel
private theorem small019_cell_20 : PeriodAffine.check ⟨qfrac 8 9, qfrac 105 118, 90565279⟩=true := by decide +kernel
private theorem small019_cell_21 : PeriodAffine.check ⟨qfrac 105 118, qfrac 83 93, 297400630⟩=true := by decide +kernel
private theorem small019_cell_22 : PeriodAffine.check ⟨qfrac 83 93, qfrac 25 28, 48696512⟩=true := by decide +kernel
private theorem small019_cell_23 : PeriodAffine.check ⟨qfrac 25 28, qfrac 67 75, 60189370⟩=true := by decide +kernel
private theorem small019_cell_24 : PeriodAffine.check ⟨qfrac 67 75, qfrac 17 19, 174693996⟩=true := by decide +kernel
private theorem small019_cell_25 : PeriodAffine.check ⟨qfrac 17 19, qfrac 61 68, 279779637⟩=true := by decide +kernel
private theorem small019_cell_26 : PeriodAffine.check ⟨qfrac 61 68, qfrac 53 59, 148193845⟩=true := by decide +kernel
private theorem small019_cell_27 : PeriodAffine.check ⟨qfrac 53 59, qfrac 9 10, 208165395⟩=true := by decide +kernel
private theorem small019_cell_28 : PeriodAffine.check ⟨qfrac 9 10, qfrac 46 51, 88479499⟩=true := by decide +kernel
private theorem small019_cell_29 : PeriodAffine.check ⟨qfrac 46 51, qfrac 37 41, 23612317⟩=true := by decide +kernel
private theorem small019_cell_30 : PeriodAffine.check ⟨qfrac 37 41, qfrac 28 31, 40623044⟩=true := by decide +kernel
private theorem small019_cell_31 : PeriodAffine.check ⟨qfrac 28 31, qfrac 19 21, 85550109⟩=true := by decide +kernel

theorem small019_affine_check : small019.all PeriodAffine.check=true := by
  simp only [small019, List.all_cons, List.all_nil, Bool.and_self,
    small019_cell_0,
    small019_cell_1,
    small019_cell_2,
    small019_cell_3,
    small019_cell_4,
    small019_cell_5,
    small019_cell_6,
    small019_cell_7,
    small019_cell_8,
    small019_cell_9,
    small019_cell_10,
    small019_cell_11,
    small019_cell_12,
    small019_cell_13,
    small019_cell_14,
    small019_cell_15,
    small019_cell_16,
    small019_cell_17,
    small019_cell_18,
    small019_cell_19,
    small019_cell_20,
    small019_cell_21,
    small019_cell_22,
    small019_cell_23,
    small019_cell_24,
    small019_cell_25,
    small019_cell_26,
    small019_cell_27,
    small019_cell_28,
    small019_cell_29,
    small019_cell_30,
    small019_cell_31]

end OddZetaSix.B40a.Cert
