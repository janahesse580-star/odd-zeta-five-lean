import OddZetaSix.B40a.Arithmetic.PeriodicAffine
import OddZetaSix.B40a.Certificate.Generated.Small000
import OddZetaSix.B40a.Certificate.Generated.Small001

namespace OddZetaSix.B40a.Cert
set_option maxHeartbeats 0
set_option maxRecDepth 32768

private theorem small000_cell_0 : PeriodAffine.check ⟨qfrac 0 1, qfrac 1 118, 584643792⟩=true := by decide +kernel
private theorem small000_cell_1 : PeriodAffine.check ⟨qfrac 1 118, qfrac 1 93, 220869745⟩=true := by decide +kernel
private theorem small000_cell_2 : PeriodAffine.check ⟨qfrac 1 93, qfrac 1 84, 125053235⟩=true := by decide +kernel
private theorem small000_cell_3 : PeriodAffine.check ⟨qfrac 1 84, qfrac 1 76, 134815273⟩=true := by decide +kernel
private theorem small000_cell_4 : PeriodAffine.check ⟨qfrac 1 76, qfrac 1 75, 18629033⟩=true := by decide +kernel
private theorem small000_cell_5 : PeriodAffine.check ⟨qfrac 1 75, qfrac 1 68, 143671690⟩=true := by decide +kernel
private theorem small000_cell_6 : PeriodAffine.check ⟨qfrac 1 68, qfrac 1 59, 235573294⟩=true := by decide +kernel
private theorem small000_cell_7 : PeriodAffine.check ⟨qfrac 1 59, qfrac 1 51, 294908571⟩=true := by decide +kernel
private theorem small000_cell_8 : PeriodAffine.check ⟨qfrac 1 51, qfrac 1 50, 45362413⟩=true := by decide +kernel
private theorem small000_cell_9 : PeriodAffine.check ⟨qfrac 1 50, qfrac 2 93, 61843759⟩=true := by decide +kernel
private theorem small000_cell_10 : PeriodAffine.check ⟨qfrac 2 93, qfrac 1 43, 81100864⟩=true := by decide +kernel
private theorem small000_cell_11 : PeriodAffine.check ⟨qfrac 1 43, qfrac 1 42, 27667324⟩=true := by decide +kernel
private theorem small000_cell_12 : PeriodAffine.check ⟨qfrac 1 42, qfrac 1 41, 30060160⟩=true := by decide +kernel
private theorem small000_cell_13 : PeriodAffine.check ⟨qfrac 1 41, qfrac 3 118, 56143139⟩=true := by decide +kernel
private theorem small000_cell_14 : PeriodAffine.check ⟨qfrac 3 118, qfrac 1 38, 51207166⟩=true := by decide +kernel
private theorem small000_cell_15 : PeriodAffine.check ⟨qfrac 1 38, qfrac 2 75, 20838762⟩=true := by decide +kernel
private theorem small000_cell_16 : PeriodAffine.check ⟨qfrac 2 75, qfrac 1 34, 176434313⟩=true := by decide +kernel
private theorem small000_cell_17 : PeriodAffine.check ⟨qfrac 1 34, qfrac 1 33, 18029865⟩=true := by decide +kernel
private theorem small000_cell_18 : PeriodAffine.check ⟨qfrac 1 33, qfrac 1 32, 24962699⟩=true := by decide +kernel
private theorem small000_cell_19 : PeriodAffine.check ⟨qfrac 1 32, qfrac 1 31, 12711618⟩=true := by decide +kernel
private theorem small000_cell_20 : PeriodAffine.check ⟨qfrac 1 31, qfrac 2 59, 20990834⟩=true := by decide +kernel
private theorem small000_cell_21 : PeriodAffine.check ⟨qfrac 2 59, qfrac 1 28, 34680668⟩=true := by decide +kernel
private theorem small000_cell_22 : PeriodAffine.check ⟨qfrac 1 28, qfrac 2 51, 94905480⟩=true := by decide +kernel
private theorem small000_cell_23 : PeriodAffine.check ⟨qfrac 2 51, qfrac 3 76, 6672170⟩=true := by decide +kernel
private theorem small000_cell_24 : PeriodAffine.check ⟨qfrac 3 76, qfrac 1 25, 13478237⟩=true := by decide +kernel
private theorem small000_cell_25 : PeriodAffine.check ⟨qfrac 1 25, qfrac 5 118, 190284129⟩=true := by decide +kernel
private theorem small000_cell_26 : PeriodAffine.check ⟨qfrac 5 118, qfrac 4 93, 54159916⟩=true := by decide +kernel
private theorem small000_cell_27 : PeriodAffine.check ⟨qfrac 4 93, qfrac 3 68, 97031622⟩=true := by decide +kernel
private theorem small000_cell_28 : PeriodAffine.check ⟨qfrac 3 68, qfrac 2 43, 223043610⟩=true := by decide +kernel
private theorem small000_cell_29 : PeriodAffine.check ⟨qfrac 2 43, qfrac 1 21, 109218392⟩=true := by decide +kernel
private theorem small000_cell_30 : PeriodAffine.check ⟨qfrac 1 21, qfrac 2 41, 118671244⟩=true := by decide +kernel
private theorem small000_cell_31 : PeriodAffine.check ⟨qfrac 2 41, qfrac 3 59, 221677705⟩=true := by decide +kernel

theorem small000_affine_check : small000.all PeriodAffine.check=true := by
  simp only [small000, List.all_cons, List.all_nil, Bool.and_self,
    small000_cell_0,
    small000_cell_1,
    small000_cell_2,
    small000_cell_3,
    small000_cell_4,
    small000_cell_5,
    small000_cell_6,
    small000_cell_7,
    small000_cell_8,
    small000_cell_9,
    small000_cell_10,
    small000_cell_11,
    small000_cell_12,
    small000_cell_13,
    small000_cell_14,
    small000_cell_15,
    small000_cell_16,
    small000_cell_17,
    small000_cell_18,
    small000_cell_19,
    small000_cell_20,
    small000_cell_21,
    small000_cell_22,
    small000_cell_23,
    small000_cell_24,
    small000_cell_25,
    small000_cell_26,
    small000_cell_27,
    small000_cell_28,
    small000_cell_29,
    small000_cell_30,
    small000_cell_31]

private theorem small001_cell_0 : PeriodAffine.check ⟨qfrac 3 59, qfrac 1 19, 202305315⟩=true := by decide +kernel
private theorem small001_cell_1 : PeriodAffine.check ⟨qfrac 1 19, qfrac 4 75, 82381064⟩=true := by decide +kernel
private theorem small001_cell_2 : PeriodAffine.check ⟨qfrac 4 75, qfrac 5 93, 51261440⟩=true := by decide +kernel
private theorem small001_cell_3 : PeriodAffine.check ⟨qfrac 5 93, qfrac 1 18, 219792959⟩=true := by decide +kernel
private theorem small001_cell_4 : PeriodAffine.check ⟨qfrac 1 18, qfrac 1 17, 426109167⟩=true := by decide +kernel
private theorem small001_cell_5 : PeriodAffine.check ⟨qfrac 1 17, qfrac 7 118, 42461986⟩=true := by decide +kernel
private theorem small001_cell_6 : PeriodAffine.check ⟨qfrac 7 118, qfrac 5 84, 17529697⟩=true := by decide +kernel
private theorem small001_cell_7 : PeriodAffine.check ⟨qfrac 5 84, qfrac 3 50, 41880741⟩=true := by decide +kernel
private theorem small001_cell_8 : PeriodAffine.check ⟨qfrac 3 50, qfrac 2 33, 11236125⟩=true := by decide +kernel
private theorem small001_cell_9 : PeriodAffine.check ⟨qfrac 2 33, qfrac 1 16, 50681121⟩=true := by decide +kernel
private theorem small001_cell_10 : PeriodAffine.check ⟨qfrac 1 16, qfrac 2 31, 50016697⟩=true := by decide +kernel
private theorem small001_cell_11 : PeriodAffine.check ⟨qfrac 2 31, qfrac 5 76, 36418359⟩=true := by decide +kernel
private theorem small001_cell_12 : PeriodAffine.check ⟨qfrac 5 76, qfrac 1 15, 21130924⟩=true := by decide +kernel
private theorem small001_cell_13 : PeriodAffine.check ⟨qfrac 1 15, qfrac 4 59, 21135811⟩=true := by decide +kernel
private theorem small001_cell_14 : PeriodAffine.check ⟨qfrac 4 59, qfrac 3 43, 34895014⟩=true := by decide +kernel
private theorem small001_cell_15 : PeriodAffine.check ⟨qfrac 3 43, qfrac 1 14, 38594416⟩=true := by decide +kernel
private theorem small001_cell_16 : PeriodAffine.check ⟨qfrac 1 14, qfrac 3 41, 48161704⟩=true := by decide +kernel
private theorem small001_cell_17 : PeriodAffine.check ⟨qfrac 3 41, qfrac 5 68, 10438971⟩=true := by decide +kernel
private theorem small001_cell_18 : PeriodAffine.check ⟨qfrac 5 68, qfrac 7 93, 56357659⟩=true := by decide +kernel
private theorem small001_cell_19 : PeriodAffine.check ⟨qfrac 7 93, qfrac 9 118, 36722278⟩=true := by decide +kernel
private theorem small001_cell_20 : PeriodAffine.check ⟨qfrac 9 118, qfrac 4 51, 89651405⟩=true := by decide +kernel
private theorem small001_cell_21 : PeriodAffine.check ⟨qfrac 4 51, qfrac 3 38, 23539103⟩=true := by decide +kernel
private theorem small001_cell_22 : PeriodAffine.check ⟨qfrac 3 38, qfrac 2 25, 50570062⟩=true := by decide +kernel
private theorem small001_cell_23 : PeriodAffine.check ⟨qfrac 2 25, qfrac 1 12, 349439247⟩=true := by decide +kernel
private theorem small001_cell_24 : PeriodAffine.check ⟨qfrac 1 12, qfrac 5 59, 158240972⟩=true := by decide +kernel
private theorem small001_cell_25 : PeriodAffine.check ⟨qfrac 5 59, qfrac 8 93, 148138031⟩=true := by decide +kernel
private theorem small001_cell_26 : PeriodAffine.check ⟨qfrac 8 93, qfrac 3 34, 268913277⟩=true := by decide +kernel
private theorem small001_cell_27 : PeriodAffine.check ⟨qfrac 3 34, qfrac 1 11, 211405684⟩=true := by decide +kernel
private theorem small001_cell_28 : PeriodAffine.check ⟨qfrac 1 11, qfrac 7 76, 101714701⟩=true := by decide +kernel
private theorem small001_cell_29 : PeriodAffine.check ⟨qfrac 7 76, qfrac 4 43, 81037256⟩=true := by decide +kernel
private theorem small001_cell_30 : PeriodAffine.check ⟨qfrac 4 43, qfrac 11 118, 17727625⟩=true := by decide +kernel
private theorem small001_cell_31 : PeriodAffine.check ⟨qfrac 11 118, qfrac 7 75, 10235843⟩=true := by decide +kernel

theorem small001_affine_check : small001.all PeriodAffine.check=true := by
  simp only [small001, List.all_cons, List.all_nil, Bool.and_self,
    small001_cell_0,
    small001_cell_1,
    small001_cell_2,
    small001_cell_3,
    small001_cell_4,
    small001_cell_5,
    small001_cell_6,
    small001_cell_7,
    small001_cell_8,
    small001_cell_9,
    small001_cell_10,
    small001_cell_11,
    small001_cell_12,
    small001_cell_13,
    small001_cell_14,
    small001_cell_15,
    small001_cell_16,
    small001_cell_17,
    small001_cell_18,
    small001_cell_19,
    small001_cell_20,
    small001_cell_21,
    small001_cell_22,
    small001_cell_23,
    small001_cell_24,
    small001_cell_25,
    small001_cell_26,
    small001_cell_27,
    small001_cell_28,
    small001_cell_29,
    small001_cell_30,
    small001_cell_31]

end OddZetaSix.B40a.Cert
