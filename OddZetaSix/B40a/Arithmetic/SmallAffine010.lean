import OddZetaSix.B40a.Arithmetic.PeriodicAffine
import OddZetaSix.B40a.Arithmetic.SmallAffine006
import OddZetaSix.B40a.Certificate.Generated.Small010
import OddZetaSix.B40a.Certificate.Generated.Small011

namespace OddZetaSix.B40a.Cert
set_option maxHeartbeats 0
set_option maxRecDepth 32768

private theorem small010_cell_0 : PeriodAffine.check ⟨qfrac 14 31, qfrac 19 42, 58849894⟩=true := by decide +kernel
private theorem small010_cell_1 : PeriodAffine.check ⟨qfrac 19 42, qfrac 34 75, 73888704⟩=true := by decide +kernel
private theorem small010_cell_2 : PeriodAffine.check ⟨qfrac 34 75, qfrac 5 11, 95475259⟩=true := by decide +kernel
private theorem small010_cell_3 : PeriodAffine.check ⟨qfrac 5 11, qfrac 31 68, 107150856⟩=true := by decide +kernel
private theorem small010_cell_4 : PeriodAffine.check ⟨qfrac 31 68, qfrac 27 59, 144891267⟩=true := by decide +kernel
private theorem small010_cell_5 : PeriodAffine.check ⟨qfrac 27 59, qfrac 23 50, 209445134⟩=true := by decide +kernel
private theorem small010_cell_6 : PeriodAffine.check ⟨qfrac 23 50, qfrac 35 76, 22925612⟩=true := by decide +kernel
private theorem small010_cell_7 : PeriodAffine.check ⟨qfrac 35 76, qfrac 43 93, 85720625⟩=true := by decide +kernel
private theorem small010_cell_8 : PeriodAffine.check ⟨qfrac 43 93, qfrac 19 41, 50656012⟩=true := by decide +kernel
private theorem small010_cell_9 : PeriodAffine.check ⟨qfrac 19 41, qfrac 13 28, 43008223⟩=true := by decide +kernel
private theorem small010_cell_10 : PeriodAffine.check ⟨qfrac 13 28, qfrac 20 43, 41786562⟩=true := by decide +kernel
private theorem small010_cell_11 : PeriodAffine.check ⟨qfrac 20 43, qfrac 55 118, 50535986⟩=true := by decide +kernel
private theorem small010_cell_12 : PeriodAffine.check ⟨qfrac 55 118, qfrac 7 15, 29448425⟩=true := by decide +kernel
private theorem small010_cell_13 : PeriodAffine.check ⟨qfrac 7 15, qfrac 15 32, 111663198⟩=true := by decide +kernel
private theorem small010_cell_14 : PeriodAffine.check ⟨qfrac 15 32, qfrac 8 17, 67707225⟩=true := by decide +kernel
private theorem small010_cell_15 : PeriodAffine.check ⟨qfrac 8 17, qfrac 44 93, 18155830⟩=true := by decide +kernel
private theorem small010_cell_16 : PeriodAffine.check ⟨qfrac 44 93, qfrac 9 19, 7011177⟩=true := by decide +kernel
private theorem small010_cell_17 : PeriodAffine.check ⟨qfrac 9 19, qfrac 28 59, 8660516⟩=true := by decide +kernel
private theorem small010_cell_18 : PeriodAffine.check ⟨qfrac 28 59, qfrac 10 21, 17835899⟩=true := by decide +kernel
private theorem small010_cell_19 : PeriodAffine.check ⟨qfrac 10 21, qfrac 12 25, 65303513⟩=true := by decide +kernel
private theorem small010_cell_20 : PeriodAffine.check ⟨qfrac 12 25, qfrac 57 118, 194920769⟩=true := by decide +kernel
private theorem small010_cell_21 : PeriodAffine.check ⟨qfrac 57 118, qfrac 15 31, 57936850⟩=true := by decide +kernel
private theorem small010_cell_22 : PeriodAffine.check ⟨qfrac 15 31, qfrac 16 33, 71850071⟩=true := by decide +kernel
private theorem small010_cell_23 : PeriodAffine.check ⟨qfrac 16 33, qfrac 33 68, 32682941⟩=true := by decide +kernel
private theorem small010_cell_24 : PeriodAffine.check ⟨qfrac 33 68, qfrac 37 76, 116493496⟩=true := by decide +kernel
private theorem small010_cell_25 : PeriodAffine.check ⟨qfrac 37 76, qfrac 20 41, 75449521⟩=true := by decide +kernel
private theorem small010_cell_26 : PeriodAffine.check ⟨qfrac 20 41, qfrac 41 84, 23198478⟩=true := by decide +kernel
private theorem small010_cell_27 : PeriodAffine.check ⟨qfrac 41 84, qfrac 21 43, 22310496⟩=true := by decide +kernel
private theorem small010_cell_28 : PeriodAffine.check ⟨qfrac 21 43, qfrac 25 51, 151651342⟩=true := by decide +kernel
private theorem small010_cell_29 : PeriodAffine.check ⟨qfrac 25 51, qfrac 29 59, 115577796⟩=true := by decide +kernel
private theorem small010_cell_30 : PeriodAffine.check ⟨qfrac 29 59, qfrac 37 75, 164253551⟩=true := by decide +kernel
private theorem small010_cell_31 : PeriodAffine.check ⟨qfrac 37 75, qfrac 46 93, 122236692⟩=true := by decide +kernel

theorem small010_affine_check : small010.all PeriodAffine.check=true := by
  simp only [small010, List.all_cons, List.all_nil, Bool.and_self,
    small010_cell_0,
    small010_cell_1,
    small010_cell_2,
    small010_cell_3,
    small010_cell_4,
    small010_cell_5,
    small010_cell_6,
    small010_cell_7,
    small010_cell_8,
    small010_cell_9,
    small010_cell_10,
    small010_cell_11,
    small010_cell_12,
    small010_cell_13,
    small010_cell_14,
    small010_cell_15,
    small010_cell_16,
    small010_cell_17,
    small010_cell_18,
    small010_cell_19,
    small010_cell_20,
    small010_cell_21,
    small010_cell_22,
    small010_cell_23,
    small010_cell_24,
    small010_cell_25,
    small010_cell_26,
    small010_cell_27,
    small010_cell_28,
    small010_cell_29,
    small010_cell_30,
    small010_cell_31]

private theorem small011_cell_0 : PeriodAffine.check ⟨qfrac 46 93, qfrac 1 2, 553597463⟩=true := by decide +kernel
private theorem small011_cell_1 : PeriodAffine.check ⟨qfrac 1 2, qfrac 47 93, 67489370⟩=true := by decide +kernel
private theorem small011_cell_2 : PeriodAffine.check ⟨qfrac 47 93, qfrac 38 75, 30080347⟩=true := by decide +kernel
private theorem small011_cell_3 : PeriodAffine.check ⟨qfrac 38 75, qfrac 30 59, 32179024⟩=true := by decide +kernel
private theorem small011_cell_4 : PeriodAffine.check ⟨qfrac 30 59, qfrac 26 51, 24206016⟩=true := by decide +kernel
private theorem small011_cell_5 : PeriodAffine.check ⟨qfrac 26 51, qfrac 22 43, 51372333⟩=true := by decide +kernel
private theorem small011_cell_6 : PeriodAffine.check ⟨qfrac 22 43, qfrac 43 84, 9663650⟩=true := by decide +kernel
private theorem small011_cell_7 : PeriodAffine.check ⟨qfrac 43 84, qfrac 21 41, 10375901⟩=true := by decide +kernel
private theorem small011_cell_8 : PeriodAffine.check ⟨qfrac 21 41, qfrac 39 76, 34486197⟩=true := by decide +kernel
private theorem small011_cell_9 : PeriodAffine.check ⟨qfrac 39 76, qfrac 35 68, 56373184⟩=true := by decide +kernel
private theorem small011_cell_10 : PeriodAffine.check ⟨qfrac 35 68, qfrac 17 33, 16428490⟩=true := by decide +kernel
private theorem small011_cell_11 : PeriodAffine.check ⟨qfrac 17 33, qfrac 16 31, 36377253⟩=true := by decide +kernel
private theorem small011_cell_12 : PeriodAffine.check ⟨qfrac 16 31, qfrac 61 118, 30854416⟩=true := by decide +kernel
private theorem small011_cell_13 : PeriodAffine.check ⟨qfrac 61 118, qfrac 13 25, 117509799⟩=true := by decide +kernel
private theorem small011_cell_14 : PeriodAffine.check ⟨qfrac 13 25, qfrac 11 21, 317383705⟩=true := by decide +kernel
private theorem small011_cell_15 : PeriodAffine.check ⟨qfrac 11 21, qfrac 31 59, 145039104⟩=true := by decide +kernel
private theorem small011_cell_16 : PeriodAffine.check ⟨qfrac 31 59, qfrac 10 19, 82868379⟩=true := by decide +kernel
private theorem small011_cell_17 : PeriodAffine.check ⟨qfrac 10 19, qfrac 49 93, 53591835⟩=true := by decide +kernel
private theorem small011_cell_18 : PeriodAffine.check ⟨qfrac 49 93, qfrac 9 17, 249099121⟩=true := by decide +kernel
private theorem small011_cell_19 : PeriodAffine.check ⟨qfrac 9 17, qfrac 17 32, 118281171⟩=true := by decide +kernel
private theorem small011_cell_20 : PeriodAffine.check ⟨qfrac 17 32, qfrac 8 15, 107254336⟩=true := by decide +kernel
private theorem small011_cell_21 : PeriodAffine.check ⟨qfrac 8 15, qfrac 63 118, 31174577⟩=true := by decide +kernel
private theorem small011_cell_22 : PeriodAffine.check ⟨qfrac 63 118, qfrac 23 43, 57871254⟩=true := by decide +kernel
private theorem small011_cell_23 : PeriodAffine.check ⟨qfrac 23 43, qfrac 15 28, 53772519⟩=true := by decide +kernel
private theorem small011_cell_24 : PeriodAffine.check ⟨qfrac 15 28, qfrac 22 41, 58538265⟩=true := by decide +kernel
private theorem small011_cell_25 : PeriodAffine.check ⟨qfrac 22 41, qfrac 50 93, 70269240⟩=true := by decide +kernel
private theorem small011_cell_26 : PeriodAffine.check ⟨qfrac 50 93, qfrac 41 76, 124424207⟩=true := by decide +kernel
private theorem small011_cell_27 : PeriodAffine.check ⟨qfrac 41 76, qfrac 27 50, 35853461⟩=true := by decide +kernel
private theorem small011_cell_28 : PeriodAffine.check ⟨qfrac 27 50, qfrac 32 59, 49277222⟩=true := by decide +kernel
private theorem small011_cell_29 : PeriodAffine.check ⟨qfrac 32 59, qfrac 37 68, 36577554⟩=true := by decide +kernel
private theorem small011_cell_30 : PeriodAffine.check ⟨qfrac 37 68, qfrac 6 11, 36445407⟩=true := by decide +kernel
private theorem small011_cell_31 : PeriodAffine.check ⟨qfrac 6 11, qfrac 41 75, 39842448⟩=true := by decide +kernel

theorem small011_affine_check : small011.all PeriodAffine.check=true := by
  simp only [small011, List.all_cons, List.all_nil, Bool.and_self,
    small011_cell_0,
    small011_cell_1,
    small011_cell_2,
    small011_cell_3,
    small011_cell_4,
    small011_cell_5,
    small011_cell_6,
    small011_cell_7,
    small011_cell_8,
    small011_cell_9,
    small011_cell_10,
    small011_cell_11,
    small011_cell_12,
    small011_cell_13,
    small011_cell_14,
    small011_cell_15,
    small011_cell_16,
    small011_cell_17,
    small011_cell_18,
    small011_cell_19,
    small011_cell_20,
    small011_cell_21,
    small011_cell_22,
    small011_cell_23,
    small011_cell_24,
    small011_cell_25,
    small011_cell_26,
    small011_cell_27,
    small011_cell_28,
    small011_cell_29,
    small011_cell_30,
    small011_cell_31]

end OddZetaSix.B40a.Cert
