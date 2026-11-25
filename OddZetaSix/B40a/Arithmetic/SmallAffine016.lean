import OddZetaSix.B40a.Arithmetic.PeriodicAffine
import OddZetaSix.B40a.Arithmetic.SmallAffine012
import OddZetaSix.B40a.Certificate.Generated.Small016
import OddZetaSix.B40a.Certificate.Generated.Small017

namespace OddZetaSix.B40a.Cert
set_option maxHeartbeats 0
set_option maxRecDepth 32768

private theorem small016_cell_0 : PeriodAffine.check ⟨qfrac 37 51, qfrac 61 84, 46773509⟩=true := by decide +kernel
private theorem small016_cell_1 : PeriodAffine.check ⟨qfrac 61 84, qfrac 8 11, 74408062⟩=true := by decide +kernel
private theorem small016_cell_2 : PeriodAffine.check ⟨qfrac 8 11, qfrac 43 59, 110335642⟩=true := by decide +kernel
private theorem small016_cell_3 : PeriodAffine.check ⟨qfrac 43 59, qfrac 68 93, 179959178⟩=true := by decide +kernel
private theorem small016_cell_4 : PeriodAffine.check ⟨qfrac 68 93, qfrac 30 41, 41520223⟩=true := by decide +kernel
private theorem small016_cell_5 : PeriodAffine.check ⟨qfrac 30 41, qfrac 11 15, 132585119⟩=true := by decide +kernel
private theorem small016_cell_6 : PeriodAffine.check ⟨qfrac 11 15, qfrac 25 34, 167586286⟩=true := by decide +kernel
private theorem small016_cell_7 : PeriodAffine.check ⟨qfrac 25 34, qfrac 14 19, 82844118⟩=true := by decide +kernel
private theorem small016_cell_8 : PeriodAffine.check ⟨qfrac 14 19, qfrac 87 118, 24851256⟩=true := by decide +kernel
private theorem small016_cell_9 : PeriodAffine.check ⟨qfrac 87 118, qfrac 31 42, 46090520⟩=true := by decide +kernel
private theorem small016_cell_10 : PeriodAffine.check ⟨qfrac 31 42, qfrac 37 50, 114508073⟩=true := by decide +kernel
private theorem small016_cell_11 : PeriodAffine.check ⟨qfrac 37 50, qfrac 23 31, 37864206⟩=true := by decide +kernel
private theorem small016_cell_12 : PeriodAffine.check ⟨qfrac 23 31, qfrac 32 43, 51763435⟩=true := by decide +kernel
private theorem small016_cell_13 : PeriodAffine.check ⟨qfrac 32 43, qfrac 38 51, 19252844⟩=true := by decide +kernel
private theorem small016_cell_14 : PeriodAffine.check ⟨qfrac 38 51, qfrac 44 59, 14491733⟩=true := by decide +kernel
private theorem small016_cell_15 : PeriodAffine.check ⟨qfrac 44 59, qfrac 56 75, 23535043⟩=true := by decide +kernel
private theorem small016_cell_16 : PeriodAffine.check ⟨qfrac 56 75, qfrac 3 4, 130157687⟩=true := by decide +kernel
private theorem small016_cell_17 : PeriodAffine.check ⟨qfrac 3 4, qfrac 70 93, 103467016⟩=true := by decide +kernel
private theorem small016_cell_18 : PeriodAffine.check ⟨qfrac 70 93, qfrac 89 118, 56214377⟩=true := by decide +kernel
private theorem small016_cell_19 : PeriodAffine.check ⟨qfrac 89 118, qfrac 31 41, 64186130⟩=true := by decide +kernel
private theorem small016_cell_20 : PeriodAffine.check ⟨qfrac 31 41, qfrac 25 33, 50028284⟩=true := by decide +kernel
private theorem small016_cell_21 : PeriodAffine.check ⟨qfrac 25 33, qfrac 19 25, 84019064⟩=true := by decide +kernel
private theorem small016_cell_22 : PeriodAffine.check ⟨qfrac 19 25, qfrac 16 21, 138246733⟩=true := by decide +kernel
private theorem small016_cell_23 : PeriodAffine.check ⟨qfrac 16 21, qfrac 45 59, 60952947⟩=true := by decide +kernel
private theorem small016_cell_24 : PeriodAffine.check ⟨qfrac 45 59, qfrac 29 38, 34295390⟩=true := by decide +kernel
private theorem small016_cell_25 : PeriodAffine.check ⟨qfrac 29 38, qfrac 71 93, 21986355⟩=true := by decide +kernel
private theorem small016_cell_26 : PeriodAffine.check ⟨qfrac 71 93, qfrac 13 17, 100430939⟩=true := by decide +kernel
private theorem small016_cell_27 : PeriodAffine.check ⟨qfrac 13 17, qfrac 33 43, 132661675⟩=true := by decide +kernel
private theorem small016_cell_28 : PeriodAffine.check ⟨qfrac 33 43, qfrac 91 118, 213822086⟩=true := by decide +kernel
private theorem small016_cell_29 : PeriodAffine.check ⟨qfrac 91 118, qfrac 58 75, 150824556⟩=true := by decide +kernel
private theorem small016_cell_30 : PeriodAffine.check ⟨qfrac 58 75, qfrac 65 84, 37715781⟩=true := by decide +kernel
private theorem small016_cell_31 : PeriodAffine.check ⟨qfrac 65 84, qfrac 24 31, 30933354⟩=true := by decide +kernel

theorem small016_affine_check : small016.all PeriodAffine.check=true := by
  simp only [small016, List.all_cons, List.all_nil, Bool.and_self,
    small016_cell_0,
    small016_cell_1,
    small016_cell_2,
    small016_cell_3,
    small016_cell_4,
    small016_cell_5,
    small016_cell_6,
    small016_cell_7,
    small016_cell_8,
    small016_cell_9,
    small016_cell_10,
    small016_cell_11,
    small016_cell_12,
    small016_cell_13,
    small016_cell_14,
    small016_cell_15,
    small016_cell_16,
    small016_cell_17,
    small016_cell_18,
    small016_cell_19,
    small016_cell_20,
    small016_cell_21,
    small016_cell_22,
    small016_cell_23,
    small016_cell_24,
    small016_cell_25,
    small016_cell_26,
    small016_cell_27,
    small016_cell_28,
    small016_cell_29,
    small016_cell_30,
    small016_cell_31]

private theorem small017_cell_0 : PeriodAffine.check ⟨qfrac 24 31, qfrac 59 76, 170555239⟩=true := by decide +kernel
private theorem small017_cell_1 : PeriodAffine.check ⟨qfrac 59 76, qfrac 7 9, 116970018⟩=true := by decide +kernel
private theorem small017_cell_2 : PeriodAffine.check ⟨qfrac 7 9, qfrac 53 68, 128722840⟩=true := by decide +kernel
private theorem small017_cell_3 : PeriodAffine.check ⟨qfrac 53 68, qfrac 46 59, 19394807⟩=true := by decide +kernel
private theorem small017_cell_4 : PeriodAffine.check ⟨qfrac 46 59, qfrac 39 50, 26545626⟩=true := by decide +kernel
private theorem small017_cell_5 : PeriodAffine.check ⟨qfrac 39 50, qfrac 32 41, 13012163⟩=true := by decide +kernel
private theorem small017_cell_6 : PeriodAffine.check ⟨qfrac 32 41, qfrac 25 32, 21378214⟩=true := by decide +kernel
private theorem small017_cell_7 : PeriodAffine.check ⟨qfrac 25 32, qfrac 40 51, 69191664⟩=true := by decide +kernel
private theorem small017_cell_8 : PeriodAffine.check ⟨qfrac 40 51, qfrac 73 93, 18378467⟩=true := by decide +kernel
private theorem small017_cell_9 : PeriodAffine.check ⟨qfrac 73 93, qfrac 11 14, 23641514⟩=true := by decide +kernel
private theorem small017_cell_10 : PeriodAffine.check ⟨qfrac 11 14, qfrac 59 75, 30115401⟩=true := by decide +kernel
private theorem small017_cell_11 : PeriodAffine.check ⟨qfrac 59 75, qfrac 26 33, 39587229⟩=true := by decide +kernel
private theorem small017_cell_12 : PeriodAffine.check ⟨qfrac 26 33, qfrac 93 118, 8564668⟩=true := by decide +kernel
private theorem small017_cell_13 : PeriodAffine.check ⟨qfrac 93 118, qfrac 15 19, 45684676⟩=true := by decide +kernel
private theorem small017_cell_14 : PeriodAffine.check ⟨qfrac 15 19, qfrac 34 43, 43308755⟩=true := by decide +kernel
private theorem small017_cell_15 : PeriodAffine.check ⟨qfrac 34 43, qfrac 27 34, 128673241⟩=true := by decide +kernel
private theorem small017_cell_16 : PeriodAffine.check ⟨qfrac 27 34, qfrac 74 93, 16369807⟩=true := by decide +kernel
private theorem small017_cell_17 : PeriodAffine.check ⟨qfrac 74 93, qfrac 47 59, 11394733⟩=true := by decide +kernel
private theorem small017_cell_18 : PeriodAffine.check ⟨qfrac 47 59, qfrac 67 84, 15010618⟩=true := by decide +kernel
private theorem small017_cell_19 : PeriodAffine.check ⟨qfrac 67 84, qfrac 4 5, 42396076⟩=true := by decide +kernel
private theorem small017_cell_20 : PeriodAffine.check ⟨qfrac 4 5, qfrac 61 76, 144157416⟩=true := by decide +kernel
private theorem small017_cell_21 : PeriodAffine.check ⟨qfrac 61 76, qfrac 41 51, 76074239⟩=true := by decide +kernel
private theorem small017_cell_22 : PeriodAffine.check ⟨qfrac 41 51, qfrac 33 41, 58690819⟩=true := by decide +kernel
private theorem small017_cell_23 : PeriodAffine.check ⟨qfrac 33 41, qfrac 95 118, 12938846⟩=true := by decide +kernel
private theorem small017_cell_24 : PeriodAffine.check ⟨qfrac 95 118, qfrac 25 31, 87928333⟩=true := by decide +kernel
private theorem small017_cell_25 : PeriodAffine.check ⟨qfrac 25 31, qfrac 55 68, 162146572⟩=true := by decide +kernel
private theorem small017_cell_26 : PeriodAffine.check ⟨qfrac 55 68, qfrac 17 21, 50148132⟩=true := by decide +kernel
private theorem small017_cell_27 : PeriodAffine.check ⟨qfrac 17 21, qfrac 13 16, 224894722⟩=true := by decide +kernel
private theorem small017_cell_28 : PeriodAffine.check ⟨qfrac 13 16, qfrac 61 75, 51881926⟩=true := by decide +kernel
private theorem small017_cell_29 : PeriodAffine.check ⟨qfrac 61 75, qfrac 48 59, 14321833⟩=true := by decide +kernel
private theorem small017_cell_30 : PeriodAffine.check ⟨qfrac 48 59, qfrac 35 43, 25243986⟩=true := by decide +kernel
private theorem small017_cell_31 : PeriodAffine.check ⟨qfrac 35 43, qfrac 31 38, 122095669⟩=true := by decide +kernel

theorem small017_affine_check : small017.all PeriodAffine.check=true := by
  simp only [small017, List.all_cons, List.all_nil, Bool.and_self,
    small017_cell_0,
    small017_cell_1,
    small017_cell_2,
    small017_cell_3,
    small017_cell_4,
    small017_cell_5,
    small017_cell_6,
    small017_cell_7,
    small017_cell_8,
    small017_cell_9,
    small017_cell_10,
    small017_cell_11,
    small017_cell_12,
    small017_cell_13,
    small017_cell_14,
    small017_cell_15,
    small017_cell_16,
    small017_cell_17,
    small017_cell_18,
    small017_cell_19,
    small017_cell_20,
    small017_cell_21,
    small017_cell_22,
    small017_cell_23,
    small017_cell_24,
    small017_cell_25,
    small017_cell_26,
    small017_cell_27,
    small017_cell_28,
    small017_cell_29,
    small017_cell_30,
    small017_cell_31]

end OddZetaSix.B40a.Cert
