import OddZetaSix.B40a.Arithmetic.MiddleScaling
import OddZetaSix.B40a.Arithmetic.MiddleCapMean

namespace OddZetaSix.B40a
open Finset

private def capStep (R : ℤ) (w : ℕ→ℤ) (s : ℤ×ℤ) (i : ℕ) :=
  (s.1+w i,s.2+min R (s.1+w i))

private theorem capStep_fold (R : ℤ) (w : ℕ→ℤ) (a len top : ℕ) (hab : a+len=top) :
    (List.range' a len).reverse.foldl (capStep R w) (0,0) =
      (∑ i ∈ Ico a top,w i, ∑ j ∈ Ico a top,min R (∑ i ∈ Ico j top,w i)) := by
  induction len generalizing a with
  | zero =>
    have : a=top := by omega
    subst a; simp
  | succ len ih =>
    have hlt : a<top := by omega
    rw [List.range'_succ,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [show a+1*1=a+1 by omega]
    rw [ih (a+1) (by omega)]
    unfold capStep
    have h1 := Finset.sum_eq_sum_Ico_succ_bot hlt w
    have h2 := Finset.sum_eq_sum_Ico_succ_bot hlt (fun j => min R (∑ i ∈ Ico j top,w i))
    apply Prod.ext
    · dsimp; omega
    · dsimp; rw [show (∑ i ∈ Ico (a+1) top,w i)+w a = ∑ i ∈ Ico a top,w i by omega]
      omega

/-- Meaning of cappedLayers for the actual 17-bin array. -/
theorem cappedLayers_eq_levels (d : ℤ) (H : Array ℤ) :
    Cert.cappedLayers d H=∑ j ∈ Ico 1 17,min (40*d) (∑ i ∈ Ico j 17,H[i]!) := by
  unfold Cert.cappedLayers
  rw [show Cert.nrange 1 17=List.range' 1 16 by decide]
  exact congrArg Prod.snd (capStep_fold (40*d) (fun i=>H[i]!) 1 16 17 rfl)

/-- The certificate stops at j=q+7. For every omitted index, reaching
any positive layer after the row correction is arithmetically impossible. -/
theorem middle_trim_folded_rank {w : ℤ} (h : w≤16) {q j : ℕ} (hj : q+8≤j) :
    w-2*((j-q:ℕ):ℤ)≤0 := by omega

/-- The exact sorted arrays used by the original middleClasses. -/
theorem middleClasses_eq_sorted (p d : ℤ) :
    Cert.middleClasses p d = (Cert.adjacent (Cert.increasingZ
      (0::(p/2)::([16,17,25,34,59]:List ℤ).map (fun e => middleFoldWall p (e*d))))).map
        (fun (a,b) => (b-a,(middleSortedSlots
          ((middleClassSites p d ((a+b)/2)).flatMap (Cert.middleSite p d))).toArray)) := rfl

end OddZetaSix.B40a
