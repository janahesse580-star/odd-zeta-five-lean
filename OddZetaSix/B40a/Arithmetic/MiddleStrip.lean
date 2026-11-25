import OddZetaSix.B40a.Arithmetic.MiddleSiteBridge

namespace OddZetaSix.B40a

/-- Both endpoints and all intervening points avoid the indicated translates. -/
def middleWallFree (p d x y : ℤ) : Prop :=
  ∀ e ∈ ([-59,-34,-25,-17,-16,16,17,25,34,59] : List ℤ),
    ∀ j : ℤ, ¬ (x ≤ e*d+j*p ∧ e*d+j*p ≤ y)

private theorem sub_floor_constant (p u x y : ℤ) (hp : 0<p) (hxy : x≤y)
    (h : ∀ j : ℤ, ¬(x≤u+j*p ∧ u+j*p≤y)) :
    (u-x)/p=(u-y)/p := by
  have hle : (u-y)/p ≤ (u-x)/p := Int.ediv_le_ediv hp (by omega)
  by_contra hne
  have hlt : (u-y)/p < (u-x)/p := by omega
  have hu := (Int.ediv_lt_iff_lt_mul hp).mp hlt
  have hl := (Int.le_ediv_iff_mul_le hp).mp (le_refl ((u-x)/p))
  specialize h (-((u-x)/p))
  rw [neg_mul] at h
  omega

private theorem add_floor_constant (p u x y : ℤ) (hp : 0<p) (hxy : x≤y)
    (h : ∀ j : ℤ, ¬(x≤ -u+j*p ∧ -u+j*p≤y)) :
    (u+x)/p=(u+y)/p := by
  have hle : (u+x)/p ≤ (u+y)/p := Int.ediv_le_ediv hp (by omega)
  by_contra hne
  have hlt : (u+x)/p < (u+y)/p := by omega
  have hu := (Int.ediv_lt_iff_lt_mul hp).mp hlt
  have hl := (Int.le_ediv_iff_mul_le hp).mp (le_refl ((u+y)/p))
  specialize h ((u+y)/p)
  omega

/-- The same certificate bag, including multiplicities, at all points of a
single open strip. This works with integer scales and both harmonic cutoffs. -/
theorem middleSite_constant_on_strip (p d x y : ℤ) (hp : 0<p) (hxy : x≤y)
    (hw : middleWallFree p d x y) : Cert.middleSite p d x=Cert.middleSite p d y := by
  have f (e : ℤ) (he : e ∈ ([-59,-34,-25,-17,-16,16,17,25,34,59]:List ℤ)) :
      (e*d-x)/p=(e*d-y)/p := sub_floor_constant _ _ _ _ hp hxy (hw _ he)
  have cutoff (e : ℤ) (he : e ∈ ([-59,-34,-25,-17,-16,16,17,25,34,59]:List ℤ)) :
      (x<e*d) ↔ (y<e*d) := by
    have h := hw e he 0
    simp only [zero_mul,add_zero] at h
    omega
  have ha : (34*d+x)/p = (34*d+y)/p := by
    apply add_floor_constant _ _ _ _ hp hxy
    simpa only [neg_mul] using (hw (-34) (by decide))
  have h16 := cutoff 16 (by decide)
  have h17 := cutoff 17 (by decide)
  rw [middleSite_eq_suffix, middleSite_eq_suffix]
  simp only [h16,h17]
  have hφ : certificateAtom p d x=certificateAtom p d y := by
    funext a e
    unfold certificateAtom
    dsimp only
    simp only [h16,h17,ha,f 25 (by decide),f (-25) (by decide),f 17 (by decide),f (-17) (by decide),
      f 16 (by decide),f (-16) (by decide),f (-34) (by decide),f (-59) (by decide),
      f 59 (by decide),f 34 (by decide)]
  rw [hφ]

/-- Test a whole class interval by checking each folded-wall residue only
once. This condition is invariant under translating the strip by periods. -/
theorem middleWallFree_translate (p d x y j : ℤ) (h : middleWallFree p d x y) :
    middleWallFree p d (x+j*p) (y+j*p) := by
  intro e he k hxy
  apply h e he (k-j)
  rw [sub_mul]
  omega

theorem middleWallFree_reflect (p d x y : ℤ) (h : middleWallFree p d x y) :
    middleWallFree p d (-y) (-x) := by
  intro e he j hxy
  have he' : -e ∈ ([-59,-34,-25,-17,-16,16,17,25,34,59]:List ℤ) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he ⊢
    omega
  apply h (-e) he' (-j)
  simp only [neg_mul]
  omega

end OddZetaSix.B40a
