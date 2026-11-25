import OddZetaSix.B40a.Arithmetic.MiddleFoldWalls

namespace OddZetaSix.B40a

private theorem branch_range_eq (p d x y : ℤ) (hp : 0<p) (hxy : x≤y)
    (hwall : middleWallFree p d x y) :
    (Cert.iRange x (25*d) p).flatMap (Cert.middleSite p d) =
      (Cert.iRange y (25*d) p).flatMap (Cert.middleSite p d) := by
  have hfree := hwall 25 (by decide)
  let u := 25*d+p-1
  have sides : (u-x)/p=(u-y)/p := by
    have hle : (u-y)/p ≤ (u-x)/p := Int.ediv_le_ediv hp (by omega)
    by_contra hne
    have hlt : (u-y)/p < (u-x)/p := by omega
    have ha := (Int.ediv_lt_iff_lt_mul hp).mp hlt
    have hb := (Int.le_ediv_iff_mul_le hp).mp (le_refl ((u-x)/p))
    specialize hfree (1-(u-x)/p)
    rw [sub_mul,one_mul] at hfree
    dsimp [u] at ha hb hfree
    omega
  unfold Cert.iRange
  rw [ite_eq_right (by omega : ¬p≤0),ite_eq_right (by omega : ¬p≤0)]
  have hx : 25*d-x+p-1=u-x := by dsimp [u]; ring
  have hy : 25*d-y+p-1=u-y := by dsimp [u]; ring
  rw [hx,hy,sides]
  simp only [List.flatMap_map]
  apply congrArg (fun (f : ℕ → List ℤ) => (List.range ((u-y)/p).toNat).flatMap f)
  funext j
  exact middleSite_constant_on_strip _ _ _ _ hp (by omega)
    (middleWallFree_translate _ _ _ _ (j:ℤ) hwall)

/-- Equality of the complete raw class bags accumulated by middleClasses.
No assumed bijection between the two sets of sites is needed: both finite
progressions keep their actual lengths on this strip. -/
theorem middle_strip_bag_constant (p d x y : ℤ) (hp : 0<p)
    (hx : 0≤x) (hxy : x≤y) (hy : 2*y≤p)
    (hw : ∀ e ∈ ([16,17,25,34,59]:List ℤ),
      ¬(x≤middleFoldWall p (e*d) ∧ middleFoldWall p (e*d)≤y)) :
    ((Cert.iRange x (25*d) p ++ Cert.iRange (p-x) (25*d) p).flatMap (Cert.middleSite p d)) =
    ((Cert.iRange y (25*d) p ++ Cert.iRange (p-y) (25*d) p).flatMap (Cert.middleSite p d)) := by
  have h := middleWallFree_of_folded _ _ _ _ hp hx hy hw
  have hr := middleWallFree_translate _ _ _ _ 1 (middleWallFree_reflect _ _ _ _ h)
  rw [one_mul,show -y+p=p-y by ring,show -x+p=p-x by ring] at hr
  simp only [List.flatMap_append]
  rw [branch_range_eq p d x y hp hxy h,branch_range_eq p d (p-y) (p-x) hp (by omega) hr]

end OddZetaSix.B40a
