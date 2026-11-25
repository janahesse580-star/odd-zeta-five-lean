import OddZetaSix.B40a.Arithmetic.MiddleStrip

namespace OddZetaSix.B40a

def middleFoldWall (p u : ℤ) := min (u%p) (p-u%p)

theorem middleFoldWall_neg (p u : ℤ) (hp : 0<p) :
    middleFoldWall p (-u)=middleFoldWall p u := by
  unfold middleFoldWall
  rw [Int.neg_emod]
  have hpa : (p.natAbs : ℤ) = p := Int.natAbs_of_nonneg hp.le
  split_ifs with h
  · rw [Int.emod_eq_zero_of_dvd h]
  · rw [hpa]; omega

/-- Only the five residues used in the original certificate need to be
excluded, independently of how many signed translates occur at this prime. -/
theorem middleWallFree_of_folded (p d x y : ℤ) (hp : 0<p)
    (hx : 0≤x) (hy : 2*y≤p) (hwall : ∀ e ∈ ([16,17,25,34,59]:List ℤ),
      ¬(x≤middleFoldWall p (e*d) ∧ middleFoldWall p (e*d)≤y)) :
    middleWallFree p d x y := by
  intro e he j h
  let v := e*d+j*p
  have hv0 : 0≤v := hx.trans h.1
  have hvh : 2*v ≤ p := by dsimp [v]; omega
  have hvp : v<p := by omega
  have hf : middleFoldWall p (e*d)=v := by
    have hh : v%p = (e*d)%p := Int.add_mul_emod_self_right _ _ _
    rw [Int.emod_eq_of_lt hv0 hvp] at hh
    unfold middleFoldWall
    rw [←hh]; omega
  by_cases he0 : 0≤e
  · have hmem : e ∈ ([16,17,25,34,59]:List ℤ) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he ⊢; omega
    exact hwall e hmem (hf.symm ▸ h)
  · have hmem : -e ∈ ([16,17,25,34,59]:List ℤ) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he ⊢; omega
    apply hwall (-e) hmem
    rw [neg_mul,middleFoldWall_neg _ _ hp,hf]
    exact h

/-- Both site families in middleClasses are constant across each open
folded strip, at every period translate. -/
theorem middle_classes_pair_constant (p d x y j : ℤ) (hp : 0<p)
    (hx : 0≤x) (hxy : x≤y) (hy : 2*y≤p)
    (hw : ∀ e ∈ ([16,17,25,34,59]:List ℤ),
      ¬(x≤middleFoldWall p (e*d) ∧ middleFoldWall p (e*d)≤y)) :
    Cert.middleSite p d (x+j*p) = Cert.middleSite p d (y+j*p) ∧
    Cert.middleSite p d (-x+j*p) = Cert.middleSite p d (-y+j*p) := by
  have h := middleWallFree_of_folded p d x y hp hx hy hw
  exact ⟨middleSite_constant_on_strip _ _ _ _ hp (by omega)
      (middleWallFree_translate _ _ _ _ j h),
    (middleSite_constant_on_strip _ _ _ _ hp (by omega)
      (middleWallFree_translate _ _ _ _ j (middleWallFree_reflect _ _ _ _ h))).symm⟩

end OddZetaSix.B40a
