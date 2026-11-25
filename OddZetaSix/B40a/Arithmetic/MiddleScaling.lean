import OddZetaSix.B40a.Arithmetic.MiddleRanked

namespace OddZetaSix.B40a

/-- Homogeneity of all floors, strict cutoffs, and Taylor penalties in
the original integer checker. The scale need not be prime. -/
theorem middleSite_scale (p d t k : ℤ) (hk : 0<k) :
    Cert.middleSite (k*p) (k*d) (k*t)=Cert.middleSite p d t := by
  have hsub (a : ℤ) : (a*(k*d)-k*t)/(k*p)=(a*d-t)/p := by
    rw [show a*(k*d)-k*t=k*(a*d-t) by ring,Int.mul_ediv_mul_of_pos _ _ hk]
  have hadd (a : ℤ) : (a*(k*d)+k*t)/(k*p)=(a*d+t)/p := by
    rw [show a*(k*d)+k*t=k*(a*d+t) by ring,Int.mul_ediv_mul_of_pos _ _ hk]
  have hmul (a : ℤ) : (a*(k*d))/(k*p)=(a*d)/p := by
    rw [show a*(k*d)=k*(a*d) by ring,Int.mul_ediv_mul_of_pos _ _ hk]
  have hcut (a : ℤ) : k*t<a*(k*d) ↔ t<a*d := by
    rw [show a*(k*d)=k*(a*d) by ring,mul_lt_mul_iff_right₀ hk]
  unfold Cert.middleSite
  simp only [hsub,hadd,hmul,hcut]

theorem middle_progression_scale (a b p k : ℤ) (hp : 0<p) (hk : 0<k) :
    Cert.iRange (k*a) (k*b) (k*p)=(Cert.iRange a b p).map (k*·) := by
  have hkp := mul_pos hk hp
  have HL : ((k*b-k*a+k*p-1)/(k*p)).toNat=((b-a+p-1)/p).toNat := by
    have H (i : ℕ) : i<((k*b-k*a+k*p-1)/(k*p)).toNat ↔ i<((b-a+p-1)/p).toNat := by
      rw [middle_range_index _ _ _ _ hkp,middle_range_index _ _ _ _ hp,
        show k*a+(i:ℤ)*(k*p)=k*(a+i*p) by ring,mul_lt_mul_iff_right₀ hk]
    have h₁ := H (((k*b-k*a+k*p-1)/(k*p)).toNat)
    have h₂ := H (((b-a+p-1)/p).toNat)
    omega
  unfold Cert.iRange
  simp only [ite_eq_right hp.not_ge,ite_eq_right hkp.not_ge,HL,List.map_map]
  apply List.map_congr_left
  intro x _
  dsimp; ring

theorem middleRawBag_scale (p d t k : ℤ) (hp : 0<p) (hk : 0<k) :
    (middleClassSites (k*p) (k*d) (k*t)).flatMap (Cert.middleSite (k*p) (k*d)) =
      (middleClassSites p d t).flatMap (Cert.middleSite p d) := by
  unfold middleClassSites
  rw [show 25*(k*d)=k*(25*d) by ring,←mul_sub,
    middle_progression_scale _ _ _ _ hp hk,middle_progression_scale _ _ _ _ hp hk,←List.map_append]
  simp only [List.flatMap_map,middleSite_scale _ _ _ _ hk]

end OddZetaSix.B40a
