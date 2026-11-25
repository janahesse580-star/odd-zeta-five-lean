import OddZetaSix.B40a.Analysis.WitnessBudget
noncomputable section
namespace OddZetaSix.B40a.Witness
open Cert Finset ComplexConjugate

private def ctr (c : Cert.Circle) : ℂ := ((c.re:ℝ)/(coord:ℝ):ℝ)+((c.im:ℝ)/(coord:ℝ):ℝ)*Complex.I
private def rad (c : Cert.Circle) : ℝ := (c.radius:ℝ)/coord
private def wei (c : Cert.Circle) : ℝ := (c.mass:ℝ)/(2*massTotal)
private def atom (z : ℂ) (c : Cert.Circle) := wei c*circlePotential (ctr c) (rad c) z

private theorem ref_ctr (c : Cert.Circle) : ctr (reflectCircle c)=conj (ctr c) := by
  apply Complex.ext <;> simp [ctr,reflectCircle,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,neg_div]
private theorem atom_conj (z : ℂ) (c : Cert.Circle) : atom (conj z) c=atom z (reflectCircle c) := by
  unfold atom circlePotential
  rw [ref_ctr,show ‖conj z-ctr c‖=‖z-conj (ctr c)‖ by
    rw [←Complex.norm_conj (conj z-ctr c),map_sub]; simp]
  rfl

theorem potential_conj (z : ℂ) : potential (conj z)=potential z := by
  have eqn (v : ℂ) : potential v=(entries.map (atom v)).sum := sum_entries (atom v)
  rw [eqn,eqn]
  have pairs (cs : List Cert.Circle) :
      ((allCircles cs).map (atom (conj z))).sum=((allCircles cs).map (atom z)).sum := by
    induction cs with
    | nil => rfl
    | cons a cs ih =>
      change atom (conj z) (scaleCircle a)+(atom (conj z) (reflectCircle (scaleCircle a))+((allCircles cs).map (atom (conj z))).sum) =
        atom z (scaleCircle a)+(atom z (reflectCircle (scaleCircle a))+((allCircles cs).map (atom z)).sum)
      rw [ih,atom_conj,atom_conj]
      have h (c : Cert.Circle) : reflectCircle (reflectCircle c)=c := by cases c; simp [reflectCircle]
      rw [h]; ring
  exact pairs circles

theorem potential_square_shift (z v : ℂ) :
    potential ((z+v)^2)≤potential (z^2)+errorSlope*‖v‖*(2*‖z‖+‖v‖) := by
  have ds : ‖(z+v)^2-z^2‖≤‖v‖*(2*‖z‖+‖v‖) := by
    rw [show (z+v)^2-z^2=v*((z+z)+v) by ring,norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg v)
    exact (norm_add_le _ _).trans (by linarith only [norm_add_le z z])
  let d := ‖v‖*(2*‖z‖+‖v‖)
  have W (i : Index) : b i*circlePotential (u i) (r i) ((z+v)^2)≤
      b i*circlePotential (u i) (r i) (z^2)+(b i/r i)*d := by
    have H := (circlePotential_le_add_dist (u i) (z^2) ((z+v)^2) (r i) (valid i).1).trans
      (add_le_add (le_refl _) (div_le_div_of_nonneg_right ds (valid i).1.le))
    apply (mul_le_mul_of_nonneg_left H (valid i).2).trans_eq; ring
  have T := sum_le_sum (s:=univ) (fun i _=>W i)
  simp only [sum_add_distrib,←sum_mul] at T
  apply T.trans_eq
  change _+errorSlope*d=_
  unfold d potential; ring

def anchorDrift (n : ℕ) : ℝ := ((17:ℝ)*n/20-anchor n+1/2)/(50*n)

theorem anchorDrift_bounds (n : ℕ) (hn : 0<n) :
    0≤anchorDrift n ∧ anchorDrift n≤3/(100*(n:ℝ)) := by
  have L : 20*anchor n≤17*n := by unfold anchor; omega
  have H : 17*n<20*(anchor n+1) := by unfold anchor; omega
  have L' : (20:ℝ)*(anchor n:ℝ)≤17*n := by exact_mod_cast L
  have H' : (17:ℝ)*n<20*((anchor n:ℝ)+1) := by exact_mod_cast H
  have N : (0:ℝ)<n := by exact_mod_cast hn
  unfold anchorDrift
  constructor
  · exact div_nonneg (by linarith) (by positivity)
  · apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_lt_mul_of_pos_right H' N]

theorem scaled_node_real (n : ℕ) (hn : 0<n) (j : Fin 8) :
    (bendNodeX n j+(OddZetaSix.B40a.center n:ℝ))/(50*(n:ℝ))=118/100-bendC j+anchorDrift n := by
  have N : (0:ℝ)<n := by exact_mod_cast hn
  unfold bendNodeX contourAbscissa OddZetaSix.B40a.center anchorDrift
  push_cast
  field_simp [N.ne']; ring
end OddZetaSix.B40a.Witness
