import OddZetaSix.B40a.Analysis.WitnessRowChecks
noncomputable section
namespace OddZetaSix.B40a.Witness
open Finset Cert Orbit

theorem sum_entries {G} [AddCommMonoid G] (f : Cert.Circle→G) :
    (∑ i : Index,f (entry i))=(entries.map f).sum := by
  rw [←List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map entries f)

theorem energy_lower : (energySum:ℝ)/(4*(massTotal:ℝ)^2*fix)≤energy := by
  have total : (∑ i : Index,∑ j : Index,rawPair (entry i) (entry j))=2*energySum := by
    simp_rw [sum_entries]; exact raw_budget
  have totalR : (∑ i : Index,∑ j : Index,(rawPair (entry i) (entry j):ℝ))=2*(energySum:ℝ) := by exact_mod_cast total
  let den : ℝ := 8*(massTotal:ℝ)^2*fix
  have hd : 0<den := by norm_num [den,massTotal,fix]
  have one (i j : Index) : ((rawPair (entry i) (entry j)):ℝ)/den≤
      b i*b j*interaction (u i) (u j) (r i) (r j) := by
    have hh := mul_le_mul_of_nonneg_left (pair_lower i j) (mul_nonneg (valid i).2 (valid j).2)
    apply le_trans _ hh
    apply le_of_eq
    unfold rawPair b den; push_cast; norm_num [fix,massTotal]; ring
  have H := sum_le_sum (s:=univ) (fun i _=>sum_le_sum (s:=univ) (fun j _=>one i j))
  simp_rw [←Finset.sum_div] at H
  rw [totalR] at H
  exact le_trans (by apply le_of_eq; norm_num [den,fix,massTotal]; ring) H

end OddZetaSix.B40a.Witness
