import OddZetaSix.B40a.Analysis.PotentialEndpoints
import OddZetaSix.B40a.Analysis.EndpointChecks

noncomputable section
namespace OddZetaSix.B40a.Witness
open Cert

def nodeField (t : ℤ) :=
  phaseReal (contourZ t).1 (contourZ t).2 + (8/5)*potential (squarePoint (contourZ t).1 (contourZ t).2)

theorem checked_node {t : ℤ} (h : nodeOK t=true) : nodeField t≤(peak:ℝ)/fix := by
  have H := of_decide_eq_true h
  have hf : (0:ℝ)<fix := by norm_num [fix]
  apply (le_div_iff₀ hf).mpr
  rw [mul_comm]
  exact (endpoint_sound t H.1).trans (by exact_mod_cast H.2)

theorem endpoints_real_bound {p : Panel} (hp : p∈panelsRows) :
    nodeField p.a≤(peak:ℝ)/fix ∧ nodeField p.b≤(peak:ℝ)/fix := by
  have hh := List.all_eq_true.mp endpoints_checked p hp
  simp only [Bool.and_eq_true] at hh
  exact ⟨checked_node hh.1,checked_node hh.2⟩
end OddZetaSix.B40a.Witness
