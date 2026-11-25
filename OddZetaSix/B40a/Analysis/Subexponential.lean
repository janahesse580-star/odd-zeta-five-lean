import OddZetaSix.B40a.Analysis.Coordinates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
noncomputable section
namespace OddZetaSix.B40a.Cert
open Filter Real
open scoped Topology
theorem scale_tendsto : Tendsto scaleN atTop atTop :=
  Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ)<50) tendsto_natCast_atTop_atTop

/-- Fixed constants and any fixed power of the physical scale are negligible
in the exponent, with the height cutoff kept independent. -/
theorem const_log_over_scale (A B : ℝ) :
    Tendsto (fun n=> (A+B*Real.log (scaleN n))/(scaleN n)) atTop (𝓝 0) := by
  have h1 := (tendsto_const_nhds (x:=A)).div_atTop scale_tendsto
  have h2 := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp scale_tendsto
  convert h1.add (h2.const_mul B) using 1
  · funext n; simp only [Function.comp_apply,id_eq]; ring
  · simp
end OddZetaSix.B40a.Cert
