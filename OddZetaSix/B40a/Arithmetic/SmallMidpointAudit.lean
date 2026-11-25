import OddZetaSix.B40a.Arithmetic.PeriodicMidpoint
import OddZetaSix.B40a.Certificate.Generated.All

namespace OddZetaSix.B40a.Cert
set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def rowOK (r : ArithRow) := midpointOK ((r.left+r.right)/2)

private theorem small000_strip_check : small000.all rowOK = true := by decide +kernel

private theorem small001_strip_check : small001.all rowOK = true := by decide +kernel

private theorem small002_strip_check : small002.all rowOK = true := by decide +kernel

private theorem small003_strip_check : small003.all rowOK = true := by decide +kernel

private theorem small004_strip_check : small004.all rowOK = true := by decide +kernel

private theorem small005_strip_check : small005.all rowOK = true := by decide +kernel

private theorem small006_strip_check : small006.all rowOK = true := by decide +kernel

private theorem small007_strip_check : small007.all rowOK = true := by decide +kernel

private theorem small008_strip_check : small008.all rowOK = true := by decide +kernel

private theorem small009_strip_check : small009.all rowOK = true := by decide +kernel

private theorem small010_strip_check : small010.all rowOK = true := by decide +kernel

private theorem small011_strip_check : small011.all rowOK = true := by decide +kernel

private theorem small012_strip_check : small012.all rowOK = true := by decide +kernel

private theorem small013_strip_check : small013.all rowOK = true := by decide +kernel

private theorem small014_strip_check : small014.all rowOK = true := by decide +kernel

private theorem small015_strip_check : small015.all rowOK = true := by decide +kernel

private theorem small016_strip_check : small016.all rowOK = true := by decide +kernel

private theorem small017_strip_check : small017.all rowOK = true := by decide +kernel

private theorem small018_strip_check : small018.all rowOK = true := by decide +kernel

private theorem small019_strip_check : small019.all rowOK = true := by decide +kernel

private theorem small020_strip_check : small020.all rowOK = true := by decide +kernel

private theorem small021_strip_check : small021.all rowOK = true := by decide +kernel

private theorem small022_strip_check : small022.all rowOK = true := by decide +kernel

private theorem smallRows_strip_check : smallRows.all rowOK = true := by
  simp only [smallRows,List.all_append,small000_strip_check,
    small001_strip_check,
    small002_strip_check,
    small003_strip_check,
    small004_strip_check,
    small005_strip_check,
    small006_strip_check,
    small007_strip_check,
    small008_strip_check,
    small009_strip_check,
    small010_strip_check,
    small011_strip_check,
    small012_strip_check,
    small013_strip_check,
    small014_strip_check,
    small015_strip_check,
    small016_strip_check,
    small017_strip_check,
    small018_strip_check,
    small019_strip_check,
    small020_strip_check,
    small021_strip_check,
    small022_strip_check,Bool.and_self]

/-- The two real integrals equal the rational moments used in every one of the 706 rows. -/
theorem smallRows_midpoint_integrals (r : ArithRow) (hr : r ∈ smallRows) :
    let t := (r.left+r.right)/2
    ((periodScores t).1 : ℝ) = ∫ u in (0:ℝ)..1,(periodicScore (t:ℝ) u : ℝ) ∧
    ((periodScores t).2 : ℝ) = ∫ u in (0:ℝ)..1,(((periodicScore (t:ℝ) u-1)^2/4 : ℤ):ℝ) :=
  periodScores_integrals_of_check _ ((List.all_eq_true.mp smallRows_strip_check) r hr)

end OddZetaSix.B40a.Cert
