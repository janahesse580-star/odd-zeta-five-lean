import OddZetaSix.B40a.Arithmetic.MiddleRowWalls

namespace OddZetaSix.B40a.Cert
set_option maxHeartbeats 0
set_option maxRecDepth 32768

private theorem middle000_freq : middle000.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle001_freq : middle001.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle002_freq : middle002.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle003_freq : middle003.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle004_freq : middle004.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle005_freq : middle005.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle006_freq : middle006.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle007_freq : middle007.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle008_freq : middle008.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle009_freq : middle009.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle010_freq : middle010.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle011_freq : middle011.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle012_freq : middle012.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle013_freq : middle013.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle014_freq : middle014.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle015_freq : middle015.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle016_freq : middle016.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle017_freq : middle017.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle018_freq : middle018.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle019_freq : middle019.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle020_freq : middle020.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle021_freq : middle021.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle022_freq : middle022.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle023_freq : middle023.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle024_freq : middle024.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle025_freq : middle025.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle026_freq : middle026.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle027_freq : middle027.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle028_freq : middle028.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle029_freq : middle029.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle030_freq : middle030.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle031_freq : middle031.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle032_freq : middle032.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle033_freq : middle033.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle034_freq : middle034.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle035_freq : middle035.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle036_freq : middle036.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle037_freq : middle037.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle038_freq : middle038.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle039_freq : middle039.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle040_freq : middle040.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle041_freq : middle041.all checkMiddleFrequencies = true := by decide +kernel
private theorem middle042_freq : middle042.all checkMiddleFrequencies = true := by decide +kernel

theorem middleRows_freq : middleRows.all checkMiddleFrequencies = true := by
  simp only [middleRows,List.all_append,Bool.true_and,middle000_freq,
    middle001_freq,
    middle002_freq,
    middle003_freq,
    middle004_freq,
    middle005_freq,
    middle006_freq,
    middle007_freq,
    middle008_freq,
    middle009_freq,
    middle010_freq,
    middle011_freq,
    middle012_freq,
    middle013_freq,
    middle014_freq,
    middle015_freq,
    middle016_freq,
    middle017_freq,
    middle018_freq,
    middle019_freq,
    middle020_freq,
    middle021_freq,
    middle022_freq,
    middle023_freq,
    middle024_freq,
    middle025_freq,
    middle026_freq,
    middle027_freq,
    middle028_freq,
    middle029_freq,
    middle030_freq,
    middle031_freq,
    middle032_freq,
    middle033_freq,
    middle034_freq,
    middle035_freq,
    middle036_freq,
    middle037_freq,
    middle038_freq,
    middle039_freq,
    middle040_freq,
    middle041_freq,
    middle042_freq]

/-- Every listed crossing frequency has a single floor on the interior of every actual certificate row. -/
theorem middleRows_floor {r : ArithRow} (hr : r∈middleRows) {P : ℝ} (hP : P ∈ Set.Ioo (r.left:ℝ) r.right) {k : ℕ} (hk : k∈middleFrequencies) :
    ⌊(k:ℝ)/P⌋ = middleFloor r k := middle_floor_of_row_check (List.all_eq_true.mp middleRows_freq _ hr) hP hk

theorem middleRows_exact_budget : arithTotal middleRows = 5244756877432 := by decide +kernel

end OddZetaSix.B40a.Cert
