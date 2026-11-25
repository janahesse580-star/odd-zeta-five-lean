import OddZetaSix.B40a.Certificate.FastMiddle
import OddZetaSix.B40a.Certificate.Generated.Middle000

namespace OddZetaSix.B40a.Cert
set_option maxHeartbeats 0
set_option maxRecDepth 16384

def pilotCuts : List (Option ℕ) :=
  [141,141,141,141,141,141,140,140,140,140,140,140,140,140,142,142,142,142,141,141,141,141,
    141,141,141,141,141,141,140,140,138,137].map fun q : ℕ => some q

-- The first list uses the previously generated optimal cut for each row.
#eval (do
  let t ← IO.monoNanosNow
  unless checkFastMiddle middle000 pilotCuts do
    throw (IO.userError "fast check returned false")
  let elapsed := (← IO.monoNanosNow) - t
  IO.println s!"#eval passed; elapsed_ns={elapsed}" : IO Unit)

set_option profiler.threshold 1 in
set_option profiler true in
theorem fastFirstShard : checkFastMiddle middle000 pilotCuts = true := by
  decide +kernel

#print axioms fastFirstShard
end OddZetaSix.B40a.Cert
