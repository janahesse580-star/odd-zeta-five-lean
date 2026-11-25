import OddZetaSix.B40a.Certificate.Generated.All

namespace OddZetaSix.B40a.Cert
set_option maxRecDepth 32768
set_option maxHeartbeats 0
def nodeOK (t : ℤ) : Bool :=
  let z := contourZ t
  let b := squareBox z.1 z.2
  decide ((-50000000≤b.xlo ∧ b.xlo≤50000000 ∧ -50000000≤b.xhi ∧ b.xhi≤50000000 ∧
    -50000000≤b.ylo ∧ b.ylo≤50000000 ∧ -50000000≤b.yhi ∧ b.yhi≤50000000) ∧
    endpoint lookup circles t ≤ peak)
private theorem node0 : nodeOK 0=true := by decide +kernel
private theorem node1250 : nodeOK 1250=true := by decide +kernel
private theorem node1875 : nodeOK 1875=true := by decide +kernel
private theorem node2500 : nodeOK 2500=true := by decide +kernel
private theorem node3125 : nodeOK 3125=true := by decide +kernel
private theorem node3750 : nodeOK 3750=true := by decide +kernel
private theorem node4062 : nodeOK 4062=true := by decide +kernel
private theorem node4375 : nodeOK 4375=true := by decide +kernel
private theorem node4687 : nodeOK 4687=true := by decide +kernel
private theorem node5000 : nodeOK 5000=true := by decide +kernel
private theorem node5312 : nodeOK 5312=true := by decide +kernel
private theorem node5625 : nodeOK 5625=true := by decide +kernel
private theorem node5937 : nodeOK 5937=true := by decide +kernel
private theorem node6250 : nodeOK 6250=true := by decide +kernel
private theorem node6562 : nodeOK 6562=true := by decide +kernel
private theorem node6875 : nodeOK 6875=true := by decide +kernel
private theorem node7187 : nodeOK 7187=true := by decide +kernel
private theorem node7500 : nodeOK 7500=true := by decide +kernel
private theorem node7812 : nodeOK 7812=true := by decide +kernel
private theorem node8125 : nodeOK 8125=true := by decide +kernel
private theorem node8437 : nodeOK 8437=true := by decide +kernel
private theorem node8750 : nodeOK 8750=true := by decide +kernel
private theorem node9062 : nodeOK 9062=true := by decide +kernel
private theorem node9375 : nodeOK 9375=true := by decide +kernel
private theorem node9687 : nodeOK 9687=true := by decide +kernel
private theorem node10000 : nodeOK 10000=true := by decide +kernel
private theorem node10312 : nodeOK 10312=true := by decide +kernel
private theorem node10625 : nodeOK 10625=true := by decide +kernel
private theorem node10937 : nodeOK 10937=true := by decide +kernel
private theorem node11250 : nodeOK 11250=true := by decide +kernel
private theorem node11562 : nodeOK 11562=true := by decide +kernel
private theorem node11875 : nodeOK 11875=true := by decide +kernel
private theorem node12187 : nodeOK 12187=true := by decide +kernel
private theorem node12500 : nodeOK 12500=true := by decide +kernel
private theorem node12812 : nodeOK 12812=true := by decide +kernel
private theorem node13125 : nodeOK 13125=true := by decide +kernel
private theorem node13437 : nodeOK 13437=true := by decide +kernel
private theorem node13750 : nodeOK 13750=true := by decide +kernel
private theorem node14062 : nodeOK 14062=true := by decide +kernel
private theorem node14375 : nodeOK 14375=true := by decide +kernel
private theorem node14687 : nodeOK 14687=true := by decide +kernel
private theorem node15000 : nodeOK 15000=true := by decide +kernel
private theorem node15312 : nodeOK 15312=true := by decide +kernel
private theorem node15625 : nodeOK 15625=true := by decide +kernel
private theorem node15937 : nodeOK 15937=true := by decide +kernel
private theorem node16250 : nodeOK 16250=true := by decide +kernel
private theorem node16562 : nodeOK 16562=true := by decide +kernel
private theorem node16875 : nodeOK 16875=true := by decide +kernel
private theorem node17187 : nodeOK 17187=true := by decide +kernel
private theorem node17343 : nodeOK 17343=true := by decide +kernel
private theorem node17656 : nodeOK 17656=true := by decide +kernel
private theorem node17812 : nodeOK 17812=true := by decide +kernel
private theorem node18125 : nodeOK 18125=true := by decide +kernel
private theorem node18437 : nodeOK 18437=true := by decide +kernel
private theorem node18750 : nodeOK 18750=true := by decide +kernel
private theorem node19062 : nodeOK 19062=true := by decide +kernel
private theorem node19375 : nodeOK 19375=true := by decide +kernel
private theorem node19687 : nodeOK 19687=true := by decide +kernel
private theorem node20000 : nodeOK 20000=true := by decide +kernel
private theorem node20234 : nodeOK 20234=true := by decide +kernel
private theorem node20468 : nodeOK 20468=true := by decide +kernel
private theorem node20702 : nodeOK 20702=true := by decide +kernel
private theorem node20937 : nodeOK 20937=true := by decide +kernel
private theorem node21406 : nodeOK 21406=true := by decide +kernel
private theorem node21875 : nodeOK 21875=true := by decide +kernel
private theorem node22343 : nodeOK 22343=true := by decide +kernel
private theorem node22577 : nodeOK 22577=true := by decide +kernel
private theorem node23046 : nodeOK 23046=true := by decide +kernel
private theorem node23281 : nodeOK 23281=true := by decide +kernel
private theorem node23750 : nodeOK 23750=true := by decide +kernel
private theorem node24218 : nodeOK 24218=true := by decide +kernel
private theorem node24687 : nodeOK 24687=true := by decide +kernel
private theorem node24921 : nodeOK 24921=true := by decide +kernel
private theorem node25156 : nodeOK 25156=true := by decide +kernel
private theorem node25625 : nodeOK 25625=true := by decide +kernel
private theorem node26093 : nodeOK 26093=true := by decide +kernel
private theorem node26562 : nodeOK 26562=true := by decide +kernel
private theorem node27031 : nodeOK 27031=true := by decide +kernel
private theorem node27500 : nodeOK 27500=true := by decide +kernel
private theorem node27968 : nodeOK 27968=true := by decide +kernel
private theorem node28437 : nodeOK 28437=true := by decide +kernel
private theorem node28906 : nodeOK 28906=true := by decide +kernel
private theorem node29375 : nodeOK 29375=true := by decide +kernel
private theorem node29843 : nodeOK 29843=true := by decide +kernel
private theorem node30312 : nodeOK 30312=true := by decide +kernel
private theorem node30781 : nodeOK 30781=true := by decide +kernel
private theorem node31250 : nodeOK 31250=true := by decide +kernel
private theorem node31718 : nodeOK 31718=true := by decide +kernel
private theorem node32187 : nodeOK 32187=true := by decide +kernel
private theorem node32656 : nodeOK 32656=true := by decide +kernel
private theorem node33125 : nodeOK 33125=true := by decide +kernel
private theorem node33593 : nodeOK 33593=true := by decide +kernel
private theorem node34062 : nodeOK 34062=true := by decide +kernel
private theorem node34531 : nodeOK 34531=true := by decide +kernel
private theorem node35000 : nodeOK 35000=true := by decide +kernel
private theorem node35312 : nodeOK 35312=true := by decide +kernel
private theorem node35625 : nodeOK 35625=true := by decide +kernel
private theorem node36250 : nodeOK 36250=true := by decide +kernel
private theorem node36875 : nodeOK 36875=true := by decide +kernel
private theorem node37500 : nodeOK 37500=true := by decide +kernel
private theorem node38125 : nodeOK 38125=true := by decide +kernel
private theorem node38750 : nodeOK 38750=true := by decide +kernel
private theorem node39375 : nodeOK 39375=true := by decide +kernel
private theorem node40000 : nodeOK 40000=true := by decide +kernel
private theorem node40625 : nodeOK 40625=true := by decide +kernel
private theorem node41250 : nodeOK 41250=true := by decide +kernel
private theorem node41875 : nodeOK 41875=true := by decide +kernel
private theorem node42500 : nodeOK 42500=true := by decide +kernel
private theorem node43125 : nodeOK 43125=true := by decide +kernel
private theorem node43750 : nodeOK 43750=true := by decide +kernel
private theorem node45000 : nodeOK 45000=true := by decide +kernel
private theorem node47500 : nodeOK 47500=true := by decide +kernel
private theorem node50000 : nodeOK 50000=true := by decide +kernel
private theorem node55000 : nodeOK 55000=true := by decide +kernel
private theorem node70000 : nodeOK 70000=true := by decide +kernel
private theorem node85000 : nodeOK 85000=true := by decide +kernel
private theorem node124375 : nodeOK 124375=true := by decide +kernel
private theorem node163750 : nodeOK 163750=true := by decide +kernel
private theorem node242500 : nodeOK 242500=true := by decide +kernel
private theorem node400000 : nodeOK 400000=true := by decide +kernel
theorem endpoints_checked : panelsRows.all (fun p=>nodeOK p.a && nodeOK p.b)=true := by
  simp only [panelsRows,panels000,panels001,panels002,panels003,List.all_append,List.all_cons,List.all_nil,Bool.true_and,node0,node1250,node1875,node2500,node3125,node3750,node4062,node4375,node4687,node5000,node5312,node5625,node5937,node6250,node6562,node6875,node7187,node7500,node7812,node8125,node8437,node8750,node9062,node9375,node9687,node10000,node10312,node10625,node10937,node11250,node11562,node11875,node12187,node12500,node12812,node13125,node13437,node13750,node14062,node14375,node14687,node15000,node15312,node15625,node15937,node16250,node16562,node16875,node17187,node17343,node17656,node17812,node18125,node18437,node18750,node19062,node19375,node19687,node20000,node20234,node20468,node20702,node20937,node21406,node21875,node22343,node22577,node23046,node23281,node23750,node24218,node24687,node24921,node25156,node25625,node26093,node26562,node27031,node27500,node27968,node28437,node28906,node29375,node29843,node30312,node30781,node31250,node31718,node32187,node32656,node33125,node33593,node34062,node34531,node35000,node35312,node35625,node36250,node36875,node37500,node38125,node38750,node39375,node40000,node40625,node41250,node41875,node42500,node43125,node43750,node45000,node47500,node50000,node55000,node70000,node85000,node124375,node163750,node242500,node400000]

end OddZetaSix.B40a.Cert
