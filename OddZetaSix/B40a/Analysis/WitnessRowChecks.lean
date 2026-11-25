import OddZetaSix.B40a.Analysis.WitnessDistance
import OddZetaSix.B40a.Certificate.Generated.All

namespace OddZetaSix.B40a.Witness
open Cert
set_option maxRecDepth 32768
set_option maxHeartbeats 0
def rawPair (a b : Cert.Circle) := a.mass*b.mass*squaredLog lookup (distCode a b) false
def rawRow (a : Cert.Circle) := (entries.map (rawPair a)).sum
def rawTotal := (entries.map rawRow).sum
private theorem row_0 : rawRow ⟨(1343000),(45000),(12000),(1)⟩ = (-3492826070797) := by decide +kernel
private theorem row_1 : rawRow ⟨(1343000),(-45000),(12000),(1)⟩ = (-3492826070797) := by decide +kernel
private theorem row_2 : rawRow ⟨(1348000),(76000),(12000),(29)⟩ = (-105683122950275) := by decide +kernel
private theorem row_3 : rawRow ⟨(1348000),(-76000),(12000),(29)⟩ = (-105683122950275) := by decide +kernel
private theorem row_4 : rawRow ⟨(1362000),(106000),(13000),(40)⟩ = (-151764662485840) := by decide +kernel
private theorem row_5 : rawRow ⟨(1362000),(-106000),(13000),(40)⟩ = (-151764662485840) := by decide +kernel
private theorem row_6 : rawRow ⟨(1377000),(138000),(13000),(44)⟩ = (-171845744606624) := by decide +kernel
private theorem row_7 : rawRow ⟨(1377000),(-138000),(13000),(44)⟩ = (-171845744606624) := by decide +kernel
private theorem row_8 : rawRow ⟨(1394000),(169000),(14000),(50)⟩ = (-198615620173900) := by decide +kernel
private theorem row_9 : rawRow ⟨(1394000),(-169000),(14000),(50)⟩ = (-198615620173900) := by decide +kernel
private theorem row_10 : rawRow ⟨(1411000),(201000),(14000),(46)⟩ = (-183643040780988) := by decide +kernel
private theorem row_11 : rawRow ⟨(1411000),(-201000),(14000),(46)⟩ = (-183643040780988) := by decide +kernel
private theorem row_12 : rawRow ⟨(1427000),(234000),(14000),(46)⟩ = (-183288278594150) := by decide +kernel
private theorem row_13 : rawRow ⟨(1427000),(-234000),(14000),(46)⟩ = (-183288278594150) := by decide +kernel
private theorem row_14 : rawRow ⟨(1443000),(267000),(14000),(45)⟩ = (-177981720297210) := by decide +kernel
private theorem row_15 : rawRow ⟨(1443000),(-267000),(14000),(45)⟩ = (-177981720297210) := by decide +kernel
private theorem row_16 : rawRow ⟨(1459000),(300000),(14000),(45)⟩ = (-175778785994850) := by decide +kernel
private theorem row_17 : rawRow ⟨(1459000),(-300000),(14000),(45)⟩ = (-175778785994850) := by decide +kernel
private theorem row_18 : rawRow ⟨(1475000),(334000),(14000),(44)⟩ = (-168772624773016) := by decide +kernel
private theorem row_19 : rawRow ⟨(1475000),(-334000),(14000),(44)⟩ = (-168772624773016) := by decide +kernel
private theorem row_20 : rawRow ⟨(1491000),(368000),(14000),(42)⟩ = (-157456660882962) := by decide +kernel
private theorem row_21 : rawRow ⟨(1491000),(-368000),(14000),(42)⟩ = (-157456660882962) := by decide +kernel
private theorem row_22 : rawRow ⟨(1507000),(402000),(14000),(41)⟩ = (-149640327104110) := by decide +kernel
private theorem row_23 : rawRow ⟨(1507000),(-402000),(14000),(41)⟩ = (-149640327104110) := by decide +kernel
private theorem row_24 : rawRow ⟨(1522000),(437000),(15000),(40)⟩ = (-141233556235640) := by decide +kernel
private theorem row_25 : rawRow ⟨(1522000),(-437000),(15000),(40)⟩ = (-141233556235640) := by decide +kernel
private theorem row_26 : rawRow ⟨(1537000),(473000),(15000),(39)⟩ = (-132793854006450) := by decide +kernel
private theorem row_27 : rawRow ⟨(1537000),(-473000),(15000),(39)⟩ = (-132793854006450) := by decide +kernel
private theorem row_28 : rawRow ⟨(1552000),(509000),(15000),(37)⟩ = (-121029630844189) := by decide +kernel
private theorem row_29 : rawRow ⟨(1552000),(-509000),(15000),(37)⟩ = (-121029630844189) := by decide +kernel
private theorem row_30 : rawRow ⟨(1564000),(544000),(14000),(35)⟩ = (-109834283763750) := by decide +kernel
private theorem row_31 : rawRow ⟨(1564000),(-544000),(14000),(35)⟩ = (-109834283763750) := by decide +kernel
private theorem row_32 : rawRow ⟨(1576000),(581000),(15000),(34)⟩ = (-101344772421114) := by decide +kernel
private theorem row_33 : rawRow ⟨(1576000),(-581000),(15000),(34)⟩ = (-101344772421114) := by decide +kernel
private theorem row_34 : rawRow ⟨(1589000),(617000),(15000),(33)⟩ = (-93241593716865) := by decide +kernel
private theorem row_35 : rawRow ⟨(1589000),(-617000),(15000),(33)⟩ = (-93241593716865) := by decide +kernel
private theorem row_36 : rawRow ⟨(1600000),(654000),(15000),(31)⟩ = (-82452464057356) := by decide +kernel
private theorem row_37 : rawRow ⟨(1600000),(-654000),(15000),(31)⟩ = (-82452464057356) := by decide +kernel
private theorem row_38 : rawRow ⟨(1612000),(692000),(15000),(30)⟩ = (-74581921551990) := by decide +kernel
private theorem row_39 : rawRow ⟨(1612000),(-692000),(15000),(30)⟩ = (-74581921551990) := by decide +kernel
private theorem row_40 : rawRow ⟨(1624000),(729000),(15000),(29)⟩ = (-67057429124235) := by decide +kernel
private theorem row_41 : rawRow ⟨(1624000),(-729000),(15000),(29)⟩ = (-67057429124235) := by decide +kernel
private theorem row_42 : rawRow ⟨(1635000),(767000),(15000),(27)⟩ = (-57452363618805) := by decide +kernel
private theorem row_43 : rawRow ⟨(1635000),(-767000),(15000),(27)⟩ = (-57452363618805) := by decide +kernel
private theorem row_44 : rawRow ⟨(1646000),(806000),(15000),(26)⟩ = (-50364210378742) := by decide +kernel
private theorem row_45 : rawRow ⟨(1646000),(-806000),(15000),(26)⟩ = (-50364210378742) := by decide +kernel
private theorem row_46 : rawRow ⟨(1656000),(844000),(15000),(24)⟩ = (-41926678390440) := by decide +kernel
private theorem row_47 : rawRow ⟨(1656000),(-844000),(15000),(24)⟩ = (-41926678390440) := by decide +kernel
private theorem row_48 : rawRow ⟨(1667000),(884000),(16000),(23)⟩ = (-35446919108345) := by decide +kernel
private theorem row_49 : rawRow ⟨(1667000),(-884000),(16000),(23)⟩ = (-35446919108345) := by decide +kernel
private theorem row_50 : rawRow ⟨(1677000),(923000),(15000),(21)⟩ = (-28234319971389) := by decide +kernel
private theorem row_51 : rawRow ⟨(1677000),(-923000),(15000),(21)⟩ = (-28234319971389) := by decide +kernel
private theorem row_52 : rawRow ⟨(1685000),(963000),(15000),(19)⟩ = (-21665591731597) := by decide +kernel
private theorem row_53 : rawRow ⟨(1685000),(-963000),(15000),(19)⟩ = (-21665591731597) := by decide +kernel
private theorem row_54 : rawRow ⟨(1692000),(1002000),(15000),(18)⟩ = (-16938736683156) := by decide +kernel
private theorem row_55 : rawRow ⟨(1692000),(-1002000),(15000),(18)⟩ = (-16938736683156) := by decide +kernel
private theorem row_56 : rawRow ⟨(1699000),(1042000),(15000),(16)⟩ = (-11717930447920) := by decide +kernel
private theorem row_57 : rawRow ⟨(1699000),(-1042000),(15000),(16)⟩ = (-11717930447920) := by decide +kernel
private theorem row_58 : rawRow ⟨(1706000),(1082000),(16000),(14)⟩ = (-7279496603078) := by decide +kernel
private theorem row_59 : rawRow ⟨(1706000),(-1082000),(16000),(14)⟩ = (-7279496603078) := by decide +kernel
private theorem row_60 : rawRow ⟨(1712000),(1123000),(16000),(12)⟩ = (-3661820005476) := by decide +kernel
private theorem row_61 : rawRow ⟨(1712000),(-1123000),(16000),(12)⟩ = (-3661820005476) := by decide +kernel
private theorem row_62 : rawRow ⟨(1718000),(1164000),(16000),(10)⟩ = (-904120193670) := by decide +kernel
private theorem row_63 : rawRow ⟨(1718000),(-1164000),(16000),(10)⟩ = (-904120193670) := by decide +kernel
private theorem row_64 : rawRow ⟨(1724000),(1205000),(16000),(7)⟩ = (876902338494) := by decide +kernel
private theorem row_65 : rawRow ⟨(1724000),(-1205000),(16000),(7)⟩ = (876902338494) := by decide +kernel
private theorem row_66 : rawRow ⟨(1729000),(1246000),(16000),(2)⟩ = (673781630076) := by decide +kernel
private theorem row_67 : rawRow ⟨(1729000),(-1246000),(16000),(2)⟩ = (673781630076) := by decide +kernel
private theorem entries_literal : entries = [⟨(1343000),(45000),(12000),(1)⟩,⟨(1343000),(-45000),(12000),(1)⟩,⟨(1348000),(76000),(12000),(29)⟩,⟨(1348000),(-76000),(12000),(29)⟩,⟨(1362000),(106000),(13000),(40)⟩,⟨(1362000),(-106000),(13000),(40)⟩,⟨(1377000),(138000),(13000),(44)⟩,⟨(1377000),(-138000),(13000),(44)⟩,⟨(1394000),(169000),(14000),(50)⟩,⟨(1394000),(-169000),(14000),(50)⟩,⟨(1411000),(201000),(14000),(46)⟩,⟨(1411000),(-201000),(14000),(46)⟩,⟨(1427000),(234000),(14000),(46)⟩,⟨(1427000),(-234000),(14000),(46)⟩,⟨(1443000),(267000),(14000),(45)⟩,⟨(1443000),(-267000),(14000),(45)⟩,⟨(1459000),(300000),(14000),(45)⟩,⟨(1459000),(-300000),(14000),(45)⟩,⟨(1475000),(334000),(14000),(44)⟩,⟨(1475000),(-334000),(14000),(44)⟩,⟨(1491000),(368000),(14000),(42)⟩,⟨(1491000),(-368000),(14000),(42)⟩,⟨(1507000),(402000),(14000),(41)⟩,⟨(1507000),(-402000),(14000),(41)⟩,⟨(1522000),(437000),(15000),(40)⟩,⟨(1522000),(-437000),(15000),(40)⟩,⟨(1537000),(473000),(15000),(39)⟩,⟨(1537000),(-473000),(15000),(39)⟩,⟨(1552000),(509000),(15000),(37)⟩,⟨(1552000),(-509000),(15000),(37)⟩,⟨(1564000),(544000),(14000),(35)⟩,⟨(1564000),(-544000),(14000),(35)⟩,⟨(1576000),(581000),(15000),(34)⟩,⟨(1576000),(-581000),(15000),(34)⟩,⟨(1589000),(617000),(15000),(33)⟩,⟨(1589000),(-617000),(15000),(33)⟩,⟨(1600000),(654000),(15000),(31)⟩,⟨(1600000),(-654000),(15000),(31)⟩,⟨(1612000),(692000),(15000),(30)⟩,⟨(1612000),(-692000),(15000),(30)⟩,⟨(1624000),(729000),(15000),(29)⟩,⟨(1624000),(-729000),(15000),(29)⟩,⟨(1635000),(767000),(15000),(27)⟩,⟨(1635000),(-767000),(15000),(27)⟩,⟨(1646000),(806000),(15000),(26)⟩,⟨(1646000),(-806000),(15000),(26)⟩,⟨(1656000),(844000),(15000),(24)⟩,⟨(1656000),(-844000),(15000),(24)⟩,⟨(1667000),(884000),(16000),(23)⟩,⟨(1667000),(-884000),(16000),(23)⟩,⟨(1677000),(923000),(15000),(21)⟩,⟨(1677000),(-923000),(15000),(21)⟩,⟨(1685000),(963000),(15000),(19)⟩,⟨(1685000),(-963000),(15000),(19)⟩,⟨(1692000),(1002000),(15000),(18)⟩,⟨(1692000),(-1002000),(15000),(18)⟩,⟨(1699000),(1042000),(15000),(16)⟩,⟨(1699000),(-1042000),(15000),(16)⟩,⟨(1706000),(1082000),(16000),(14)⟩,⟨(1706000),(-1082000),(16000),(14)⟩,⟨(1712000),(1123000),(16000),(12)⟩,⟨(1712000),(-1123000),(16000),(12)⟩,⟨(1718000),(1164000),(16000),(10)⟩,⟨(1718000),(-1164000),(16000),(10)⟩,⟨(1724000),(1205000),(16000),(7)⟩,⟨(1724000),(-1205000),(16000),(7)⟩,⟨(1729000),(1246000),(16000),(2)⟩,⟨(1729000),(-1246000),(16000),(2)⟩] := rfl
theorem raw_budget : rawTotal=2*energySum := by
  unfold rawTotal
  rw [entries_literal]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,row_0,row_1,row_2,row_3,row_4,row_5,row_6,row_7,row_8,row_9,row_10,row_11,row_12,row_13,row_14,row_15,row_16,row_17,row_18,row_19,row_20,row_21,row_22,row_23,row_24,row_25,row_26,row_27,row_28,row_29,row_30,row_31,row_32,row_33,row_34,row_35,row_36,row_37,row_38,row_39,row_40,row_41,row_42,row_43,row_44,row_45,row_46,row_47,row_48,row_49,row_50,row_51,row_52,row_53,row_54,row_55,row_56,row_57,row_58,row_59,row_60,row_61,row_62,row_63,row_64,row_65,row_66,row_67]
  decide +kernel
end OddZetaSix.B40a.Witness
