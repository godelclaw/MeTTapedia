import KrennRawLRAT

namespace Krenn.CollapseSupportCover.GlobalRawLRATTest

raw_lrat_proof contradiction
  (include_str "LRAT/GlobalSupportCover.cnf")
  (include_str "LRAT/GlobalSupportCover.lrat")

#check contradiction
#print axioms contradiction

end Krenn.CollapseSupportCover.GlobalRawLRATTest
