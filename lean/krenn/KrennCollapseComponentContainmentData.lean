import KrennCollapseComponentContainmentBalance00
import KrennCollapseComponentContainmentBalance01
import KrennCollapseComponentContainmentBalance02
import KrennCollapseComponentContainmentBalance03
import KrennCollapseComponentContainmentBalance04
import KrennCollapseComponentContainmentBalance05
import KrennCollapseComponentContainmentBalance06

/-! Aggregate interface for all concrete signed-chain balances. -/

namespace Krenn.CollapseComponentContainmentData

open Krenn.LatticeCombinationReflection

theorem chainBalance (index : Fin 91) :
    ExponentBalance relation
      (generatorBinomial (chainCertificate index).target)
      (chainCertificate index).steps := by
  fin_cases index
  · exact chainBalance000
  · exact chainBalance001
  · exact chainBalance002
  · exact chainBalance003
  · exact chainBalance004
  · exact chainBalance005
  · exact chainBalance006
  · exact chainBalance007
  · exact chainBalance008
  · exact chainBalance009
  · exact chainBalance010
  · exact chainBalance011
  · exact chainBalance012
  · exact chainBalance013
  · exact chainBalance014
  · exact chainBalance015
  · exact chainBalance016
  · exact chainBalance017
  · exact chainBalance018
  · exact chainBalance019
  · exact chainBalance020
  · exact chainBalance021
  · exact chainBalance022
  · exact chainBalance023
  · exact chainBalance024
  · exact chainBalance025
  · exact chainBalance026
  · exact chainBalance027
  · exact chainBalance028
  · exact chainBalance029
  · exact chainBalance030
  · exact chainBalance031
  · exact chainBalance032
  · exact chainBalance033
  · exact chainBalance034
  · exact chainBalance035
  · exact chainBalance036
  · exact chainBalance037
  · exact chainBalance038
  · exact chainBalance039
  · exact chainBalance040
  · exact chainBalance041
  · exact chainBalance042
  · exact chainBalance043
  · exact chainBalance044
  · exact chainBalance045
  · exact chainBalance046
  · exact chainBalance047
  · exact chainBalance048
  · exact chainBalance049
  · exact chainBalance050
  · exact chainBalance051
  · exact chainBalance052
  · exact chainBalance053
  · exact chainBalance054
  · exact chainBalance055
  · exact chainBalance056
  · exact chainBalance057
  · exact chainBalance058
  · exact chainBalance059
  · exact chainBalance060
  · exact chainBalance061
  · exact chainBalance062
  · exact chainBalance063
  · exact chainBalance064
  · exact chainBalance065
  · exact chainBalance066
  · exact chainBalance067
  · exact chainBalance068
  · exact chainBalance069
  · exact chainBalance070
  · exact chainBalance071
  · exact chainBalance072
  · exact chainBalance073
  · exact chainBalance074
  · exact chainBalance075
  · exact chainBalance076
  · exact chainBalance077
  · exact chainBalance078
  · exact chainBalance079
  · exact chainBalance080
  · exact chainBalance081
  · exact chainBalance082
  · exact chainBalance083
  · exact chainBalance084
  · exact chainBalance085
  · exact chainBalance086
  · exact chainBalance087
  · exact chainBalance088
  · exact chainBalance089
  · exact chainBalance090

end Krenn.CollapseComponentContainmentData
