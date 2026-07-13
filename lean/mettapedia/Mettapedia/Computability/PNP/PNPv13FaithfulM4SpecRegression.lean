import Mettapedia.Computability.PNP.PNPv13FaithfulM4Spec

/-!
# Regression checks for the faithful Appendix D/I M4 specification
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

#check V13M4Region
#check V13M4LayeredGeometry
#check V13M4LocalComponents
#check V13M4LocalComponents.GaugeVectorActionSpec
#check V13D8LockedMessageRigidity
#check V13D30NoPublicTargetTags
#check V13D33AtomCompleteness
#check V13M4UniformGaugeLift
#check V13FiniteCoupling
#check V13D48CompatibleCouplings
#check V13M4UniformCNFCompilation
#check V13M4OpenConstructionObligations
#check V13M4FaithfulConditionalEndpointTarget

#print axioms V13M4Region
#print axioms V13M4LayeredGeometry
#print axioms V13M4LocalComponents
#print axioms V13M4LocalComponents.GaugeVectorActionSpec
#print axioms V13D8LockedMessageRigidity
#print axioms V13D30NoPublicTargetTags
#print axioms V13D33AtomCompleteness
#print axioms V13M4UniformGaugeLift
#print axioms V13FiniteCoupling
#print axioms V13D48CompatibleCouplings
#print axioms V13M4UniformCNFCompilation
#print axioms V13M4OpenConstructionObligations
#print axioms V13M4FaithfulConditionalEndpointTarget

end Mettapedia.Computability.PNP
