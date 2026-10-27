import Mettapedia.OSLF.NativeTypes.Consumers.DependentChecking
import Mettapedia.OSLF.NativeTypes.Consumers.DependentCheckingControls
import Mettapedia.OSLF.NativeTypes.Consumers.MM0Admission
import Mettapedia.OSLF.NativeTypes.Consumers.MM0AdmissionControls
import Mettapedia.OSLF.NativeTypes.Consumers.PLNEvidence
import Mettapedia.OSLF.NativeTypes.Consumers.PLNEvidenceControls
import Mettapedia.OSLF.NativeTypes.Consumers.MM2Batch
import Mettapedia.OSLF.NativeTypes.Consumers.MM2BatchControls
import Mettapedia.OSLF.NativeTypes.Consumers.ExecutorQualification
import Mettapedia.OSLF.NativeTypes.Consumers.ExecutorQualificationControls
import Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpace
import Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceControls
import Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceSpatial
import Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceSpatialControls
import Mettapedia.OSLF.NativeTypes.Consumers.IndexedAppend
import Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceFrontDoor
import Mettapedia.OSLF.NativeTypes.Consumers.IndexedAppendFrontDoor
import Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceSpatialFrontDoor
import Mettapedia.OSLF.NativeTypes.Consumers.PLNEvidenceFrontDoor
import Mettapedia.OSLF.NativeTypes.Consumers.MM0AdmissionFrontDoor
import Mettapedia.OSLF.NativeTypes.Consumers.ExecutorQualificationFrontDoor
import Mettapedia.OSLF.NativeTypes.Consumers.MM2BatchFrontDoor
import Mettapedia.OSLF.NativeTypes.Consumers.MM2BatchFrontDoorControls
import Mettapedia.OSLF.NativeTypes.Consumers.DependentCheckingFrontDoor
import Mettapedia.OSLF.NativeTypes.Consumers.DependentCheckingFrontDoorControls

/-! # Executable observations for existing dependent, proof and runtime consumers.

Each consumer also answers through the generated front door (`*FrontDoor`): its own check or generated native type is
a formula of Φ(L) over the consumer's system, with controls the kernel evaluates where the inputs are pure. -/
