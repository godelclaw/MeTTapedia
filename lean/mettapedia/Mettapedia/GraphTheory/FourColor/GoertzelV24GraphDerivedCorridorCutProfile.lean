import Mettapedia.GraphTheory.FourColor.GoertzelV24HexSlabConnectivityProfile

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24GraphDerivedCorridorCutProfile

open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24WindingClassification

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Raw graph coordinates for one corridor cut. This carries no validity or
splice conclusion: edge membership, port distinctness, strand connectivity,
and partial face lengths are all separate computed predicates or values. -/
structure GraphCorridorCutData (RS : RotationSystem V E)
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) where
  regionEdges : Finset E
  crossingEdge : Fin crossingEdgeCount → E
  terminalEdge : Fin terminalCount → E
  fragmentFace : Fin faceFragmentCount → OrbitFace RS
  fragmentEdges : Fin faceFragmentCount → Finset E

/-- The ambient edge represented by either kind of profile port. -/
def GraphCorridorCutData.portEdge
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount) :
    CorridorPort crossingEdgeCount terminalCount → E
  | .inl crossing => data.crossingEdge crossing
  | .inr terminal => data.terminalEdge terminal

/-- Every named port is genuinely present in the stored regional edge set. -/
def GraphCorridorCutData.PortsInRegion
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount) : Prop :=
  ∀ port, data.portEdge port ∈ data.regionEdges

/-- Port distinctness as a predicate on raw graph data, not as an assumed
profile field. -/
def GraphCorridorCutData.PortsInjective
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount) : Prop :=
  Function.Injective data.portEdge

/-- The portion of one named fragment that genuinely lies both on its named
ambient face and in the regional edge set. -/
def GraphCorridorCutData.regionalFragmentEdges
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount) (fragment : Fin faceFragmentCount) : Finset E :=
  data.fragmentEdges fragment ∩
    orbitFaceBoundary RS (data.fragmentFace fragment) ∩ data.regionEdges

/-- Every raw fragment edge lies on its named face and in the region. This is
a computed well-formedness predicate; it is not stored as evidence. -/
def GraphCorridorCutData.FragmentsOnFaceInRegion
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount) : Prop :=
  ∀ fragment, data.fragmentEdges fragment ⊆
    orbitFaceBoundary RS (data.fragmentFace fragment) ∩ data.regionEdges

theorem GraphCorridorCutData.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (hfragments : data.FragmentsOnFaceInRegion)
    (fragment : Fin faceFragmentCount) :
    data.regionalFragmentEdges fragment = data.fragmentEdges fragment := by
  apply Finset.Subset.antisymm
  · intro edge hedge
    exact (Finset.mem_inter.1 (Finset.mem_inter.1 hedge).1).1
  · intro edge hedge
    have hvalid := hfragments fragment hedge
    have hvalid' := Finset.mem_inter.1 hvalid
    exact Finset.mem_inter.2
      ⟨Finset.mem_inter.2 ⟨hedge, hvalid'.1⟩, hvalid'.2⟩

/-- Partial face length capped at five, represented in `Fin 6`. Five is the
only saturation value needed when the preserved test is face length at least
five. -/
def GraphCorridorCutData.cappedRegionalFaceLength
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount) (fragment : Fin faceFragmentCount) : Fin 6 :=
  ⟨min (data.regionalFragmentEdges fragment).card 5, by omega⟩

/-- Complete finite corridor profile computed from raw graph coordinates and
an actual Tait coloring. No connectivity or face datum is supplied as a free
proposition. -/
def GraphCorridorCutData.profile
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    CorridorCutProfile crossingEdgeCount terminalCount faceFragmentCount where
  edgeColor crossing :=
    strandColorOfNonzero (C (data.crossingEdge crossing))
      (hC (data.crossingEdge crossing))
  strandConnected pair left right :=
    regionalTrackedConnectivity RS data.regionEdges C pair
      (data.portEdge left) (data.portEdge right)
  faceContinues left right :=
    decide (data.fragmentFace left = data.fragmentFace right)
  fragmentContainsPort fragment port :=
    decide (data.portEdge port ∈ data.regionalFragmentEdges fragment)
  faceLengthCap := data.cappedRegionalFaceLength

@[simp]
theorem GraphCorridorCutData.profile_edgeColor_toColor
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (crossing : Fin crossingEdgeCount) :
    ((data.profile C hC).edgeColor crossing).toColor =
      C (data.crossingEdge crossing) := by
  simp [GraphCorridorCutData.profile]

theorem GraphCorridorCutData.profile_strandConnected_eq_true_iff
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (pair : TrackedColorPair)
    (left right : CorridorPort crossingEdgeCount terminalCount) :
    (data.profile C hC).strandConnected pair left right = true ↔
      data.portEdge left ∈ data.regionEdges ∧
      data.portEdge right ∈ data.regionEdges ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (C (data.portEdge left)) ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (C (data.portEdge right)) ∧
      (regionalTrackedEdgeGraph RS data.regionEdges C
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable
          (data.portEdge left) (data.portEdge right) := by
  exact regionalTrackedConnectivity_eq_true_iff RS data.regionEdges C
    pair (data.portEdge left) (data.portEdge right)

@[simp]
theorem GraphCorridorCutData.profile_faceContinues_eq_true_iff
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (left right : Fin faceFragmentCount) :
    (data.profile C hC).faceContinues left right = true ↔
      data.fragmentFace left = data.fragmentFace right := by
  simp [GraphCorridorCutData.profile]

@[simp]
theorem GraphCorridorCutData.profile_fragmentContainsPort_eq_true_iff
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (fragment : Fin faceFragmentCount)
    (port : CorridorPort crossingEdgeCount terminalCount) :
    (data.profile C hC).fragmentContainsPort fragment port = true ↔
      data.portEdge port ∈ data.regionalFragmentEdges fragment := by
  simp [GraphCorridorCutData.profile]

@[simp]
theorem GraphCorridorCutData.profile_faceLengthCap_val
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (fragment : Fin faceFragmentCount) :
    ((data.profile C hC).faceLengthCap fragment).val =
      min (data.regionalFragmentEdges fragment).card 5 :=
  rfl

theorem GraphCorridorCutData.profile_faceLengthCap_eq_five_iff
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (fragment : Fin faceFragmentCount) :
    (data.profile C hC).faceLengthCap fragment = (5 : Fin 6) ↔
      5 ≤ (data.regionalFragmentEdges fragment).card := by
  rw [Fin.ext_iff]
  simp [GraphCorridorCutData.profile_faceLengthCap_val]

/-- When the raw cut has all ports in its region, diagonal connectivity has
the exact intended meaning: membership in the selected tracked color pair. -/
theorem GraphCorridorCutData.profile_strandConnected_self_eq_true_iff
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (hports : data.PortsInRegion)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (pair : TrackedColorPair)
    (port : CorridorPort crossingEdgeCount terminalCount) :
    (data.profile C hC).strandConnected pair port port = true ↔
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (C (data.portEdge port)) := by
  change regionalTrackedConnectivity RS data.regionEdges C pair
      (data.portEdge port) (data.portEdge port) = true ↔ _
  simpa [hports port] using regionalTrackedConnectivity_self_eq_true_iff
    RS data.regionEdges C pair (data.portEdge port)

/-- Equality of two graph-derived profiles preserves the actual ambient
colors on corresponding crossing edges. -/
theorem crossingEdge_color_eq_of_profiles_eq
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (left right : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (C₁ C₂ : RS.EdgeColoring Color)
    (hC₁ : RS.IsTaitEdgeColoring C₁) (hC₂ : RS.IsTaitEdgeColoring C₂)
    (hprofiles : left.profile C₁ hC₁ = right.profile C₂ hC₂)
    (crossing : Fin crossingEdgeCount) :
    C₁ (left.crossingEdge crossing) = C₂ (right.crossingEdge crossing) := by
  have hcolors := congrFun (congrArg CorridorCutProfile.edgeColor hprofiles) crossing
  exact (left.profile_edgeColor_toColor C₁ hC₁ crossing).symm.trans
    ((congrArg StrandColor.toColor hcolors).trans
      (right.profile_edgeColor_toColor C₂ hC₂ crossing))

/-- Equality of two graph-derived profiles preserves every tracked-port
connectivity observation. -/
theorem strandConnected_eq_of_profiles_eq
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (left right : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (C₁ C₂ : RS.EdgeColoring Color)
    (hC₁ : RS.IsTaitEdgeColoring C₁) (hC₂ : RS.IsTaitEdgeColoring C₂)
    (hprofiles : left.profile C₁ hC₁ = right.profile C₂ hC₂)
    (pair : TrackedColorPair)
    (first second : CorridorPort crossingEdgeCount terminalCount) :
    (left.profile C₁ hC₁).strandConnected pair first second =
      (right.profile C₂ hC₂).strandConnected pair first second := by
  exact congrFun (congrFun (congrFun
    (congrArg CorridorCutProfile.strandConnected hprofiles) pair) first) second

/-- Equality of graph-derived profiles preserves which named fragments belong
to the same ambient face. -/
theorem faceContinues_eq_of_profiles_eq
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (left right : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (C₁ C₂ : RS.EdgeColoring Color)
    (hC₁ : RS.IsTaitEdgeColoring C₁) (hC₂ : RS.IsTaitEdgeColoring C₂)
    (hprofiles : left.profile C₁ hC₁ = right.profile C₂ hC₂)
    (first second : Fin faceFragmentCount) :
    (left.fragmentFace first = left.fragmentFace second) ↔
      (right.fragmentFace first = right.fragmentFace second) := by
  rw [← left.profile_faceContinues_eq_true_iff C₁ hC₁,
    ← right.profile_faceContinues_eq_true_iff C₂ hC₂]
  have hvalues := congrFun (congrFun
    (congrArg CorridorCutProfile.faceContinues hprofiles) first) second
  simp [hvalues]

/-- Equality of graph-derived profiles preserves which actual port edges lie
in each corresponding regional face fragment. -/
theorem fragmentContainsPort_iff_of_profiles_eq
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (left right : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (C₁ C₂ : RS.EdgeColoring Color)
    (hC₁ : RS.IsTaitEdgeColoring C₁) (hC₂ : RS.IsTaitEdgeColoring C₂)
    (hprofiles : left.profile C₁ hC₁ = right.profile C₂ hC₂)
    (fragment : Fin faceFragmentCount)
    (port : CorridorPort crossingEdgeCount terminalCount) :
    left.portEdge port ∈ left.regionalFragmentEdges fragment ↔
      right.portEdge port ∈ right.regionalFragmentEdges fragment := by
  rw [← left.profile_fragmentContainsPort_eq_true_iff C₁ hC₁,
    ← right.profile_fragmentContainsPort_eq_true_iff C₂ hC₂]
  have hvalues := congrFun (congrFun
    (congrArg CorridorCutProfile.fragmentContainsPort hprofiles) fragment) port
  simp [hvalues]

/-- Equality of graph-derived profiles preserves every capped partial face
length. -/
theorem faceLengthCap_eq_of_profiles_eq
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (left right : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (C₁ C₂ : RS.EdgeColoring Color)
    (hC₁ : RS.IsTaitEdgeColoring C₁) (hC₂ : RS.IsTaitEdgeColoring C₂)
    (hprofiles : left.profile C₁ hC₁ = right.profile C₂ hC₂)
    (fragment : Fin faceFragmentCount) :
    min (left.regionalFragmentEdges fragment).card 5 =
      min (right.regionalFragmentEdges fragment).card 5 := by
  have hlength := congrFun
    (congrArg CorridorCutProfile.faceLengthCap hprofiles) fragment
  exact congrArg Fin.val hlength

end


end GoertzelV24GraphDerivedCorridorCutProfile

end Mettapedia.GraphTheory.FourColor
