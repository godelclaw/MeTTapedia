import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueQuiz

/-!
# Classical quiz preembeddings

A fitting classical quiz determines more than a matching list of face
arities.  Its source traversal is a transversal of the configuration kernel,
so the corresponding target traversal canonically pairs every kernel face
with an ambient face of the same length.  Transport around those paired
cycles gives the partial face map used by the classical reducibility
argument.

This file states the four preembedding obligations with their standard
hypermap meanings and constructs the partial map directly from a checked
catalogue quiz.  A reflected source-geometry check and the recursive quiz
structure force the paired traversal representatives to be edge-central, so
kernel coverage follows.  The resulting constructor leaves only the standard
`R`-link connectivity field to be supplied.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateQuizPreembedding

open ClassicalCertificateCatalogueQuiz
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermap
open ClassicalCertificateQuiz
open ClassicalCertificateReductionMetadata

noncomputable section

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The union of the face cycles meeting a boundary walk.  This is the
hypermap `fband` predicate. -/
def FaceBand (H : FiniteHypermap D) (boundary : List D) (dart : D) : Prop :=
  ∃ anchor ∈ boundary, H.face.SameCycle dart anchor

/-- The configuration kernel is the complement of the face band of its outer
ring. -/
def FaceKernel (H : FiniteHypermap D) (boundary : List D) (dart : D) : Prop :=
  ¬ FaceBand H boundary dart

/-- Closure of a predicate under complete face cycles.  For a permutation
this is exactly MathComp's `fclosure face`. -/
def FaceClosure (H : FiniteHypermap D) (predicate : D → Prop) (dart : D) : Prop :=
  ∃ anchor, predicate anchor ∧ H.face.SameCycle dart anchor

/-- An edge is central for a partial hypermap map when the map commutes with
the edge permutation there. -/
def EdgeCentral
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (source : FiniteHypermap Source) (target : FiniteHypermap Target)
    (mapDart : Source → Target) (dart : Source) : Prop :=
  mapDart (source.edge dart) = target.edge (mapDart dart)

/-- Every hypermap edge is an involution. -/
def IsPlain (H : FiniteHypermap D) : Prop :=
  ∀ dart, H.edge (H.edge dart) = dart

/-- Every vertex permutation has period three. -/
def IsCubic (H : FiniteHypermap D) : Prop :=
  ∀ dart, H.node (H.node (H.node dart)) = dart

/-- Period-three vertex rotation on a specified source domain. -/
def IsCubicOn (H : FiniteHypermap D) (domain : D → Prop) : Prop :=
  ∀ dart, domain dart → H.node (H.node (H.node dart)) = dart

/-- A domain consists of complete face cycles. -/
def FaceInvariant (H : FiniteHypermap D) (domain : D → Prop) : Prop :=
  ∀ dart, domain (H.face dart) ↔ domain dart

/-- A list-valued path for a binary relation, with the first vertex supplied
separately. -/
def RelationPath {A : Type*} (relation : A → A → Prop) (start : A) :
    List A → Prop
  | [] => True
  | next :: rest => relation start next ∧ RelationPath relation next rest

/-- The classical `R`-link crosses the edge at its source and may then move
any distance around the resulting face. -/
def RLink (H : FiniteHypermap D) (source target : D) : Prop :=
  H.face.SameCycle (H.edge source) target

/-- Exact list-path formulation of classical `rlink_connected`.  Endpoints
belong to the predicate; all strict intermediate vertices do as well. -/
def RLinkConnected (H : FiniteHypermap D) (predicate : D → Prop) : Prop :=
  ∀ x, predicate x → ∀ y, predicate y →
    ∃ middle : List D,
      RelationPath (RLink H) (H.node (H.face x)) (middle ++ [y]) ∧
        ∀ dart ∈ middle, predicate dart

/-- The four fields of the classical partial embedding, stated over standard
finite hypermaps. -/
structure Preembedding
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (source : FiniteHypermap Source) (target : FiniteHypermap Target)
    (domain : Source → Prop) (mapDart : Source → Target) : Prop where
  face : ∀ dart, domain dart →
    mapDart (source.face dart) = target.face (mapDart dart)
  arity : ∀ dart, domain dart →
    hypermapFaceArity source dart =
      hypermapFaceArity target (mapDart dart)
  cover : ∀ dart, domain dart →
    FaceClosure source (EdgeCentral source target mapDart) dart
  rlinked : RLinkConnected source
    (fun dart => domain dart ∧ EdgeCentral source target mapDart dart)

/-- The first two, purely facial, fields of a preembedding. -/
structure FacialPreembedding
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (source : FiniteHypermap Source) (target : FiniteHypermap Target)
    (domain : Source → Prop) (mapDart : Source → Target) : Prop where
  face : ∀ dart, domain dart →
    mapDart (source.face dart) = target.face (mapDart dart)
  arity : ∀ dart, domain dart →
    hypermapFaceArity source dart =
      hypermapFaceArity target (mapDart dart)

theorem faceBand_face_iff (H : FiniteHypermap D) (boundary : List D)
    (dart : D) :
    FaceBand H boundary (H.face dart) ↔ FaceBand H boundary dart := by
  constructor
  · rintro ⟨anchor, hanchor, hsame⟩
    exact ⟨anchor, hanchor,
      (Mettapedia.GraphTheory.EquivPermSameCycle.step_right H.face dart).trans
        hsame⟩
  · rintro ⟨anchor, hanchor, hsame⟩
    exact ⟨anchor, hanchor,
      (Mettapedia.GraphTheory.EquivPermSameCycle.step_right H.face dart).symm.trans
        hsame⟩

theorem faceKernel_face_iff (H : FiniteHypermap D) (boundary : List D)
    (dart : D) :
    FaceKernel H boundary (H.face dart) ↔ FaceKernel H boundary dart := by
  simp only [FaceKernel, faceBand_face_iff]

theorem faceClosure_of_sameCycle
    (H : FiniteHypermap D) (predicate : D → Prop)
    {dart anchor : D} (hanchor : predicate anchor)
    (hsame : H.face.SameCycle dart anchor) :
    FaceClosure H predicate dart :=
  ⟨anchor, hanchor, hsame⟩

/-- Cubicity rewrites one face step after an edge crossing as two node
steps. -/
theorem face_edge_eq_node_node_of_cube
    (H : FiniteHypermap D) (dart : D)
    (hcube : H.node (H.node (H.node dart)) = dart) :
    H.face (H.edge dart) = H.node (H.node dart) := by
  have hidentity := H.face_edge_node (H.node (H.node dart))
  rw [hcube] at hidentity
  exact hidentity

/-- If the target of one face step is cubic, that step is two node turns after
crossing the incoming edge. -/
theorem face_eq_node_node_edge_of_face_cube
    (H : FiniteHypermap D) (hplain : IsPlain H) (dart : D)
    (hcube : H.node (H.node (H.node (H.face dart))) = H.face dart) :
    H.face dart = H.node (H.node (H.edge dart)) := by
  have hnode : H.node (H.face dart) = H.edge dart := by
    apply H.edge.injective
    rw [H.edge_node_face, hplain]
  calc
    H.face dart = H.node (H.node (H.node (H.face dart))) := hcube.symm
    _ = H.node (H.node (H.edge dart)) := by rw [hnode]

/-- The node just beyond a double-left quiz turn is the second face successor
of the seed's crossed edge. -/
theorem node_qstepL_node_eq_face_face_edge
    (H : FiniteHypermap D) (hplain : IsPlain H) (dart : D)
    (hcube : H.node (H.node (H.node dart)) = dart)
    (hfaceFaceCube :
      H.node (H.node (H.node (H.face (H.face (H.edge dart))))) =
        H.face (H.face (H.edge dart))) :
    H.node (qstepLWith H.edge H.node (H.node dart)) =
      H.face (H.face (H.edge dart)) := by
  unfold qstepLWith
  have hfirst := face_edge_eq_node_node_of_cube H dart hcube
  have hnextCube :
      H.node (H.node (H.node (H.face (H.node (H.node dart))))) =
        H.face (H.node (H.node dart)) := by
    rw [← hfirst]
    exact hfaceFaceCube
  calc
    H.node (H.node (H.edge (H.node (H.node dart)))) =
        H.face (H.node (H.node dart)) :=
      (face_eq_node_node_edge_of_face_cube H hplain
        (H.node (H.node dart)) hnextCube).symm
    _ = H.face (H.face (H.edge dart)) :=
      (congrArg H.face hfirst).symm

/-- A face-invariant domain contains the predecessor `edge (node dart)` of
each one of its darts. -/
theorem domain_edge_node
    (H : FiniteHypermap D) {domain : D → Prop}
    (hinvariant : FaceInvariant H domain) (dart : D)
    (hdart : domain dart) : domain (H.edge (H.node dart)) := by
  apply (hinvariant (H.edge (H.node dart))).1
  rw [H.face_edge_node]
  exact hdart

/-- In a cubic hypermap, face invariance also transports membership from
`edge dart` to `node² dart`. -/
theorem domain_node_node_of_edge
    (H : FiniteHypermap D) {domain : D → Prop}
    (hinvariant : FaceInvariant H domain) (dart : D)
    (hedge : domain (H.edge dart))
    (hcube : H.node (H.node (H.node dart)) = dart) :
    domain (H.node (H.node dart)) := by
  rw [← face_edge_eq_node_node_of_cube H dart hcube]
  exact (hinvariant (H.edge dart)).2 hedge

/-- A partial face morphism sends the canonical face predecessor of a dart to
the corresponding target predecessor. -/
theorem map_edge_node
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (source : FiniteHypermap Source) (target : FiniteHypermap Target)
    {domain : Source → Prop} (mapDart : Source → Target)
    (hinvariant : FaceInvariant source domain)
    (hface : ∀ dart, domain dart →
      mapDart (source.face dart) = target.face (mapDart dart))
    (dart : Source) (hdart : domain dart) :
    mapDart (source.edge (source.node dart)) =
      target.edge (target.node (mapDart dart)) := by
  have hpredecessor := domain_edge_node source hinvariant dart hdart
  apply target.face.injective
  rw [← hface _ hpredecessor]
  simp only [source.face_edge_node, target.face_edge_node]

/-- Edge-centrality is invariant under crossing an edge in plain source and
target hypermaps. -/
theorem edgeCentral_edge
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (source : FiniteHypermap Source) (target : FiniteHypermap Target)
    (mapDart : Source → Target)
    (hsourcePlain : IsPlain source) (htargetPlain : IsPlain target)
    (dart : Source)
    (hcentral : EdgeCentral source target mapDart dart) :
    EdgeCentral source target mapDart (source.edge dart) := by
  unfold EdgeCentral at hcentral ⊢
  rw [hsourcePlain dart, hcentral, htargetPlain]

/-- If a mapped question head is the corresponding target node step, facial
transport makes that head edge-central. -/
theorem edgeCentral_node_of_map_node
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (source : FiniteHypermap Source) (target : FiniteHypermap Target)
    {domain : Source → Prop} (mapDart : Source → Target)
    (hinvariant : FaceInvariant source domain)
    (hface : ∀ dart, domain dart →
      mapDart (source.face dart) = target.face (mapDart dart))
    (dart : Source) (hdart : domain dart)
    (hnode : mapDart (source.node dart) = target.node (mapDart dart)) :
    EdgeCentral source target mapDart (source.node dart) := by
  unfold EdgeCentral
  rw [map_edge_node source target mapDart hinvariant hface dart hdart,
    hnode]

/-- A mapped node head turns its right predecessor into the next mapped
edge-central recursion seed. -/
theorem rightSeed_of_map_node
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (source : FiniteHypermap Source) (target : FiniteHypermap Target)
    {domain : Source → Prop} (mapDart : Source → Target)
    (hinvariant : FaceInvariant source domain)
    (hface : ∀ dart, domain dart →
      mapDart (source.face dart) = target.face (mapDart dart))
    (hsourcePlain : IsPlain source) (htargetPlain : IsPlain target)
    (dart : Source) (hdart : domain dart)
    (hnode : mapDart (source.node dart) = target.node (mapDart dart)) :
    mapDart (source.edge (source.node dart)) =
        target.edge (target.node (mapDart dart)) ∧
      EdgeCentral source target mapDart
        (source.edge (source.node dart)) := by
  have hmap := map_edge_node source target mapDart hinvariant hface dart hdart
  refine ⟨hmap, ?_⟩
  unfold EdgeCentral
  rw [hsourcePlain, hnode, hmap, htargetPlain]

/-- A mapped node head and a central seed similarly produce the left
predecessor `edge (node² dart)` as a mapped central recursion seed. -/
theorem leftSeed_of_map_node
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (source : FiniteHypermap Source) (target : FiniteHypermap Target)
    {domain : Source → Prop} (mapDart : Source → Target)
    (hinvariant : FaceInvariant source domain)
    (hface : ∀ dart, domain dart →
      mapDart (source.face dart) = target.face (mapDart dart))
    (hsourcePlain : IsPlain source) (htargetPlain : IsPlain target)
    (dart : Source) (hedge : domain (source.edge dart))
    (hnodeDomain : domain (source.node dart))
    (hsourceCube : source.node (source.node (source.node dart)) = dart)
    (htargetCube : target.node (target.node (target.node (mapDart dart))) =
      mapDart dart)
    (hcentral : EdgeCentral source target mapDart dart)
    (hnode : mapDart (source.node dart) = target.node (mapDart dart)) :
    mapDart (source.edge (source.node (source.node dart))) =
        target.edge (target.node (target.node (mapDart dart))) ∧
      EdgeCentral source target mapDart
        (source.edge (source.node (source.node dart))) := by
  have hmap := map_edge_node source target mapDart hinvariant hface
    (source.node dart) hnodeDomain
  have hmapSeed :
      mapDart (source.edge (source.node (source.node dart))) =
        target.edge (target.node (target.node (mapDart dart))) := by
    simpa only [hnode] using hmap
  have hnodeNode :
      mapDart (source.node (source.node dart)) =
        target.node (target.node (mapDart dart)) := by
    calc
      mapDart (source.node (source.node dart)) =
          mapDart (source.face (source.edge dart)) := by
        rw [face_edge_eq_node_node_of_cube source dart hsourceCube]
      _ = target.face (mapDart (source.edge dart)) :=
        hface (source.edge dart) hedge
      _ = target.face (target.edge (mapDart dart)) := by
        rw [hcentral]
      _ = target.node (target.node (mapDart dart)) :=
        face_edge_eq_node_node_of_cube target (mapDart dart) htargetCube
  refine ⟨hmapSeed, ?_⟩
  unfold EdgeCentral
  rw [hsourcePlain, hnodeNode, hmapSeed, htargetPlain]

/-- A partial face morphism commutes with two successive face steps whenever
its domain is face-invariant. -/
theorem map_face_face
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (source : FiniteHypermap Source) (target : FiniteHypermap Target)
    {domain : Source → Prop} (mapDart : Source → Target)
    (hinvariant : FaceInvariant source domain)
    (hface : ∀ dart, domain dart →
      mapDart (source.face dart) = target.face (mapDart dart))
    (dart : Source) (hdart : domain dart) :
    mapDart (source.face (source.face dart)) =
      target.face (target.face (mapDart dart)) := by
  have hnext : domain (source.face dart) := (hinvariant dart).2 hdart
  rw [hface _ hnext, hface _ hdart]

/-- Constructor-generic centrality propagation for a question rooted one node
step beyond an already central seed. -/
theorem questionWalk_node_edgeCentral
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (source : FiniteHypermap Source) (target : FiniteHypermap Target)
    {domain : Source → Prop} (mapDart : Source → Target)
    (hinvariant : FaceInvariant source domain)
    (hface : ∀ dart, domain dart →
      mapDart (source.face dart) = target.face (mapDart dart))
    (hsourcePlain : IsPlain source) (htargetPlain : IsPlain target)
    (hsourceCubic : IsCubicOn source domain)
    (htargetCubic : IsCubic target) :
    ∀ (question : Question) (seed : Source),
      domain seed →
      domain (source.edge seed) →
      EdgeCentral source target mapDart seed →
      (∀ dart ∈ questionWalkWith source.edge source.node
        (source.node seed) question, domain dart) →
      (questionWalkWith source.edge source.node
          (source.node seed) question).map mapDart =
        questionWalkWith target.edge target.node
          (target.node (mapDart seed)) question →
      ∀ dart ∈ questionWalkWith source.edge source.node
        (source.node seed) question,
          EdgeCentral source target mapDart dart := by
  intro question
  induction question with
  | empty => simp [questionWalkWith]
  | check arity =>
      intro seed hseed hedge hseedCentral hwalkDomain hwalkMap dart hdart
      have hnodeMap : mapDart (source.node seed) =
          target.node (mapDart seed) := by
        simpa [questionWalkWith] using hwalkMap
      have hdartEq : dart = source.node seed := by
        simpa [questionWalkWith] using hdart
      subst dart
      exact edgeCentral_node_of_map_node source target mapDart hinvariant
        hface seed hseed hnodeMap
  | left arity next ih =>
      intro seed hseed hedge hseedCentral hwalkDomain hwalkMap dart hdart
      let nextSeed := source.edge (source.node (source.node seed))
      let targetNextSeed :=
        target.edge (target.node (target.node (mapDart seed)))
      change
        mapDart (source.node seed) ::
            (questionWalkWith source.edge source.node
              (source.node nextSeed) next).map mapDart =
          target.node (mapDart seed) ::
            questionWalkWith target.edge target.node
              (target.node targetNextSeed) next at hwalkMap
      rcases List.cons.inj hwalkMap with ⟨hnodeMap, htailMap⟩
      have hnodeDomain : domain (source.node seed) :=
        hwalkDomain _ (by simp [questionWalkWith])
      have hseedCube := hsourceCubic seed hseed
      have hnextDomain : domain nextSeed := by
        exact domain_edge_node source hinvariant (source.node seed) hnodeDomain
      have hnextEdgeDomain : domain (source.edge nextSeed) := by
        dsimp [nextSeed]
        rw [hsourcePlain]
        exact domain_node_node_of_edge source hinvariant seed hedge hseedCube
      have hnextData := leftSeed_of_map_node source target mapDart hinvariant
        hface hsourcePlain htargetPlain seed hedge hnodeDomain hseedCube
        (htargetCubic (mapDart seed)) hseedCentral hnodeMap
      have hnextMap : mapDart nextSeed = targetNextSeed := hnextData.1
      have hnextCentral : EdgeCentral source target mapDart nextSeed :=
        hnextData.2
      have htailDomain : ∀ other ∈
          questionWalkWith source.edge source.node (source.node nextSeed) next,
          domain other := by
        intro other hother
        apply hwalkDomain other
        simp only [questionWalkWith, List.mem_cons]
        exact Or.inr hother
      have htailMap' :
          (questionWalkWith source.edge source.node
              (source.node nextSeed) next).map mapDart =
            questionWalkWith target.edge target.node
              (target.node (mapDart nextSeed)) next := by
        simpa only [hnextMap] using htailMap
      have htailCentral := ih nextSeed hnextDomain hnextEdgeDomain
        hnextCentral htailDomain htailMap'
      simp only [questionWalkWith, List.mem_cons] at hdart
      rcases hdart with rfl | hdart
      · exact edgeCentral_node_of_map_node source target mapDart hinvariant
          hface seed hseed hnodeMap
      · exact htailCentral dart hdart
  | right arity next ih =>
      intro seed hseed hedge hseedCentral hwalkDomain hwalkMap dart hdart
      let nextSeed := source.edge (source.node seed)
      let targetNextSeed := target.edge (target.node (mapDart seed))
      change
        mapDart (source.node seed) ::
            (questionWalkWith source.edge source.node
              (source.node nextSeed) next).map mapDart =
          target.node (mapDart seed) ::
            questionWalkWith target.edge target.node
              (target.node targetNextSeed) next at hwalkMap
      rcases List.cons.inj hwalkMap with ⟨hnodeMap, htailMap⟩
      have hnodeDomain : domain (source.node seed) :=
        hwalkDomain _ (by simp [questionWalkWith])
      have hnextDomain : domain nextSeed :=
        domain_edge_node source hinvariant seed hseed
      have hnextEdgeDomain : domain (source.edge nextSeed) := by
        dsimp [nextSeed]
        rw [hsourcePlain]
        exact hnodeDomain
      have hnextData := rightSeed_of_map_node source target mapDart hinvariant
        hface hsourcePlain htargetPlain seed hseed hnodeMap
      have hnextMap : mapDart nextSeed = targetNextSeed := hnextData.1
      have hnextCentral : EdgeCentral source target mapDart nextSeed :=
        hnextData.2
      have htailDomain : ∀ other ∈
          questionWalkWith source.edge source.node (source.node nextSeed) next,
          domain other := by
        intro other hother
        apply hwalkDomain other
        simp only [questionWalkWith, List.mem_cons]
        exact Or.inr hother
      have htailMap' :
          (questionWalkWith source.edge source.node
              (source.node nextSeed) next).map mapDart =
            questionWalkWith target.edge target.node
              (target.node (mapDart nextSeed)) next := by
        simpa only [hnextMap] using htailMap
      have htailCentral := ih nextSeed hnextDomain hnextEdgeDomain
        hnextCentral htailDomain htailMap'
      simp only [questionWalkWith, List.mem_cons] at hdart
      rcases hdart with rfl | hdart
      · exact edgeCentral_node_of_map_node source target mapDart hinvariant
          hface seed hseed hnodeMap
      · exact htailCentral dart hdart
  | fork arity left right ihLeft ihRight =>
      intro seed hseed hedge hseedCentral hwalkDomain hwalkMap dart hdart
      let leftSeed := source.edge (source.node (source.node seed))
      let targetLeftSeed :=
        target.edge (target.node (target.node (mapDart seed)))
      let rightSeed := source.edge (source.node seed)
      let targetRightSeed := target.edge (target.node (mapDart seed))
      let sourceLeftWalk :=
        questionWalkWith source.edge source.node (source.node leftSeed) left
      let sourceRightWalk :=
        questionWalkWith source.edge source.node (source.node rightSeed) right
      let targetLeftWalk :=
        questionWalkWith target.edge target.node
          (target.node targetLeftSeed) left
      let targetRightWalk :=
        questionWalkWith target.edge target.node
          (target.node targetRightSeed) right
      simp only [questionWalkWith, List.map_cons, List.map_append] at hwalkMap
      change
        mapDart (source.node seed) ::
            (sourceLeftWalk.map mapDart ++ sourceRightWalk.map mapDart) =
          target.node (mapDart seed) ::
            (targetLeftWalk ++ targetRightWalk) at hwalkMap
      rcases List.cons.inj hwalkMap with ⟨hnodeMap, htailMap⟩
      have hlength : (sourceLeftWalk.map mapDart).length =
          targetLeftWalk.length := by
        simp [sourceLeftWalk, targetLeftWalk, length_questionWalkWith]
      rcases (append_eq_append_iff_of_length_eq hlength).1 htailMap with
        ⟨hleftMap, hrightMap⟩
      have hnodeDomain : domain (source.node seed) :=
        hwalkDomain _ (by simp [questionWalkWith])
      have hseedCube := hsourceCubic seed hseed
      have hleftDomain : domain leftSeed :=
        domain_edge_node source hinvariant (source.node seed) hnodeDomain
      have hleftEdgeDomain : domain (source.edge leftSeed) := by
        dsimp [leftSeed]
        rw [hsourcePlain]
        exact domain_node_node_of_edge source hinvariant seed hedge hseedCube
      have hleftData := leftSeed_of_map_node source target mapDart hinvariant
        hface hsourcePlain htargetPlain seed hedge hnodeDomain hseedCube
        (htargetCubic (mapDart seed)) hseedCentral hnodeMap
      have hleftMapSeed : mapDart leftSeed = targetLeftSeed := hleftData.1
      have hleftCentral : EdgeCentral source target mapDart leftSeed :=
        hleftData.2
      have hrightDomain : domain rightSeed :=
        domain_edge_node source hinvariant seed hseed
      have hrightEdgeDomain : domain (source.edge rightSeed) := by
        dsimp [rightSeed]
        rw [hsourcePlain]
        exact hnodeDomain
      have hrightData := rightSeed_of_map_node source target mapDart hinvariant
        hface hsourcePlain htargetPlain seed hseed hnodeMap
      have hrightMapSeed : mapDart rightSeed = targetRightSeed := hrightData.1
      have hrightCentral : EdgeCentral source target mapDart rightSeed :=
        hrightData.2
      have hleftWalkDomain : ∀ other ∈ sourceLeftWalk, domain other := by
        intro other hother
        apply hwalkDomain other
        simp only [questionWalkWith, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl hother)
      have hrightWalkDomain : ∀ other ∈ sourceRightWalk, domain other := by
        intro other hother
        apply hwalkDomain other
        simp only [questionWalkWith, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr hother)
      have hleftMap' : sourceLeftWalk.map mapDart =
          questionWalkWith target.edge target.node
            (target.node (mapDart leftSeed)) left := by
        simpa only [hleftMapSeed] using hleftMap
      have hrightMap' : sourceRightWalk.map mapDart =
          questionWalkWith target.edge target.node
            (target.node (mapDart rightSeed)) right := by
        simpa only [hrightMapSeed] using hrightMap
      have hleftAll := ihLeft leftSeed hleftDomain hleftEdgeDomain
        hleftCentral hleftWalkDomain hleftMap'
      have hrightAll := ihRight rightSeed hrightDomain hrightEdgeDomain
        hrightCentral hrightWalkDomain hrightMap'
      simp only [questionWalkWith, List.mem_cons, List.mem_append] at hdart
      rcases hdart with rfl | hdart
      · exact edgeCentral_node_of_map_node source target mapDart hinvariant
          hface seed hseed hnodeMap
      · rcases hdart with hleft | hright
        · exact hleftAll dart hleft
        · exact hrightAll dart hright
  | skewLeft arity next ih =>
      intro seed hseed hedge hseedCentral hwalkDomain hwalkMap dart hdart
      let sourceZ :=
        source.node (qstepLWith source.edge source.node (source.node seed))
      let targetZ :=
        target.node (qstepLWith target.edge target.node
          (target.node (mapDart seed)))
      let nextSeed := source.edge sourceZ
      let targetNextSeed := target.edge targetZ
      change
        mapDart nextSeed ::
            (questionWalkWith source.edge source.node
              (source.node nextSeed) next).map mapDart =
          targetNextSeed ::
            questionWalkWith target.edge target.node
              (target.node targetNextSeed) next at hwalkMap
      rcases List.cons.inj hwalkMap with ⟨hnextMap, htailMap⟩
      have hnextDomain : domain nextSeed :=
        hwalkDomain _ (by
          simp [questionWalkWith, nextSeed, sourceZ, qstepLWith])
      have hfaceEdgeDomain : domain (source.face (source.edge seed)) :=
        (hinvariant (source.edge seed)).2 hedge
      have hfaceFaceEdgeDomain :
          domain (source.face (source.face (source.edge seed))) :=
        (hinvariant (source.face (source.edge seed))).2 hfaceEdgeDomain
      have hseedCube := hsourceCubic seed hseed
      have hfaceFaceCube := hsourceCubic
        (source.face (source.face (source.edge seed))) hfaceFaceEdgeDomain
      have hsourceZ : sourceZ =
          source.face (source.face (source.edge seed)) :=
        node_qstepL_node_eq_face_face_edge source hsourcePlain seed
          hseedCube hfaceFaceCube
      have htargetZ : targetZ =
          target.face (target.face (target.edge (mapDart seed))) :=
        node_qstepL_node_eq_face_face_edge target htargetPlain (mapDart seed)
          (htargetCubic (mapDart seed))
          (htargetCubic
            (target.face (target.face (target.edge (mapDart seed)))))
      have hmapZ : mapDart sourceZ = targetZ := by
        calc
          mapDart sourceZ =
              mapDart (source.face (source.face (source.edge seed))) := by
            rw [hsourceZ]
          _ = target.face (target.face (mapDart (source.edge seed))) :=
            map_face_face source target mapDart hinvariant hface
              (source.edge seed) hedge
          _ = target.face (target.face (target.edge (mapDart seed))) := by
            rw [hseedCentral]
          _ = targetZ := htargetZ.symm
      have hsourceZDomain : domain sourceZ := by
        rw [hsourceZ]
        exact hfaceFaceEdgeDomain
      have hnextEdgeDomain : domain (source.edge nextSeed) := by
        dsimp [nextSeed]
        rw [hsourcePlain]
        exact hsourceZDomain
      have hnextCentral : EdgeCentral source target mapDart nextSeed := by
        unfold EdgeCentral
        dsimp [nextSeed, targetNextSeed] at hnextMap ⊢
        rw [hsourcePlain, hmapZ, hnextMap, htargetPlain]
      have htailDomain : ∀ other ∈
          questionWalkWith source.edge source.node (source.node nextSeed) next,
          domain other := by
        intro other hother
        apply hwalkDomain other
        simp only [questionWalkWith, List.mem_cons]
        exact Or.inr hother
      have htailMap' :
          (questionWalkWith source.edge source.node
              (source.node nextSeed) next).map mapDart =
            questionWalkWith target.edge target.node
              (target.node (mapDart nextSeed)) next := by
        simpa only [hnextMap] using htailMap
      have htailAll := ih nextSeed hnextDomain hnextEdgeDomain
        hnextCentral htailDomain htailMap'
      simp only [questionWalkWith, List.mem_cons] at hdart
      change dart = nextSeed ∨
        dart ∈ questionWalkWith source.edge source.node
          (source.node nextSeed) next at hdart
      rcases hdart with rfl | hdart
      · exact hnextCentral
      · exact htailAll dart hdart
  | skewRight arity next ih =>
      intro seed hseed hedge hseedCentral hwalkDomain hwalkMap dart hdart
      let rightSeed := source.edge (source.node seed)
      let targetRightSeed := target.edge (target.node (mapDart seed))
      let head := source.node rightSeed
      let targetHead := target.node targetRightSeed
      let nextSeed := source.edge head
      let targetNextSeed := target.edge targetHead
      change
        mapDart head ::
            (questionWalkWith source.edge source.node
              (source.node nextSeed) next).map mapDart =
          targetHead ::
            questionWalkWith target.edge target.node
              (target.node targetNextSeed) next at hwalkMap
      rcases List.cons.inj hwalkMap with ⟨hheadMap, htailMap⟩
      have hheadDomain : domain head :=
        hwalkDomain _ (by
          simp [questionWalkWith, head, rightSeed, qstepRWith])
      have hrightDomain : domain rightSeed :=
        domain_edge_node source hinvariant seed hseed
      have hrightMap : mapDart rightSeed = targetRightSeed :=
        map_edge_node source target mapDart hinvariant hface seed hseed
      have hheadMap' : mapDart (source.node rightSeed) =
          target.node (mapDart rightSeed) := by
        simpa only [head, targetHead, hrightMap] using hheadMap
      have hheadCentral : EdgeCentral source target mapDart head := by
        exact edgeCentral_node_of_map_node source target mapDart hinvariant
          hface rightSeed hrightDomain hheadMap'
      have hnextDomain : domain nextSeed :=
        domain_edge_node source hinvariant rightSeed hrightDomain
      have hnextEdgeDomain : domain (source.edge nextSeed) := by
        dsimp [nextSeed]
        rw [hsourcePlain]
        exact hheadDomain
      have hnextCentral : EdgeCentral source target mapDart nextSeed :=
        edgeCentral_edge source target mapDart hsourcePlain htargetPlain
          head hheadCentral
      have hnextMap : mapDart nextSeed = targetNextSeed := by
        dsimp [nextSeed, targetNextSeed, targetHead]
        unfold EdgeCentral at hheadCentral
        simpa only [hheadMap] using hheadCentral
      have htailDomain : ∀ other ∈
          questionWalkWith source.edge source.node (source.node nextSeed) next,
          domain other := by
        intro other hother
        apply hwalkDomain other
        simp only [questionWalkWith, List.mem_cons]
        exact Or.inr hother
      have htailMap' :
          (questionWalkWith source.edge source.node
              (source.node nextSeed) next).map mapDart =
            questionWalkWith target.edge target.node
              (target.node (mapDart nextSeed)) next := by
        simpa only [hnextMap] using htailMap
      have htailAll := ih nextSeed hnextDomain hnextEdgeDomain
        hnextCentral htailDomain htailMap'
      simp only [questionWalkWith, List.mem_cons] at hdart
      change dart = head ∨
        dart ∈ questionWalkWith source.edge source.node
          (source.node nextSeed) next at hdart
      rcases hdart with rfl | hdart
      · exact hheadCentral
      · exact htailAll dart hdart

/-- A question accepted by the right-rooted checker has a right constructor
at its root. -/
theorem exists_right_of_questionIsRightRooted
    {question : Question} (hright : questionIsRightRooted question = true) :
    ∃ arity next, question = .right arity next := by
  cases question <;> simp [questionIsRightRooted] at hright
  exact ⟨_, _, rfl⟩

/-- In plain cubic hypermaps, an aligned right-rooted quiz traversal is
edge-central at every visited dart. -/
theorem quizWalk_edgeCentral_of_rightRooted
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (source : FiniteHypermap Source) (target : FiniteHypermap Target)
    {domain : Source → Prop} (mapDart : Source → Target)
    (hinvariant : FaceInvariant source domain)
    (hface : ∀ dart, domain dart →
      mapDart (source.face dart) = target.face (mapDart dart))
    (hsourcePlain : IsPlain source) (htargetPlain : IsPlain target)
    (hsourceCubic : IsCubicOn source domain)
    (htargetCubic : IsCubic target)
    (sourceRoot : Source) (targetRoot : Target) (quiz : Quiz)
    (hright : quizIsRightRooted quiz = true)
    (hwalkDomain : ∀ dart ∈
      quizWalkWith source.edge source.node sourceRoot quiz, domain dart)
    (hwalkMap :
      (quizWalkWith source.edge source.node sourceRoot quiz).map mapDart =
        quizWalkWith target.edge target.node targetRoot quiz) :
    ∀ dart ∈ quizWalkWith source.edge source.node sourceRoot quiz,
      EdgeCentral source target mapDart dart := by
  simp only [quizIsRightRooted, Bool.and_eq_true] at hright
  have hfirstRight : questionIsRightRooted quiz.first = true :=
    hright.1
  have hsecondRight : questionIsRightRooted quiz.second = true :=
    hright.2
  obtain ⟨firstArity, firstTail, hfirst⟩ :=
    exists_right_of_questionIsRightRooted hfirstRight
  obtain ⟨secondArity, secondTail, hsecond⟩ :=
    exists_right_of_questionIsRightRooted hsecondRight
  cases quiz with
  | mk first second =>
    simp only at hfirst hsecond
    subst first
    subst second
    simp only [quizWalkWith, List.map_append] at hwalkMap
    have hfirstLength :
        ((questionWalkWith source.edge source.node sourceRoot
          (.right firstArity firstTail)).map mapDart).length =
        (questionWalkWith target.edge target.node targetRoot
          (.right firstArity firstTail)).length := by
      simp [length_questionWalkWith]
    rcases (append_eq_append_iff_of_length_eq hfirstLength).1 hwalkMap with
      ⟨hfirstMap, hsecondMap⟩
    simp only [questionWalkWith, List.map_cons, List.cons.injEq] at hfirstMap hsecondMap
    rcases hfirstMap with ⟨hrootMap, hfirstTailMap⟩
    rcases hsecondMap with ⟨hedgeRootMap, hsecondTailMap⟩
    have hrootDomain : domain sourceRoot :=
      hwalkDomain sourceRoot (by
        simp [quizWalkWith, questionWalkWith])
    have hedgeRootDomain : domain (source.edge sourceRoot) :=
      hwalkDomain (source.edge sourceRoot) (by
        simp [quizWalkWith, questionWalkWith])
    have hsourceEdgeEdge :
        source.edge (source.edge sourceRoot) = sourceRoot :=
      hsourcePlain sourceRoot
    have htargetEdgeEdge :
        target.edge (target.edge targetRoot) = targetRoot :=
      htargetPlain targetRoot
    have hrootCentral : EdgeCentral source target mapDart sourceRoot := by
      unfold EdgeCentral
      simpa only [hrootMap] using hedgeRootMap
    have hedgeRootCentral :
        EdgeCentral source target mapDart (source.edge sourceRoot) :=
      edgeCentral_edge source target mapDart hsourcePlain htargetPlain
        sourceRoot hrootCentral
    have hfirstTailDomain : ∀ dart ∈
        questionWalkWith source.edge source.node
          (source.node (source.edge sourceRoot)) firstTail,
        domain dart := by
      intro dart hdart
      apply hwalkDomain dart
      simp only [quizWalkWith, questionWalkWith, List.mem_append,
        List.mem_cons]
      exact Or.inl (Or.inr hdart)
    have hsecondTailDomain : ∀ dart ∈
        questionWalkWith source.edge source.node
          (source.node sourceRoot) secondTail,
        domain dart := by
      intro dart hdart
      apply hwalkDomain dart
      simp only [quizWalkWith, questionWalkWith, List.mem_append,
        List.mem_cons]
      exact Or.inr (Or.inr (by
        simpa only [qstepRWith, hsourceEdgeEdge] using hdart))
    have hfirstTailMap' :
        (questionWalkWith source.edge source.node
          (source.node (source.edge sourceRoot)) firstTail).map mapDart =
        questionWalkWith target.edge target.node
          (target.node (mapDart (source.edge sourceRoot))) firstTail := by
      simpa only [qstepRWith, hedgeRootMap] using hfirstTailMap
    have hsecondTailMap' :
        (questionWalkWith source.edge source.node
          (source.node sourceRoot) secondTail).map mapDart =
        questionWalkWith target.edge target.node
          (target.node (mapDart sourceRoot)) secondTail := by
      simpa only [qstepRWith, hsourceEdgeEdge, htargetEdgeEdge, hrootMap] using
        hsecondTailMap
    have hfirstTailCentral := questionWalk_node_edgeCentral source target
      mapDart hinvariant hface hsourcePlain htargetPlain hsourceCubic
      htargetCubic firstTail (source.edge sourceRoot) hedgeRootDomain
      (by simpa only [hsourceEdgeEdge] using hrootDomain) hedgeRootCentral
      hfirstTailDomain hfirstTailMap'
    have hsecondTailCentral := questionWalk_node_edgeCentral source target
      mapDart hinvariant hface hsourcePlain htargetPlain hsourceCubic
      htargetCubic secondTail sourceRoot hrootDomain hedgeRootDomain
      hrootCentral hsecondTailDomain hsecondTailMap'
    intro dart hdart
    simp only [quizWalkWith, questionWalkWith, List.mem_append,
      List.mem_cons] at hdart
    rcases hdart with (rfl | hdart) | (rfl | hdart)
    · exact hrootCentral
    · exact hfirstTailCentral dart hdart
    · exact hedgeRootCentral
    · apply hsecondTailCentral dart
      simpa only [qstepRWith, hsourceEdgeEdge] using hdart

/-- One pair of entries occupying the same position in two traversals. -/
structure AlignedFaceAnchor
    {Source Target Class : Type*}
    (sourceWalk : List Source) (targetWalk : List Target)
    (sourceClass : Source → Class)
    (sourceArity : Source → Nat) (targetArity : Target → Nat)
    (face : Class) where
  source : Source
  target : Target
  aligned : (source, target) ∈ sourceWalk.zip targetWalk
  source_class : sourceClass source = face
  arity_eq : sourceArity source = targetArity target

/-- Equality of the arity words pairs every represented source class with an
aligned target entry of the same arity. -/
theorem exists_alignedFaceAnchor
    {Source Target Class : Type*}
    [DecidableEq Class]
    (sourceClass : Source → Class)
    (sourceArity : Source → Nat) (targetArity : Target → Nat) :
    ∀ {sourceWalk : List Source} {targetWalk : List Target} {face : Class},
      face ∈ sourceWalk.map sourceClass →
      sourceWalk.map sourceArity = targetWalk.map targetArity →
      Nonempty
        (AlignedFaceAnchor sourceWalk targetWalk sourceClass
          sourceArity targetArity face) := by
  intro sourceWalk
  induction sourceWalk with
  | nil => simp
  | cons source rest ih =>
      intro targetWalk face hface harities
      cases targetWalk with
      | nil => simp at harities
      | cons target targets =>
          simp only [List.map_cons, List.cons.injEq] at harities
          rcases harities with ⟨hhead, htail⟩
          simp only [List.mem_map, List.mem_cons] at hface
          rcases hface with ⟨entry, hentry, rfl⟩
          rcases hentry with rfl | hentry
          · exact ⟨⟨entry, target, by simp, rfl, hhead⟩⟩
          · obtain ⟨anchor⟩ := ih
              (List.mem_map.2 ⟨entry, hentry, rfl⟩) htail
            exact ⟨⟨anchor.source, anchor.target, by
              simp only [List.zip_cons_cons, List.mem_cons]
              exact Or.inr anchor.aligned,
              anchor.source_class, anchor.arity_eq⟩⟩

/-- In a traversal with no repeated source face, an aligned pair is uniquely
determined by its source face class. -/
theorem AlignedFaceAnchor.eq_of_sourceClass_nodup
    {Source Target Class : Type*}
    [DecidableEq Source] [DecidableEq Target] [DecidableEq Class]
    {sourceWalk : List Source} {targetWalk : List Target}
    {sourceClass : Source → Class}
    {sourceArity : Source → Nat} {targetArity : Target → Nat}
    {face : Class}
    (hnodup : (sourceWalk.map sourceClass).Nodup)
    (left right : AlignedFaceAnchor sourceWalk targetWalk sourceClass
      sourceArity targetArity face) :
    left.source = right.source ∧ left.target = right.target := by
  induction sourceWalk generalizing targetWalk with
  | nil =>
      have : False := by simpa using left.aligned
      contradiction
  | cons source rest ih =>
      cases targetWalk with
      | nil =>
          have : False := by simpa using left.aligned
          contradiction
      | cons target targets =>
          simp only [List.map_cons, List.nodup_cons] at hnodup
          rcases hnodup with ⟨hnotmem, htailNodup⟩
          have hleftCases :
              (left.source, left.target) = (source, target) ∨
                (left.source, left.target) ∈ rest.zip targets := by
            simpa using left.aligned
          have hrightCases :
              (right.source, right.target) = (source, target) ∨
                (right.source, right.target) ∈ rest.zip targets := by
            simpa using right.aligned
          rcases hleftCases with hleft | hleft <;>
            rcases hrightCases with hright | hright
          · exact ⟨(congrArg Prod.fst hleft).trans
                (congrArg Prod.fst hright).symm,
              (congrArg Prod.snd hleft).trans
                (congrArg Prod.snd hright).symm⟩
          · have hleftSource : left.source = source := congrArg Prod.fst hleft
            exfalso
            apply hnotmem
            apply List.mem_map.2
            exact ⟨right.source, (List.of_mem_zip hright).1, by
              calc
                sourceClass right.source = face := right.source_class
                _ = sourceClass source := by
                  rw [← left.source_class, hleftSource]⟩
          · have hrightSource : right.source = source := congrArg Prod.fst hright
            exfalso
            apply hnotmem
            apply List.mem_map.2
            exact ⟨left.source, (List.of_mem_zip hleft).1, by
              calc
                sourceClass left.source = face := left.source_class
                _ = sourceClass source := by
                  rw [← right.source_class, hrightSource]⟩
          · let leftTail : AlignedFaceAnchor rest targets sourceClass
                sourceArity targetArity face :=
              ⟨left.source, left.target, hleft,
                left.source_class, left.arity_eq⟩
            let rightTail : AlignedFaceAnchor rest targets sourceClass
                sourceArity targetArity face :=
              ⟨right.source, right.target, hright,
                right.source_class, right.arity_eq⟩
            exact ih htailNodup leftTail rightTail

/-- Equality of mapped lists gives equality at every aligned pair. -/
theorem eq_of_mem_zip_of_map_eq
    {Source Target Value : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (sourceValue : Source → Value) (targetValue : Target → Value) :
    ∀ {sourceWalk : List Source} {targetWalk : List Target}
      {source : Source} {target : Target},
      (source, target) ∈ sourceWalk.zip targetWalk →
      sourceWalk.map sourceValue = targetWalk.map targetValue →
      sourceValue source = targetValue target := by
  intro sourceWalk
  induction sourceWalk with
  | nil => simp
  | cons head rest ih =>
      intro targetWalk source target haligned hmap
      cases targetWalk with
      | nil => simp at haligned
      | cons targetHead targets =>
          simp only [List.zip_cons_cons, List.mem_cons] at haligned
          simp only [List.map_cons, List.cons.injEq] at hmap
          rcases hmap with ⟨hhead, htail⟩
          rcases haligned with haligned | haligned
          · have hsource : source = head := congrArg Prod.fst haligned
            have htarget : target = targetHead := congrArg Prod.snd haligned
            simpa [hsource, htarget] using hhead
          · exact ih haligned htail

/-- A pointwise equality on aligned entries, together with equal lengths,
reconstructs equality of the complete mapped lists. -/
theorem map_eq_of_forall_mem_zip
    {Source Value : Type*}
    [DecidableEq Source] [DecidableEq Value]
    (sourceValue : Source → Value) :
    ∀ {sourceWalk : List Source} {targetWalk : List Value},
      sourceWalk.length = targetWalk.length →
      (∀ source target,
        (source, target) ∈ sourceWalk.zip targetWalk →
          sourceValue source = target) →
      sourceWalk.map sourceValue = targetWalk := by
  intro sourceWalk
  induction sourceWalk with
  | nil =>
      intro targetWalk hlength hpoint
      cases targetWalk with
      | nil => rfl
      | cons target targets => simp at hlength
  | cons source rest ih =>
      intro targetWalk hlength hpoint
      cases targetWalk with
      | nil => simp at hlength
      | cons target targets =>
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          simp only [List.map_cons, List.cons.injEq]
          constructor
          · apply hpoint source target
            simp
          · apply ih hlength
            intro other targetOther haligned
            apply hpoint other targetOther
            simp only [List.zip_cons_cons, List.mem_cons]
            exact Or.inr haligned

/-- Anchored cycle transport sends its source anchor to its target anchor. -/
theorem cycleTransport_root
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (source : Equiv.Perm Source) (target : Equiv.Perm Target)
    (sourceRoot : Source) (targetRoot : Target)
    (hcard : (permutationOrbit source sourceRoot).card =
      (permutationOrbit target targetRoot).card) :
    cycleTransport source target sourceRoot targetRoot hcard sourceRoot
        (mem_permutationOrbit_self source sourceRoot) = targetRoot := by
  let exponent := cycleExponent source sourceRoot sourceRoot
    (mem_permutationOrbit_self source sourceRoot)
  have hsourcePower : (source ^ exponent) sourceRoot = sourceRoot :=
    cycleExponent_spec source sourceRoot sourceRoot
      (mem_permutationOrbit_self source sourceRoot)
  have hsourceMod : exponent ≡ 0
      [MOD (permutationOrbit source sourceRoot).card] :=
    ((permutationOrbit_isCycleOn source sourceRoot).pow_apply_eq_pow_apply
      (mem_permutationOrbit_self source sourceRoot)).1 (by
        simpa using hsourcePower)
  have htargetMod : exponent ≡ 0
      [MOD (permutationOrbit target targetRoot).card] := by
    simpa [hcard] using hsourceMod
  have htargetPower : (target ^ exponent) targetRoot = targetRoot := by
    have :=
      ((permutationOrbit_isCycleOn target targetRoot).pow_apply_eq_pow_apply
        (mem_permutationOrbit_self target targetRoot)).2 htargetMod
    simpa using this
  exact htargetPower

variable {code : ClassicalCertificateReductionMetadata.Code}
  {root : Nat} {quiz : Quiz}

/-- Executable edge-involution condition on a materialized configuration. -/
def RawPlain (code : ClassicalCertificateReductionMetadata.Code) : Prop :=
  ∀ dart : Fin code.hypermap.dartCount,
    rawEdge code (rawEdge code dart.val) = dart.val

/-- Executable cubicity condition on the faces belonging to the configuration
kernel.  Boundary vertices may have smaller degree in a configuration. -/
def RawCubicOnKernel
    (code : ClassicalCertificateReductionMetadata.Code) : Prop :=
  ∀ dart : Fin code.hypermap.dartCount,
    rawFaceClass code dart.val ∈ kernelFaceClasses code →
      rawNode code (rawNode code (rawNode code dart.val)) = dart.val

instance (code : ClassicalCertificateReductionMetadata.Code) :
    Decidable (RawPlain code) := by
  unfold RawPlain
  infer_instance

instance (code : ClassicalCertificateReductionMetadata.Code) :
    Decidable (RawCubicOnKernel code) := by
  unfold RawCubicOnKernel
  infer_instance

/-- Reflected local geometry needed by the recursive quiz traversal. -/
structure SourceGeometryValid
    (code : ClassicalCertificateReductionMetadata.Code) : Prop where
  plain : RawPlain code
  cubicOnKernel : RawCubicOnKernel code

/-- Boolean checker for the source geometry used by quiz preembeddings. -/
def sourceGeometryChecker
    (code : ClassicalCertificateReductionMetadata.Code) : Bool :=
  decide (RawPlain code ∧ RawCubicOnKernel code)

theorem sourceGeometryValid_of_checker_true
    (code : ClassicalCertificateReductionMetadata.Code)
    (hchecker : sourceGeometryChecker code = true) :
    SourceGeometryValid code := by
  have hconditions : RawPlain code ∧ RawCubicOnKernel code :=
    Bool.of_decide_true (by
      simpa [sourceGeometryChecker] using hchecker)
  exact ⟨hconditions.1, hconditions.2⟩

theorem cf001_sourceGeometry_checker :
    sourceGeometryChecker cf001Code = true := by decide

set_option maxRecDepth 10000 in
theorem cf003_sourceGeometry_checker :
    sourceGeometryChecker cf003Code = true := by decide

set_option maxRecDepth 10000 in
theorem cf006_sourceGeometry_checker :
    sourceGeometryChecker cf006Code = true := by decide

set_option maxRecDepth 10000 in
theorem cf009_sourceGeometry_checker :
    sourceGeometryChecker cf009Code = true := by decide

theorem cf024_sourceGeometry_checker :
    sourceGeometryChecker cf024Code = true := by decide

set_option maxRecDepth 10000 in
theorem cf139_sourceGeometry_checker :
    sourceGeometryChecker cf139Code = true := by decide

set_option maxRecDepth 10000 in
theorem cf182_sourceGeometry_checker :
    sourceGeometryChecker cf182Code = true := by decide

/-- The semantic source traversal has exactly the checked list of face-class
numbers. -/
theorem map_val_sourceWalk_faceClass_eq_visited
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code) :
    (((quizWalkWith
        (checkedHypermap valid.partitionValid).edge
        (checkedHypermap valid.partitionValid).node
        (⟨root, quizValid.rootInRange⟩ : Fin code.hypermap.dartCount) quiz).map
      (faceClass valid.partitionValid)).map Fin.val) =
      visitedFaceClasses code root quiz := by
  rw [List.map_map]
  unfold visitedFaceClasses
  rw [← map_val_quizWalk_checked_eq_raw valid
    (⟨root, quizValid.rootInRange⟩ : Fin code.hypermap.dartCount) quiz]
  rw [List.map_map]
  apply List.map_congr_left
  intro dart hdart
  rfl

/-- Face simplicity checked on raw class numbers is face simplicity of the
standard materialized source hypermap. -/
theorem sourceWalk_faceClass_nodup
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code) :
    ((quizWalkWith
        (checkedHypermap valid.partitionValid).edge
        (checkedHypermap valid.partitionValid).node
        (⟨root, quizValid.rootInRange⟩ : Fin code.hypermap.dartCount) quiz).map
      (faceClass valid.partitionValid)).Nodup := by
  apply List.Nodup.of_map Fin.val
  rw [map_val_sourceWalk_faceClass_eq_visited quizValid valid]
  exact quizValid.simpleFaces

/-- The checked kernel-class list is the standard complement of the face band
of the materialized outer ring. -/
theorem faceKernel_iff_faceClass_mem_kernelFaceClasses
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (dart : Fin code.hypermap.dartCount) :
    FaceKernel (checkedHypermap valid.partitionValid)
        (ClassicalCertificateReductionMetadata.ring code) dart ↔
      (faceClass valid.partitionValid dart).val ∈
        kernelFaceClasses code := by
  let H := checkedHypermap valid.partitionValid
  have hband : FaceBand H (ClassicalCertificateReductionMetadata.ring code) dart ↔
      ∃ raw ∈ code.ringValues,
        rawFaceClass code raw = (faceClass valid.partitionValid dart).val := by
    constructor
    · rintro ⟨anchor, hanchor, hsame⟩
      refine ⟨anchor.val, ?_, ?_⟩
      · have : anchor.val ∈
        (ClassicalCertificateReductionMetadata.ring code).map Fin.val :=
          List.mem_map_of_mem (f := Fin.val) hanchor
        rwa [valid.ring_map_val] at this
      · have hclass := (faceClass_eq_iff_sameCycle valid dart anchor).2 hsame
        simpa [rawFaceClass, faceClass] using congrArg Fin.val hclass.symm
    · rintro ⟨raw, hraw, hclass⟩
      have hraw' : raw ∈
          (ClassicalCertificateReductionMetadata.ring code).map Fin.val := by
        rwa [valid.ring_map_val]
      rcases List.mem_map.1 hraw' with ⟨anchor, hanchor, hvalue⟩
      refine ⟨anchor, hanchor, ?_⟩
      apply (faceClass_eq_iff_sameCycle valid dart anchor).1
      apply Fin.ext
      simpa [rawFaceClass, faceClass, ← hvalue] using hclass.symm
  rw [FaceKernel, hband]
  simp only [kernelFaceClasses, List.mem_filter, List.mem_range,
    Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq]
  constructor
  · intro hnone
    refine ⟨valid.partitionValid.classInRange dart, ?_⟩
    intro raw hraw hclass
    exact hnone ⟨raw, hraw, hclass⟩
  · rintro ⟨_, hnone⟩ ⟨raw, hraw, hclass⟩
    exact hnone raw hraw hclass

/-- The reflected edge condition is plainness of the checked source
hypermap. -/
theorem SourceGeometryValid.isPlain
    (geometry : SourceGeometryValid code)
    (valid : ClassicalCertificateReductionMetadata.Valid code) :
    IsPlain (checkedHypermap valid.partitionValid) := by
  intro dart
  apply Fin.ext
  simp only [checkedHypermap_edge_val valid]
  exact geometry.plain dart

/-- The reflected kernel condition is cubicity on the semantic face
kernel. -/
theorem SourceGeometryValid.isCubicOnFaceKernel
    (geometry : SourceGeometryValid code)
    (valid : ClassicalCertificateReductionMetadata.Valid code) :
    IsCubicOn (checkedHypermap valid.partitionValid)
      (FaceKernel (checkedHypermap valid.partitionValid)
        (ClassicalCertificateReductionMetadata.ring code)) := by
  intro dart hdart
  apply Fin.ext
  simp only [checkedHypermap_node_val valid]
  apply geometry.cubicOnKernel dart
  exact (faceKernel_iff_faceClass_mem_kernelFaceClasses valid dart).1 hdart

/-- Kernel coverage in the raw checker is coverage by the semantic source
traversal, face for face. -/
theorem faceClass_mem_sourceWalk_iff_kernel
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (face : Fin code.partition.faceCount) :
    face ∈ (quizWalkWith
        (checkedHypermap valid.partitionValid).edge
        (checkedHypermap valid.partitionValid).node
        (⟨root, quizValid.rootInRange⟩ : Fin code.hypermap.dartCount) quiz).map
          (faceClass valid.partitionValid) ↔
      face.val ∈ kernelFaceClasses code := by
  let sourceClasses :=
    (quizWalkWith
      (checkedHypermap valid.partitionValid).edge
      (checkedHypermap valid.partitionValid).node
      (⟨root, quizValid.rootInRange⟩ : Fin code.hypermap.dartCount) quiz).map
        (faceClass valid.partitionValid)
  have hvalues : sourceClasses.map Fin.val = visitedFaceClasses code root quiz :=
    map_val_sourceWalk_faceClass_eq_visited quizValid valid
  have hvisited : face.val ∈ visitedFaceClasses code root quiz ↔
      face.val ∈ kernelFaceClasses code := by
    constructor
    · intro hface
      have hfinset : face.val ∈
          (visitedFaceClasses code root quiz).toFinset := by simpa using hface
      rw [quizValid.coversKernel] at hfinset
      simpa using hfinset
    · intro hface
      have hfinset : face.val ∈ (kernelFaceClasses code).toFinset := by
        simpa using hface
      rw [← quizValid.coversKernel] at hfinset
      simpa using hfinset
  constructor
  · intro hface
    apply hvisited.1
    rw [← hvalues]
    exact List.mem_map_of_mem (f := Fin.val) hface
  · intro hface
    have hvalue : face.val ∈ sourceClasses.map Fin.val := by
      rw [hvalues]
      exact hvisited.2 hface
    rcases List.mem_map.1 hvalue with ⟨other, hother, heq⟩
    have : other = face := Fin.ext heq
    change face ∈ sourceClasses
    rw [← this]
    exact hother

/-- Semantic quiz traversal in a checked catalogue source. -/
noncomputable def sourceQuizWalk
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code) :
    List (Fin code.hypermap.dartCount) :=
  quizWalkWith
    (checkedHypermap valid.partitionValid).edge
    (checkedHypermap valid.partitionValid).node
    (⟨root, quizValid.rootInRange⟩ : Fin code.hypermap.dartCount) quiz

/-- Semantic quiz traversal in an arbitrary target hypermap. -/
def targetQuizWalk
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target) (quiz : Quiz) :
    List Target :=
  quizWalkWith target.edge target.node targetRoot quiz

/-- For a kernel face, choose the unique aligned source/target traversal pair.
Existence comes from kernel coverage and equality of the two arity words. -/
noncomputable def kernelAlignedAnchor
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz)
    (face : Fin code.partition.faceCount)
    (hface : face.val ∈ kernelFaceClasses code) :
    AlignedFaceAnchor
      (sourceQuizWalk quizValid valid)
      (targetQuizWalk target targetRoot quiz)
      (faceClass valid.partitionValid)
      (hypermapFaceArity (checkedHypermap valid.partitionValid))
      (hypermapFaceArity target) face := by
  classical
  apply Classical.choice
  apply exists_alignedFaceAnchor
    (faceClass valid.partitionValid)
    (hypermapFaceArity (checkedHypermap valid.partitionValid))
    (hypermapFaceArity target)
  · exact (faceClass_mem_sourceWalk_iff_kernel quizValid valid face).2 hface
  · exact (quizValid.hypermapQuizFits valid).symm.trans targetFits

/-- Source anchor selected by a face class, with a harmless representative
fallback outside the kernel. -/
noncomputable def sourceAnchorForClass
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz)
    (face : Fin code.partition.faceCount) :
    Fin code.hypermap.dartCount :=
  if hface : face.val ∈ kernelFaceClasses code then
    (kernelAlignedAnchor quizValid valid target targetRoot targetFits
      face hface).source
  else faceRepresentative valid.partitionValid face

/-- Target anchor selected at the same quiz position as the source anchor. -/
noncomputable def targetAnchorForClass
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz)
    (face : Fin code.partition.faceCount) : Target :=
  if hface : face.val ∈ kernelFaceClasses code then
    (kernelAlignedAnchor quizValid valid target targetRoot targetFits
      face hface).target
  else targetRoot

@[simp] theorem sourceAnchorForClass_of_mem
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz)
    (face : Fin code.partition.faceCount)
    (hface : face.val ∈ kernelFaceClasses code) :
    sourceAnchorForClass quizValid valid target targetRoot targetFits face =
      (kernelAlignedAnchor quizValid valid target targetRoot targetFits
        face hface).source := by
  simp [sourceAnchorForClass, hface]

@[simp] theorem targetAnchorForClass_of_mem
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz)
    (face : Fin code.partition.faceCount)
    (hface : face.val ∈ kernelFaceClasses code) :
    targetAnchorForClass quizValid valid target targetRoot targetFits face =
      (kernelAlignedAnchor quizValid valid target targetRoot targetFits
        face hface).target := by
  simp [targetAnchorForClass, hface]

/-- A checked source quiz and a fitting target quiz canonically pair every
kernel face with an equal-length target face. -/
noncomputable def faceAnchorAssignment
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz) :
    FaceAnchorAssignment
      (checkedHypermap valid.partitionValid).face target.face
      (FaceKernel (checkedHypermap valid.partitionValid)
        (ClassicalCertificateReductionMetadata.ring code)) where
  sourceAnchor := fun dart =>
    sourceAnchorForClass quizValid valid target targetRoot targetFits
      (faceClass valid.partitionValid dart)
  targetAnchor := fun dart =>
    targetAnchorForClass quizValid valid target targetRoot targetFits
      (faceClass valid.partitionValid dart)
  domain_face := by
    intro dart hdart
    exact (faceKernel_face_iff
      (checkedHypermap valid.partitionValid)
      (ClassicalCertificateReductionMetadata.ring code) dart).2 hdart
  source_mem := by
    intro dart hdart
    have hface :=
      (faceKernel_iff_faceClass_mem_kernelFaceClasses valid dart).1
        hdart
    let anchor := kernelAlignedAnchor quizValid valid target targetRoot
      targetFits (faceClass valid.partitionValid dart) hface
    rw [sourceAnchorForClass_of_mem quizValid valid target targetRoot
      targetFits (faceClass valid.partitionValid dart) hface]
    simp only [permutationOrbit, Finset.mem_filter, Finset.mem_univ, true_and]
    apply (faceClass_eq_iff_sameCycle valid anchor.source dart).1
    exact anchor.source_class
  orbit_card_eq := by
    intro dart hdart
    have hface :=
      (faceKernel_iff_faceClass_mem_kernelFaceClasses valid dart).1
        hdart
    let anchor := kernelAlignedAnchor quizValid valid target targetRoot
      targetFits (faceClass valid.partitionValid dart) hface
    rw [sourceAnchorForClass_of_mem quizValid valid target targetRoot
      targetFits (faceClass valid.partitionValid dart) hface]
    rw [targetAnchorForClass_of_mem quizValid valid target targetRoot
      targetFits (faceClass valid.partitionValid dart) hface]
    exact anchor.arity_eq
  sourceAnchor_face := by
    intro dart _hdart
    have hclass : faceClass valid.partitionValid
          ((checkedHypermap valid.partitionValid).face dart) =
        faceClass valid.partitionValid dart := by
      simpa using faceClass_face valid.partitionValid dart
    rw [hclass]
  targetAnchor_face := by
    intro dart _hdart
    have hclass : faceClass valid.partitionValid
          ((checkedHypermap valid.partitionValid).face dart) =
        faceClass valid.partitionValid dart := by
      simpa using faceClass_face valid.partitionValid dart
    rw [hclass]

/-- The total map underlying the checked quiz face transport.  Only its values
on the standard face kernel are subsequently used. -/
noncomputable def quizFaceMap
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz) :
    Fin code.hypermap.dartCount → Target :=
  (faceAnchorAssignment quizValid valid target targetRoot targetFits).map

/-- The checked quiz map commutes with face successor throughout the source
kernel. -/
theorem quizFaceMap_face
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz)
    (dart : Fin code.hypermap.dartCount)
    (hdart : FaceKernel (checkedHypermap valid.partitionValid)
      (ClassicalCertificateReductionMetadata.ring code) dart) :
    quizFaceMap quizValid valid target targetRoot targetFits
        ((checkedHypermap valid.partitionValid).face dart) =
      target.face
        (quizFaceMap quizValid valid target targetRoot targetFits dart) := by
  exact (faceAnchorAssignment quizValid valid target targetRoot targetFits).map_source
    dart hdart

/-- The checked quiz map preserves every kernel-face arity. -/
theorem quizFaceMap_arity
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz)
    (dart : Fin code.hypermap.dartCount)
    (hdart : FaceKernel (checkedHypermap valid.partitionValid)
      (ClassicalCertificateReductionMetadata.ring code) dart) :
    hypermapFaceArity (checkedHypermap valid.partitionValid) dart =
      hypermapFaceArity target
        (quizFaceMap quizValid valid target targetRoot targetFits dart) := by
  exact (faceAnchorAssignment quizValid valid target targetRoot targetFits).orbit_card_map_eq
    dart hdart

/-- The first two fields of the classical preembedding are therefore fully
discharged for every checked catalogue quiz. -/
noncomputable def quizFacialPreembedding
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz) :
    FacialPreembedding
      (checkedHypermap valid.partitionValid) target
      (FaceKernel (checkedHypermap valid.partitionValid)
        (ClassicalCertificateReductionMetadata.ring code))
      (quizFaceMap quizValid valid target targetRoot targetFits) where
  face := quizFaceMap_face quizValid valid target targetRoot targetFits
  arity := quizFaceMap_arity quizValid valid target targetRoot targetFits

/-- Every dart visited by the source quiz lies in the standard source kernel. -/
theorem faceKernel_of_mem_sourceQuizWalk
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {dart : Fin code.hypermap.dartCount}
    (hdart : dart ∈ sourceQuizWalk quizValid valid) :
    FaceKernel (checkedHypermap valid.partitionValid)
      (ClassicalCertificateReductionMetadata.ring code) dart := by
  apply (faceKernel_iff_faceClass_mem_kernelFaceClasses valid dart).2
  apply (faceClass_mem_sourceWalk_iff_kernel quizValid valid
    (faceClass valid.partitionValid dart)).1
  exact List.mem_map_of_mem (f := faceClass valid.partitionValid) hdart

/-- The source and target quiz traversals have equal arity words pointwise. -/
theorem source_target_arity_map_eq
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz) :
    (sourceQuizWalk quizValid valid).map
        (hypermapFaceArity (checkedHypermap valid.partitionValid)) =
      (targetQuizWalk target targetRoot quiz).map
        (hypermapFaceArity target) :=
  (quizValid.hypermapQuizFits valid).symm.trans targetFits

/-- Any aligned source/target pair is the pair selected for its source face. -/
theorem kernelAlignedAnchor_eq_of_aligned
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz)
    {source : Fin code.hypermap.dartCount} {targetDart : Target}
    (haligned : (source, targetDart) ∈
      (sourceQuizWalk quizValid valid).zip
        (targetQuizWalk target targetRoot quiz)) :
    let hkernel := faceKernel_of_mem_sourceQuizWalk quizValid valid
      (List.of_mem_zip haligned).1
    let hface :=
      (faceKernel_iff_faceClass_mem_kernelFaceClasses valid source).1 hkernel
    let chosen := kernelAlignedAnchor quizValid valid target targetRoot
      targetFits (faceClass valid.partitionValid source) hface
    chosen.source = source ∧ chosen.target = targetDart := by
  let hkernel := faceKernel_of_mem_sourceQuizWalk quizValid valid
    (List.of_mem_zip haligned).1
  let hface :=
    (faceKernel_iff_faceClass_mem_kernelFaceClasses valid source).1 hkernel
  let chosen := kernelAlignedAnchor quizValid valid target targetRoot
    targetFits (faceClass valid.partitionValid source) hface
  let actual : AlignedFaceAnchor
      (sourceQuizWalk quizValid valid)
      (targetQuizWalk target targetRoot quiz)
      (faceClass valid.partitionValid)
      (hypermapFaceArity (checkedHypermap valid.partitionValid))
      (hypermapFaceArity target)
      (faceClass valid.partitionValid source) :=
    ⟨source, targetDart, haligned, rfl,
      eq_of_mem_zip_of_map_eq
        (hypermapFaceArity (checkedHypermap valid.partitionValid))
        (hypermapFaceArity target) haligned
        (source_target_arity_map_eq quizValid valid target targetRoot
          targetFits)⟩
  exact AlignedFaceAnchor.eq_of_sourceClass_nodup
    (sourceWalk_faceClass_nodup quizValid valid) chosen actual

/-- The canonical face map sends every source quiz representative to the
target representative occupying the same traversal position. -/
theorem quizFaceMap_eq_of_aligned
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz)
    {source : Fin code.hypermap.dartCount} {targetDart : Target}
    (haligned : (source, targetDart) ∈
      (sourceQuizWalk quizValid valid).zip
        (targetQuizWalk target targetRoot quiz)) :
    quizFaceMap quizValid valid target targetRoot targetFits source =
      targetDart := by
  have hsourceMem := (List.of_mem_zip haligned).1
  have hkernel := faceKernel_of_mem_sourceQuizWalk quizValid valid hsourceMem
  have hface :=
    (faceKernel_iff_faceClass_mem_kernelFaceClasses valid source).1 hkernel
  let chosen := kernelAlignedAnchor quizValid valid target targetRoot
    targetFits (faceClass valid.partitionValid source) hface
  have hchosen := kernelAlignedAnchor_eq_of_aligned quizValid valid target
    targetRoot targetFits haligned
  have hsourceAnchor :
      (faceAnchorAssignment quizValid valid target targetRoot targetFits).sourceAnchor
          source = source := by
    change sourceAnchorForClass quizValid valid target targetRoot targetFits
      (faceClass valid.partitionValid source) = source
    rw [sourceAnchorForClass_of_mem quizValid valid target targetRoot
      targetFits (faceClass valid.partitionValid source) hface]
    exact hchosen.1
  have htargetAnchor :
      (faceAnchorAssignment quizValid valid target targetRoot targetFits).targetAnchor
          source = targetDart := by
    change targetAnchorForClass quizValid valid target targetRoot targetFits
      (faceClass valid.partitionValid source) = targetDart
    rw [targetAnchorForClass_of_mem quizValid valid target targetRoot
      targetFits (faceClass valid.partitionValid source) hface]
    exact hchosen.2
  unfold quizFaceMap FaceAnchorAssignment.map
  rw [dif_pos hkernel]
  simpa only [hsourceAnchor, htargetAnchor] using
    (cycleTransport_root
      (checkedHypermap valid.partitionValid).face target.face
      source targetDart
      (by simpa only [hsourceAnchor, htargetAnchor] using
        (faceAnchorAssignment quizValid valid target targetRoot
          targetFits).orbit_card_eq source hkernel))

/-- Consequently the canonical map carries the entire source traversal to the
target traversal, not merely their arity labels. -/
theorem map_quizFaceMap_sourceQuizWalk
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz) :
    (sourceQuizWalk quizValid valid).map
        (quizFaceMap quizValid valid target targetRoot targetFits) =
      targetQuizWalk target targetRoot quiz := by
  apply map_eq_of_forall_mem_zip
  · simp [sourceQuizWalk, targetQuizWalk, quizWalkWith,
      length_questionWalkWith]
  · intro source targetDart haligned
    exact quizFaceMap_eq_of_aligned quizValid valid target targetRoot
      targetFits haligned

/-- Checked source geometry and an aligned right-rooted quiz force the
canonical face map to be edge-central on every traversal representative. -/
theorem quizFaceMap_sourceWalk_edgeCentral
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (geometry : SourceGeometryValid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz)
    (htargetPlain : IsPlain target) (htargetCubic : IsCubic target) :
    ∀ source ∈ sourceQuizWalk quizValid valid,
      EdgeCentral (checkedHypermap valid.partitionValid) target
        (quizFaceMap quizValid valid target targetRoot targetFits) source := by
  apply quizWalk_edgeCentral_of_rightRooted
    (checkedHypermap valid.partitionValid) target
    (quizFaceMap quizValid valid target targetRoot targetFits)
  · intro dart
    exact faceKernel_face_iff (checkedHypermap valid.partitionValid)
      (ClassicalCertificateReductionMetadata.ring code) dart
  · exact quizFaceMap_face quizValid valid target targetRoot targetFits
  · exact geometry.isPlain valid
  · exact htargetPlain
  · exact geometry.isCubicOnFaceKernel valid
  · exact htargetCubic
  · exact quizValid.rightRooted
  · intro dart hdart
    exact faceKernel_of_mem_sourceQuizWalk quizValid valid hdart
  · exact map_quizFaceMap_sourceQuizWalk quizValid valid target targetRoot
      targetFits

/-- Edge-centrality on the source traversal already covers every kernel face,
because that traversal is its face transversal. -/
theorem quizFaceMap_cover_of_sourceWalk_edgeCentral
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz)
    (hcentral : ∀ source ∈ sourceQuizWalk quizValid valid,
      EdgeCentral (checkedHypermap valid.partitionValid) target
        (quizFaceMap quizValid valid target targetRoot targetFits) source)
    (dart : Fin code.hypermap.dartCount)
    (hdart : FaceKernel (checkedHypermap valid.partitionValid)
      (ClassicalCertificateReductionMetadata.ring code) dart) :
    FaceClosure (checkedHypermap valid.partitionValid)
      (EdgeCentral (checkedHypermap valid.partitionValid) target
        (quizFaceMap quizValid valid target targetRoot targetFits)) dart := by
  have hface :=
    (faceKernel_iff_faceClass_mem_kernelFaceClasses valid dart).1 hdart
  have hrepresented :=
    (faceClass_mem_sourceWalk_iff_kernel quizValid valid
      (faceClass valid.partitionValid dart)).2 hface
  rcases List.mem_map.1 hrepresented with
    ⟨anchor, hanchor, hclass⟩
  refine ⟨anchor, hcentral anchor hanchor, ?_⟩
  exact (faceClass_eq_iff_sameCycle valid dart anchor).1 hclass.symm

/-- The exact remaining local obligations—centrality of traversal anchors and
`R`-link connectivity—complete the classical preembedding. -/
noncomputable def quizPreembeddingOfCentralWalkAndRLink
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz)
    (hcentral : ∀ source ∈ sourceQuizWalk quizValid valid,
      EdgeCentral (checkedHypermap valid.partitionValid) target
        (quizFaceMap quizValid valid target targetRoot targetFits) source)
    (hrlinked : RLinkConnected (checkedHypermap valid.partitionValid)
      (fun source =>
        FaceKernel (checkedHypermap valid.partitionValid)
            (ClassicalCertificateReductionMetadata.ring code) source ∧
          EdgeCentral (checkedHypermap valid.partitionValid) target
            (quizFaceMap quizValid valid target targetRoot targetFits)
              source)) :
    Preembedding (checkedHypermap valid.partitionValid) target
      (FaceKernel (checkedHypermap valid.partitionValid)
        (ClassicalCertificateReductionMetadata.ring code))
      (quizFaceMap quizValid valid target targetRoot targetFits) where
  face := quizFaceMap_face quizValid valid target targetRoot targetFits
  arity := quizFaceMap_arity quizValid valid target targetRoot targetFits
  cover := quizFaceMap_cover_of_sourceWalk_edgeCentral quizValid valid
    target targetRoot targetFits hcentral
  rlinked := hrlinked

/-- Once the source geometry is checked, `R`-link connectivity is the sole
remaining field of the classical preembedding constructor. -/
noncomputable def quizPreembeddingOfSourceGeometryAndRLink
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (geometry : SourceGeometryValid code)
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (target : FiniteHypermap Target) (targetRoot : Target)
    (targetFits : HypermapQuizFits target targetRoot quiz)
    (htargetPlain : IsPlain target) (htargetCubic : IsCubic target)
    (hrlinked : RLinkConnected (checkedHypermap valid.partitionValid)
      (fun source =>
        FaceKernel (checkedHypermap valid.partitionValid)
            (ClassicalCertificateReductionMetadata.ring code) source ∧
          EdgeCentral (checkedHypermap valid.partitionValid) target
            (quizFaceMap quizValid valid target targetRoot targetFits)
              source)) :
    Preembedding (checkedHypermap valid.partitionValid) target
      (FaceKernel (checkedHypermap valid.partitionValid)
        (ClassicalCertificateReductionMetadata.ring code))
      (quizFaceMap quizValid valid target targetRoot targetFits) :=
  quizPreembeddingOfCentralWalkAndRLink quizValid valid target targetRoot
    targetFits
    (quizFaceMap_sourceWalk_edgeCentral quizValid valid geometry target
      targetRoot targetFits htargetPlain htargetCubic)
    hrlinked

/-- The finite hypermap associated to a rotation system is plain. -/
theorem rotationSystem_toFiniteHypermap_isPlain
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) : IsPlain RS.toFiniteHypermap := by
  intro dart
  exact RS.alpha_involutive dart

/-- Cubicity of a cyclic rotation system gives period three for the inverse
node permutation used by its finite hypermap. -/
theorem rotationSystem_toFiniteHypermap_isCubic
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : GoertzelV24FaceDualConnectedness.VertexRotationCyclic RS) :
    IsCubic RS.toFiniteHypermap := by
  intro dart
  have hcube := congrArg (fun permutation : Equiv.Perm RS.D =>
      permutation dart)
    (ClassicalCertificateCubicWord.rho_symm_cube_eq_one RS hcubic hrotation)
  simpa [pow_succ, Equiv.Perm.mul_apply] using hcube

/-- Rotation-system quiz fitting is exactly the generic finite-hypermap
fitting premise used by the preembedding constructor. -/
theorem hypermapQuizFits_toFiniteHypermap_of_fits
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (targetRoot : RS.D) (quiz : Quiz)
    (hfits : Quiz.Fits RS targetRoot quiz) :
    HypermapQuizFits RS.toFiniteHypermap targetRoot quiz := by
  have harities :=
    (quiz_fits_iff_arities_eq_map RS targetRoot quiz).1 hfits
  unfold HypermapQuizFits
  change quizArities quiz =
    (quizWalkWith RS.alpha RS.rho.symm targetRoot quiz).map
      (hypermapFaceArity RS.toFiniteHypermap)
  rw [harities]
  apply List.map_congr_left
  intro dart hdart
  rfl

/-- A fitting quiz in a cubic cyclic rotation system is edge-central on every
checked source representative. -/
theorem quizFaceMap_sourceWalk_edgeCentral_of_rotationSystemFit
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (geometry : SourceGeometryValid code)
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : GoertzelV24FaceDualConnectedness.VertexRotationCyclic RS)
    (targetRoot : RS.D) (hfits : Quiz.Fits RS targetRoot quiz) :
    ∀ source ∈ sourceQuizWalk quizValid valid,
      EdgeCentral (checkedHypermap valid.partitionValid) RS.toFiniteHypermap
        (quizFaceMap quizValid valid RS.toFiniteHypermap targetRoot
          (hypermapQuizFits_toFiniteHypermap_of_fits RS targetRoot quiz hfits))
        source :=
  quizFaceMap_sourceWalk_edgeCentral quizValid valid geometry
    RS.toFiniteHypermap targetRoot
    (hypermapQuizFits_toFiniteHypermap_of_fits RS targetRoot quiz hfits)
    (rotationSystem_toFiniteHypermap_isPlain RS)
    (rotationSystem_toFiniteHypermap_isCubic RS hcubic hrotation)

/-- A checked catalogue quiz fitting in an actual rotation system therefore
supplies the facial half of its classical preembedding there. -/
noncomputable def quizFacialPreembeddingOfRotationSystemFit
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (targetRoot : RS.D)
    (hfits : Quiz.Fits RS targetRoot quiz) :
    FacialPreembedding
      (checkedHypermap valid.partitionValid) RS.toFiniteHypermap
      (FaceKernel (checkedHypermap valid.partitionValid)
        (ClassicalCertificateReductionMetadata.ring code))
      (quizFaceMap quizValid valid RS.toFiniteHypermap targetRoot
        (hypermapQuizFits_toFiniteHypermap_of_fits RS targetRoot quiz hfits)) :=
  quizFacialPreembedding quizValid valid RS.toFiniteHypermap targetRoot
    (hypermapQuizFits_toFiniteHypermap_of_fits RS targetRoot quiz hfits)

/-- For a checked source and a fitting cubic rotation-system target, an
`R`-link certificate completes the full classical preembedding. -/
noncomputable def quizPreembeddingOfRotationSystemFitAndRLink
    (quizValid : ValidAt code root quiz)
    (valid : ClassicalCertificateReductionMetadata.Valid code)
    (geometry : SourceGeometryValid code)
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : GoertzelV24FaceDualConnectedness.VertexRotationCyclic RS)
    (targetRoot : RS.D) (hfits : Quiz.Fits RS targetRoot quiz)
    (hrlinked : RLinkConnected (checkedHypermap valid.partitionValid)
      (fun source =>
        FaceKernel (checkedHypermap valid.partitionValid)
            (ClassicalCertificateReductionMetadata.ring code) source ∧
          EdgeCentral (checkedHypermap valid.partitionValid)
            RS.toFiniteHypermap
            (quizFaceMap quizValid valid RS.toFiniteHypermap targetRoot
              (hypermapQuizFits_toFiniteHypermap_of_fits RS targetRoot quiz
                hfits)) source)) :
    Preembedding (checkedHypermap valid.partitionValid) RS.toFiniteHypermap
      (FaceKernel (checkedHypermap valid.partitionValid)
        (ClassicalCertificateReductionMetadata.ring code))
      (quizFaceMap quizValid valid RS.toFiniteHypermap targetRoot
        (hypermapQuizFits_toFiniteHypermap_of_fits RS targetRoot quiz
          hfits)) :=
  quizPreembeddingOfSourceGeometryAndRLink quizValid valid geometry
    RS.toFiniteHypermap targetRoot
    (hypermapQuizFits_toFiniteHypermap_of_fits RS targetRoot quiz hfits)
    (rotationSystem_toFiniteHypermap_isPlain RS)
    (rotationSystem_toFiniteHypermap_isCubic RS hcubic hrotation)
    hrlinked

end

end ClassicalCertificateQuizPreembedding

end Mettapedia.GraphTheory.FourColor
