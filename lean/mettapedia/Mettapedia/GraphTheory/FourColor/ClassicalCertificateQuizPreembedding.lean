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
hypermap meanings and constructs the facial part of the map directly from a
checked catalogue quiz.  The remaining local obligation is expressed without
loss: the paired traversal representatives must be edge-central.  Once that
is proved, kernel coverage follows immediately.
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

end

end ClassicalCertificateQuizPreembedding

end Mettapedia.GraphTheory.FourColor
