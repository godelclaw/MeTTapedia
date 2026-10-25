import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorPrograms
import Mettapedia.TypeTheory.IndexedContainerInduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PairSpine

/-!
# A proof-relevant `All` family derived from native Vector elimination

The admitted native Vector eliminator can define a predicate over every
element of one exact source vector.  `allType P n xs` eliminates `xs` into the
universe: nil gives a singleton identity type and cons gives a dependent pair
of a head witness and the recursively produced tail evidence.

`allEvidence` performs a second Vector elimination.  Given a pointwise witness
function `Π x, P x`, it builds an inhabitant of `allType P n xs`.  The source
vector remains an argument of the motive, so this is stronger than returning
an unrelated vector of the same length.

The construction uses the existing formed Nat/Vec signature and its checked
iota decoder.  It introduces no new primitive declaration or conversion rule.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll

open Presentation Declaration RussellTarski TypedEquality.Normalization
open NativeNaturalVectorFamilies

/-- Specialize the native Vector element universe at `α` and its elimination
universe at `succ α`.  The one-level gap is exactly what lets the eliminator
compute a type in `U α`. -/
def allLevels (parameter : Nat) : LevelExpr Nat :=
  if parameter = 0 then .param 0
  else if parameter = 1 then .succ (.param 0)
  else .param parameter

abbrev elementLevel : LevelExpr Nat := allLevels 0
abbrev motiveLevel : LevelExpr Nat := .param 0
abbrev eliminationLevel : LevelExpr Nat := allLevels 1

def levelInstance : LevelInstance NativeNaturalVectorFamilies.rawSignature allLevels where
  computation := NativeNaturalVectorFamilies.iotaComputation
  computationMap step := by
    obtain ⟨evidence⟩ := step
    exact ⟨NativeNaturalVectorFamilies.Programs.mapIota
      (substLevelsHead allLevels) evidence⟩

abbrev signature := levelInstance.signature
abbrev rules : Rules Tower.Head := levelInstance.rules

theorem signature_formed : signature.Formed Tower.rules :=
  levelInstance.formed NativeNaturalVectorFamilies.rawSignature_formed

def decoder : StructuralConversionCode.RootDecoder rules.computation :=
  DeclarationConversionCode.rootDecoder
    (base := Tower.rules) (signature := signature) (.ofEmpty _ rfl)
    NativeNaturalVectorFamilies.Checking.iotaDecoder

def weaken2 {n : Nat} (term : Tower.Tm n) : Tower.Tm (n + 2) :=
  rename (fun index => index.succ.succ) term

def weaken4 {n : Nat} (term : Tower.Tm n) : Tower.Tm (n + 4) :=
  rename (fun index => index.succ.succ.succ.succ) term

@[simp] theorem rename_weaken2 {n m : Nat} (rho : Ren n m)
    (term : Tower.Tm n) :
    rename (liftRen (liftRen rho)) (weaken2 term) =
      weaken2 (rename rho term) := by
  unfold weaken2
  rw [rename_comp, rename_comp]
  apply rename_ext
  intro index
  rfl

@[simp] theorem rename_weaken4 {n m : Nat} (rho : Ren n m)
    (term : Tower.Tm n) :
    rename (liftRen (liftRen (liftRen (liftRen rho)))) (weaken4 term) =
      weaken4 (rename rho term) := by
  unfold weaken4
  rw [rename_comp, rename_comp]
  apply rename_ext
  intro index
  rfl

@[simp] theorem subst_weaken2 {n m : Nat}
    (sigma : Sub Tower.Head n m) (term : Tower.Tm n) :
    subst (liftSub (liftSub sigma)) (weaken2 term) =
      weaken2 (subst sigma term) := by
  unfold weaken2
  rw [subst_rename, rename_subst]
  apply subst_ext
  intro index
  change rename wk (rename wk (sigma index)) =
    rename (fun i => i.succ.succ) (sigma index)
  rw [rename_comp]
  apply rename_ext
  intro i
  rfl

@[simp] theorem subst_weaken4 {n m : Nat}
    (sigma : Sub Tower.Head n m) (term : Tower.Tm n) :
    subst (liftSub (liftSub (liftSub (liftSub sigma)))) (weaken4 term) =
      weaken4 (subst sigma term) := by
  unfold weaken4
  rw [subst_rename, rename_subst]
  apply subst_ext
  intro index
  change rename wk (rename wk (rename wk (rename wk (sigma index)))) =
    rename (fun i => i.succ.succ.succ.succ) (sigma index)
  rw [rename_comp, rename_comp, rename_comp]
  apply rename_ext
  intro i
  rfl

@[simp] theorem liftRen_four_two {n m : Nat} (rho : Ren n m) :
    liftRen (liftRen (liftRen (liftRen rho))) (2 : Fin (n + 4)) = 2 := rfl

@[simp] theorem liftRen_five_one {n m : Nat} (rho : Ren n m) :
    liftRen (liftRen (liftRen (liftRen (liftRen rho))))
      (1 : Fin (n + 5)) = 1 := rfl

@[simp] theorem liftRen_four_zero {n m : Nat} (rho : Ren n m) :
    liftRen (liftRen (liftRen (liftRen rho))) (0 : Fin (n + 4)) = 0 := rfl

@[simp] theorem liftRen_two_one {n m : Nat} (rho : Ren n m) :
    liftRen (liftRen rho) (1 : Fin (n + 2)) = 1 := rfl

@[simp] theorem liftRen_two_zero {n m : Nat} (rho : Ren n m) :
    liftRen (liftRen rho) (0 : Fin (n + 2)) = 0 := rfl

@[simp] theorem liftSub_four_two {n m : Nat} (sigma : Sub Tower.Head n m) :
    liftSub (liftSub (liftSub (liftSub sigma))) (2 : Fin (n + 4)) =
      (.var 2 : Tower.Tm (m + 4)) := rfl

@[simp] theorem liftSub_five_one {n m : Nat} (sigma : Sub Tower.Head n m) :
    liftSub (liftSub (liftSub (liftSub (liftSub sigma))))
      (1 : Fin (n + 5)) = (.var 1 : Tower.Tm (m + 5)) := rfl

@[simp] theorem liftSub_four_zero {n m : Nat} (sigma : Sub Tower.Head n m) :
    liftSub (liftSub (liftSub (liftSub sigma))) (0 : Fin (n + 4)) =
      (.var 0 : Tower.Tm (m + 4)) := rfl

@[simp] theorem liftSub_two_one {n m : Nat} (sigma : Sub Tower.Head n m) :
    liftSub (liftSub sigma) (1 : Fin (n + 2)) =
      (.var 1 : Tower.Tm (m + 2)) := rfl

@[simp] theorem liftSub_two_zero {n m : Nat} (sigma : Sub Tower.Head n m) :
    liftSub (liftSub sigma) (0 : Fin (n + 2)) =
      (.var 0 : Tower.Tm (m + 2)) := rfl

/-- A canonical inhabited base type, used as `All P 0 nil`. -/
def unitType {n : Nat} : Tower.Tm n :=
  .id natTm zeroTm zeroTm

def unitEvidence {n : Nat} : Tower.Tm n :=
  .refl zeroTm

/-- The type-level Vector-eliminator motive is constantly the selected motive
universe. -/
def allUniverseMotive {n : Nat} : Tower.Tm n :=
  .lam (.lam (sortTm motiveLevel))

/-- In the cons branch, binders are length, head, tail and the recursively
computed `All` type. -/
def allTypeConsCase {n : Nat} (predicate : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.lam (.lam
    (.sigma (.app (weaken4 predicate) (.var 2)) (.var 1)))))

/-- `All P n xs`, computed from the exact Vector `xs`. -/
def allType {n : Nat}
    (element predicate length vector : Tower.Tm n) : Tower.Tm n :=
  vecEliminateApp element allUniverseMotive unitType
    (allTypeConsCase predicate) length vector

/-- The evidence-producing motive returns `All P n xs`. -/
def allEvidenceMotive {n : Nat}
    (element predicate : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam
    (allType (weaken2 element) (weaken2 predicate) (.var 1) (.var 0)))

/-- The cons evidence pairs the head witness with the recursively constructed
tail evidence. -/
def allEvidenceConsCase {n : Nat}
    (witness : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.lam (.lam
    (.pair (.app (weaken4 witness) (.var 2)) (.var 0)))))

/-- Build `All P n xs` from a pointwise witness function. -/
def allEvidence {n : Nat}
    (element predicate witness length vector : Tower.Tm n) : Tower.Tm n :=
  vecEliminateApp element (allEvidenceMotive element predicate) unitEvidence
    (allEvidenceConsCase witness) length vector

@[simp] theorem rename_allType {n m : Nat} (rho : Ren n m)
    (element predicate length vector : Tower.Tm n) :
    rename rho (allType element predicate length vector) =
      allType (rename rho element) (rename rho predicate)
        (rename rho length) (rename rho vector) := by
  simp [allType, allUniverseMotive, allTypeConsCase,
    unitType, natTm, zeroTm, sortTm, vecEliminateApp, rename]

@[simp] theorem subst_allType {n m : Nat} (sigma : Sub Tower.Head n m)
    (element predicate length vector : Tower.Tm n) :
    subst sigma (allType element predicate length vector) =
      allType (subst sigma element) (subst sigma predicate)
        (subst sigma length) (subst sigma vector) := by
  simp [allType, allUniverseMotive, allTypeConsCase,
    unitType, natTm, zeroTm, sortTm, vecEliminateApp, subst]

@[simp] theorem rename_allEvidence {n m : Nat} (rho : Ren n m)
    (element predicate witness length vector : Tower.Tm n) :
    rename rho (allEvidence element predicate witness length vector) =
      allEvidence (rename rho element) (rename rho predicate)
        (rename rho witness) (rename rho length) (rename rho vector) := by
  simp [allEvidence, allEvidenceMotive, allEvidenceConsCase, allType,
    allUniverseMotive, allTypeConsCase, vecEliminateApp,
    unitType, unitEvidence, natTm, zeroTm, sortTm, rename]

@[simp] theorem subst_allEvidence {n m : Nat} (sigma : Sub Tower.Head n m)
    (element predicate witness length vector : Tower.Tm n) :
    subst sigma (allEvidence element predicate witness length vector) =
      allEvidence (subst sigma element) (subst sigma predicate)
        (subst sigma witness) (subst sigma length) (subst sigma vector) := by
  simp [allEvidence, allEvidenceMotive, allEvidenceConsCase, allType,
    allUniverseMotive, allTypeConsCase, vecEliminateApp,
    unitType, unitEvidence, natTm, zeroTm, sortTm, subst]

/-! ## Formation-sensitive qualification -/

/-- In context `A`, predicates classify elements of `A`. -/
def predicateType : Tower.Tm 1 :=
  .pi (.var 0) (sortTm motiveLevel)

/-- In context `A,P`, a witness function supplies `P x` for every `x : A`. -/
def witnessType : Tower.Tm 2 :=
  .pi (.var 1) (.app (.var 1) (.var 0))

def contextA : Tower.Ctx 1 :=
  .snoc .nil (sortTm elementLevel)

def contextAP : Tower.Ctx 2 :=
  .snoc contextA predicateType

def contextAPW : Tower.Ctx 3 :=
  .snoc contextAP witnessType

def contextAPWN : Tower.Ctx 4 :=
  .snoc contextAPW natTm

def contextAPWNV : Tower.Ctx 5 :=
  .snoc contextAPWN (vecApp (.var 3) (.var 0))

namespace TypeFormation

/-- Forming `All P xs` requires a predicate, length and vector, without a
pointwise witness function. -/
def contextAPN : Tower.Ctx 3 :=
  .snoc NativeVectorAll.contextAP natTm

def context : Tower.Ctx 4 :=
  .snoc contextAPN (vecApp (.var 2) (.var 0))

def subject : Tower.Tm 4 :=
  allType (.var 3) (.var 2) (.var 1) (.var 0)

end TypeFormation

def allTypeControl : Tower.Tm 5 :=
  allType (.var 4) (.var 3) (.var 1) (.var 0)

def allEvidenceControl : Tower.Tm 5 :=
  allEvidence (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

def motiveExpected {n : Nat} (element : Tower.Tm n) : Tower.Tm n :=
  .pi natTm
    (.pi (vecApp (rename wk element) (.var 0)) (sortTm motiveLevel))

def allTypeConsExpected {n : Nat} (element : Tower.Tm n) : Tower.Tm n :=
  .pi natTm
    (.pi (rename wk element)
      (.pi (vecApp (weaken2 element) (.var 1))
        (.pi (sortTm motiveLevel) (sortTm motiveLevel))))

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def searchRows {n : Nat} (term : Tower.Tm n) :
    List (Fin NativeNaturalVectorFamilies.Checking.table.length) →
      Option (SchemaTableConversionCode.Code Tower.Head n)
  | [] => none
  | index :: rest =>
      match ExecutableSchemaMatching.reconstruct
          (NativeNaturalVectorFamilies.Checking.table.get index).2.1 term with
      | none => searchRows term rest
      | some assignment => some (SchemaTableConversionCode.encode
          NativeNaturalVectorFamilies.Checking.table index assignment)

def searchRoot {n : Nat} (term : Tower.Tm n) : Option (decoder.Code n) :=
  (searchRows term
    (List.finRange NativeNaturalVectorFamilies.Checking.table.length)).map
      .declared

def choices : FormationSensitiveElaboration.Choices Tower.Head decoder.Code where
  headType head := some (StructuralTypingReplay.TowerDecisions.headTarget head)
  join first second := match first, second with
    | .sort first, .sort second => some (.sort (.max first second))
    | _, _ => none
  cumulative first second := decide (rules.cumulative first second)
  normalize := fun fuel term =>
    match StructuralConversionSearch.normalize decoder searchRoot
        (headEq := rules.headEq) fuel term with
    | none => term
    | some candidate => candidate.term
  conversion := fun fuel left right =>
    StructuralConversionSearch.compare decoder searchRoot
      (headEq := rules.headEq) fuel left right

def accepted {n : Nat} (context : Tower.Ctx n)
    (term type : Tower.Tm n) : Bool :=
  (FormationSensitiveElaboration.elaborate rules decoder choices 128
    context term type).isSome

theorem accepted_sound {n : Nat} {context : Tower.Ctx n}
    {term type : Tower.Tm n} (checked : accepted context term type = true) :
    FormationSensitive.Judgment rules context term type := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp checked
  exact FormationSensitiveElaboration.elaborate_sound rules decoder
    choices 128 context term type submission produced

/-! ## Canonical Vector-bundle adequacy -/

namespace CanonicalAdequacy

open Mettapedia.TypeTheory.IndexedContainer

/-- Canonical natural quotation used only for constructor-spine adequacy. -/
def numeral {n : Nat} : Nat → Tower.Tm n
  | 0 => zeroTm
  | length + 1 => succApp (numeral length)

/-- Encode a source-ordered finite spine with the actual native Vector
constructors. -/
def encodeVector {n : Nat} (element : Tower.Tm n) :
    List (Tower.Tm n) → Tower.Tm n
  | [] => vnilApp element
  | head :: tail =>
      vconsApp element (numeral tail.length) head (encodeVector element tail)

private def weaken1 {n : Nat} (term : Tower.Tm n) : Tower.Tm (n + 1) :=
  rename wk term

private def weaken3 {n : Nat} (term : Tower.Tm n) : Tower.Tm (n + 3) :=
  rename (fun index => index.succ.succ.succ) term

private theorem subst_vars_eq_rename {n m : Nat} (rho : Ren n m)
    (term : Tower.Tm n) :
    subst (fun index => .var (rho index)) term = rename rho term := by
  calc
    subst (fun index => .var (rho index)) term =
        subst (fun index => rename rho (ids index)) term := by
          apply subst_ext
          intro index
          rfl
    _ = rename rho (subst ids term) :=
      (rename_subst (rho := rho) (sigma := ids) (term := term)).symm
    _ = rename rho term := by rw [subst_ids]

private theorem instantiate_weaken4_outer {n : Nat}
    (term argument : Tower.Tm n) :
    subst (liftSub (liftSub (liftSub (subst0 argument)))) (weaken4 term) =
      weaken3 term := by
  unfold weaken4 weaken3
  rw [subst_rename]
  rw [← subst_vars_eq_rename]
  apply subst_ext
  intro index
  rfl

private theorem instantiate_weaken3_outer {n : Nat}
    (term argument : Tower.Tm n) :
    subst (liftSub (liftSub (subst0 argument))) (weaken3 term) =
      weaken2 term := by
  unfold weaken3 weaken2
  rw [subst_rename]
  rw [← subst_vars_eq_rename]
  apply subst_ext
  intro index
  rfl

private theorem instantiate_weaken2_outer {n : Nat}
    (term argument : Tower.Tm n) :
    subst (liftSub (subst0 argument)) (weaken2 term) = weaken1 term := by
  unfold weaken2 weaken1
  rw [subst_rename]
  rw [← subst_vars_eq_rename]
  apply subst_ext
  intro index
  rfl

private theorem instantiate_weaken1_outer {n : Nat}
    (term argument : Tower.Tm n) :
    subst (subst0 argument) (weaken1 term) = term := by
  unfold weaken1
  rw [subst_rename]
  convert subst_ids term using 1
  apply subst_ext
  intro index
  rfl

private theorem instantiate_head_index {n : Nat}
    (length head tail recursive : Tower.Tm n) :
    subst (subst0 recursive)
      (subst (liftSub (subst0 tail))
        (subst (liftSub (liftSub (subst0 head)))
          (liftSub (liftSub (liftSub (subst0 length)))
            (2 : Fin (n + 4))))) = head := by
  have selectedHead :
      subst (liftSub (liftSub (subst0 head)))
        (liftSub (liftSub (liftSub (subst0 length)))
          (2 : Fin (n + 4))) = weaken2 head := by
    change rename wk (rename wk head) = weaken2 head
    unfold weaken2
    rw [rename_comp]
    apply rename_ext
    intro index
    rfl
  rw [selectedHead, instantiate_weaken2_outer, instantiate_weaken1_outer]

private theorem instantiate_recursive_index {n : Nat}
    (length head tail recursive : Tower.Tm n) :
    subst (subst0 recursive)
      (subst (liftSub (subst0 tail))
        (subst (liftSub (liftSub (subst0 head)))
          (liftSub (liftSub (liftSub (subst0 length)))
            (0 : Fin (n + 4))))) = recursive := by
  have selectedRecursive :
      subst (liftSub (subst0 tail))
        (subst (liftSub (liftSub (subst0 head)))
          (liftSub (liftSub (liftSub (subst0 length)))
            (0 : Fin (n + 4)))) = (.var 0 : Tower.Tm (n + 1)) := by
    change (.var 0 : Tower.Tm (n + 1)) = .var 0
    rfl
  rw [selectedRecursive]
  rfl

/-- The semantic witness at one Vector position is the exact application of
the selected pointwise witness term to the source element at that position. -/
abbrev Witness {n : Nat} (witness element : Tower.Tm n) :=
  { evidence : Tower.Tm n // evidence = .app witness element }

/-- One exact witness for every source element, in source order. -/
def pointwiseBundle {n : Nat} (witness : Tower.Tm n) :
    (values : List (Tower.Tm n)) → ListAll (Witness witness) values
  | [] => .nil
  | head :: tail =>
      .cons ⟨.app witness head, rfl⟩ (pointwiseBundle witness tail)

/-- Quote a semantic witness spine with the same nested-pair representation
computed by the native `All` eliminator. -/
def quoteBundle {n : Nat} {witness : Tower.Tm n} :
    {values : List (Tower.Tm n)} →
      ListAll (Witness witness) values → Tower.Tm n
  | [], .nil => unitEvidence
  | _ :: _, .cons head tail => .pair head.1 (quoteBundle tail)

/-- Quote independent, ordered position witnesses using the same pair
representation as the native All program. The final identity proof is the
existing canonical base evidence. -/
def quoteWitnesses {n : Nat} (witnesses : List (Tower.Tm n)) : Tower.Tm n :=
  PairSpine.assemble witnesses unitEvidence

@[simp] theorem quoteWitnesses_nil {n : Nat} :
    quoteWitnesses ([] : List (Tower.Tm n)) = unitEvidence := rfl

@[simp] theorem quoteWitnesses_cons {n : Nat} (head : Tower.Tm n)
    (tail : List (Tower.Tm n)) :
    quoteWitnesses (head :: tail) = .pair head (quoteWitnesses tail) := rfl

/-- The previous pointwise witness quotation is a specialization of the
ordered quotation, without identifying distinct position witnesses. -/
theorem quoteBundle_pointwise_eq_quoteWitnesses {n : Nat} (witness : Tower.Tm n)
    (values : List (Tower.Tm n)) :
    quoteBundle (pointwiseBundle witness values) =
      quoteWitnesses (values.map (fun value => .app witness value)) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      change Tm.pair (.app witness head) (quoteBundle (pointwiseBundle witness tail)) =
        Tm.pair (.app witness head) (quoteWitnesses (tail.map (fun value => .app witness value)))
      rw [ih]

/-- Componentwise source reduction is retained by the actual Vector encoding. -/
theorem encodeVector_reduces (R : Rules Tower.Head) {n : Nat} (element : Tower.Tm n)
    {first second : List (Tower.Tm n)}
    (related : List.Forall₂ (TypedEquality.Reduces R) first second) :
    TypedEquality.Reduces R (encodeVector element first) (encodeVector element second) := by
  induction related with
  | nil => exact .refl
  | @cons first second firsts seconds firstPath restPaths ih =>
      have lengths : firsts.length = seconds.length := restPaths.length_eq
      change TypedEquality.Reduces R
        (vconsApp element (numeral firsts.length) first (encodeVector element firsts))
        (vconsApp element (numeral seconds.length) second (encodeVector element seconds))
      rw [lengths]
      exact (Relation.ReflTransGen.lift
        (fun value => vconsApp element (numeral seconds.length) value (encodeVector element firsts))
        (fun _ _ step => StepCore.congAppFun (StepCore.congAppArg step)) _ _ firstPath).trans
          (Relation.ReflTransGen.lift (vconsApp element (numeral seconds.length) second)
            (fun _ _ step => StepCore.congAppArg step) _ _ ih)


/-- The canonical Vector value selected by an ordinary source list. -/
def semanticValue {n : Nat} (values : List (Tower.Tm n)) :
    IndexedContainer.Examples.vector.Extension (Tower.Tm n) values.length :=
  ⟨(), values.get⟩

/-- The semantic Vector bundle and the source-ordered witness spine are
equivalent. This is the exact indexed-container bundle, rather than a second
notion of Vector positions. -/
noncomputable def semanticBundleEquiv {n : Nat} (witness : Tower.Tm n)
    (values : List (Tower.Tm n)) :
    (IndexedContainer.vectorInductionBundle (Witness witness)).Bundle
        (semanticValue values) ≃
      ListAll (Witness witness) values :=
  ((IndexedContainer.vectorInductionBundle (Witness witness)).exact
      (semanticValue values)).trans
    (listAllEquiv (Witness witness) values).symm

/-- The semantic indexed-container bundle selected by the pointwise witness
term. -/
noncomputable def semanticBundle {n : Nat} (witness : Tower.Tm n)
    (values : List (Tower.Tm n)) :
    (IndexedContainer.vectorInductionBundle (Witness witness)).Bundle
      (semanticValue values) :=
  (semanticBundleEquiv witness values).symm
    (pointwiseBundle witness values)

@[simp] theorem semanticBundle_representation {n : Nat}
    (witness : Tower.Tm n) (values : List (Tower.Tm n)) :
    semanticBundleEquiv witness values (semanticBundle witness values) =
      pointwiseBundle witness values :=
  (semanticBundleEquiv witness values).apply_symm_apply _

/-- The chosen semantic bundle contains the expected witness at every exact
`Fin length` position. -/
theorem pointwiseBundle_exact {n : Nat} (witness : Tower.Tm n)
    (values : List (Tower.Tm n)) (position : Fin values.length) :
    (listAllEquiv (Witness witness) values).toFun
        (pointwiseBundle witness values) position =
      ⟨.app witness (values.get position), rfl⟩ := by
  apply Subtype.ext
  exact ((listAllEquiv (Witness witness) values).toFun
    (pointwiseBundle witness values) position).property

/-- Structural reduction generated by the selected native rules. -/
abbrev Steps {n : Nat} (left right : Tower.Tm n) : Prop :=
  Relation.ReflTransGen (StepCore rules.computation rules.headEq) left right

private theorem steps_pair_snd {n : Nat} (first : Tower.Tm n)
    {left right : Tower.Tm n} (steps : Steps left right) :
    Steps (.pair first left) (.pair first right) := by
  induction steps with
  | refl => exact .refl
  | tail prior step ih => exact .tail ih (.congPairSnd step)

private theorem consCase_steps {n : Nat}
    (witness length head tail recursive : Tower.Tm n) :
    Steps
      (.app (.app (.app (.app (allEvidenceConsCase witness) length) head)
        tail) recursive)
      (.pair (.app witness head) recursive) := by
  refine Relation.ReflTransGen.head (.congAppFun (.congAppFun
    (.congAppFun (.betaPi _ _)))) ?_
  refine Relation.ReflTransGen.head (.congAppFun (.congAppFun
    (.betaPi _ _))) ?_
  refine Relation.ReflTransGen.head (.congAppFun (.betaPi _ _)) ?_
  convert Relation.ReflTransGen.single
    (StepCore.betaPi (root := rules.computation) (headEq := rules.headEq) _ _) using 1
  all_goals first | rfl | (
    simp only [inst0, subst]
    rw [instantiate_weaken4_outer, instantiate_weaken3_outer,
      instantiate_weaken2_outer, instantiate_weaken1_outer,
      instantiate_head_index, instantiate_recursive_index])

/-- Native `All` evidence over a canonical Vector constructor spine reduces
to the quotation of the exact source-ordered semantic witness bundle. -/
theorem allEvidence_steps {n : Nat}
    (element predicate witness : Tower.Tm n) :
    ∀ values : List (Tower.Tm n),
      Steps
        (allEvidence element predicate witness (numeral values.length)
          (encodeVector element values))
        (quoteBundle (pointwiseBundle witness values))
  | [] => by
      apply Relation.ReflTransGen.single
      apply StepCore.root
      exact RootStep.declared
        ⟨NativeNaturalVectorFamilies.IotaEvidence.vecNil
          element (allEvidenceMotive element predicate) unitEvidence
          (allEvidenceConsCase witness)⟩
  | head :: tail => by
      apply Relation.ReflTransGen.head
      · apply StepCore.root
        exact RootStep.declared
          ⟨NativeNaturalVectorFamilies.IotaEvidence.vecCons
            element (allEvidenceMotive element predicate) unitEvidence
            (allEvidenceConsCase witness) (numeral tail.length) head
            (encodeVector element tail)⟩
      · exact (consCase_steps witness (numeral tail.length) head
          (encodeVector element tail)
          (allEvidence element predicate witness (numeral tail.length)
            (encodeVector element tail))).trans
          (steps_pair_snd (.app witness head)
            (allEvidence_steps element predicate witness tail))

/-- The reduction target is precisely the object quotation of the selected
semantic indexed-container bundle. -/
theorem allEvidence_steps_semanticBundle {n : Nat}
    (element predicate witness : Tower.Tm n)
    (values : List (Tower.Tm n)) :
    Steps
      (allEvidence element predicate witness (numeral values.length)
        (encodeVector element values))
      (quoteBundle
        (semanticBundleEquiv witness values (semanticBundle witness values))) := by
  rw [semanticBundle_representation]
  exact allEvidence_steps element predicate witness values

/-- Swapping two distinguishable position witnesses changes the quoted
bundle. The object representation therefore retains source order. -/
theorem two_position_order_retained {n : Nat} (witness first second : Tower.Tm n)
    (different : Tm.app witness first ≠ Tm.app witness second) :
    quoteBundle (pointwiseBundle witness [first, second]) ≠
      quoteBundle (pointwiseBundle witness [second, first]) := by
  intro equal
  exact different (Tm.pair.inj equal).1

end CanonicalAdequacy

#print axioms rename_allType
#print axioms subst_allType
#print axioms rename_allEvidence
#print axioms subst_allEvidence
#print axioms signature_formed
#print axioms accepted_sound
#print axioms CanonicalAdequacy.semanticBundleEquiv
#print axioms CanonicalAdequacy.pointwiseBundle_exact
#print axioms CanonicalAdequacy.allEvidence_steps
#print axioms CanonicalAdequacy.allEvidence_steps_semanticBundle
#print axioms CanonicalAdequacy.two_position_order_retained

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll
