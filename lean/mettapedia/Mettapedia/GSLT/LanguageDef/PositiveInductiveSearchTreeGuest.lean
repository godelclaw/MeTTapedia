import Mettapedia.GSLT.LanguageDef.ModuleSource.PositiveInductiveLoweringControls
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestDeclarations
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.IntrinsicNativeListRelatorLevels
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSearch
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveHeadMap

/-!
# A registered-List search tree in the cumulative guest calculus

This is the first object-syntax realization of a registered nested source
block.  Its declaration inventory is tied to the admitted `SearchTree`
`.module` source.  The branch method receives a proof-relevant List lift: one
recursive result at every actual child position.  The lift is built by the
already admitted native List eliminator.

The module is deliberately scoped to the registered List instance.  It does
not claim a generic guest realization for every positive container.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeGuest

open Presentation Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeIndexedFamilies

abbrev level : LevelExpr Nat := Tower.zero
abbrev baseRules : Rules Tower.Head := IntrinsicRelatorLevels.rulesAt level
abbrev baseDecoder := IntrinsicRelatorLevels.rootDecoder level

def treeName : DeclName := `Generated.SearchTree
def solvedName : DeclName := `Generated.SearchTree.solved
def branchName : DeclName := `Generated.SearchTree.branch
def eliminateName : DeclName := `Generated.SearchTree.eliminate

def treeApp {n : Nat} (answer : Tower.Tm n) : Tower.Tm n :=
  .app (.const treeName) answer

def solvedApp {n : Nat} (answer value : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const solvedName) answer) value

def branchApp {n : Nat} (answer children : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const branchName) answer) children

def eliminateApp {n : Nat}
    (answer motive solvedCase branchCase tree : Tower.Tm n) :
    Tower.Tm n :=
  .app (.app (.app (.app (.app (.const eliminateName) answer) motive)
    solvedCase) branchCase) tree

def weaken1 {n : Nat} (term : Tower.Tm n) : Tower.Tm (n + 1) :=
  rename wk term

def weaken2 {n : Nat} (term : Tower.Tm n) : Tower.Tm (n + 2) :=
  rename (fun index => index.succ.succ) term

def weaken3 {n : Nat} (term : Tower.Tm n) : Tower.Tm (n + 3) :=
  rename (fun index => index.succ.succ.succ) term

@[simp] theorem liftRen_zero {n m : Nat} (rho : Ren n m) :
    liftRen rho 0 = 0 := rfl

@[simp] theorem liftRen_succ {n m : Nat} (rho : Ren n m)
    (index : Fin n) : liftRen rho index.succ = (rho index).succ := rfl

@[simp] theorem liftRen_two_one {n m : Nat} (rho : Ren n m) :
    liftRen (liftRen rho) (1 : Fin (n + 2)) = 1 := by rfl

@[simp] theorem liftRen_three_one {n m : Nat} (rho : Ren n m) :
    liftRen (liftRen (liftRen rho)) (1 : Fin (n + 3)) = 1 := by rfl

@[simp] theorem liftRen_three_two {n m : Nat} (rho : Ren n m) :
    liftRen (liftRen (liftRen rho)) (2 : Fin (n + 3)) = 2 := by rfl

@[simp] theorem liftSub_two_one {n m : Nat} (sigma : Sub Tower.Head n m) :
    liftSub (liftSub sigma) (1 : Fin (n + 2)) = (.var 1 : Tower.Tm (m + 2)) := by
  rfl

@[simp] theorem liftSub_three_one {n m : Nat} (sigma : Sub Tower.Head n m) :
    liftSub (liftSub (liftSub sigma)) (1 : Fin (n + 3)) =
      (.var 1 : Tower.Tm (m + 3)) := by
  rfl

@[simp] theorem liftSub_three_two {n m : Nat} (sigma : Sub Tower.Head n m) :
    liftSub (liftSub (liftSub sigma)) (2 : Fin (n + 3)) =
      (.var 2 : Tower.Tm (m + 3)) := by
  rfl

@[simp] theorem rename_weaken1 {n m : Nat} (rho : Ren n m)
    (term : Tower.Tm n) :
    rename (liftRen rho) (weaken1 term) = weaken1 (rename rho term) := by
  unfold weaken1
  rw [rename_comp, rename_comp]
  apply rename_ext
  intro index
  rfl

@[simp] theorem rename_weaken2 {n m : Nat} (rho : Ren n m)
    (term : Tower.Tm n) :
    rename (liftRen (liftRen rho)) (weaken2 term) =
      weaken2 (rename rho term) := by
  unfold weaken2
  rw [rename_comp, rename_comp]
  apply rename_ext
  intro index
  rfl

@[simp] theorem rename_weaken3 {n m : Nat} (rho : Ren n m)
    (term : Tower.Tm n) :
    rename (liftRen (liftRen (liftRen rho))) (weaken3 term) =
      weaken3 (rename rho term) := by
  unfold weaken3
  rw [rename_comp, rename_comp]
  apply rename_ext
  intro index
  rfl

@[simp] theorem subst_weaken1 {n m : Nat} (sigma : Sub Tower.Head n m)
    (term : Tower.Tm n) :
    subst (liftSub sigma) (weaken1 term) = weaken1 (subst sigma term) := by
  unfold weaken1
  rw [subst_rename, rename_subst]
  apply subst_ext
  intro index
  rfl

@[simp] theorem subst_weaken2 {n m : Nat} (sigma : Sub Tower.Head n m)
    (term : Tower.Tm n) :
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

@[simp] theorem subst_weaken3 {n m : Nat} (sigma : Sub Tower.Head n m)
    (term : Tower.Tm n) :
    subst (liftSub (liftSub (liftSub sigma))) (weaken3 term) =
      weaken3 (subst sigma term) := by
  unfold weaken3
  rw [subst_rename, rename_subst]
  apply subst_ext
  intro index
  change rename wk (rename wk (rename wk (sigma index))) =
    rename (fun i => i.succ.succ.succ) (sigma index)
  rw [rename_comp, rename_comp]
  apply rename_ext
  intro i
  rfl

/-- `Sigma child : SearchTree A, P child`. -/
def packedType {n : Nat} (tree motive : Tower.Tm n) : Tower.Tm n :=
  .sigma tree (.app (weaken1 motive) (.var 0))

/-- Relate a source child to a packed recursive result by retaining exact
identity of the child's first projection. -/
def packedRelation {n : Nat} (tree : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.id (weaken2 tree) (.var 1) (.fst (.var 0))))

/-- A List lift retains a packed recursive result for every source child. -/
def bundleType {n : Nat} (tree motive children : Tower.Tm n) : Tower.Tm n :=
  let packed := packedType tree motive
  let relation := packedRelation tree
  .sigma (Intrinsic.listApp packed)
    (IntrinsicRelator.mapRelApp (weaken1 tree) (weaken1 packed)
      (weaken1 relation) (weaken1 children) (.var 0))

/-- The List-eliminator motive producing a complete recursive-result bundle. -/
def bundleMotive {n : Nat} (tree motive : Tower.Tm n) : Tower.Tm n :=
  .lam (bundleType (weaken1 tree) (weaken1 motive) (.var 0))

def nilBundle {n : Nat} (tree motive : Tower.Tm n) : Tower.Tm n :=
  let packed := packedType tree motive
  let relation := packedRelation tree
  .pair (Intrinsic.nilApp packed)
    (IntrinsicRelator.nilRelApp tree packed relation)

/-- The cons step pairs the head with its structural recursive call and
extends both the target List and its exact relation evidence. -/
def consBundleCase {n : Nat}
    (answer motive solvedCase branchCase : Tower.Tm n) :
    Tower.Tm n :=
  let tree := treeApp answer
  let packed := packedType tree motive
  let relation := packedRelation tree
  .lam (.lam (.lam
    (let answer' := weaken3 answer
     let motive' := weaken3 motive
     let solvedCase' := weaken3 solvedCase
     let branchCase' := weaken3 branchCase
     let tree' := weaken3 tree
     let packed' := weaken3 packed
     let relation' := weaken3 relation
     let packedHead := .pair (.var 2)
       (eliminateApp answer' motive' solvedCase' branchCase' (.var 2))
     let targetTail := .fst (.var 0)
     let targetList := Intrinsic.consApp packed' packedHead targetTail
     let evidence := IntrinsicRelator.consRelApp tree' packed' relation'
       (.var 2) packedHead (.var 1) targetTail (.refl (.var 2)) (.snd (.var 0))
     .pair targetList evidence)))

/-- Traverse an arbitrary open child List and retain every structural
recursive result in a typed relation spine. -/
def liftChildren {n : Nat}
    (answer motive solvedCase branchCase children : Tower.Tm n) :
    Tower.Tm n :=
  let tree := treeApp answer
  Intrinsic.eliminateApp tree (bundleMotive tree motive)
    (nilBundle tree motive)
    (consBundleCase answer motive solvedCase branchCase) children

@[simp] theorem rename_liftChildren {n m : Nat} (rho : Ren n m)
    (answer motive solvedCase branchCase children : Tower.Tm n) :
    rename rho (liftChildren answer motive solvedCase branchCase children) =
      liftChildren (rename rho answer) (rename rho motive)
        (rename rho solvedCase) (rename rho branchCase) (rename rho children) := by
  simp [liftChildren, consBundleCase, nilBundle, bundleMotive, bundleType,
    packedType, packedRelation, treeApp, eliminateApp, rename,
    Intrinsic.eliminateApp, Intrinsic.listApp,
    Intrinsic.nilApp, Intrinsic.consApp, IntrinsicRelator.mapRelApp,
    IntrinsicRelator.nilRelApp, IntrinsicRelator.consRelApp]

@[simp] theorem subst_liftChildren {n m : Nat}
    (substitution : Sub Tower.Head n m)
    (answer motive solvedCase branchCase children : Tower.Tm n) :
    subst substitution (liftChildren answer motive solvedCase branchCase children) =
      liftChildren (subst substitution answer) (subst substitution motive)
        (subst substitution solvedCase) (subst substitution branchCase)
        (subst substitution children) := by
  simp [liftChildren, consBundleCase, nilBundle, bundleMotive, bundleType,
    packedType, packedRelation, treeApp, eliminateApp, subst,
    Intrinsic.eliminateApp, Intrinsic.listApp,
    Intrinsic.nilApp, Intrinsic.consApp, IntrinsicRelator.mapRelApp,
    IntrinsicRelator.nilRelApp, IntrinsicRelator.consRelApp]

/-! ## Generated declaration types -/

def familyType : Tower.Tm 0 :=
  .pi (sortTm level) (sortTm level)

def solvedType : Tower.Tm 0 :=
  .pi (sortTm level)
    (.pi (.var 0) (treeApp (.var 1)))

def branchType : Tower.Tm 0 :=
  .pi (sortTm level)
    (.pi (Intrinsic.listApp (treeApp (.var 0))) (treeApp (.var 1)))

/-- In context `A`, motives classify each tree at the selected level. -/
def motiveType : Tower.Tm 1 :=
  .pi (treeApp (.var 0)) (sortTm level)

/-- In context `A,P`, the solved method. -/
def solvedCaseType : Tower.Tm 2 :=
  .pi (.var 1)
    (.app (.var 1) (solvedApp (.var 2) (.var 0)))

/-- In context `A,P,solvedCase`, the branch method receives the child List
and its exact positionwise recursive-result bundle. -/
def branchCaseType : Tower.Tm 3 :=
  .pi (Intrinsic.listApp (treeApp (.var 2)))
    (.pi (bundleType (treeApp (.var 3)) (.var 2) (.var 0))
      (.app (.var 3) (branchApp (.var 4) (.var 1))))

/-- In context `A,P,solvedCase,branchCase`, eliminate every tree. -/
def eliminateResultType : Tower.Tm 4 :=
  .pi (treeApp (.var 3)) (.app (.var 3) (.var 0))

def eliminateType : Tower.Tm 0 :=
  .pi (sortTm level)
    (.pi motiveType
      (.pi solvedCaseType
        (.pi branchCaseType eliminateResultType)))

def entries : List (DeclName × Entry Tower.Head) :=
  [(treeName, ⟨familyType, none⟩),
   (solvedName, ⟨solvedType, none⟩),
   (branchName, ⟨branchType, none⟩),
   (eliminateName, ⟨eliminateType, none⟩)]

/-! ## Connection to the admitted `.module` source -/

open Mettapedia.TypeTheory.PositiveInductiveBlock
open Mettapedia.TypeTheory.PositiveInductiveScenarios

/-- Compile exactly the registered-List fragment used by the SearchTree
source. An unregistered container spelling does not silently become List. -/
def sourceConstructorBody {n : Nat} (answer : Tower.Tm n) :
    {context : List Search.interface.SortCode} →
      Code Search.registry Search.interface 1 context → Option (Tower.Tm n)
  | _, .result _ => some (treeApp answer)
  | _, .data .answer rest =>
      (sourceConstructorBody (rename wk answer) rest).map (.pi answer)
  | _, .recursive _ rest =>
      (sourceConstructorBody (rename wk answer) rest).map
        (.pi (treeApp answer))
  | _, .nested name _ _ rest =>
      if name = "List" then
        (sourceConstructorBody (rename wk answer) rest).map
          (.pi (Intrinsic.listApp (treeApp answer)))
      else none

def sourceConstructorEntry
    (constructor : Constructor Search.registry Search.interface 1 []) :
    Option (DeclName × Entry Tower.Head) := do
  let body ← sourceConstructorBody (.var 0) constructor.body
  pure (.str treeName constructor.name, ⟨.pi (sortTm level) body, none⟩)

def sourceConstructorEntries :
    Option (List (DeclName × Entry Tower.Head)) :=
  Search.admitted.constructors.mapM sourceConstructorEntry

/-- The object declaration rows are computed from the exact admitted source
constructor order, not from a parallel handwritten inventory. -/
theorem sourceConstructorEntries_eq :
    sourceConstructorEntries =
      some [(solvedName, ⟨solvedType, none⟩),
        (branchName, ⟨branchType, none⟩)] := by
  rfl

/-- The shared textual lowering reaches the same block consumed here. -/
theorem textual_source_eq :
    ModuleSource.PositiveInductiveLoweringControls.Search.resolvedFamily.erase =
      Search.admitted :=
  ModuleSource.PositiveInductiveLoweringControls.Search.erased_family_eq_existing

/-! ## Independent prefix admission -/

local instance : DecidableRel baseRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred baseRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (baseRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel baseRules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel baseRules.headEq :=
  LevelTower.instDecidableHeadEq

def choices : IndexedInductive.Guest.Declarations.Choices baseRules baseDecoder where
  headType head := some (StructuralTypingReplay.TowerDecisions.headTarget head)
  join first second := match first, second with
    | .sort first, .sort second => some (.sort (.max first second))
    | _, _ => none
  cumulative first second := decide (baseRules.cumulative first second)
  normalize := fun _ term => term
  conversion := fun _ left right =>
    if left = right then some (.refl left)
    else match left, right with
      | .head first, .head second => some (.single (.head first second))
      | _, _ => none

def inventoryCertificates :=
  IndexedInductive.Guest.Declarations.elaborate baseRules baseDecoder choices 256 [] entries

def inventoryAccepted : Bool := inventoryCertificates.isSome

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem inventoryAccepted_eq_true : inventoryAccepted = true := by
  decide +kernel

theorem inventory_admitted :
    DeclarationAdmissionReplay.Admitted baseRules [] entries := by
  obtain ⟨certificates, produced⟩ := Option.isSome_iff_exists.mp
    inventoryAccepted_eq_true
  exact IndexedInductive.Guest.Declarations.elaborate_sound
    baseRules baseDecoder choices 256 [] entries certificates produced

def inventorySignature : Signature Tower.Head := Signature.ofList entries
abbrev inventoryRules : Rules Tower.Head := extendRules baseRules inventorySignature
def inventoryDecoder := DeclarationConversionCode.ofList baseRules baseDecoder entries

theorem inventory_formed : inventorySignature.Formed baseRules := by
  apply IndexedInductive.Guest.Declarations.opaque_formed baseRules entries
    inventory_admitted
  intro item member
  simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

/-! ## Generated iota endpoints, checked before authority -/

def contextA : Tower.Ctx 1 := .snoc .nil (sortTm level)
def contextAP : Tower.Ctx 2 := .snoc contextA motiveType
def contextAPS : Tower.Ctx 3 := .snoc contextAP solvedCaseType
def contextAPSB : Tower.Ctx 4 := .snoc contextAPS branchCaseType
def solvedContext : Tower.Ctx 5 := .snoc contextAPSB (.var 3)
def branchContext : Tower.Ctx 5 :=
  .snoc contextAPSB (Intrinsic.listApp (treeApp (.var 3)))

def solvedLeft : Tower.Tm 5 :=
  eliminateApp (.var 4) (.var 3) (.var 2) (.var 1)
    (solvedApp (.var 4) (.var 0))
def solvedRight : Tower.Tm 5 := .app (.var 2) (.var 0)
def solvedIotaType : Tower.Tm 5 :=
  .app (.var 3) (solvedApp (.var 4) (.var 0))

def branchLeft : Tower.Tm 5 :=
  eliminateApp (.var 4) (.var 3) (.var 2) (.var 1)
    (branchApp (.var 4) (.var 0))
def branchRight : Tower.Tm 5 :=
  .app (.app (.var 1) (.var 0))
    (liftChildren (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
def branchIotaType : Tower.Tm 5 :=
  .app (.var 3) (branchApp (.var 4) (.var 0))

def emptyBundleExpectedEvidenceType : Tower.Tm 4 :=
  let tree := treeApp (.var 3)
  let packed := packedType tree (.var 2)
  let relation := packedRelation tree
  inst0 (Intrinsic.nilApp packed)
    (IntrinsicRelator.mapRelApp (rename wk tree) (rename wk packed)
      (rename wk relation) (rename wk (Intrinsic.nilApp tree)) (.var 0))

def emptyBundleActualEvidenceType : Tower.Tm 4 :=
  let tree := treeApp (.var 3)
  let packed := packedType tree (.var 2)
  IntrinsicRelator.mapRelApp tree packed (packedRelation tree)
    (Intrinsic.nilApp tree) (Intrinsic.nilApp packed)

theorem emptyBundleEvidenceType_exact :
    emptyBundleExpectedEvidenceType = emptyBundleActualEvidenceType := by
  decide

def listMotiveType {n : Nat} (tree : Tower.Tm n) : Tower.Tm n :=
  .pi (Intrinsic.listApp tree) (sortTm level)

def listConsCaseType {n : Nat}
    (tree listMotive : Tower.Tm n) : Tower.Tm n :=
  .pi tree
    (.pi (Intrinsic.listApp (rename wk tree))
      (.pi (.app (rename wk (rename wk listMotive)) (.var 0))
        (.app (rename wk (rename wk (rename wk listMotive)))
          (Intrinsic.consApp
            (rename wk (rename wk (rename wk tree))) (.var 2) (.var 1)))))

local instance : DecidableRel inventoryRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (baseRules.headTyping h u))
local instance : DecidablePred inventoryRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (baseRules.isUniverse h))
local instance : ∀ u v w, Decidable (inventoryRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (baseRules.join u v w))
local instance : DecidableRel inventoryRules.cumulative :=
  fun u v => inferInstanceAs (Decidable (baseRules.cumulative u v))
local instance : DecidableRel inventoryRules.headEq :=
  LevelTower.instDecidableHeadEq

def inventoryChoices : FormationSensitiveElaboration.Choices Tower.Head
    inventoryDecoder.Code where
  headType head := some (StructuralTypingReplay.TowerDecisions.headTarget head)
  join first second := match first, second with
    | .sort first, .sort second => some (.sort (.max first second))
    | _, _ => none
  cumulative first second := decide (inventoryRules.cumulative first second)
  normalize := fun fuel term =>
    (StructuralConversionSearch.produce inventoryDecoder.decode
      (fun _ => none) fuel term).term
  conversion := fun fuel left right =>
    StructuralConversionSearch.compare inventoryDecoder
      (fun _ => none) (headEq := inventoryRules.headEq) fuel left right

def endpointAccepted {n : Nat} (context : Tower.Ctx n)
    (term type : Tower.Tm n) : Bool :=
  (FormationSensitiveElaboration.elaborate inventoryRules inventoryDecoder
    inventoryChoices 512 context term type).isSome

theorem endpointAccepted_sound {n : Nat} {context : Tower.Ctx n}
    {term type : Tower.Tm n} (checked : endpointAccepted context term type = true) :
    FormationSensitive.Judgment inventoryRules context term type := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp checked
  exact FormationSensitiveElaboration.elaborate_sound inventoryRules
    inventoryDecoder inventoryChoices 512 context term type submission produced

/-! ## Proof-relevant nested iota receipts -/

inductive IotaEvidence (n : Nat) : Tower.Tm n → Tower.Tm n → Type where
  | solved (answer motive solvedCase branchCase value : Tower.Tm n) :
      IotaEvidence n
        (eliminateApp answer motive solvedCase branchCase
          (solvedApp answer value))
        (.app solvedCase value)
  | branch (answer motive solvedCase branchCase children : Tower.Tm n) :
      IotaEvidence n
        (eliminateApp answer motive solvedCase branchCase
          (branchApp answer children))
        (.app (.app branchCase children)
          (liftChildren answer motive solvedCase branchCase children))

def IotaEvidence.rename {n m : Nat} {left right : Tower.Tm n}
    (evidence : IotaEvidence n left right) (rho : Ren n m) :
    IotaEvidence m (rename rho left) (rename rho right) := by
  cases evidence with
  | solved => exact .solved _ _ _ _ _
  | branch answer motive solvedCase branchCase children =>
      simpa [treeApp, eliminateApp, branchApp, Presentation.rename] using
        (IotaEvidence.branch
        (Presentation.rename rho answer) (Presentation.rename rho motive)
        (Presentation.rename rho solvedCase)
        (Presentation.rename rho branchCase)
        (Presentation.rename rho children))

def IotaEvidence.substitute {n m : Nat} {left right : Tower.Tm n}
    (evidence : IotaEvidence n left right) (substitution : Sub Tower.Head n m) :
    IotaEvidence m (subst substitution left) (subst substitution right) := by
  cases evidence with
  | solved => exact .solved _ _ _ _ _
  | branch answer motive solvedCase branchCase children =>
      simpa [treeApp, eliminateApp, branchApp, Presentation.subst] using
        (IotaEvidence.branch
        (Presentation.subst substitution answer)
        (Presentation.subst substitution motive)
        (Presentation.subst substitution solvedCase)
        (Presentation.subst substitution branchCase)
        (Presentation.subst substitution children))

def iotaComputation : ProofRelevantRootComputation Tower.Head where
  Evidence := IotaEvidence _
  rename := by
    intro n m rho left right evidence
    exact evidence.rename rho
  substitute := by
    intro n m substitution left right evidence
    exact evidence.substitute substitution

/-- Candidate declaration signature. Raw iota evidence is retained, while
global preservation remains a separate authorization obligation. -/
def signature : Signature Tower.Head :=
  { inventorySignature with computation := iotaComputation.support }

abbrev rules : Rules Tower.Head := extendRules baseRules signature

theorem inventory_extends_signature : inventorySignature.Extends signature where
  entries := fun selected => selected
  computation := by
    intro n left right impossible
    change (Signature.ofList entries).computation.step left right at impossible
    rw [Signature.computation_ofList] at impossible
    exact impossible.elim

theorem signature_formed : signature.Formed baseRules where
  fresh := inventory_formed.fresh
  types := by
    intro name type selected
    obtain ⟨u, isUniverse, typed⟩ := inventory_formed.types selected
    refine ⟨u, isUniverse, ?_⟩
    simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
      typed.mapHead (extensionMorphism baseRules inventory_extends_signature)
  values := by
    intro name type value typeSelected valueSelected
    have typed := inventory_formed.values typeSelected valueSelected
    simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
      typed.mapHead (extensionMorphism baseRules inventory_extends_signature)
  noSelfDelta := fun selected => inventory_formed.noSelfDelta selected

theorem liftJudgment {n : Nat} {context : Tower.Ctx n}
    {term type : Tower.Tm n}
    (judgment : FormationSensitive.Judgment inventoryRules context term type) :
    FormationSensitive.Judgment rules context term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
    judgment.mapHead (extensionMorphism baseRules inventory_extends_signature)

#print axioms sourceConstructorEntries_eq
#print axioms textual_source_eq
#print axioms inventory_admitted
#print axioms inventory_formed
#print axioms rename_liftChildren
#print axioms subst_liftChildren
#print axioms signature_formed

end Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeGuest
