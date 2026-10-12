import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeKindEncoding

/-!
# Executable cube kind inference emits common native certificates

Finite argument traversal constructs actual dependent kind evidence. Successful
inference emits an ordinary native witness and its complete finite rule tree.
The independent free-code formation relation characterizes inference exactly;
the full native checker validates every emitted tree.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeKindSearch

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open CubeEnrichment CubeNativeDeclarations CubeNativeKindEncoding
open Mettapedia.OSLF.NativeTypes.Certificates

variable {D : CubeEnrichment.Signature} (vertex : Vertex D)

def collect {n : Nat} {types : Fin n → Type} (values : ∀ position, Option (types position)) :
    Option (∀ position, types position) :=
  if accepted : ∀ position, (values position).isSome = true then
    some (fun position => (values position).get (accepted position)) else none

theorem collect_exact {n : Nat} {types : Fin n → Type} (values : ∀ position, Option (types position)) :
    (collect values).isSome = true ↔ ∀ position, (values position).isSome = true := by
  unfold collect
  split <;> simp_all

def atKind {carrier : D.Carrier} {code : PureCode carrier}
    (computed : Option (Σ kind, Kinded vertex code kind)) (desired : HSort) :
    Option (Kinded vertex code desired) :=
  match computed with
  | none => none
  | some ⟨kind, evidence⟩ =>
      if same : kind = desired then some (same ▸ evidence) else none

theorem atKind_complete {carrier : D.Carrier} {code : PureCode carrier}
    (computed : Option (Σ kind, Kinded vertex code kind)) (desired : HSort)
    (found : computed.isSome = true) (evidence : Kinded vertex code desired) :
    (atKind vertex computed desired).isSome = true := by
  cases computed with
  | none => cases found
  | some result =>
      rcases result with ⟨kind, generated⟩
      have same : kind = desired := Option.some.inj
        ((inferKind_complete generated).symm.trans (inferKind_complete evidence))
      simp only [atKind, dif_pos same, Option.isSome_some]

/-- Unlike extraction from Nonempty witnesses, this inference is computable. -/
def infer : {carrier : D.Carrier} → (code : PureCode carrier) →
    Option (Σ kind, Kinded vertex code kind)
  | _, .operational impossible => nomatch impossible
  | _, .sort .star => some ⟨.box, .star⟩
  | _, .sort .box => none
  | _, .former declaration arguments =>
      (collect (fun position => atKind vertex (infer (arguments position))
        (inputSort D vertex declaration position))).map
        (fun premises => ⟨outputSort D vertex declaration, .former declaration arguments premises⟩)

theorem infer_complete {carrier : D.Carrier} {code : PureCode carrier} {kind : HSort}
    (evidence : Kinded vertex code kind) : (infer vertex code).isSome = true := by
  induction evidence with
  | star => rfl
  | former declaration arguments premises hypotheses =>
      have accepted : ∀ position,
          (atKind vertex (infer vertex (arguments position))
            (inputSort D vertex declaration position)).isSome = true :=
        fun position => atKind_complete vertex _ _ (hypotheses position) (premises position)
      have collected := (collect_exact _).mpr accepted
      change (Option.map _ (collect _)).isSome = true
      cases result : collect (fun position => atKind vertex (infer vertex (arguments position))
          (inputSort D vertex declaration position)) with
      | none => rw [result] at collected; cases collected
      | some value => rfl

theorem infer_exact {carrier : D.Carrier} (code : PureCode carrier) (kind : HSort) :
    (atKind vertex (infer vertex code) kind).isSome = true ↔ Nonempty (Kinded vertex code kind) := by
  constructor
  · intro accepted
    exact ⟨(atKind vertex (infer vertex code) kind).get accepted⟩
  · intro ⟨evidence⟩
    exact atKind_complete vertex _ _ (infer_complete vertex evidence) evidence

def nativeFormation? {carrier : D.Carrier} (code : PureCode carrier) (kind : HSort) :
    Option (TermExpr (symbols D) 0 × Refinement.Certificate (signature vertex)) :=
  (atKind vertex (infer vertex code) kind).map fun evidence =>
    (witness vertex evidence, Refinement.erase
      (witnessFormation vertex (emptyFormed vertex) evidence))

/-- Native output exists precisely when the independent free code judgment
has a witness; this does not claim every raw native certificate has this shape. -/
theorem nativeFormation?_exact {carrier : D.Carrier} (code : PureCode carrier) (kind : HSort) :
    (nativeFormation? vertex code kind).isSome = true ↔ Nonempty (Kinded vertex code kind) := by
  unfold nativeFormation?
  rw [Option.isSome_map]
  exact infer_exact vertex code kind

variable [DecidableEq D.Carrier] [DecidableEq D.Former]

theorem nativeFormation?_checked {carrier : D.Carrier} (code : PureCode carrier) (kind : HSort)
    (term : TermExpr (symbols D) 0) (certificate : Refinement.Certificate (signature vertex))
    (emitted : nativeFormation? vertex code kind = some (term, certificate)) :
    Refinement.check certificate (.term .nil term (typingType carrier (encode code) (sortCode carrier kind 0))) = true := by
  unfold nativeFormation? at emitted
  cases returned : atKind vertex (infer vertex code) kind with
  | none => rw [returned] at emitted; cases emitted
  | some evidence =>
      rw [returned] at emitted
      cases emitted
      exact Refinement.check_erase (witnessFormation vertex (emptyFormed vertex) evidence)

variable [Encodable D.Carrier] [Encodable D.Former]

theorem emitted_discoverable {carrier : D.Carrier} (code : PureCode carrier) (kind : HSort)
    (term : TermExpr (symbols D) 0) (certificate : Refinement.Certificate (signature vertex))
    (emitted : nativeFormation? vertex code kind = some (term, certificate)) :
    ∃ found, (CubeNativeDeclarations.search vertex
      (.term .nil term (typingType carrier (encode code) (sortCode carrier kind 0)))
      (Tree.discoveryBound (Tree.wireSize certificate))).found = some found :=
  CubeNativeDeclarations.search_discovers vertex _ certificate
    (nativeFormation?_checked vertex code kind term certificate emitted)

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeKindSearch
