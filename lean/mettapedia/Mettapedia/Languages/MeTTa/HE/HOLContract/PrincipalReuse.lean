import Mettapedia.Languages.MeTTa.HE.HOLContract.PrincipalNative
import Mettapedia.Machines.ReadCertifiedQueryReuse

/-!
# Reusing principal types: a read-certified type query

`Machines.ReadCertifiedQueryReuse` reuses a recorded observation while its read certificate
still agrees with the store.  The principal checker's answer for an expression reads only the
declarations of the expression's subatoms (`principal_congr`), so it is such an observation:
the store is the declarations, the reads are the declarations of the subatoms, and a recorded
answer is reused exactly while they are unchanged (`typeQueries`, `reuse_principal`).

A type query reads no equation.  Adding an atom that is not a type declaration, such as an
equation, keeps every recorded certificate valid (`reads_agree_after_add`), so the type queries
and the plans of equation bodies keep separate dependency sets; adding a declaration of a
subatom does not (`Controls.declaration_breaks_certificate`).  The certificate covers the
contract's answer, which no subtype declaration changes; a cache of HE's own answers also reads
the subtype declarations (`subtype_edge_outside_declarations`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract.Principal

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.TypeGrounding
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type

/-! ## What a type query reads -/

mutual

/-- The subatoms of an atom, the atom first. -/
def subatomList : Atom → List Atom
  | .symbol name => [.symbol name]
  | .var name => [.var name]
  | .grounded value => [.grounded value]
  | .expression atoms => .expression atoms :: subatomLists atoms

def subatomLists : List Atom → List Atom
  | [] => []
  | atom :: atoms => subatomList atom ++ subatomLists atoms

end

theorem self_mem_subatomList : ∀ atom : Atom, atom ∈ subatomList atom
  | .symbol _ => by simp [subatomList]
  | .var _ => by simp [subatomList]
  | .grounded _ => by simp [subatomList]
  | .expression _ => by simp [subatomList]

theorem subatomList_subset_of_mem {atom : Atom} :
    ∀ {atoms : List Atom}, atom ∈ atoms → ∀ sub ∈ subatomList atom, sub ∈ subatomLists atoms
  | [], member => by simp at member
  | first :: rest, member => by
      intro sub inner
      rcases List.mem_cons.mp member with rfl | inRest
      · simp [subatomLists, inner]
      · simp [subatomLists, subatomList_subset_of_mem inRest sub inner]

theorem candidatesList_congr {space other : Space} :
    ∀ {atoms : List Atom},
      (∀ atom ∈ atoms, ∀ position,
        candidates space position atom = candidates other position atom) →
      ∀ position index,
        candidatesList space position index atoms = candidatesList other position index atoms
  | [], _, _, _ => by simp [candidatesList]
  | atom :: atoms, same, position, index => by
      simp only [candidatesList]
      rw [same atom (by simp) (position ++ [index]),
        candidatesList_congr (fun other member => same other (List.mem_cons_of_mem _ member))
          position (index + 1)]

/-- **The candidates read only the declarations of the subatoms.** -/
theorem candidates_congr {space other : Space} :
    ∀ (atom : Atom) (position : List ℕ),
      (∀ sub ∈ subatomList atom, declarations space sub = declarations other sub) →
      candidates space position atom = candidates other position atom := by
  intro atom
  induction atom using Atom.rec (motive_2 := fun atoms =>
      ∀ atom ∈ atoms, ∀ position : List ℕ,
        (∀ sub ∈ subatomList atom, declarations space sub = declarations other sub) →
        candidates space position atom = candidates other position atom) with
  | symbol name =>
      intro position same
      simp only [candidates, declaredCandidates]
      rw [same _ (self_mem_subatomList _)]
  | var name =>
      intro position same
      simp only [candidates, declaredCandidates]
      rw [same _ (self_mem_subatomList _)]
  | grounded value =>
      intro position same
      simp only [candidates, declaredCandidates]
      rw [same _ (self_mem_subatomList _)]
  | expression atoms ih =>
      intro position same
      cases atoms with
      | nil =>
          simp only [candidates, declaredCandidates]
          rw [same _ (self_mem_subatomList _)]
      | cons head arguments =>
          have below : ∀ atom ∈ head :: arguments, ∀ sub ∈ subatomList atom,
              declarations space sub = declarations other sub := fun atom member sub inner =>
            same sub (List.mem_cons_of_mem _ (subatomList_subset_of_mem member sub inner))
          have pointwise : ∀ atom ∈ head :: arguments, ∀ position,
              candidates space position atom = candidates other position atom :=
            fun atom member position => ih atom member position (below atom member)
          have whole := same _ (self_mem_subatomList (.expression (head :: arguments)))
          simp only [candidates, declaredCandidates]
          rw [pointwise head (by simp) (position ++ [0]),
            candidatesList_congr (fun atom member => pointwise atom (List.mem_cons_of_mem _ member))
              position 1,
            whole]
  | nil => rename_i _ member _ _; simp at member
  | cons first rest firstIH restIH =>
      rename_i atom member position same
      rcases List.mem_cons.mp member with rfl | inRest
      · exact firstIH position same
      · exact restIH atom inRest position same

/-- **The principal types read only the declarations of the subatoms.** -/
theorem principal_congr {space other : Space} {expression : Atom}
    (same : ∀ sub ∈ subatomList expression, declarations space sub = declarations other sub) :
    principal space expression = principal other expression := by
  unfold principal
  rw [candidates_congr expression [] same]

/-! ## The type query as a read-certified family -/

open Mettapedia.Machines.ReadCertifiedQueryReuse

/-- The reads of the type query of an expression: the declarations of its subatoms. -/
def typeQueryReads (space : Space) (expression : Atom) :
    Mettapedia.Machines.ReadOnlyQuery.Reads Atom (List Atom) :=
  (subatomList expression).map fun sub => (sub, declarations space sub)

/-- **The principal-type query is read-certified.**  The store is the declarations, a query is an
expression, and its observation is its principal types with the declarations it read. -/
def typeQueries :
    Supported.Family Space Unit Atom Atom (List Atom) (Option (List TypeTerm)) where
  authority := fun _ => ()
  memory := declarations
  observe := fun space expression => ⟨principal space expression, typeQueryReads space expression⟩
  certifies := by
    intro space expression read member
    obtain ⟨sub, _, rfl⟩ := List.mem_map.mp member
    rfl
  stable := by
    intro first second expression _ agrees
    apply principal_congr
    intro sub member
    exact agrees (sub, declarations first sub) (List.mem_map.mpr ⟨sub, member, rfl⟩)

/-- **Reuse is exact.**  A recorded principal-type answer, reused while the declarations it read
are unchanged, is the answer the checker computes now; otherwise the query runs again. -/
theorem reuse_principal (space : Space) (expression : Atom)
    (entry : Entry Unit Atom Atom (List Atom) (Option (List TypeTerm)))
    (recorded : Supported.Recorded typeQueries entry) :
    (Supported.reuse typeQueries space expression entry).1 = principal space expression :=
  Supported.reuse_exact typeQueries space expression entry recorded

/-- **Equations are not read.**  Adding an atom that is not a type declaration keeps the read
certificate of every type query valid. -/
theorem reads_agree_after_add {space : Space} {atom : Atom}
    (notDeclaration : Space.isTypeAnnotation atom = false) (expression : Atom) :
    Mettapedia.Machines.ReadOnlyQuery.Agrees (declarations (space.add atom))
      (typeQueryReads space expression) := by
  intro read member
  obtain ⟨sub, _, rfl⟩ := List.mem_map.mp member
  exact sameDeclarations_add notDeclaration sub

namespace Controls

/-- The equation `(= (twice $x) $x)`. -/
abbrev equation : Atom :=
  .expression [.symbol "=", .expression [.symbol "twice", .var "x"], .var "x"]

/-- The declaration `(: z Nat)`. -/
abbrev declaration : Atom := .expression [.symbol ":", .symbol "z", .symbol "Nat"]

/-- **Positive control: an equation keeps the certificate of `z`.** -/
theorem equation_keeps_certificate :
    Mettapedia.Machines.ReadOnlyQuery.Agrees (declarations ((Space.ofList []).add equation))
      (typeQueryReads (Space.ofList []) (.symbol "z")) :=
  reads_agree_after_add (by decide) _

/-- **Negative control: a declaration of `z` breaks the certificate of `z`.** -/
theorem declaration_breaks_certificate :
    ¬Mettapedia.Machines.ReadOnlyQuery.Agrees (declarations ((Space.ofList []).add declaration))
      (typeQueryReads (Space.ofList []) (.symbol "z")) := by
  intro agrees
  have := agrees (.symbol "z", declarations (Space.ofList []) (.symbol "z"))
    (by simp [typeQueryReads, subatomList])
  revert this
  decide

end Controls

end Mettapedia.Languages.MeTTa.HE.HOLContract.Principal

#print axioms Mettapedia.Languages.MeTTa.HE.HOLContract.Principal.principal_congr
#print axioms Mettapedia.Languages.MeTTa.HE.HOLContract.Principal.typeQueries
#print axioms Mettapedia.Languages.MeTTa.HE.HOLContract.Principal.reuse_principal
#print axioms Mettapedia.Languages.MeTTa.HE.HOLContract.Principal.reads_agree_after_add
#print axioms Mettapedia.Languages.MeTTa.HE.HOLContract.Principal.Controls.declaration_breaks_certificate
