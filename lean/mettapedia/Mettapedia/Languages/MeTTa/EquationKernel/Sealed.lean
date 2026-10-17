import Mettapedia.Languages.MeTTa.EquationKernel.Certificate
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Sealed theorems: the LCF form of the kernel

A `Theorem program` is a claim `source →* target` that only the kernel rules
produce; its type records its theory, and `Theorem.weaken` moves it to a
theory containing that one, checked by `included`. `SealedTheorem` carries
the theory as data, as the MeTTa kernel's sealed values do. Its constructor is private to this file. Elsewhere a theorem comes
from `Theorem.refl`, `Theorem.step`, `Theorem.congr` and `Theorem.trans`, or
from minting an accepted certificate. A theorem stores no certificate: at run
time it is its two atoms, and its proof field is erased.

Recording runs the same rules and appends one row per rule application to a
session log. A recorded theorem is its row index in that log; a theorem used
twice is cited twice and written once. Exporting the log gives a certificate
the checker accepts (`Session.check_certificate`), and the recorded rules compute
the same claims as the unrecorded ones (`Session.step_claim`).

Minting replays a certificate through the sealed rules. Replaying and
checking are one computation (`mintRows_claims`), so a certificate mints a
theorem exactly when it is accepted (`mint_isSome_iff_check`). A theorem of a
claim exists exactly when an accepted certificate exists
(`nonempty_theorem_iff_exists_check`), and exactly when the claim is
reachable (`nonempty_theorem_iff_reaches`).

Reading a theorem returns the judgment it retains, variables included; renaming
or instantiating them is a separate inference (`Theorem.instantiate`). A
reading that renamed variables apart would break transitivity
(`InspectionScenarios`). A theory is identified exactly: any hash into a finite
type identifies two theories that prove different claims
(`hash_identification_unsound`). Theorems of two theories combine in their
union only when a checked map allows it (`SealedTheorem.join`): definitional
theories with conflicting definitions are not joined.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.EquationKernel

open Mettapedia.Languages.MeTTa.OSLFCore (Atom Atomspace)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Var Subst subst vars)

/-- A claim minted by the kernel rules. -/
structure Theorem (program : List Atom) where
  private mk ::
  source : Atom
  target : Atom
  derived : Derives (spaceOf program) source target

namespace Theorem

variable {program : List Atom}

def claim (theorem_ : Theorem program) : Claim := (theorem_.source, theorem_.target)

theorem sound (theorem_ : Theorem program) :
    Reaches (spaceOf program) theorem_.source theorem_.target :=
  theorem_.derived.reaches

theorem ext {first second : Theorem program} (same : first.claim = second.claim) :
    first = second := by
  rcases first with ⟨source, target, _⟩
  rcases second with ⟨source', target', _⟩
  simp only [claim, Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  rfl

/-- Reflexivity. -/
def refl (program : List Atom) (atom : Atom) : Theorem program := ⟨atom, atom, .refl atom⟩

theorem stored_of_sides {program : List Atom} {citation : Citation} {left right : Atom}
    (sides : equationSides citation.equation = some (left, right))
    (cited : citation.copy < program.count citation.equation) :
    Atom.equality left right ∈ (spaceOf program).atoms := by
  have stored := (Citation.valid_spaceOf.mpr cited).mem
  rwa [equationSides_eq_some.mp sides] at stored

/-- One application of a cited stored copy at a position of the target. -/
def step (theorem_ : Theorem program) (citation : Citation) (path : List Nat)
    (bindings : Bindings) : Option (Theorem program) :=
  match sides : equationSides citation.equation with
  | some (left, right) =>
      if valid : citation.copy < program.count citation.equation ∧
          subatom? theorem_.target path = some (subst bindings.toSubst left) then
        match replaced : replaceAt? theorem_.target path (subst bindings.toSubst right) with
        | some next => some ⟨theorem_.source, next,
            .step path bindings.toSubst theorem_.derived (stored_of_sides sides valid.1)
              valid.2 replaced⟩
        | none => none
      else none
  | none => none

/-- Congruence in one argument. -/
def congr (left : List Atom) (theorem_ : Theorem program) (right : List Atom) : Theorem program :=
  ⟨.expression (left ++ theorem_.source :: right), .expression (left ++ theorem_.target :: right),
    .congr left right theorem_.derived⟩

/-- Transitivity, when the middle atoms are equal. -/
def trans (first second : Theorem program) : Option (Theorem program) :=
  if same : first.target = second.source then
    some ⟨first.source, second.target, .trans first.derived (same ▸ second.derived)⟩
  else none

theorem step_claim (theorem_ : Theorem program) (citation : Citation) (path : List Nat)
    (bindings : Bindings) :
    (theorem_.step citation path bindings).map claim =
      (Row.step 0 citation path bindings).claim? program [theorem_.claim] := by
  unfold step
  simp only [Row.claim?, List.getElem?_cons_zero, claim]
  split
  · rename_i left right sides
    simp only [sides]
    split_ifs with valid
    · split
      · rename_i next replaced
        simp only [replaced, Option.map_some]
        rfl
      · rename_i replaced
        simp only [replaced, Option.map_none]
    · rfl
  · rename_i sides
    simp [sides]

theorem congr_claim (left : List Atom) (theorem_ : Theorem program) (right : List Atom) :
    (congr left theorem_ right).claim =
      (.expression (left ++ theorem_.source :: right), .expression (left ++ theorem_.target :: right)) :=
  rfl

/-- Multiset inclusion of theories, decided by counts. -/
def _root_.Mettapedia.Languages.MeTTa.EquationKernel.included (small large : List Atom) : Bool :=
  small.all fun equation => decide (small.count equation ≤ large.count equation)

theorem _root_.Mettapedia.Languages.MeTTa.EquationKernel.included_mem {small large : List Atom}
    (contained : included small large = true) {equation : Atom} (member : equation ∈ small) :
    equation ∈ large := by
  have bound := of_decide_eq_true ((List.all_eq_true.mp contained) equation member)
  exact List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr member) bound)

/-- A theorem of a theory is a theorem of every theory containing it. -/
def weaken (theorem_ : Theorem program) (larger : List Atom) (contained : included program larger = true) :
    Theorem larger :=
  ⟨theorem_.source, theorem_.target, Derives.of_reaches (theorem_.sound.mono fun _ member =>
    mem_spaceOf.mpr (included_mem contained (mem_spaceOf.mp member)))⟩

theorem weaken_claim (theorem_ : Theorem program) (larger : List Atom)
    (contained : included program larger = true) :
    (theorem_.weaken larger contained).claim = theorem_.claim := rfl

theorem trans_claim (first second : Theorem program) :
    (first.trans second).map claim =
      (Row.trans 0 1).claim? program [first.claim, second.claim] := by
  unfold trans
  simp only [Row.claim?, claim, List.getElem?_cons_zero, List.getElem?_cons_succ]
  split_ifs with same
  · rfl
  · rfl

end Theorem

/-! ## Minting: replaying a certificate through the sealed rules -/

/-- The theorem of one row, from the theorems of the earlier rows. -/
def Row.mint? {program : List Atom} (table : List (Theorem program)) : Row → Option (Theorem program)
  | .refl atom => some (Theorem.refl program atom)
  | .step prior citation path bindings =>
      (table[prior]?).bind fun theorem_ => theorem_.step citation path bindings
  | .congr left inner right => (table[inner]?).map fun theorem_ => Theorem.congr left theorem_ right
  | .trans first second =>
      (table[first]?).bind fun earlier => (table[second]?).bind fun later => earlier.trans later

def mintRows {program : List Atom} : List (Theorem program) → List Row → Option (List (Theorem program))
  | table, [] => some table
  | table, row :: rows =>
      match row.mint? table with
      | some theorem_ => mintRows (table ++ [theorem_]) rows
      | none => none

/-- Mint the theorem of a certificate's root, if the certificate is accepted
for the claim. -/
def mint (program : List Atom) (certificate : Certificate) (claim : Claim) :
    Option (Theorem program) :=
  ((mintRows [] certificate.rows).bind fun table => table[certificate.root]?).bind
    fun theorem_ => if theorem_.claim = claim then some theorem_ else none

theorem Row.claim?_step_at {program : List Atom} {table other : List Claim} {prior : Nat}
    (same : table[prior]? = other[0]?) (citation : Citation) (path : List Nat)
    (bindings : Bindings) :
    (Row.step prior citation path bindings).claim? program table =
      (Row.step 0 citation path bindings).claim? program other := by
  simp only [Row.claim?, same]

theorem Row.claim?_trans_at {program : List Atom} {table other : List Claim} {first second : Nat}
    (sameFirst : table[first]? = other[0]?) (sameSecond : table[second]? = other[1]?) :
    (Row.trans first second).claim? program table = (Row.trans 0 1).claim? program other := by
  simp only [Row.claim?, sameFirst, sameSecond]

theorem Row.mint?_claim {program : List Atom} (table : List (Theorem program)) (row : Row) :
    (row.mint? table).map Theorem.claim = row.claim? program (table.map Theorem.claim) := by
  cases row with
  | refl atom => rfl
  | step prior citation path bindings =>
      cases found : table[prior]? with
      | none => simp [Row.mint?, Row.claim?, List.getElem?_map, found]
      | some theorem_ =>
          simp only [Row.mint?, found, Option.bind_some]
          rw [theorem_.step_claim]
          exact (Row.claim?_step_at (table := table.map Theorem.claim) (other := [theorem_.claim])
            (by simp [List.getElem?_map, found]) citation path bindings).symm
  | congr left inner right =>
      simp only [Row.mint?, Row.claim?, List.getElem?_map, Option.map_map]
      rfl
  | trans first second =>
      cases atFirst : table[first]? with
      | none => simp [Row.mint?, Row.claim?, List.getElem?_map, atFirst]
      | some earlier =>
          cases atSecond : table[second]? with
          | none =>
              simp only [Row.mint?, atFirst, atSecond, Option.bind_some, Option.bind_none,
                Option.map_none, Row.claim?, List.getElem?_map, Option.map_some]
          | some later =>
              simp only [Row.mint?, atFirst, atSecond, Option.bind_some]
              rw [earlier.trans_claim later]
              exact (Row.claim?_trans_at (table := table.map Theorem.claim)
                (other := [earlier.claim, later.claim])
                (by simp [List.getElem?_map, atFirst]) (by simp [List.getElem?_map, atSecond])).symm

/-- Replaying through the sealed rules computes exactly the checker's table. -/
theorem mintRows_claims {program : List Atom} (table : List (Theorem program)) (rows : List Row) :
    (mintRows table rows).map (List.map Theorem.claim) =
      checkRows program (table.map Theorem.claim) rows := by
  induction rows generalizing table with
  | nil => rfl
  | cons row rows ih =>
      have same := Row.mint?_claim table row
      simp only [mintRows, checkRows]
      cases minted : row.mint? table with
      | none =>
          rw [minted] at same
          rw [← same]
          rfl
      | some theorem_ =>
          rw [minted] at same
          rw [← same]
          simp only [Option.map_some]
          have := ih (table ++ [theorem_])
          simpa using this

theorem mint_claim {program : List Atom} {certificate : Certificate} {claim : Claim}
    {theorem_ : Theorem program} (minted : mint program certificate claim = some theorem_) :
    theorem_.claim = claim := by
  unfold mint at minted
  obtain ⟨found, _, accepted⟩ := Option.bind_eq_some_iff.mp minted
  split_ifs at accepted with same
  cases accepted
  exact same

/-- Checking a certificate and minting from it are one computation. -/
theorem mint_isSome_iff_check (program : List Atom) (certificate : Certificate) (claim : Claim) :
    (mint program certificate claim).isSome = true ↔ check program certificate claim = true := by
  have tables := mintRows_claims (program := program) [] certificate.rows
  simp only [List.map_nil] at tables
  rw [check_eq_checkReference]
  unfold mint checkReference
  cases minted : mintRows [] certificate.rows with
  | none =>
      rw [minted] at tables
      rw [← tables]
      simp
  | some table =>
      rw [minted] at tables
      rw [← tables]
      simp only [Option.bind_some, Option.map_some, List.getElem?_map]
      cases table[certificate.root]? with
      | none => simp
      | some theorem_ =>
          simp only [Option.bind_some, Option.map_some, Option.some.injEq]
          split_ifs with same <;> simp [same]

/-! ## Recording -/

/-- A recording session: the certificate rows written so far and the
theorem minted by each row. -/
structure Session (program : List Atom) where
  rows : List Row
  theorems : List (Theorem program)
  replayed : mintRows [] rows = some theorems

namespace Session

variable {program : List Atom}

def empty : Session program := ⟨[], [], rfl⟩

theorem mintRows_append {table : List (Theorem program)} {front : List Row}
    {middle : List (Theorem program)} (minted : mintRows table front = some middle) (back : List Row) :
    mintRows table (front ++ back) = mintRows middle back := by
  induction front generalizing table with
  | nil =>
      cases minted
      rfl
  | cons row rows ih =>
      simp only [mintRows] at minted
      simp only [List.cons_append, mintRows]
      cases found : row.mint? table with
      | none =>
          rw [found] at minted
          cases minted
      | some theorem_ =>
          rw [found] at minted
          exact ih minted

/-- Apply one rule to recorded theorems and record its row. -/
def record (session : Session program) (row : Row) : Option (Session program × Nat) :=
  match minted : row.mint? session.theorems with
  | some theorem_ => some (⟨session.rows ++ [row], session.theorems ++ [theorem_], by
      rw [mintRows_append session.replayed]
      simp [mintRows, minted]⟩, session.theorems.length)
  | none => none

def refl (session : Session program) (atom : Atom) : Option (Session program × Nat) :=
  session.record (.refl atom)

def step (session : Session program) (prior : Nat) (citation : Citation) (path : List Nat)
    (bindings : Bindings) : Option (Session program × Nat) :=
  session.record (.step prior citation path bindings)

def congr (session : Session program) (left : List Atom) (inner : Nat) (right : List Atom) :
    Option (Session program × Nat) :=
  session.record (.congr left inner right)

def trans (session : Session program) (first second : Nat) : Option (Session program × Nat) :=
  session.record (.trans first second)

/-- The certificate of a recorded theorem: the whole log, rooted at its row. -/
def certificate (session : Session program) (index : Nat) : Certificate := ⟨session.rows, index⟩

/-- The certificate of every recorded theorem is accepted. -/
theorem check_certificate (session : Session program) {index : Nat} {theorem_ : Theorem program}
    (recorded : session.theorems[index]? = some theorem_) :
    check program (session.certificate index) theorem_.claim = true := by
  have tables := mintRows_claims (program := program) [] session.rows
  rw [session.replayed] at tables
  simp only [List.map_nil, Option.map_some] at tables
  rw [check_eq_checkReference]
  unfold checkReference certificate
  simp only [← tables, List.getElem?_map, recorded, Option.map_some, decide_true]

theorem record_extends {session next : Session program} {row : Row} {index : Nat}
    (recorded : session.record row = some (next, index)) :
    ∃ theorem_, next.theorems = session.theorems ++ [theorem_] ∧ index = session.theorems.length ∧
      row.mint? session.theorems = some theorem_ := by
  unfold record at recorded
  split at recorded
  · rename_i theorem_ minted
    cases recorded
    exact ⟨theorem_, rfl, rfl, minted⟩
  · cases recorded

/-- Recording does not change what a rule computes: the recorded step mints
the same claim as the unrecorded sealed step. -/
theorem step_claim {session next : Session program} {prior index : Nat} {citation : Citation}
    {path : List Nat} {bindings : Bindings} {earlier : Theorem program}
    (atPrior : session.theorems[prior]? = some earlier)
    (recorded : session.step prior citation path bindings = some (next, index)) :
    ∃ theorem_, next.theorems[index]? = some theorem_ ∧
      earlier.step citation path bindings = some theorem_ := by
  obtain ⟨theorem_, extended, rfl, minted⟩ := record_extends recorded
  refine ⟨theorem_, by simp [extended], ?_⟩
  simpa [Row.mint?, atPrior] using minted

end Session

/-! ## Adequacy of the two styles -/

/-- Every derivation is minted by the public sealed rules alone. -/
theorem exists_theorem_of_derives {program : List Atom} {source target : Atom}
    (derived : Derives (spaceOf program) source target) :
    ∃ theorem_ : Theorem program, theorem_.claim = (source, target) := by
  obtain ⟨rows, claims, valid, last⟩ := exists_rows_of_derives derived []
  have checked : check program ⟨rows, claims.length - 1⟩ (source, target) = true :=
    (check_exact _ _ _).mpr ⟨_, valid, by simpa using getElem?_last (table := []) last⟩
  obtain ⟨theorem_, minted⟩ := Option.isSome_iff_exists.mp
    ((mint_isSome_iff_check _ _ _).mpr checked)
  exact ⟨theorem_, mint_claim minted⟩

/-- A sealed theorem of a claim exists exactly when an accepted certificate
of it exists. -/
theorem nonempty_theorem_iff_exists_check (program : List Atom) (claim : Claim) :
    (∃ theorem_ : Theorem program, theorem_.claim = claim) ↔
      ∃ certificate, check program certificate claim = true := by
  constructor
  · rintro ⟨theorem_, rfl⟩
    exact exists_check_of_reaches theorem_.sound
  · rintro ⟨certificate, accepted⟩
    obtain ⟨theorem_, minted⟩ := Option.isSome_iff_exists.mp
      ((mint_isSome_iff_check _ _ _).mpr accepted)
    exact ⟨theorem_, mint_claim minted⟩

theorem nonempty_theorem_iff_reaches (program : List Atom) (source target : Atom) :
    (∃ theorem_ : Theorem program, theorem_.claim = (source, target)) ↔
      Reaches (spaceOf program) source target := by
  rw [nonempty_theorem_iff_exists_check, exists_check_iff_reaches]

/-! ## Theorems with their theory

The MeTTa kernel seals a theorem together with its theory. A step cites the
premise's own theory, transitivity requires equal theories, and a theorem
moves to a larger theory only by a checked weakening. -/

structure SealedTheorem where
  theory : List Atom
  theorem_ : Theorem theory

namespace SealedTheorem

def claim (sealed : SealedTheorem) : Claim := sealed.theorem_.claim

theorem sound (sealed : SealedTheorem) : Reaches (spaceOf sealed.theory) sealed.claim.1 sealed.claim.2 :=
  sealed.theorem_.sound

def refl (theory : List Atom) (atom : Atom) : SealedTheorem := ⟨theory, Theorem.refl theory atom⟩

def step (sealed : SealedTheorem) (citation : Citation) (path : List Nat) (bindings : Bindings) :
    Option SealedTheorem :=
  (sealed.theorem_.step citation path bindings).map (⟨sealed.theory, ·⟩)

def congr (left : List Atom) (sealed : SealedTheorem) (right : List Atom) : SealedTheorem :=
  ⟨sealed.theory, Theorem.congr left sealed.theorem_ right⟩

def trans (first second : SealedTheorem) : Option SealedTheorem :=
  if same : first.theory = second.theory then
    (first.theorem_.trans (same ▸ second.theorem_)).map (⟨first.theory, ·⟩)
  else none

def weaken (sealed : SealedTheorem) (larger : List Atom) : Option SealedTheorem :=
  if contained : included sealed.theory larger = true then
    some ⟨larger, sealed.theorem_.weaken larger contained⟩
  else none

theorem step_theory {sealed result : SealedTheorem} {citation : Citation} {path : List Nat}
    {bindings : Bindings} (stepped : sealed.step citation path bindings = some result) :
    result.theory = sealed.theory := by
  unfold step at stepped
  obtain ⟨theorem_, _, rfl⟩ := Option.map_eq_some_iff.mp stepped
  rfl

theorem trans_theory {first second result : SealedTheorem}
    (joined : first.trans second = some result) :
    first.theory = second.theory ∧ result.theory = first.theory := by
  unfold trans at joined
  split at joined
  · rename_i same
    obtain ⟨theorem_, _, rfl⟩ := Option.map_eq_some_iff.mp joined
    exact ⟨same, rfl⟩
  · cases joined

theorem weaken_theory {sealed result : SealedTheorem} {larger : List Atom}
    (weakened : sealed.weaken larger = some result) :
    included sealed.theory larger = true ∧ result.theory = larger ∧ result.claim = sealed.claim := by
  unfold weaken at weakened
  split at weakened
  · rename_i contained
    cases weakened
    exact ⟨contained, rfl, rfl⟩
  · cases weakened

end SealedTheorem

/-- Every theory-carrying theorem is a certificate-checked claim of its own
theory, and conversely. -/
theorem nonempty_sealed_iff_exists_check (theory : List Atom) (claim : Claim) :
    (∃ sealed : SealedTheorem, sealed.theory = theory ∧ sealed.claim = claim) ↔
      ∃ certificate, check theory certificate claim = true := by
  constructor
  · rintro ⟨⟨theory', theorem_⟩, rfl, rfl⟩
    exact (nonempty_theorem_iff_exists_check theory' _).mp ⟨theorem_, rfl⟩
  · intro accepted
    obtain ⟨theorem_, same⟩ := (nonempty_theorem_iff_exists_check theory claim).mpr accepted
    exact ⟨⟨theory, theorem_⟩, rfl, same⟩

namespace SealedScenarios

def atomA : Atom := .symbol "A"
def atomB : Atom := .symbol "B"
def atomC : Atom := .symbol "C"
def equationAB : Atom := Atom.equality atomA atomB
def equationBC : Atom := Atom.equality atomB atomC

def fromA : Option SealedTheorem := (SealedTheorem.refl [equationAB] atomA).step ⟨equationAB, 0⟩ [] []

example : fromA.map SealedTheorem.claim = some (atomA, atomB) := by decide

/-- The reviewed mixing: a theorem of `{A → B}` cannot take a step by
`B → C`, which its theory does not contain. -/
example : (fromA.bind fun sealed => sealed.step ⟨equationBC, 0⟩ [] []).map SealedTheorem.claim = none := by
  decide

/-- Nor can it be joined with a theorem of `{B → C}`. -/
example : (fromA.bind fun first =>
    ((SealedTheorem.refl [equationBC] atomB).step ⟨equationBC, 0⟩ [] []).bind fun second =>
      first.trans second).map SealedTheorem.claim = none := by decide

/-- After a checked weakening to `{A → B, B → C}` the step is licensed, and
the result records the larger theory. -/
example : ((fromA.bind fun sealed => sealed.weaken [equationAB, equationBC]).bind fun sealed =>
    sealed.step ⟨equationBC, 0⟩ [] []).map (fun sealed => (sealed.theory, sealed.claim)) =
      some ([equationAB, equationBC], (atomA, atomC)) := by decide

/-- Weakening to a theory that lacks an equation is refused. -/
example : ((SealedTheorem.refl [equationAB, equationBC] atomA).weaken [equationAB]).map
    SealedTheorem.claim = none := by decide

end SealedScenarios

/-! ## Inspection and instantiation

Reading a sealed theorem (`Theorem.claim`, `SealedTheorem.claim`) returns the
judgment it retains. Its variables are constants of the claim (`Judgment`), so
a reading that renamed them would read a different judgment. Instantiating
them, renaming apart included, is a separate inference, sound because
reachability is stable under substituting the whole claim
(`Reaches.substitute`). -/

namespace Theorem

variable {program : List Atom}

/-- Instantiate the variables of a theorem's claim. -/
def instantiate (theorem_ : Theorem program) (θ : Subst) : Theorem program :=
  ⟨subst θ theorem_.source, subst θ theorem_.target,
    Derives.of_reaches (theorem_.sound.substitute θ)⟩

theorem instantiate_claim (theorem_ : Theorem program) (θ : Subst) :
    (theorem_.instantiate θ).claim = (subst θ theorem_.source, subst θ theorem_.target) := rfl

end Theorem

namespace SealedTheorem

/-- Instantiate the variables of a sealed theorem's claim, in its own theory. -/
def instantiate (sealed : SealedTheorem) (θ : Subst) : SealedTheorem :=
  ⟨sealed.theory, sealed.theorem_.instantiate θ⟩

theorem instantiate_theory (sealed : SealedTheorem) (θ : Subst) :
    (sealed.instantiate θ).theory = sealed.theory := rfl

end SealedTheorem

/-- Renaming every variable `v` to `v ++ tag`. -/
def renameApart (tag : String) : Subst := fun name => some (.var (name ++ tag))

/-- A claim with its variables renamed apart. -/
def freshenClaim (tag : String) (claim : Claim) : Claim :=
  (subst (renameApart tag) claim.1, subst (renameApart tag) claim.2)

namespace InspectionScenarios

def x : Atom := .var "x"
def fOf (a : Atom) : Atom := .expression [.symbol "f", a]
def gOf (a : Atom) : Atom := .expression [.symbol "g", a]
def hOf (a : Atom) : Atom := .expression [.symbol "h", a]
def equationFG : Atom := Atom.equality (fOf (.var "y")) (gOf (.var "y"))
def equationGH : Atom := Atom.equality (gOf (.var "z")) (hOf (.var "z"))
def program : List Atom := [equationFG, equationGH]

/-- `(f $x) → (g $x)` and `(g $x) → (h $x)`, about the same variable. -/
def first : Option SealedTheorem :=
  (SealedTheorem.refl program (fOf x)).step ⟨equationFG, 0⟩ [] [("y", x)]
def second : Option SealedTheorem :=
  (SealedTheorem.refl program (gOf x)).step ⟨equationGH, 0⟩ [] [("z", x)]

example : first.map SealedTheorem.claim = some (fOf x, gOf x) := by decide
example : second.map SealedTheorem.claim = some (gOf x, hOf x) := by decide

/-- Read as retained, the two theorems compose. -/
example : (first.bind fun t => second.bind fun u => t.trans u).map SealedTheorem.claim =
    some (fOf x, hOf x) := by decide

/-- The transitivity row on the retained claims gives `(f $x) → (h $x)`. -/
example : (Row.trans 0 1).claim? program [(fOf x, gOf x), (gOf x, hOf x)] = some (fOf x, hOf x) := by
  decide

/-- If each reading renamed variables apart, the same row would refuse: the two
readings of `$x` differ. -/
example : (Row.trans 0 1).claim? program
    [freshenClaim "#1" (fOf x, gOf x), freshenClaim "#2" (gOf x, hOf x)] = none := by decide

/-- And two readings of one theorem would not even agree. -/
example : freshenClaim "#1" (fOf x, gOf x) ≠ freshenClaim "#2" (fOf x, gOf x) := by decide

/-- Renaming apart, when wanted, is an explicit instantiation: a theorem of the
renamed claim, in the same theory. -/
example : (first.map fun t => (t.instantiate (renameApart "#1")).claim) =
    some (freshenClaim "#1" (fOf x, gOf x)) := by decide

end InspectionScenarios

/-! ## Theory identity

A theorem's theory is compared exactly. A hash of a theory is a lookup aid:
any hash into a finite type identifies two theories that prove different
claims, so reading a theorem of one theory in another because their hashes
agree is unsound. -/

theorem Context.eq_hole_of_fill_symbol {context : Context} {a : Atom} {s : String}
    (filled : context.fill a = .symbol s) : context = .hole ∧ a = .symbol s := by
  cases context with
  | hole => exact ⟨rfl, filled⟩
  | arg left inner right => simp [Context.fill] at filled

theorem Context.eq_hole_of_fill_grounded {context : Context} {a : Atom} {g : OSLFCore.GroundedValue}
    (filled : context.fill a = .grounded g) : context = .hole ∧ a = .grounded g := by
  cases context with
  | hole => exact ⟨rfl, filled⟩
  | arg left inner right => simp [Context.fill] at filled

/-- In the theory that defines the symbol `c` as a grounded value, `c` reaches
only itself and that value. -/
theorem reaches_defined_symbol {c : String} {g : OSLFCore.GroundedValue} {target : Atom}
    (reach : Reaches (spaceOf [Atom.equality (.symbol c) (.grounded g)]) (.symbol c) target) :
    target = .symbol c ∨ target = .grounded g := by
  induction reach with
  | refl => exact Or.inl rfl
  | tail _ step ih =>
      cases step with
      | @rewrite left right context σ stored =>
      have sides : left = .symbol c ∧ right = .grounded g := by
        simpa [Atom.equality] using List.mem_singleton.mp (mem_spaceOf.mp stored)
      obtain ⟨rfl, rfl⟩ := sides
      simp only [subst] at ih ⊢
      rcases ih with filled | filled
      · obtain ⟨rfl, _⟩ := Context.eq_hole_of_fill_symbol filled
        exact Or.inr rfl
      · obtain ⟨_, impossible⟩ := Context.eq_hole_of_fill_grounded filled
        cases impossible

/-- The theory that defines `c` as the integer `i`. -/
def definesAs (i : Nat) : List Atom := [Atom.equality (.symbol "c") (.grounded (.int (i : Int)))]

/-- **Hash identification is unsound.** For every hash of theories into a
finite type, two different theories have the same hash, and a claim has a
theorem in one and none in the other. -/
theorem hash_identification_unsound (k : Nat) (hash : List Atom → Fin k) :
    ∃ first second : List Atom, first ≠ second ∧ hash first = hash second ∧
      ∃ claim : Claim, (∃ t : Theorem first, t.claim = claim) ∧
        ¬ ∃ t : Theorem second, t.claim = claim := by
  obtain ⟨i, j, distinct, collide⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (k + 1) => hash (definesAs i))
      (by simp)
  have different : (i : Nat) ≠ j := fun same => distinct (Fin.ext same)
  refine ⟨definesAs i, definesAs j, ?_, collide, (.symbol "c", .grounded (.int i)), ?_, ?_⟩
  · intro same
    simp only [definesAs, Atom.equality, List.cons.injEq, Atom.expression.injEq, Atom.grounded.injEq,
      OSLFCore.GroundedValue.int.injEq, and_true, true_and] at same
    exact different (by omega)
  · rw [nonempty_theorem_iff_reaches]
    exact Relation.ReflTransGen.single
      (Step.of_path (path := []) (σ := fun _ => none) (List.mem_singleton_self _ |> mem_spaceOf.mpr)
        rfl rfl)
  · rw [nonempty_theorem_iff_reaches]
    intro reach
    rcases reaches_defined_symbol reach with impossible | same
    · cases impossible
    · simp only [Atom.grounded.injEq, OSLFCore.GroundedValue.int.injEq] at same
      exact different (by omega)

/-! ## Joining theories

`SealedTheorem.weaken` moves a theorem along a checked inclusion. Two theorems
of different theories combine in a theory containing both, reached by checked
weakenings. For definitional theories, in which each head has one definition,
the union must itself be definitional: conflicting definitions are not joined,
as the HOL kernel refuses to mix objects anchored on different branches. -/

/-- The head symbol an equation defines, if it defines one. -/
def definedHead : Atom → Option String
  | .expression [.symbol "=", .symbol s, _] => some s
  | .expression [.symbol "=", .expression (.symbol s :: _), _] => some s
  | _ => none

/-- No head has two different defining equations. -/
def definitional (theory : List Atom) : Bool :=
  theory.all fun e₁ => theory.all fun e₂ =>
    decide (definedHead e₁ = none) || decide (definedHead e₁ ≠ definedHead e₂) || decide (e₁ = e₂)

namespace SealedTheorem

/-- Join two theorems in the union of their theories, checked definitional. -/
def join (first second : SealedTheorem) : Option (SealedTheorem × SealedTheorem) :=
  if definitional (first.theory ++ second.theory) then
    (first.weaken (first.theory ++ second.theory)).bind fun a =>
      (second.weaken (first.theory ++ second.theory)).map fun b => (a, b)
  else none

theorem join_spec {first second a b : SealedTheorem} (joined : first.join second = some (a, b)) :
    definitional (first.theory ++ second.theory) = true ∧
      a.theory = first.theory ++ second.theory ∧ b.theory = first.theory ++ second.theory ∧
      a.claim = first.claim ∧ b.claim = second.claim := by
  unfold join at joined
  split_ifs at joined with checked
  obtain ⟨a', weakenedA, rest⟩ := Option.bind_eq_some_iff.mp joined
  obtain ⟨b', weakenedB, same⟩ := Option.map_eq_some_iff.mp rest
  cases same
  obtain ⟨_, theoryA, claimA⟩ := weaken_theory weakenedA
  obtain ⟨_, theoryB, claimB⟩ := weaken_theory weakenedB
  exact ⟨checked, theoryA, theoryB, claimA, claimB⟩

end SealedTheorem

namespace JoinScenarios

def c : Atom := .symbol "c"
def d : Atom := .symbol "d"
def one : Atom := .grounded (.int 1)
def two : Atom := .grounded (.int 2)

def cIsOne : Option SealedTheorem := (SealedTheorem.refl [Atom.equality c one] c).step
  ⟨Atom.equality c one, 0⟩ [] []
def cIsTwo : Option SealedTheorem := (SealedTheorem.refl [Atom.equality c two] c).step
  ⟨Atom.equality c two, 0⟩ [] []
def dIsTwo : Option SealedTheorem := (SealedTheorem.refl [Atom.equality d two] d).step
  ⟨Atom.equality d two, 0⟩ [] []

/-- Compatible definitions join; both theorems now live in the union. -/
example : (cIsOne.bind fun t => dIsTwo.bind fun u => t.join u).map
    (fun pair => (pair.1.theory, pair.1.claim, pair.2.claim)) =
      some ([Atom.equality c one, Atom.equality d two], (c, one), (d, two)) := by decide

/-- Conflicting definitions of `c` are not joined. -/
example : (cIsOne.bind fun t => cIsTwo.bind fun u => t.join u).isNone = true := by decide

/-- What the check refuses: in the unchecked union, the defined symbol `c`
reaches two different values. -/
example : ((SealedTheorem.refl [Atom.equality c one, Atom.equality c two] c).step
    ⟨Atom.equality c one, 0⟩ [] []).map SealedTheorem.claim = some (c, one) ∧
  ((SealedTheorem.refl [Atom.equality c one, Atom.equality c two] c).step
    ⟨Atom.equality c two, 0⟩ [] []).map SealedTheorem.claim = some (c, two) := by decide

end JoinScenarios

end Mettapedia.Languages.MeTTa.EquationKernel
