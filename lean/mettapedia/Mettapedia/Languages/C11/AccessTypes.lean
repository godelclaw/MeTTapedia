import Mettapedia.Languages.C11.IntegerProfiles

/-!
# Object access types and scalar alias permissions

This finite type description supports completed integer, character, enum,
floating, pointer, array and aggregate access views. Aggregate identities
are scoped declaration identities; pointer referents are resolved type
identities. Constructing those identities from C declarations, and checking
that every use of an identity has its declared members, are elaboration
obligations. Incomplete types, function compatibility, atomic types and
bit-fields are not interpreted by this interface.

The access permission rules follow N1570 6.5p7. Qualification of the access
view does not grant write permission. Aggregate membership searches only
for compatible or corresponding member types: a character member cannot
make its whole aggregate a universal alias.

Enum compatibility is not closed transitively. Two distinct enums may each
be compatible with their selected integer type without being compatible
with each other. Plain char remains distinct from signed and unsigned char.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.AccessTypes

inductive EnumBase where
  | plainCharacter
  | signed (family : IntegerFamily IntegerExtension)
  | unsigned (family : IntegerFamily IntegerExtension)
  deriving DecidableEq, Repr

inductive FloatingFamily where
  | float | double | longDouble | extended (identity : Nat)
  deriving DecidableEq, Repr

inductive Atom where
  | integer (type : IntegerType IntegerExtension)
  | plainCharacter
  | enumeration (identity : Nat) (base : EnumBase)
  | real (family : FloatingFamily)
  | complex (family : FloatingFamily)
  | pointer (referent : Nat)
  deriving DecidableEq, Repr

def EnumBase.atom : EnumBase → Atom
  | .plainCharacter => .plainCharacter
  | .signed family => .integer (.signed family)
  | .unsigned family => .integer (.unsigned family)

inductive Atom.Compatible : Atom → Atom → Prop where
  | same (atom : Atom) : Compatible atom atom
  | enumBase (identity : Nat) (base : EnumBase) :
      Compatible (.enumeration identity base) base.atom
  | baseEnum (identity : Nat) (base : EnumBase) :
      Compatible base.atom (.enumeration identity base)

def Atom.compatible (first second : Atom) : Bool :=
  first == second || match first, second with
  | .enumeration _ base, other => base.atom == other
  | other, .enumeration _ base => other == base.atom
  | _, _ => false

theorem Atom.compatible_iff (first second : Atom) :
    first.compatible second = true ↔ first.Compatible second := by
  constructor
  · intro accepted
    simp only [compatible, Bool.or_eq_true, beq_iff_eq] at accepted
    rcases accepted with rfl | accepted
    · exact .same _
    · split at accepted
      · rename_i identity base
        have equal : base.atom = second := by simpa only [beq_iff_eq] using accepted
        rw [← equal]
        exact .enumBase identity base
      · rename_i identity base notEnum
        have equal : first = base.atom := by simpa only [beq_iff_eq] using accepted
        rw [equal]
        exact .baseEnum identity base
      · cases accepted
  · intro compatible
    induction compatible with
    | same => simp [Atom.compatible]
    | enumBase identity base => simp [Atom.compatible]
    | baseEnum identity base => cases base <;> simp [Atom.compatible, EnumBase.atom]

inductive Atom.Corresponding : Atom → Atom → Prop where
  | signedUnsigned (family : IntegerFamily IntegerExtension) :
      Corresponding (.integer (.signed family)) (.integer (.unsigned family))
  | unsignedSigned (family : IntegerFamily IntegerExtension) :
      Corresponding (.integer (.unsigned family)) (.integer (.signed family))

def Atom.corresponding : Atom → Atom → Bool
  | .integer (.signed first), .integer (.unsigned second)
  | .integer (.unsigned first), .integer (.signed second) => first == second
  | _, _ => false

theorem Atom.corresponding_iff (first second : Atom) :
    first.corresponding second = true ↔ first.Corresponding second := by
  cases first <;> cases second <;> try { simp only [corresponding]; constructor <;> intro h <;> cases h }
  rename_i first second
  cases first <;> cases second <;> simp only [corresponding, beq_iff_eq]
  all_goals constructor
  all_goals first | (intro h; subst h; constructor) | (intro h; cases h)
  all_goals rfl

def Atom.character : Atom → Bool
  | .plainCharacter | .integer (.signed (.standard .char))
  | .integer (.unsigned (.standard .char)) => true
  | _ => false

inductive AggregateKind where
  | structure | union
  deriving DecidableEq, Repr

inductive ObjectType where
  | scalar (atom : Atom)
  | array (element : ObjectType) (count : Nat)
  | aggregate (kind : AggregateKind) (identity : Nat) (members : List ObjectType)
  deriving Repr

def compareMembers (compare : ObjectType → ObjectType → Bool) : List ObjectType → List ObjectType → Bool
  | [], [] => true
  | first :: tail, second :: rest => compare first second && compareMembers compare tail rest
  | _, _ => false

theorem compareMembers_sound (compare : ObjectType → ObjectType → Bool)
    (sound : ∀ first second, compare first second = true → first = second)
    (first second : List ObjectType) (accepted : compareMembers compare first second = true) : first = second := by
  induction first generalizing second with
  | nil => cases second <;> simp_all [compareMembers]
  | cons head tail ih =>
      cases second with
      | nil => simp [compareMembers] at accepted
      | cons other rest =>
          have pairs : compare head other = true ∧ compareMembers compare tail rest = true := by
            simpa only [compareMembers, Bool.and_eq_true] using accepted
          obtain ⟨heads, tails⟩ := pairs
          rw [sound head other heads, ih rest tails]

theorem compareMembers_self (compare : ObjectType → ObjectType → Bool) (members : List ObjectType)
    (complete : ∀ member ∈ members, compare member member = true) : compareMembers compare members members = true := by
  induction members with
  | nil => rfl
  | cons head tail ih =>
      simp only [compareMembers, complete head (List.mem_cons_self), Bool.true_and]
      exact ih (fun member present => complete member (List.mem_cons_of_mem _ present))

/-- The bound is derived from the input size, rather than a caller-supplied
proof budget. It permits executable equality of the nested type carrier. -/
def compareAt : Nat → ObjectType → ObjectType → Bool
  | 0, _, _ => false
  | _ + 1, .scalar first, .scalar second => first == second
  | fuel + 1, .array first count, .array second other => count == other && compareAt fuel first second
  | fuel + 1, .aggregate kind identity first, .aggregate other otherIdentity second =>
      kind == other && identity == otherIdentity && compareMembers (compareAt fuel) first second
  | _ + 1, _, _ => false

theorem compareAt_sound (fuel : Nat) (first second : ObjectType) (accepted : compareAt fuel first second = true) :
    first = second := by
  induction fuel generalizing first second with
  | zero => simp [compareAt] at accepted
  | succ fuel ih =>
      cases first with
      | scalar atom =>
          cases second <;> simp only [compareAt, beq_iff_eq] at accepted
          · exact congrArg ObjectType.scalar accepted
          all_goals cases accepted
      | array first count =>
          cases second with
          | scalar => simp [compareAt] at accepted
          | aggregate => simp [compareAt] at accepted
          | array second other =>
              have pairs : (count == other) = true ∧ compareAt fuel first second = true := by
                simpa only [compareAt, Bool.and_eq_true] using accepted
              obtain ⟨sizes, elements⟩ := pairs
              have same := beq_iff_eq.mp sizes
              rw [same, ih first second elements]
      | aggregate kind identity first =>
          cases second with
          | scalar => simp [compareAt] at accepted
          | array => simp [compareAt] at accepted
          | aggregate other otherIdentity second =>
              have parts : ((kind == other) = true ∧ (identity == otherIdentity) = true) ∧
                  compareMembers (compareAt fuel) first second = true := by
                simpa only [compareAt, Bool.and_eq_true] using accepted
              obtain ⟨⟨kinds, identities⟩, members⟩ := parts
              have kindEqual := beq_iff_eq.mp kinds
              have identityEqual := beq_iff_eq.mp identities
              have memberEqual := compareMembers_sound (compareAt fuel) ih first second members
              rw [kindEqual, identityEqual, memberEqual]

def maximum : List Nat → Nat
  | [] => 0
  | head :: tail => max head (maximum tail)

theorem member_le_maximum (values : List Nat) (value : Nat) (present : value ∈ values) : value ≤ maximum values := by
  induction values with
  | nil => cases present
  | cons head tail ih =>
      rcases List.mem_cons.mp present with rfl | present
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih present) (Nat.le_max_right _ _)

def height : ObjectType → Nat
  | .scalar _ => 1
  | .array element _ => height element + 1
  | .aggregate _ _ members => maximum (members.map height) + 1
termination_by type => sizeOf type

theorem height_positive (type : ObjectType) : 0 < height type := by
  cases type <;> simp [height]

theorem compareAt_self (fuel : Nat) (type : ObjectType) (bound : height type ≤ fuel) : compareAt fuel type type = true := by
  induction fuel generalizing type with
  | zero => have positive := height_positive type; omega
  | succ fuel ih =>
      cases type with
      | scalar => simp [compareAt]
      | array element count =>
          have smaller : height element ≤ fuel := by simp only [height] at bound; omega
          simp [compareAt, ih element smaller]
      | aggregate kind identity members =>
          simp only [compareAt, beq_self_eq_true, Bool.true_and]
          apply compareMembers_self
          intro member present
          apply ih
          have small := member_le_maximum (members.map height) (height member) (List.mem_map.mpr ⟨member, present, rfl⟩)
          simp only [height] at bound
          omega

def objectEquality (first second : ObjectType) : Decidable (first = second) :=
  if equal : compareAt (height first) first second = true then
    .isTrue (compareAt_sound _ first second equal)
  else .isFalse (fun same => equal (by subst second; exact compareAt_self _ first (Nat.le_refl _)))

instance : DecidableEq ObjectType := objectEquality

inductive Compatible : ObjectType → ObjectType → Prop where
  | scalar {first second : Atom} (atoms : first.Compatible second) :
      Compatible (.scalar first) (.scalar second)
  | array {first second : ObjectType} (count : Nat) (elements : Compatible first second) :
      Compatible (.array first count) (.array second count)
  | aggregate (kind : AggregateKind) (identity : Nat) (first second : List ObjectType) :
      Compatible (.aggregate kind identity first) (.aggregate kind identity second)

def compatible : ObjectType → ObjectType → Bool
  | .scalar first, .scalar second => first.compatible second
  | .array first count, .array second other => count == other && compatible first second
  | .aggregate kind identity _, .aggregate other otherIdentity _ =>
      kind == other && identity == otherIdentity
  | _, _ => false

theorem compatible_iff (first second : ObjectType) :
    compatible first second = true ↔ Compatible first second := by
  cases first with
  | scalar atom =>
      cases second <;> simp only [compatible]
      · rw [Atom.compatible_iff]
        exact ⟨Compatible.scalar, fun related => by cases related; assumption⟩
      all_goals constructor <;> intro h <;> cases h
  | array first count =>
      cases second <;> simp only [compatible]
      · constructor <;> intro h <;> cases h
      · simp only [Bool.and_eq_true, beq_iff_eq, compatible_iff first _]
        constructor
        · rintro ⟨rfl, related⟩; exact .array _ related
        · intro related; cases related; exact ⟨rfl, by assumption⟩
      · constructor <;> intro h <;> cases h
  | aggregate kind identity members =>
      cases second <;> simp only [compatible]
      · constructor <;> intro h <;> cases h
      · constructor <;> intro h <;> cases h
      · simp only [Bool.and_eq_true, beq_iff_eq]
        constructor
        · rintro ⟨rfl, rfl⟩; constructor
        · intro related; cases related; exact ⟨rfl, rfl⟩

termination_by sizeOf first

theorem Compatible.refl (type : ObjectType) : Compatible type type := by
  cases type with
  | scalar atom => exact .scalar (.same atom)
  | array element count => exact .array count (Compatible.refl element)
  | aggregate kind identity members => exact .aggregate kind identity members members
termination_by sizeOf type

def Related (view effective : ObjectType) : Prop :=
  Compatible view effective ∨ ∃ first second, view = .scalar first ∧
    effective = .scalar second ∧ first.Corresponding second

def related (view effective : ObjectType) : Bool :=
  compatible view effective || match view, effective with
  | .scalar first, .scalar second => first.corresponding second
  | _, _ => false

theorem related_iff (view effective : ObjectType) : related view effective = true ↔ Related view effective := by
  cases view <;> cases effective <;> simp only [related, Related, Bool.or_eq_true, compatible_iff]
  all_goals first
    | (simp only [Atom.corresponding_iff, ObjectType.scalar.injEq]; constructor
       · rintro (h | h); exact Or.inl h; exact Or.inr ⟨_, _, rfl, rfl, h⟩
       · rintro (h | ⟨_, _, h₁, h₂, h⟩); exact Or.inl h
         cases h₁; cases h₂; exact Or.inr h)
    | (constructor
       · rintro (h | h); exact Or.inl h; cases h
       · rintro (h | ⟨_, _, h₁, h₂, _⟩); exact Or.inl h
         cases h₁ <;> cases h₂)

/-- A proper array element or aggregate member path, never a pointer path. -/
inductive Member : ObjectType → ObjectType → Prop where
  | element (element : ObjectType) (count : Nat) : Member (.array element count) element
  | array {element target : ObjectType} (count : Nat) (inside : Member element target) :
      Member (.array element count) target
  | direct {members : List ObjectType} (kind : AggregateKind) (identity : Nat)
      (member : ObjectType) (present : member ∈ members) : Member (.aggregate kind identity members) member
  | nested {members : List ObjectType} (kind : AggregateKind) (identity : Nat)
      (member target : ObjectType) (present : member ∈ members) (inside : Member member target) :
      Member (.aggregate kind identity members) target

def membersOf : ObjectType → List ObjectType
  | .scalar _ => []
  | .array element _ => element :: membersOf element
  | .aggregate _ _ members => members.flatMap fun member => member :: membersOf member
termination_by type => sizeOf type

theorem Member.in_members {view member : ObjectType} (path : Member view member) :
    member ∈ membersOf view := by
  induction path with
  | element => simp [membersOf]
  | array count inside ih =>
      simp only [membersOf]
      exact List.mem_cons_of_mem _ ih
  | direct kind identity member present =>
      simp only [membersOf]
      exact List.mem_flatMap.mpr ⟨member, present, List.mem_cons_self⟩
  | nested kind identity head target present inside ih =>
      simp only [membersOf]
      exact List.mem_flatMap.mpr ⟨head, present, List.mem_cons_of_mem _ ih⟩

theorem membersOf_sound (view member : ObjectType) (present : member ∈ membersOf view) :
    Member view member := by
  cases view with
  | scalar atom => simp [membersOf] at present
  | array element count =>
      simp only [membersOf] at present
      rcases List.mem_cons.mp present with rfl | present
      · exact .element _ _
      · exact .array _ (membersOf_sound element member present)
  | aggregate kind identity members =>
      simp only [membersOf] at present
      obtain ⟨head, present, memberPresent⟩ := List.mem_flatMap.mp present
      rcases List.mem_cons.mp memberPresent with rfl | inside
      · exact .direct kind identity _ present
      · exact .nested kind identity head member present (membersOf_sound head member inside)
termination_by sizeOf view

theorem membersOf_iff (view member : ObjectType) : member ∈ membersOf view ↔ Member view member :=
  ⟨membersOf_sound view member, Member.in_members⟩

def character : ObjectType → Bool
  | .scalar atom => atom.character
  | _ => false

inductive Permitted (view effective : ObjectType) : Prop where
  | direct (related : Related view effective) : Permitted view effective
  | member (type : ObjectType) (inside : Member view type) (related : Related type effective) :
      Permitted view effective
  | character (isCharacter : character view = true) : Permitted view effective

def permits (view effective : ObjectType) : Bool :=
  related view effective || (membersOf view).any (fun member => related member effective) || character view

theorem permits_iff (view effective : ObjectType) : permits view effective = true ↔ Permitted view effective := by
  simp only [permits, Bool.or_eq_true, List.any_eq_true, related_iff, membersOf_iff]
  constructor
  · rintro ((direct | ⟨member, inside, related⟩) | character)
    · exact .direct direct
    · exact .member member inside related
    · exact .character character
  · intro permission
    cases permission with
    | direct related => exact Or.inl (Or.inl related)
    | member type inside related => exact Or.inl (Or.inr ⟨type, inside, related⟩)
    | character isCharacter => exact Or.inr isCharacter

structure Qualifiers where
  const : Bool := false
  volatile : Bool := false
  restrict : Bool := false
  deriving DecidableEq, Repr

structure View where
  type : ObjectType
  qualifiers : Qualifiers := {}
  deriving DecidableEq, Repr

def View.permits (view : View) (effective : ObjectType) : Bool := AccessTypes.permits view.type effective

theorem qualified_permission (view : View) (effective : ObjectType) :
    view.permits effective = true ↔ Permitted view.type effective := permits_iff _ _

end Mettapedia.Languages.C11.AccessTypes
