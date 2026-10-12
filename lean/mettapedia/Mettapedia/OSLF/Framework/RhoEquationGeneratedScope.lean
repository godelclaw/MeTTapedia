import Mettapedia.OSLF.Syntax.RhoQuotationClassFibres
import Mathlib.Order.FixedPoints

/-!+# Generated scopes on the actual sorted rho equation quotient

Each part of a parallel decomposition can be an atomic process or the drop
of an already admitted name. The alternatives can overlap. All operations
are those of the source equation quotient, including the name eta equation.

The least fixed point has exactly the names with finite certificates. A
certificate retains every process component, recursive name and atomic
premise occurrence. Thus finite generation does not require a representative
size to decrease along every possible equation-class decomposition. Neither
this equivalence nor the fixed point law asserts a decision procedure for
arbitrary atomic predicates.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoEquationGeneratedScope

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres

variable {context : Ctx sig}

abbrev NamePredicate (context : Ctx sig) := Name context → Prop

def Part (atom : Process context → Prop) (names : NamePredicate context)
    (process : Process context) : Prop :=
  atom process ∨ ∃ name, names name ∧ process = drop name

theorem part_mono {atom : Process context → Prop}
    {first second : NamePredicate context} (inclusion : first ≤ second) :
    ∀ process, Part atom first process → Part atom second process := by
  intro process admitted
  rcases admitted with atomic | ⟨name, child, readout⟩
  · exact Or.inl atomic
  · exact Or.inr ⟨name, inclusion name child, readout⟩

def step (left right : Process context → Prop) :
    NamePredicate context →o NamePredicate context where
  toFun names name := ∃ first second,
    quote (join first second) = name ∧ Part left names first ∧ Part right names second
  monotone' := by
    intro first second inclusion name
    rintro ⟨leftProcess, rightProcess, readout, leftPart, rightPart⟩
    exact ⟨leftProcess, rightProcess, readout,
      part_mono inclusion _ leftPart, part_mono inclusion _ rightPart⟩

def generated (left right : Process context → Prop) : NamePredicate context :=
  (step left right).lfp

theorem generated_unfold (left right : Process context → Prop) (name : Name context) :
    generated left right name ↔ step left right (generated left right) name :=
  (iff_of_eq (congrFun (OrderHom.map_lfp (step left right)) name)).symm

theorem generated_induction (left right : Process context → Prop)
    (invariant : NamePredicate context)
    (closed : step left right invariant ≤ invariant) :
    generated left right ≤ invariant := (step left right).lfp_le closed

inductive Certificate (left right : Process context → Prop) : Name context → Type where
  | atoms (first second : Process context) (firstAdmitted : left first)
      (secondAdmitted : right second) :
      Certificate left right (quote (join first second))
  | left (name : Name context) (child : Certificate left right name)
      (second : Process context) (secondAdmitted : right second) :
      Certificate left right (quote (join (drop name) second))
  | right (first : Process context) (firstAdmitted : left first)
      (name : Name context) (child : Certificate left right name) :
      Certificate left right (quote (join first (drop name)))
  | both (first second : Name context) (firstChild : Certificate left right first)
      (secondChild : Certificate left right second) :
      Certificate left right (quote (join (drop first) (drop second)))

theorem certificate_sound {left right : Process context → Prop} {name : Name context}
    (certificate : Certificate left right name) : generated left right name := by
  induction certificate with
  | atoms first second firstAdmitted secondAdmitted =>
      exact (generated_unfold _ _ _).mpr
        ⟨first, second, rfl, Or.inl firstAdmitted, Or.inl secondAdmitted⟩
  | left name child second secondAdmitted ih =>
      exact (generated_unfold _ _ _).mpr
        ⟨drop name, second, rfl, Or.inr ⟨name, ih, rfl⟩, Or.inl secondAdmitted⟩
  | right first firstAdmitted name child ih =>
      exact (generated_unfold _ _ _).mpr
        ⟨first, drop name, rfl, Or.inl firstAdmitted, Or.inr ⟨name, ih, rfl⟩⟩
  | both first second firstChild secondChild firstIH secondIH =>
      exact (generated_unfold _ _ _).mpr
        ⟨drop first, drop second, rfl, Or.inr ⟨first, firstIH, rfl⟩,
          Or.inr ⟨second, secondIH, rfl⟩⟩

theorem generated_has_certificate (left right : Process context → Prop) :
    generated left right ≤ fun name => Nonempty (Certificate left right name) := by
  apply generated_induction
  intro name
  rintro ⟨first, second, rfl, leftPart, rightPart⟩
  rcases leftPart with leftAtom | ⟨leftName, ⟨leftChild⟩, rfl⟩
  · rcases rightPart with rightAtom | ⟨rightName, ⟨rightChild⟩, rfl⟩
    · exact ⟨.atoms first second leftAtom rightAtom⟩
    · exact ⟨.right first leftAtom rightName rightChild⟩
  · rcases rightPart with rightAtom | ⟨rightName, ⟨rightChild⟩, rfl⟩
    · exact ⟨.left leftName leftChild second rightAtom⟩
    · exact ⟨.both leftName rightName leftChild rightChild⟩

theorem generated_iff_certificate (left right : Process context → Prop)
    (name : Name context) :
    generated left right name ↔ Nonempty (Certificate left right name) :=
  ⟨generated_has_certificate left right name,
    fun ⟨certificate⟩ => certificate_sound certificate⟩

namespace Certificate

def depth {left right : Process context → Prop} :
    {name : Name context} → Certificate left right name → Nat
  | _, .atoms _ _ _ _ => 0
  | _, .left _ child _ _ => depth child + 1
  | _, .right _ _ _ child => depth child + 1
  | _, .both _ _ first second => max (depth first) (depth second) + 1

def nodes {left right : Process context → Prop} :
    {name : Name context} → Certificate left right name → Nat
  | _, .atoms _ _ _ _ => 1
  | _, .left _ child _ _ => nodes child + 1
  | _, .right _ _ _ child => nodes child + 1
  | _, .both _ _ first second => nodes first + nodes second + 1

def atomicOrigins {left right : Process context → Prop} :
    {name : Name context} → Certificate left right name →
      List (Sum (Process context) (Process context))
  | _, .atoms first second _ _ => [.inl first, .inr second]
  | _, .left _ child second _ => atomicOrigins child ++ [.inr second]
  | _, .right first _ _ child => .inl first :: atomicOrigins child
  | _, .both _ _ first second => atomicOrigins first ++ atomicOrigins second

@[simp]
theorem atomicOrigins_cast {left right : Process context → Prop}
    {first second : Name context} (same : first = second)
    (certificate : Certificate left right first) :
    (same ▸ certificate).atomicOrigins = certificate.atomicOrigins := by
  cases same
  rfl

theorem nodes_positive {left right : Process context → Prop} {name : Name context}
    (certificate : Certificate left right name) : 0 < certificate.nodes := by
  cases certificate <;> simp only [nodes] <;> omega

theorem depth_lt_nodes {left right : Process context → Prop} {name : Name context}
    (certificate : Certificate left right name) : certificate.depth < certificate.nodes := by
  induction certificate with
  | atoms => simp only [depth, nodes]; omega
  | left _ _ _ _ ih => simp only [depth, nodes]; omega
  | right _ _ _ _ ih => simp only [depth, nodes]; omega
  | both _ _ _ _ firstIH secondIH => simp only [depth, nodes]; omega

end Certificate

theorem generated_mono {left right left' right' : Process context → Prop}
    (leftInclusion : left ≤ left') (rightInclusion : right ≤ right') :
    generated left right ≤ generated left' right' := by
  apply generated_induction
  intro name
  rintro ⟨first, second, readout, leftPart, rightPart⟩
  apply (generated_unfold _ _ _).mpr
  refine ⟨first, second, readout, ?_, ?_⟩
  · rcases leftPart with atomic | recursive
    · exact Or.inl (leftInclusion first atomic)
    · exact Or.inr recursive
  · rcases rightPart with atomic | recursive
    · exact Or.inl (rightInclusion second atomic)
    · exact Or.inr recursive

end Mettapedia.OSLF.Framework.RhoEquationGeneratedScope
