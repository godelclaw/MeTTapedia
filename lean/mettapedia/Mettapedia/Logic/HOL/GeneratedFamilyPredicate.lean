import Mettapedia.Logic.HOL.ConstructorPositionEdges
import Mettapedia.Logic.HOL.RecursiveSpacePredicate

/-!
# Positive family predicates from generated constructor guards

Constructor data, positions, bottom and constructor operations share one typed
signature. The existing positive-syntax compiler supplies retained monotonicity
and fixed-point programs for that assembled operator.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {constructors : ConstructorPrograms Const []} (positions : PositionPrograms constructors)
variable {space : Ty Base} (bottom : ClosedTerm Const space)
  (construct : ClosedTerm Const (constructors.number ⇒ payloadType constructors.fields ⇒ (constructors.number ⇒ space) ⇒ space))

def signature : RecursiveSpacePredicate.Signature Const where
  number := constructors.number
  payload := payloadType constructors.fields
  space := space
  bottom := bottom
  construct := construct
  validShape := constructors.shapeProgram
  active := positions.activeProgram
  validEdge := positions.edgeProgram construct

def operator := (positions.signature bottom construct).operator
def member := PredicateFixedPoint.least (positions.operator bottom construct)
def monotonicity := (positions.signature bottom construct).monotonicity
def fixedPoint := (positions.signature bottom construct).fixedPoint

theorem monotonicity_free : (positions.monotonicity bottom construct).FunctionExtensionalityFree :=
  (positions.signature bottom construct).monotonicity_functionExtensionalityFree
theorem fixedPoint_free : (positions.fixedPoint bottom construct).FunctionExtensionalityFree :=
  (positions.signature bottom construct).fixedPoint_functionExtensionalityFree

#print axioms monotonicity
#print axioms fixedPoint
end Mettapedia.Logic.HOL.IndexedConstructorGuards.PositionPrograms
