import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.OSLF.MeTTaIL.OccurrenceZipperAddress

/-!
# Operational permissions and typed occurrence data

Reduction permissions are finite authored data. They are independent of the
vocabulary used to check formulas, queries or source terms. Occurrence data
retains the actual zipper, child address, complete local binder context and
all grammar choices along the typing descent.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralTypedSites

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted

structure OperationalPermissions where
  enabled : Bool := true
  allConstructorArguments : Bool := false
  constructorArguments : List (String × Nat) := []
  underLambda : Bool := false
  underMultiLambda : Bool := false
  collectionKinds : List CollType := []
  deriving DecidableEq, Repr

def OperationalPermissions.permitsArgument (permissions : OperationalPermissions)
    (constructor : String) (index : Nat) : Bool :=
  permissions.allConstructorArguments || decide ((constructor, index) ∈ permissions.constructorArguments)

theorem permitsArgument_spec (permissions : OperationalPermissions)
    (constructor : String) (index : Nat) :
    permissions.permitsArgument constructor index = true ↔
      permissions.allConstructorArguments = true ∨
        (constructor, index) ∈ permissions.constructorArguments := by
  simp [OperationalPermissions.permitsArgument]

def OperationalPermissions.all : OperationalPermissions where
  allConstructorArguments := true
  underLambda := true
  underMultiLambda := true
  collectionKinds := [.vec, .hashBag, .hashSet]

def OperationalPermissions.rootOnly : OperationalPermissions := {}

def OperationalPermissions.stopped : OperationalPermissions := { enabled := false }

/-- Check the separately declared reduction policy on one structural path.
This grants no permission to an explicit-substitution frame. -/
def OperationalPermissions.permitsContext (permissions : OperationalPermissions) :
    OneHoleContext → Bool
  | .hole => permissions.enabled
  | .apply constructor before inner _ =>
      permissions.permitsArgument constructor before.length && permissions.permitsContext inner
  | .lambda _ inner => permissions.underLambda && permissions.permitsContext inner
  | .multiLambda _ _ inner => permissions.underMultiLambda && permissions.permitsContext inner
  | .collection kind _ inner _ rest =>
      decide (kind ∈ permissions.collectionKinds) && rest.isNone && permissions.permitsContext inner
  | .substBody _ _ | .substReplacement _ _ => false

/-- The ordinary child address represented by the existing zipper. -/
def contextAddress : OneHoleContext → List Nat
  | .hole => []
  | .apply _ before inner _ => before.length :: contextAddress inner
  | .lambda _ inner => 0 :: contextAddress inner
  | .multiLambda _ _ inner => 0 :: contextAddress inner
  | .substBody inner _ => 0 :: contextAddress inner
  | .substReplacement _ inner => 1 :: contextAddress inner
  | .collection _ before inner _ _ => before.length :: contextAddress inner

/-- Relevant typing alternatives are recorded by actual declaration position,
not resolved by the first successful declaration with a matching label. -/
inductive TypingFrame where
  | application (declaration argumentIndex : Nat)
  | lambda (domain : TypeExpr)
  | multiLambda (arity : Nat) (domain : TypeExpr)
  | directCollection (kind : CollType)
  | authoredCollection (declaration : Nat)
  deriving DecidableEq, Repr

structure SiteData where
  address : List Nat
  context : OneHoleContext
  focus : Pattern
  focusBound : List TypeExpr
  focusType : TypeExpr
  typingFrames : List TypingFrame
  deriving DecidableEq, Repr

namespace SiteData

def here (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) : SiteData where
  address := []
  context := .hole
  focus := source
  focusBound := bound
  focusType := expected
  typingFrames := []

def wrapApplication (declaration : Nat) (constructor : String)
    (arguments : List Pattern) (index : Nat) (inner : SiteData) : SiteData :=
  { inner with
    address := index :: inner.address
    context := .apply constructor (arguments.take index) inner.context (arguments.drop (index + 1))
    typingFrames := .application declaration index :: inner.typingFrames }

def wrapLambda (binder : Option String) (domain : TypeExpr) (inner : SiteData) : SiteData :=
  { inner with
    address := 0 :: inner.address
    context := .lambda binder inner.context
    typingFrames := .lambda domain :: inner.typingFrames }

def wrapMultiLambda (arity : Nat) (binders : List String) (domain : TypeExpr)
    (inner : SiteData) : SiteData :=
  { inner with
    address := 0 :: inner.address
    context := .multiLambda arity binders inner.context
    typingFrames := .multiLambda arity domain :: inner.typingFrames }

def wrapCollection (origin : TypingFrame) (kind : CollType) (elements : List Pattern)
    (index : Nat) (inner : SiteData) : SiteData :=
  { inner with
    address := index :: inner.address
    context := .collection kind (elements.take index) inner.context (elements.drop (index + 1)) none
    typingFrames := origin :: inner.typingFrames }

end SiteData

end Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
