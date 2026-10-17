import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Joined
import Mettapedia.OSLF.NativeTypes.Generation.BindingControls

/-! # Authored consumers with shared indices and heterogeneous focus carriers -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Consumers

open Mettapedia.OSLF.MeTTaIL.Syntax

def focus : TypeExpr := .base "Focus"
def program : TypeExpr := .base "Program"

def sharedRule : RewriteRule :=
  {name := "Shared", typeContext := [("x", focus)], premises := [],
   left := .apply "Pair" [.fvar "x", .fvar "x"], right := .apply "Done" []}

def sharedLanguage : LanguageDef :=
  {name := "SharedFocus", types := ["Focus", "Program"], terms :=
    [{label := "F0", category := "Focus", params := [], syntaxPattern := []},
     {label := "Pair", category := "Program", params :=
       [.simple "left" focus, .simple "right" focus], syntaxPattern := []},
     {label := "Done", category := "Program", params := [], syntaxPattern := []}],
   equations := [], rewrites := [sharedRule, {sharedRule with name := "SharedSecond"}]}

def sharedSource : Pattern := .apply "Pair" [.apply "F0" [], .apply "F0" []]
def sharedTarget : Pattern := .apply "Done" []

def lambdaIdentity : Pattern := .apply "Lam" [.lambda none (.bvar 0)]
def underBinderSource : Pattern := .apply "Lam" [.lambda none
  (.apply "App" [lambdaIdentity, .bvar 0])]
def underBinderTarget : Pattern := .apply "Lam" [.lambda none (.bvar 0)]
def relySource : Pattern := .apply "App" [.apply "App" [lambdaIdentity, lambdaIdentity], lambdaIdentity]

def generate (language : LanguageDef) : Except Joined.Issue Joined.Installed :=
  Joined.generate (BindingPipeline.Controls.snapshot language) BindingPipeline.Controls.fragment
    BindingPipeline.Controls.fullLogic (fun _ => .star, fun _ => .star) []

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Consumers
