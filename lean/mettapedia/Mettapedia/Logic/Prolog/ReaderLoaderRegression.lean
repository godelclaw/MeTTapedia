import Mettapedia.Logic.Prolog.ReaderSWIProfile

namespace Mettapedia.Logic.Prolog.ReaderLoaderRegression

open ReaderDirective ReaderLoader ReaderOperator ReaderSource SourceSignature

private def emptyImports : ReaderDirective.ImportProfile Unit :=
  fun _ => .ok []

private def hasDeclaration (table : ReaderOperator.Table) (name : String)
    (priority : Nat) (specifier : ReaderOperator.Specifier) : Bool :=
  table.any fun declaration =>
    declaration.name = name && declaration.priority.value = priority &&
      declaration.specifier = specifier

private def isAtom (expected : String) : SourceSignature.Term -> Bool
  | .const (.atom actual) => actual = expected
  | _ => false

private def isRightAssociatedLikes : ReaderSource.Form -> Bool
  | .clause clause =>
      match clause.head.symbol.name, List.ofFn clause.head.args, clause.body with
      | "likes", [left, right], .succeed =>
          isAtom "a" left &&
            match right with
            | .app indicator arguments =>
                indicator.name = "likes" &&
                  match List.ofFn arguments with
                  | [middle, last] => isAtom "b" middle && isAtom "c" last
                  | _ => false
            | _ => false
      | _, _, _ => false
  | _ => false

def localOperatorAffectsOnlyFollowingTerms : Bool :=
  match loadSourceWith (ReaderDirective.effectWith emptyImports) defaults
      ":- op(500, xfy, likes). a likes b likes c." with
  | .ok result =>
      result.forms.length = 2 &&
        result.forms.any isRightAssociatedLikes &&
        hasDeclaration result.operators "likes" 500 .xfy
  | .error _ => false

#guard localOperatorAffectsOnlyFollowingTerms

def fixedTableCannotReadFollowingOperatorUse : Bool :=
  match loadSourceWith noEffect defaults
      ":- op(500, xfy, likes). a likes b." with
  | .error _ => true
  | .ok _ => false

#guard fixedTableCannotReadFollowingOperatorUse

def priorityZeroRemovesBeforeNextTerm : Bool :=
  match loadSourceWith (ReaderDirective.effectWith emptyImports) defaults
      ":- op(500, xfy, likes). :- op(0, xfy, likes). a likes b." with
  | .error _ => true
  | .ok _ => false

#guard priorityZeroRemovesBeforeNextTerm

def moduleExportOperatorAffectsFollowingTerm : Bool :=
  match loadSourceWith (ReaderDirective.effectWith emptyImports) defaults
      ":- module(m, [op(500, xfy, likes)]). a likes b likes c." with
  | .ok result =>
      result.forms.length = 2 && result.forms.any isRightAssociatedLikes
  | .error _ => false

#guard moduleExportOperatorAffectsFollowingTerm

def clpfdImportAffectsFollowingTerm : Bool :=
  match loadSourceWith
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa) defaults
      ":- use_module(library(clpfd)). p(X,Y) :- X #= Y + 1." with
  | .ok result =>
      result.forms.length = 2 &&
        hasDeclaration result.operators "#=" 700 .xfx &&
        hasDeclaration result.operators ".." 450 .xfx
  | .error _ => false

#guard clpfdImportAffectsFollowingTerm

def janusImportAffectsFollowingTerm : Bool :=
  match loadSourceWith
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa) defaults
      ":- use_module(library(janus)). p :- @ value." with
  | .ok result =>
      result.forms.length = 2 &&
        hasDeclaration result.operators "@" 200 .fy &&
        hasDeclaration result.operators "#" 50 .fx
  | .error _ => false

#guard janusImportAffectsFollowingTerm

def nestedLibraryPathIsClassified : Bool :=
  match loadSourceWith
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa) defaults
      ":- use_module(library(dcg/basics)). rule --> []." with
  | .ok result => result.forms.length = 2
  | .error _ => false

#guard nestedLibraryPathIsClassified

def localMettaLoadCarriesItsReaderEnvironment : Bool :=
  match loadSourceWith
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa) defaults
      ":- ensure_loaded(metta). p(X,Y) :- @ value, X #= Y." with
  | .ok result =>
      result.forms.length = 2 &&
        hasDeclaration result.operators "@" 200 .fy &&
        hasDeclaration result.operators "#=" 700 .xfx
  | .error _ => false

#guard localMettaLoadCarriesItsReaderEnvironment

def unknownImportFailsClosed : Bool :=
  match loadSourceWith
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa) defaults
      ":- use_module(library(not_in_the_pinned_profile)). p." with
  | .error (.effect (.import (.unclassifiedImport _))) => true
  | _ => false

#guard unknownImportFailsClosed

def parserLibraryFrontierHasNoImportedOperators : Bool :=
  match loadSourceWith
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa) defaults
      ":- use_module(library(pairs)). \
       :- use_module(library(debug)). p." with
  | .ok result => result.forms.length = 3
  | .error _ => false

#guard parserLibraryFrontierHasNoImportedOperators

end Mettapedia.Logic.Prolog.ReaderLoaderRegression
