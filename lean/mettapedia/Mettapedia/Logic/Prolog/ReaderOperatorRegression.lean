import Mettapedia.Logic.Prolog.ReaderOperator

namespace Mettapedia.Logic.Prolog.ReaderOperatorRegression

open ReaderOperator

#guard defaults.length = 67

def hasDeclaration (table : Table) (priority : Nat)
    (specifier : Specifier) (name : String) : Bool :=
  table.any fun declaration =>
    declaration.name = name && declaration.priority.value = priority &&
      declaration.specifier = specifier

#guard hasDeclaration defaults 200 .fy "-"
#guard hasDeclaration defaults 500 .yfx "-"
#guard hasDeclaration defaults 1000 .xfy ","
#guard hasDeclaration defaults 1200 .xfx ":-"
#guard hasDeclaration defaults 1200 .fx ":-"

def removalIsFixityLocal : Bool :=
  match declare 0 .fy "-" defaults with
  | .error _ => false
  | .ok table =>
      !hasDeclaration table 200 .fy "-" &&
        hasDeclaration table 500 .yfx "-"

#guard removalIsFixityLocal

def redeclarationReplacesPriority : Bool :=
  match declare 300 .fy "-" defaults with
  | .error _ => false
  | .ok table =>
      hasDeclaration table 300 .fy "-" &&
        !hasDeclaration table 200 .fy "-" &&
        hasDeclaration table 500 .yfx "-"

#guard redeclarationReplacesPriority

def rejectsInvalidPriority : Bool :=
  match declare 1201 .xfx "bad" defaults with
  | .error (.priorityOutOfRange 1201) => true
  | _ => false

#guard rejectsInvalidPriority

end Mettapedia.Logic.Prolog.ReaderOperatorRegression
