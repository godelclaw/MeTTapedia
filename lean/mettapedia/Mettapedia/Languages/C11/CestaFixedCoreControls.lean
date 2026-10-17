import Mettapedia.Languages.C11.CestaFixedCore
import Mettapedia.Languages.C11.FixedCoreControls

/-!
# Cesta translation units on the fixed C core

Complete C sources are parsed by Cesta, read into core programs and run on the
core machine under the LP64 model of the core controls. Recursion, pointers
into arrays and allocations, loops with `break` and `continue`, and a call to
a host service run to the values GCC and Clang compute; sources outside the
fragment or ill-formed are refused.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.CestaFixedCoreControls

open FixedCore FixedCoreControls IntegerMemoryModel
open Mettapedia.GSLT.Distinction.ProductiveBlocks (Outcome)

/-! ## Printed trees

The trees below are the ones `cesta read` prints for the quoted sources. The
printer renders a tree in Cesta's notation; for two of the trees the build
evaluates the rendering and compares it with Cesta's printed output character
by character. -/

open Mettapedia.GSLT.Parsing.CanonicalGrammar (CanonicalTerm)
open CestaFixedCore (readUnit Signature Slot)

mutual
/-- Cesta's printed canonical notation: constructor heads carry the `c:` prefix,
lists are `c:List`, decimal constants are string literals and other tokens are
symbols. -/
def printed : CanonicalTerm → String
  | .node "IntConst" [.text spelling] => "(c:IntConst \"" ++ spelling ++ "\")"
  | .node name children => "(c:" ++ name ++ printedChildren children ++ ")"
  | .text spelling => spelling
  | .seq items => "(c:List" ++ printedChildren items ++ ")"

def printedChildren : List CanonicalTerm → String
  | [] => ""
  | child :: rest => " " ++ printed child ++ printedChildren rest
end

def runUnit (services : List (String × Signature)) (unit : CanonicalTerm) (fuel : Nat) :
    Option (List (Event model) × Outcome (Executable model) (Option (Value model)) (Request model)) :=
  (readUnit model services unit).bind fun program => runProgram program fuel

/-- `int fact(int n) { int r; if (n) { r = fact(n - 1); r = n * r; } else { r = 1; } return r; }
int main(void) { int x; x = fact(5); return x; }` -/

def factorialUnit : CanonicalTerm :=
  .node "TranslationUnit" [
    .seq [
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "fact"],
              .node "ParameterTypes" [
                .seq [
                  .node "NamedParameter" [
                    .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                    .node "Declarator" [.node "NameDeclarator" [.text "n"]]]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [.node "InitDeclarator" [.node "Declarator" [.node "NameDeclarator" [.text "r"]]]]]]],
              .node "BlockStatement" [
                .node "SelectionStatement" [
                  .node "IfElse" [
                    .node "Var" [.text "n"],
                    .node "CompoundStatement" [
                      .node "Block" [
                        .seq [
                          .node "BlockStatement" [
                            .node "ExpressionStatement" [
                              .node "SomeFullExpression" [
                                .node "Assign" [
                                  .node "Var" [.text "r"],
                                  .node "Call" [
                                    .node "Var" [.text "fact"],
                                    .node "Arguments" [
                                      .seq [
                                        .node "Subtract" [
                                          .node "Var" [.text "n"],
                                          .node "IntConst" [.text "1"]]]]]]]]],
                          .node "BlockStatement" [
                            .node "ExpressionStatement" [
                              .node "SomeFullExpression" [
                                .node "Assign" [
                                  .node "Var" [.text "r"],
                                  .node "Multiply" [.node "Var" [.text "n"], .node "Var" [.text "r"]]]]]]]]],
                    .node "CompoundStatement" [
                      .node "Block" [
                        .seq [
                          .node "BlockStatement" [
                            .node "ExpressionStatement" [
                              .node "SomeFullExpression" [
                                .node "Assign" [.node "Var" [.text "r"], .node "IntConst" [.text "1"]]]]]]]]]]],
              .node "BlockStatement" [
                .node "JumpStatement" [.node "Return" [.node "SomeFullExpression" [.node "Var" [.text "r"]]]]]]]]],
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "main"],
              .node "ParameterTypes" [
                .seq [
                  .node "AbstractParameter" [
                    .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
                    .node "NoAbstractDeclarator" []]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [.node "InitDeclarator" [.node "Declarator" [.node "NameDeclarator" [.text "x"]]]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [
                      .node "Var" [.text "x"],
                      .node "Call" [
                        .node "Var" [.text "fact"],
                        .node "Arguments" [.seq [.node "IntConst" [.text "5"]]]]]]]],
              .node "BlockStatement" [
                .node "JumpStatement" [.node "Return" [.node "SomeFullExpression" [.node "Var" [.text "x"]]]]]]]]]]]

/-- The output of `cesta read` on the factorial source. -/
def factorialPrinted : String :=
  "(c:TranslationUnit (c:List (c:ExternalFunction (c:FunctionDefinition \
  (c:PrimitiveDeclarationSpecifiers (c:Int) (c:List)) (c:Declarator (c:FunctionDeclarator \
  (c:NameDeclarator fact) (c:ParameterTypes (c:List (c:NamedParameter \
  (c:PrimitiveDeclarationSpecifiers (c:Int) (c:List)) (c:Declarator (c:NameDeclarator n))))))) \
  (c:List) (c:Block (c:List (c:BlockDeclaration (c:Declaration (c:PrimitiveDeclarationSpecifiers \
  (c:Int) (c:List)) (c:InitDeclarators (c:List (c:InitDeclarator (c:Declarator (c:NameDeclarator \
  r))))))) (c:BlockStatement (c:SelectionStatement (c:IfElse (c:Var n) (c:CompoundStatement (c:Block \
  (c:List (c:BlockStatement (c:ExpressionStatement (c:SomeFullExpression (c:Assign (c:Var r) (c:Call \
  (c:Var fact) (c:Arguments (c:List (c:Subtract (c:Var n) (c:IntConst \"1\"))))))))) \
  (c:BlockStatement (c:ExpressionStatement (c:SomeFullExpression (c:Assign (c:Var r) (c:Multiply \
  (c:Var n) (c:Var r))))))))) (c:CompoundStatement (c:Block (c:List (c:BlockStatement \
  (c:ExpressionStatement (c:SomeFullExpression (c:Assign (c:Var r) (c:IntConst \"1\"))))))))))) \
  (c:BlockStatement (c:JumpStatement (c:Return (c:SomeFullExpression (c:Var r))))))))) \
  (c:ExternalFunction (c:FunctionDefinition (c:PrimitiveDeclarationSpecifiers (c:Int) (c:List)) \
  (c:Declarator (c:FunctionDeclarator (c:NameDeclarator main) (c:ParameterTypes (c:List \
  (c:AbstractParameter (c:UniqueDeclarationSpecifiers (c:Void) (c:List)) \
  (c:NoAbstractDeclarator)))))) (c:List) (c:Block (c:List (c:BlockDeclaration (c:Declaration \
  (c:PrimitiveDeclarationSpecifiers (c:Int) (c:List)) (c:InitDeclarators (c:List (c:InitDeclarator \
  (c:Declarator (c:NameDeclarator x))))))) (c:BlockStatement (c:ExpressionStatement \
  (c:SomeFullExpression (c:Assign (c:Var x) (c:Call (c:Var fact) (c:Arguments (c:List (c:IntConst \
  \"5\")))))))) (c:BlockStatement (c:JumpStatement (c:Return (c:SomeFullExpression (c:Var \
  x)))))))))))"

#guard printed factorialUnit == factorialPrinted

theorem cesta_factorial_returns_120 : (runUnit [] factorialUnit 600).bind returned = some 120 := by
  decide +kernel

/-- A pointer program: a `void` function writing through a pointer parameter,
a loop with `break` and `continue` over an array argument, a function returning
a pointer, an allocation, nested blocks, a conversion to `long`, `free(0)` and
`*&`. GCC and Clang (with and without AddressSanitizer and UndefinedBehavior-
Sanitizer) exit with 92.

```
void put(int *q, int v) { *q = v; return; }
int sum(int *a, int n) { int s = 0, i = 0; while (i < n) { if (a[i] == 0) break;
  s = s + a[i]; i = i + 1; continue; } return s; }
int *next(int *p) { return p + 1; }
int main(void) {
  int b[3]; int *p = 0; long w = (long) 3; int *q;
  b[0] = 2; b[1] = 0; b[2] = -5;
  p = malloc(3 * sizeof(int));
  p[0] = 1; *(p + 1) = 2; p[2] = 7;
  put(&b[1], 4);
  q = next(p);
  { int z; z = sum(b, 3); b[0] = z + *q; }
  w = w * b[0];
  b[1] = 0;
  { int y; y = sum(b, 3); free(p); free(0); if (y != 3) return -1; }
  return w * 10 + *&b[0] - (b[2] < 0);
}
```
-/

def pointersUnit : CanonicalTerm :=
  .node "TranslationUnit" [
    .seq [
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "put"],
              .node "ParameterTypes" [
                .seq [
                  .node "NamedParameter" [
                    .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                    .node "PointerDeclarator" [
                      .node "Pointer" [.node "NoTypeQualifiers" []],
                      .node "NameDeclarator" [.text "q"]]],
                  .node "NamedParameter" [
                    .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                    .node "Declarator" [.node "NameDeclarator" [.text "v"]]]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [.node "Indirection" [.node "Var" [.text "q"]], .node "Var" [.text "v"]]]]],
              .node "BlockStatement" [.node "JumpStatement" [.node "Return" [.node "NoFullExpression" []]]]]]]],
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "sum"],
              .node "ParameterTypes" [
                .seq [
                  .node "NamedParameter" [
                    .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                    .node "PointerDeclarator" [
                      .node "Pointer" [.node "NoTypeQualifiers" []],
                      .node "NameDeclarator" [.text "a"]]],
                  .node "NamedParameter" [
                    .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                    .node "Declarator" [.node "NameDeclarator" [.text "n"]]]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [
                      .node "InitDeclaratorValue" [
                        .node "Declarator" [.node "NameDeclarator" [.text "s"]],
                        .node "InitializerExpression" [.node "IntConst" [.text "0"]]],
                      .node "InitDeclaratorValue" [
                        .node "Declarator" [.node "NameDeclarator" [.text "i"]],
                        .node "InitializerExpression" [.node "IntConst" [.text "0"]]]]]]],
              .node "BlockStatement" [
                .node "IterationStatement" [
                  .node "While" [
                    .node "Less" [.node "Var" [.text "i"], .node "Var" [.text "n"]],
                    .node "CompoundStatement" [
                      .node "Block" [
                        .seq [
                          .node "BlockStatement" [
                            .node "SelectionStatement" [
                              .node "If" [
                                .node "Equal" [
                                  .node "Subscript" [.node "Var" [.text "a"], .node "Var" [.text "i"]],
                                  .node "IntConst" [.text "0"]],
                                .node "JumpStatement" [.node "Break" []]]]],
                          .node "BlockStatement" [
                            .node "ExpressionStatement" [
                              .node "SomeFullExpression" [
                                .node "Assign" [
                                  .node "Var" [.text "s"],
                                  .node "Add" [
                                    .node "Var" [.text "s"],
                                    .node "Subscript" [.node "Var" [.text "a"], .node "Var" [.text "i"]]]]]]],
                          .node "BlockStatement" [
                            .node "ExpressionStatement" [
                              .node "SomeFullExpression" [
                                .node "Assign" [
                                  .node "Var" [.text "i"],
                                  .node "Add" [.node "Var" [.text "i"], .node "IntConst" [.text "1"]]]]]],
                          .node "BlockStatement" [.node "JumpStatement" [.node "Continue" []]]]]]]]],
              .node "BlockStatement" [
                .node "JumpStatement" [.node "Return" [.node "SomeFullExpression" [.node "Var" [.text "s"]]]]]]]]],
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "PointerDeclarator" [
            .node "Pointer" [.node "NoTypeQualifiers" []],
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "next"],
              .node "ParameterTypes" [
                .seq [
                  .node "NamedParameter" [
                    .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                    .node "PointerDeclarator" [
                      .node "Pointer" [.node "NoTypeQualifiers" []],
                      .node "NameDeclarator" [.text "p"]]]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockStatement" [
                .node "JumpStatement" [
                  .node "Return" [
                    .node "SomeFullExpression" [
                      .node "Add" [.node "Var" [.text "p"], .node "IntConst" [.text "1"]]]]]]]]]],
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "main"],
              .node "ParameterTypes" [
                .seq [
                  .node "AbstractParameter" [
                    .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
                    .node "NoAbstractDeclarator" []]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [
                      .node "InitDeclarator" [
                        .node "Declarator" [
                          .node "ArrayDeclarator" [
                            .node "NameDeclarator" [.text "b"],
                            .node "NoTypeQualifiers" [],
                            .node "SomeExpression" [.node "IntConst" [.text "3"]]]]]]]]],
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [
                      .node "InitDeclaratorValue" [
                        .node "PointerDeclarator" [
                          .node "Pointer" [.node "NoTypeQualifiers" []],
                          .node "NameDeclarator" [.text "p"]],
                        .node "InitializerExpression" [.node "IntConst" [.text "0"]]]]]]],
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Long" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [
                      .node "InitDeclaratorValue" [
                        .node "Declarator" [.node "NameDeclarator" [.text "w"]],
                        .node "InitializerExpression" [
                          .node "Cast" [
                            .node "TypeName" [
                              .node "PrimitiveSpecifierQualifiers" [.node "Long" [], .seq []],
                              .node "NoAbstractDeclarator" []],
                            .node "IntConst" [.text "3"]]]]]]]],
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [
                      .node "InitDeclarator" [
                        .node "PointerDeclarator" [
                          .node "Pointer" [.node "NoTypeQualifiers" []],
                          .node "NameDeclarator" [.text "q"]]]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [
                      .node "Subscript" [.node "Var" [.text "b"], .node "IntConst" [.text "0"]],
                      .node "IntConst" [.text "2"]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [
                      .node "Subscript" [.node "Var" [.text "b"], .node "IntConst" [.text "1"]],
                      .node "IntConst" [.text "0"]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [
                      .node "Subscript" [.node "Var" [.text "b"], .node "IntConst" [.text "2"]],
                      .node "Negate" [.node "IntConst" [.text "5"]]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [
                      .node "Var" [.text "p"],
                      .node "Call" [
                        .node "Var" [.text "malloc"],
                        .node "Arguments" [
                          .seq [
                            .node "Multiply" [
                              .node "IntConst" [.text "3"],
                              .node "SizeofType" [
                                .node "TypeName" [
                                  .node "PrimitiveSpecifierQualifiers" [.node "Int" [], .seq []],
                                  .node "NoAbstractDeclarator" []]]]]]]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [
                      .node "Subscript" [.node "Var" [.text "p"], .node "IntConst" [.text "0"]],
                      .node "IntConst" [.text "1"]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [
                      .node "Indirection" [
                        .node "Add" [.node "Var" [.text "p"], .node "IntConst" [.text "1"]]],
                      .node "IntConst" [.text "2"]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [
                      .node "Subscript" [.node "Var" [.text "p"], .node "IntConst" [.text "2"]],
                      .node "IntConst" [.text "7"]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Call" [
                      .node "Var" [.text "put"],
                      .node "Arguments" [
                        .seq [
                          .node "AddressOf" [
                            .node "Subscript" [.node "Var" [.text "b"], .node "IntConst" [.text "1"]]],
                          .node "IntConst" [.text "4"]]]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [
                      .node "Var" [.text "q"],
                      .node "Call" [
                        .node "Var" [.text "next"],
                        .node "Arguments" [.seq [.node "Var" [.text "p"]]]]]]]],
              .node "BlockStatement" [
                .node "CompoundStatement" [
                  .node "Block" [
                    .seq [
                      .node "BlockDeclaration" [
                        .node "Declaration" [
                          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                          .node "InitDeclarators" [
                            .seq [
                              .node "InitDeclarator" [.node "Declarator" [.node "NameDeclarator" [.text "z"]]]]]]],
                      .node "BlockStatement" [
                        .node "ExpressionStatement" [
                          .node "SomeFullExpression" [
                            .node "Assign" [
                              .node "Var" [.text "z"],
                              .node "Call" [
                                .node "Var" [.text "sum"],
                                .node "Arguments" [
                                  .seq [.node "Var" [.text "b"], .node "IntConst" [.text "3"]]]]]]]],
                      .node "BlockStatement" [
                        .node "ExpressionStatement" [
                          .node "SomeFullExpression" [
                            .node "Assign" [
                              .node "Subscript" [.node "Var" [.text "b"], .node "IntConst" [.text "0"]],
                              .node "Add" [
                                .node "Var" [.text "z"],
                                .node "Indirection" [.node "Var" [.text "q"]]]]]]]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [
                      .node "Var" [.text "w"],
                      .node "Multiply" [
                        .node "Var" [.text "w"],
                        .node "Subscript" [.node "Var" [.text "b"], .node "IntConst" [.text "0"]]]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [
                      .node "Subscript" [.node "Var" [.text "b"], .node "IntConst" [.text "1"]],
                      .node "IntConst" [.text "0"]]]]],
              .node "BlockStatement" [
                .node "CompoundStatement" [
                  .node "Block" [
                    .seq [
                      .node "BlockDeclaration" [
                        .node "Declaration" [
                          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                          .node "InitDeclarators" [
                            .seq [
                              .node "InitDeclarator" [.node "Declarator" [.node "NameDeclarator" [.text "y"]]]]]]],
                      .node "BlockStatement" [
                        .node "ExpressionStatement" [
                          .node "SomeFullExpression" [
                            .node "Assign" [
                              .node "Var" [.text "y"],
                              .node "Call" [
                                .node "Var" [.text "sum"],
                                .node "Arguments" [
                                  .seq [.node "Var" [.text "b"], .node "IntConst" [.text "3"]]]]]]]],
                      .node "BlockStatement" [
                        .node "ExpressionStatement" [
                          .node "SomeFullExpression" [
                            .node "Call" [
                              .node "Var" [.text "free"],
                              .node "Arguments" [.seq [.node "Var" [.text "p"]]]]]]],
                      .node "BlockStatement" [
                        .node "ExpressionStatement" [
                          .node "SomeFullExpression" [
                            .node "Call" [
                              .node "Var" [.text "free"],
                              .node "Arguments" [.seq [.node "IntConst" [.text "0"]]]]]]],
                      .node "BlockStatement" [
                        .node "SelectionStatement" [
                          .node "If" [
                            .node "NotEqual" [.node "Var" [.text "y"], .node "IntConst" [.text "3"]],
                            .node "JumpStatement" [
                              .node "Return" [
                                .node "SomeFullExpression" [.node "Negate" [.node "IntConst" [.text "1"]]]]]]]]]]]],
              .node "BlockStatement" [
                .node "JumpStatement" [
                  .node "Return" [
                    .node "SomeFullExpression" [
                      .node "Subtract" [
                        .node "Add" [
                          .node "Multiply" [.node "Var" [.text "w"], .node "IntConst" [.text "10"]],
                          .node "Indirection" [
                            .node "AddressOf" [
                              .node "Subscript" [.node "Var" [.text "b"], .node "IntConst" [.text "0"]]]]],
                        .node "Less" [
                          .node "Subscript" [.node "Var" [.text "b"], .node "IntConst" [.text "2"]],
                          .node "IntConst" [.text "0"]]]]]]]]]]]]]

/-- The output of `cesta read` on the pointer program. -/
def pointersPrinted : String :=
  "(c:TranslationUnit (c:List (c:ExternalFunction (c:FunctionDefinition (c:UniqueDeclarationSpecifiers \
  (c:Void) (c:List)) (c:Declarator (c:FunctionDeclarator (c:NameDeclarator put) (c:ParameterTypes \
  (c:List (c:NamedParameter (c:PrimitiveDeclarationSpecifiers (c:Int) (c:List)) (c:PointerDeclarator \
  (c:Pointer (c:NoTypeQualifiers)) (c:NameDeclarator q))) (c:NamedParameter \
  (c:PrimitiveDeclarationSpecifiers (c:Int) (c:List)) (c:Declarator (c:NameDeclarator v))))))) \
  (c:List) (c:Block (c:List (c:BlockStatement (c:ExpressionStatement (c:SomeFullExpression (c:Assign \
  (c:Indirection (c:Var q)) (c:Var v))))) (c:BlockStatement (c:JumpStatement (c:Return \
  (c:NoFullExpression)))))))) (c:ExternalFunction (c:FunctionDefinition \
  (c:PrimitiveDeclarationSpecifiers (c:Int) (c:List)) (c:Declarator (c:FunctionDeclarator \
  (c:NameDeclarator sum) (c:ParameterTypes (c:List (c:NamedParameter \
  (c:PrimitiveDeclarationSpecifiers (c:Int) (c:List)) (c:PointerDeclarator (c:Pointer \
  (c:NoTypeQualifiers)) (c:NameDeclarator a))) (c:NamedParameter (c:PrimitiveDeclarationSpecifiers \
  (c:Int) (c:List)) (c:Declarator (c:NameDeclarator n))))))) (c:List) (c:Block (c:List \
  (c:BlockDeclaration (c:Declaration (c:PrimitiveDeclarationSpecifiers (c:Int) (c:List)) \
  (c:InitDeclarators (c:List (c:InitDeclaratorValue (c:Declarator (c:NameDeclarator s)) \
  (c:InitializerExpression (c:IntConst \"0\"))) (c:InitDeclaratorValue (c:Declarator \
  (c:NameDeclarator i)) (c:InitializerExpression (c:IntConst \"0\"))))))) (c:BlockStatement \
  (c:IterationStatement (c:While (c:Less (c:Var i) (c:Var n)) (c:CompoundStatement (c:Block (c:List \
  (c:BlockStatement (c:SelectionStatement (c:If (c:Equal (c:Subscript (c:Var a) (c:Var i)) \
  (c:IntConst \"0\")) (c:JumpStatement (c:Break))))) (c:BlockStatement (c:ExpressionStatement \
  (c:SomeFullExpression (c:Assign (c:Var s) (c:Add (c:Var s) (c:Subscript (c:Var a) (c:Var i))))))) \
  (c:BlockStatement (c:ExpressionStatement (c:SomeFullExpression (c:Assign (c:Var i) (c:Add (c:Var \
  i) (c:IntConst \"1\")))))) (c:BlockStatement (c:JumpStatement (c:Continue))))))))) \
  (c:BlockStatement (c:JumpStatement (c:Return (c:SomeFullExpression (c:Var s))))))))) \
  (c:ExternalFunction (c:FunctionDefinition (c:PrimitiveDeclarationSpecifiers (c:Int) (c:List)) \
  (c:PointerDeclarator (c:Pointer (c:NoTypeQualifiers)) (c:FunctionDeclarator (c:NameDeclarator \
  next) (c:ParameterTypes (c:List (c:NamedParameter (c:PrimitiveDeclarationSpecifiers (c:Int) \
  (c:List)) (c:PointerDeclarator (c:Pointer (c:NoTypeQualifiers)) (c:NameDeclarator p))))))) \
  (c:List) (c:Block (c:List (c:BlockStatement (c:JumpStatement (c:Return (c:SomeFullExpression \
  (c:Add (c:Var p) (c:IntConst \"1\")))))))))) (c:ExternalFunction (c:FunctionDefinition \
  (c:PrimitiveDeclarationSpecifiers (c:Int) (c:List)) (c:Declarator (c:FunctionDeclarator \
  (c:NameDeclarator main) (c:ParameterTypes (c:List (c:AbstractParameter \
  (c:UniqueDeclarationSpecifiers (c:Void) (c:List)) (c:NoAbstractDeclarator)))))) (c:List) (c:Block \
  (c:List (c:BlockDeclaration (c:Declaration (c:PrimitiveDeclarationSpecifiers (c:Int) (c:List)) \
  (c:InitDeclarators (c:List (c:InitDeclarator (c:Declarator (c:ArrayDeclarator (c:NameDeclarator b) \
  (c:NoTypeQualifiers) (c:SomeExpression (c:IntConst \"3\"))))))))) (c:BlockDeclaration \
  (c:Declaration (c:PrimitiveDeclarationSpecifiers (c:Int) (c:List)) (c:InitDeclarators (c:List \
  (c:InitDeclaratorValue (c:PointerDeclarator (c:Pointer (c:NoTypeQualifiers)) (c:NameDeclarator p)) \
  (c:InitializerExpression (c:IntConst \"0\"))))))) (c:BlockDeclaration (c:Declaration \
  (c:PrimitiveDeclarationSpecifiers (c:Long) (c:List)) (c:InitDeclarators (c:List \
  (c:InitDeclaratorValue (c:Declarator (c:NameDeclarator w)) (c:InitializerExpression (c:Cast \
  (c:TypeName (c:PrimitiveSpecifierQualifiers (c:Long) (c:List)) (c:NoAbstractDeclarator)) \
  (c:IntConst \"3\")))))))) (c:BlockDeclaration (c:Declaration (c:PrimitiveDeclarationSpecifiers \
  (c:Int) (c:List)) (c:InitDeclarators (c:List (c:InitDeclarator (c:PointerDeclarator (c:Pointer \
  (c:NoTypeQualifiers)) (c:NameDeclarator q))))))) (c:BlockStatement (c:ExpressionStatement \
  (c:SomeFullExpression (c:Assign (c:Subscript (c:Var b) (c:IntConst \"0\")) (c:IntConst \"2\"))))) \
  (c:BlockStatement (c:ExpressionStatement (c:SomeFullExpression (c:Assign (c:Subscript (c:Var b) \
  (c:IntConst \"1\")) (c:IntConst \"0\"))))) (c:BlockStatement (c:ExpressionStatement \
  (c:SomeFullExpression (c:Assign (c:Subscript (c:Var b) (c:IntConst \"2\")) (c:Negate (c:IntConst \
  \"5\")))))) (c:BlockStatement (c:ExpressionStatement (c:SomeFullExpression (c:Assign (c:Var p) \
  (c:Call (c:Var malloc) (c:Arguments (c:List (c:Multiply (c:IntConst \"3\") (c:SizeofType \
  (c:TypeName (c:PrimitiveSpecifierQualifiers (c:Int) (c:List)) (c:NoAbstractDeclarator))))))))))) \
  (c:BlockStatement (c:ExpressionStatement (c:SomeFullExpression (c:Assign (c:Subscript (c:Var p) \
  (c:IntConst \"0\")) (c:IntConst \"1\"))))) (c:BlockStatement (c:ExpressionStatement \
  (c:SomeFullExpression (c:Assign (c:Indirection (c:Add (c:Var p) (c:IntConst \"1\"))) (c:IntConst \
  \"2\"))))) (c:BlockStatement (c:ExpressionStatement (c:SomeFullExpression (c:Assign (c:Subscript \
  (c:Var p) (c:IntConst \"2\")) (c:IntConst \"7\"))))) (c:BlockStatement (c:ExpressionStatement \
  (c:SomeFullExpression (c:Call (c:Var put) (c:Arguments (c:List (c:AddressOf (c:Subscript (c:Var b) \
  (c:IntConst \"1\"))) (c:IntConst \"4\"))))))) (c:BlockStatement (c:ExpressionStatement \
  (c:SomeFullExpression (c:Assign (c:Var q) (c:Call (c:Var next) (c:Arguments (c:List (c:Var \
  p)))))))) (c:BlockStatement (c:CompoundStatement (c:Block (c:List (c:BlockDeclaration \
  (c:Declaration (c:PrimitiveDeclarationSpecifiers (c:Int) (c:List)) (c:InitDeclarators (c:List \
  (c:InitDeclarator (c:Declarator (c:NameDeclarator z))))))) (c:BlockStatement \
  (c:ExpressionStatement (c:SomeFullExpression (c:Assign (c:Var z) (c:Call (c:Var sum) (c:Arguments \
  (c:List (c:Var b) (c:IntConst \"3\")))))))) (c:BlockStatement (c:ExpressionStatement \
  (c:SomeFullExpression (c:Assign (c:Subscript (c:Var b) (c:IntConst \"0\")) (c:Add (c:Var z) \
  (c:Indirection (c:Var q))))))))))) (c:BlockStatement (c:ExpressionStatement (c:SomeFullExpression \
  (c:Assign (c:Var w) (c:Multiply (c:Var w) (c:Subscript (c:Var b) (c:IntConst \"0\"))))))) \
  (c:BlockStatement (c:ExpressionStatement (c:SomeFullExpression (c:Assign (c:Subscript (c:Var b) \
  (c:IntConst \"1\")) (c:IntConst \"0\"))))) (c:BlockStatement (c:CompoundStatement (c:Block (c:List \
  (c:BlockDeclaration (c:Declaration (c:PrimitiveDeclarationSpecifiers (c:Int) (c:List)) \
  (c:InitDeclarators (c:List (c:InitDeclarator (c:Declarator (c:NameDeclarator y))))))) \
  (c:BlockStatement (c:ExpressionStatement (c:SomeFullExpression (c:Assign (c:Var y) (c:Call (c:Var \
  sum) (c:Arguments (c:List (c:Var b) (c:IntConst \"3\")))))))) (c:BlockStatement \
  (c:ExpressionStatement (c:SomeFullExpression (c:Call (c:Var free) (c:Arguments (c:List (c:Var \
  p))))))) (c:BlockStatement (c:ExpressionStatement (c:SomeFullExpression (c:Call (c:Var free) \
  (c:Arguments (c:List (c:IntConst \"0\"))))))) (c:BlockStatement (c:SelectionStatement (c:If \
  (c:NotEqual (c:Var y) (c:IntConst \"3\")) (c:JumpStatement (c:Return (c:SomeFullExpression \
  (c:Negate (c:IntConst \"1\")))))))))))) (c:BlockStatement (c:JumpStatement (c:Return \
  (c:SomeFullExpression (c:Subtract (c:Add (c:Multiply (c:Var w) (c:IntConst \"10\")) (c:Indirection \
  (c:AddressOf (c:Subscript (c:Var b) (c:IntConst \"0\"))))) (c:Less (c:Subscript (c:Var b) \
  (c:IntConst \"2\")) (c:IntConst \"0\")))))))))))))"

#guard printed pointersUnit == pointersPrinted

theorem cesta_pointer_program_returns_92 : (runUnit [] pointersUnit 2000).bind returned = some 92 := by
  decide +kernel

/-! An undefined function is a host service only when the interface offers it. -/

/-- `int main(void) { int x; x = read(); return x + 1; }` -/

def echoUnit : CanonicalTerm :=
  .node "TranslationUnit" [
    .seq [
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "main"],
              .node "ParameterTypes" [
                .seq [
                  .node "AbstractParameter" [
                    .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
                    .node "NoAbstractDeclarator" []]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [.node "InitDeclarator" [.node "Declarator" [.node "NameDeclarator" [.text "x"]]]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [
                      .node "Var" [.text "x"],
                      .node "Call" [.node "Var" [.text "read"], .node "NoArguments" []]]]]],
              .node "BlockStatement" [
                .node "JumpStatement" [
                  .node "Return" [
                    .node "SomeFullExpression" [
                      .node "Add" [.node "Var" [.text "x"], .node "IntConst" [.text "1"]]]]]]]]]]]]

def readService : List (String × Signature) := [("read", ⟨[], some (.integer .int)⟩)]

theorem undeclared_function_refused : (readUnit model [] echoUnit).isNone = true := by decide +kernel

theorem service_call_suspends_and_resumes :
    let suspended := (runUnit readService echoUnit 60).bind fun
      | (_, .suspended request saved) => if request.service == "read" then some saved else none
      | _ => none
    let program := (readUnit model readService echoUnit).getD []
    ((suspended.bind (reply model policy (.integer six))).map ((machine model policy abi program).run 60)).bind
      returned = some 7 := by
  decide +kernel

/-! Programs outside the fragment, or ill-formed, are refused rather than approximated. -/


/-- `int main(void) { int s = 0, i; for (i = 0; i < 3; i = i + 1) s = s + i; return s; }` -/
def forUnit : CanonicalTerm :=
  .node "TranslationUnit" [
    .seq [
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "main"],
              .node "ParameterTypes" [
                .seq [
                  .node "AbstractParameter" [
                    .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
                    .node "NoAbstractDeclarator" []]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [
                      .node "InitDeclaratorValue" [
                        .node "Declarator" [.node "NameDeclarator" [.text "s"]],
                        .node "InitializerExpression" [.node "IntConst" [.text "0"]]],
                      .node "InitDeclarator" [.node "Declarator" [.node "NameDeclarator" [.text "i"]]]]]]],
              .node "BlockStatement" [
                .node "IterationStatement" [
                  .node "For" [
                    .node "SomeFullExpression" [
                      .node "Assign" [.node "Var" [.text "i"], .node "IntConst" [.text "0"]]],
                    .node "SomeFullExpression" [
                      .node "Less" [.node "Var" [.text "i"], .node "IntConst" [.text "3"]]],
                    .node "SomeFullExpression" [
                      .node "Assign" [
                        .node "Var" [.text "i"],
                        .node "Add" [.node "Var" [.text "i"], .node "IntConst" [.text "1"]]]],
                    .node "ExpressionStatement" [
                      .node "SomeFullExpression" [
                        .node "Assign" [
                          .node "Var" [.text "s"],
                          .node "Add" [.node "Var" [.text "s"], .node "Var" [.text "i"]]]]]]]],
              .node "BlockStatement" [
                .node "JumpStatement" [.node "Return" [.node "SomeFullExpression" [.node "Var" [.text "s"]]]]]]]]]]]

theorem for_loop_refused : (readUnit model [] forUnit).isNone = true := by decide +kernel

/-- `int main(void) { int x; int x; return 0; }` -/
def redeclaredUnit : CanonicalTerm :=
  .node "TranslationUnit" [
    .seq [
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "main"],
              .node "ParameterTypes" [
                .seq [
                  .node "AbstractParameter" [
                    .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
                    .node "NoAbstractDeclarator" []]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [.node "InitDeclarator" [.node "Declarator" [.node "NameDeclarator" [.text "x"]]]]]]],
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [.node "InitDeclarator" [.node "Declarator" [.node "NameDeclarator" [.text "x"]]]]]]],
              .node "BlockStatement" [
                .node "JumpStatement" [
                  .node "Return" [.node "SomeFullExpression" [.node "IntConst" [.text "0"]]]]]]]]]]]

theorem redeclaration_in_one_scope_refused : (readUnit model [] redeclaredUnit).isNone = true := by decide +kernel

/-- `int main(void) { break; return 0; }` -/
def strayBreakUnit : CanonicalTerm :=
  .node "TranslationUnit" [
    .seq [
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "main"],
              .node "ParameterTypes" [
                .seq [
                  .node "AbstractParameter" [
                    .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
                    .node "NoAbstractDeclarator" []]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockStatement" [.node "JumpStatement" [.node "Break" []]],
              .node "BlockStatement" [
                .node "JumpStatement" [
                  .node "Return" [.node "SomeFullExpression" [.node "IntConst" [.text "0"]]]]]]]]]]]

theorem break_outside_loop_refused : (readUnit model [] strayBreakUnit).isNone = true := by decide +kernel

/-- `int f(void) { return; } int main(void) { return 0; }` -/
def valuelessReturnUnit : CanonicalTerm :=
  .node "TranslationUnit" [
    .seq [
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "f"],
              .node "ParameterTypes" [
                .seq [
                  .node "AbstractParameter" [
                    .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
                    .node "NoAbstractDeclarator" []]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockStatement" [.node "JumpStatement" [.node "Return" [.node "NoFullExpression" []]]]]]]],
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "main"],
              .node "ParameterTypes" [
                .seq [
                  .node "AbstractParameter" [
                    .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
                    .node "NoAbstractDeclarator" []]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockStatement" [
                .node "JumpStatement" [
                  .node "Return" [.node "SomeFullExpression" [.node "IntConst" [.text "0"]]]]]]]]]]]

theorem valueless_return_in_int_function_refused : (readUnit model [] valuelessReturnUnit).isNone = true := by decide +kernel

/-- `int main(void) { long *p; int x; p = &x; return 0; }` -/
def mismatchedPointerUnit : CanonicalTerm :=
  .node "TranslationUnit" [
    .seq [
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "main"],
              .node "ParameterTypes" [
                .seq [
                  .node "AbstractParameter" [
                    .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
                    .node "NoAbstractDeclarator" []]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Long" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [
                      .node "InitDeclarator" [
                        .node "PointerDeclarator" [
                          .node "Pointer" [.node "NoTypeQualifiers" []],
                          .node "NameDeclarator" [.text "p"]]]]]]],
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [.node "InitDeclarator" [.node "Declarator" [.node "NameDeclarator" [.text "x"]]]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [.node "Var" [.text "p"], .node "AddressOf" [.node "Var" [.text "x"]]]]]],
              .node "BlockStatement" [
                .node "JumpStatement" [
                  .node "Return" [.node "SomeFullExpression" [.node "IntConst" [.text "0"]]]]]]]]]]]

theorem pointer_type_mismatch_refused : (readUnit model [] mismatchedPointerUnit).isNone = true := by decide +kernel

/-- `int f(void) { return 1; } int main(void) { int f; int x; x = f(); return x; }` -/
def shadowedCallUnit : CanonicalTerm :=
  .node "TranslationUnit" [
    .seq [
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "f"],
              .node "ParameterTypes" [
                .seq [
                  .node "AbstractParameter" [
                    .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
                    .node "NoAbstractDeclarator" []]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockStatement" [
                .node "JumpStatement" [
                  .node "Return" [.node "SomeFullExpression" [.node "IntConst" [.text "1"]]]]]]]]],
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "main"],
              .node "ParameterTypes" [
                .seq [
                  .node "AbstractParameter" [
                    .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
                    .node "NoAbstractDeclarator" []]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [.node "InitDeclarator" [.node "Declarator" [.node "NameDeclarator" [.text "f"]]]]]]],
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [.node "InitDeclarator" [.node "Declarator" [.node "NameDeclarator" [.text "x"]]]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [
                      .node "Var" [.text "x"],
                      .node "Call" [.node "Var" [.text "f"], .node "NoArguments" []]]]]],
              .node "BlockStatement" [
                .node "JumpStatement" [.node "Return" [.node "SomeFullExpression" [.node "Var" [.text "x"]]]]]]]]]]]

theorem call_of_hidden_function_refused : (readUnit model [] shadowedCallUnit).isNone = true := by decide +kernel

/-- `int malloc(int n) { return n; } int main(void) { return 0; }` -/
def definedMallocUnit : CanonicalTerm :=
  .node "TranslationUnit" [
    .seq [
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "malloc"],
              .node "ParameterTypes" [
                .seq [
                  .node "NamedParameter" [
                    .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                    .node "Declarator" [.node "NameDeclarator" [.text "n"]]]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockStatement" [
                .node "JumpStatement" [.node "Return" [.node "SomeFullExpression" [.node "Var" [.text "n"]]]]]]]]],
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "main"],
              .node "ParameterTypes" [
                .seq [
                  .node "AbstractParameter" [
                    .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
                    .node "NoAbstractDeclarator" []]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockStatement" [
                .node "JumpStatement" [
                  .node "Return" [.node "SomeFullExpression" [.node "IntConst" [.text "0"]]]]]]]]]]]

theorem definition_of_malloc_refused : (readUnit model [] definedMallocUnit).isNone = true := by decide +kernel

/-- `int f(int n) { int n; return n; } int main(void) { return 0; }` -/
def redeclaredParameterUnit : CanonicalTerm :=
  .node "TranslationUnit" [
    .seq [
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "f"],
              .node "ParameterTypes" [
                .seq [
                  .node "NamedParameter" [
                    .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                    .node "Declarator" [.node "NameDeclarator" [.text "n"]]]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [.node "InitDeclarator" [.node "Declarator" [.node "NameDeclarator" [.text "n"]]]]]]],
              .node "BlockStatement" [
                .node "JumpStatement" [.node "Return" [.node "SomeFullExpression" [.node "Var" [.text "n"]]]]]]]]],
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "main"],
              .node "ParameterTypes" [
                .seq [
                  .node "AbstractParameter" [
                    .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
                    .node "NoAbstractDeclarator" []]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockStatement" [
                .node "JumpStatement" [
                  .node "Return" [.node "SomeFullExpression" [.node "IntConst" [.text "0"]]]]]]]]]]]

theorem parameter_redeclared_in_body_refused : (readUnit model [] redeclaredParameterUnit).isNone = true := by decide +kernel

end Mettapedia.Languages.C11.CestaFixedCoreControls
