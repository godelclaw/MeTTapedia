import Mettapedia.DocText.LogicReadmeCompositional

open Mettapedia.DocText.LogicReadmeCompositional

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.print logicReadmeMarkdown
      return 0
  | [output] =>
      IO.FS.writeFile output logicReadmeMarkdown
      return 0
  | _ =>
      IO.eprintln "Usage: GenerateLogicReadme.lean [OUTPUT]"
      return 2

