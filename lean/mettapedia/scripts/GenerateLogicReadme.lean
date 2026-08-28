import Mettapedia.DocText.LogicReadmeCompositional

open Mettapedia.DocText.LogicReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "Mettapedia/Logic/README.md" logicReadmeMarkdown
