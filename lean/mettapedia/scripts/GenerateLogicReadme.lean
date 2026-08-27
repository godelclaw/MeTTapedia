import Mettapedia.DocText.LogicReadmeCompositional

open Mettapedia.DocText.LogicReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "~/claude/lean-projects/mettapedia/Mettapedia/Logic/README.md" logicReadmeMarkdown

