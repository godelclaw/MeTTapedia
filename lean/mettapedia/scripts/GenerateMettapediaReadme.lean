import Mettapedia.DocText.MettapediaReadmeCompositional

open Mettapedia.DocText.MettapediaReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "README.md" mettapediaReadmeMarkdown
