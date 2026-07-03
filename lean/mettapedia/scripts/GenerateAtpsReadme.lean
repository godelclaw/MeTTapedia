import Mettapedia.DocText.AtpsReadmeCompositional

open Mettapedia.DocText.AtpsReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "~/claude/atps/README.md" atpsReadmeMarkdown

