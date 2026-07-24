import Veil

private def checkReadmePreviewCheckout : IO Unit := do
  let readme ← IO.FS.readFile "README.md"
  let checkoutLines := (readme.splitOn "\n").filter (·.startsWith "cd veil && git checkout ")
  unless checkoutLines == ["cd veil && git checkout veil-2.0-preview"] do
    throw <| IO.userError
      s!"README must check out the published preview branch; found {repr checkoutLines}"

#eval checkReadmePreviewCheckout
