import Veil

private def checkPreviewBranchCiTrigger : IO Unit := do
  let workflow ← IO.FS.readFile ".github/workflows/ci.yml"
  let expected := "      - 'veil-2.0*'"
  unless (workflow.splitOn "\n").contains expected do
    throw <| IO.userError "CI push branches must include the veil-2.0* pattern"

#eval checkPreviewBranchCiTrigger
