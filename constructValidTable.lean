import Noperthedron

unsafe def main (args : List String) : IO Unit := do
  let csv_filepath ←
    match args with
    | [arg] => pure arg
    | _ => throw (IO.userError "expects exactly one argument")

  let mut rows : Array Noperthedron.Solution.Row := Array.empty
  let h ← IO.FS.Handle.mk csv_filepath IO.FS.Mode.read
  let _ ← h.getLine -- ignore first line
  while True do
    let line ← h.getLine
    let line := line.trimAscii.toString
    if line.isEmpty then break
    let row ← match Noperthedron.Solution.parseRowCsv line with
              | .ok row => pure row
              | .error e => throw (IO.userError e)
    rows := rows.push row

  let table : Noperthedron.Solution.Table := rows
  IO.println s!"parsing done!"

  for (row, ii) in table.zipIdx do
    if row.ValidIx table ii
    then
     IO.println s!"row {ii}: valid"
    else
     IO.println s!"row {ii}: INVALID"
     return
