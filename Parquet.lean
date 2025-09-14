structure Parquet where

@[extern "lean_io_fs_handle_seek"]
opaque IO.FS.Handle.seek (h : @& IO.FS.Handle) (offset : Int) (whence : UInt32) : IO UInt64

def readParquetFile (path : System.FilePath) : IO Parquet := do

  if (!(← System.FilePath.pathExists path)) then
    throw (IO.userError "Path '{dataPath}' relative to project root does not exist")
  let _contents ← IO.FS.withFile path IO.FS.Mode.read (fun f => do
    f.seek 0 0
  )
  pure Parquet.mk
