structure Parquet where

@[extern "lean_io_fs_handle_seek"]
opaque IO.FS.Handle.seek (h : @& IO.FS.Handle) (offset : UInt64) (whence : Int32) : IO Int32

@[extern "lean_io_fs_SEEK_SET"]
opaque IO.FS.SEEK_SET : Unit → Int32

@[extern "lean_io_fs_SEEK_CUR"]
opaque IO.FS.SEEK_CUR : Unit → Int32

@[extern "lean_io_fs_SEEK_END"]
opaque IO.FS.SEEK_END : Unit → Int32

def readParquetFile (path : System.FilePath) : IO Parquet := do

  if (!(← System.FilePath.pathExists path)) then
    throw (IO.userError "Path '{dataPath}' relative to project root does not exist")
  let _contents ← IO.FS.withFile path IO.FS.Mode.read (fun f => do
    let z ← f.seek (-16) (IO.FS.SEEK_END ())
    IO.println s!"Got back integer {z} from FFI"
    let buf ← f.read 16
    IO.println s!"Here's a buffer: {buf}"
  )
  IO.println "Success"
  pure Parquet.mk
