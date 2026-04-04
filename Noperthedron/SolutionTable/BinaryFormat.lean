import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.RationalGlobalCheck
import Noperthedron.SolutionTable.RationalLocalCheck.Computable.Oracle

namespace Solution

/-!
# Binary format parser for solution table data

Reads `solution_table.bin` and `cert_data.bin` produced by `scripts/export_binary.py`.
Provides `@[implemented_by]` hooks for `native_decide` evaluation.

## Binary layout

**solution_table.bin** — Header (16 bytes) + N × 88-byte rows:
```
Header: magic(4) version(4) rowCount(4) reserved(4)
Row:    ID(u32) nodeType(u8) nrChildren(u8) split(u8) S_index(u8)
        IDfirstChild(u32)
        T1_min(i32) T1_max(i32) V1_min(i32) V1_max(i32)
        T2_min(i32) T2_max(i32) V2_min(i32) V2_max(i32)
        A_min(i32) A_max(i32)
        P1(u8) P2(u8) P3(u8) Q1(u8) Q2(u8) Q3(u8) sigma_Q(u8) pad(u8)
        wx(i64) wy(i64) w_denominator(i64) r(i32)
```

**cert_data.bin** — Header (16 bytes) + N × 8-byte rows:
```
Header: magic(4) version(4) rowCount(4) reserved(4)
Row:    exceeds(u8) boundR(u8) boundDelta(u8) ae1(u8) ae2(u8) span1(u8) span2(u8) be(u8)
```
-/

/-! ### Constants -/

def TABLE_MAGIC : UInt32 := 0x4E505442
def TABLE_VERSION : UInt32 := 1
def TABLE_HEADER : Nat := 16
def TABLE_ROW_SIZE : Nat := 88

def CERT_MAGIC : UInt32 := 0x4E505443
def CERT_VERSION : UInt32 := 1
def CERT_HEADER : Nat := 16
def CERT_ROW_SIZE : Nat := 8

/-! ### ByteArray readers (little-endian) -/

/-- Read uint32 LE from ByteArray. -/
@[inline] def readU32 (ba : ByteArray) (off : Nat) : UInt32 :=
  let b0 := ba.get! off |>.toUInt32
  let b1 := ba.get! (off + 1) |>.toUInt32
  let b2 := ba.get! (off + 2) |>.toUInt32
  let b3 := ba.get! (off + 3) |>.toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

/-- Read int32 LE as Int. -/
@[inline] def readI32 (ba : ByteArray) (off : Nat) : Int :=
  let u := (readU32 ba off).toNat
  if u ≥ 2 ^ 31 then (Int.ofNat u) - (Int.ofNat (2 ^ 32)) else Int.ofNat u

/-- Read int64 LE as Int. -/
@[inline] def readI64 (ba : ByteArray) (off : Nat) : Int :=
  let lo := (readU32 ba off).toNat
  let hi := (readU32 ba (off + 4)).toNat
  let u : Nat := lo + hi * 2 ^ 32
  if u ≥ 2 ^ 63 then (Int.ofNat u) - (Int.ofNat (2 ^ 64)) else Int.ofNat u

/-- Read uint64 LE as Nat. -/
@[inline] def readU64 (ba : ByteArray) (off : Nat) : Nat :=
  let lo := (readU32 ba off).toNat
  let hi := (readU32 ba (off + 4)).toNat
  lo + hi * 2 ^ 32

/-! ### Row parsing -/

/-- Construct sigma_Q element from a Nat (0 or 1). -/
private def mkSigmaQ (n : Nat) : ↥(Finset.Icc (0 : ℕ) 1) :=
  if h : n ∈ Finset.Icc (0 : ℕ) 1 then ⟨n, h⟩ else ⟨0, by decide⟩

/-- Parse a single Row from binary data at the given byte offset. -/
def parseRowBin (ba : ByteArray) (off : Nat) : Row :=
  let sIdx := (ba.get! (off + 7)).toNat
  { ID           := (readU32 ba off).toNat
    nodeType     := (ba.get! (off + 4)).toNat
    nrChildren   := (ba.get! (off + 5)).toNat
    split        := (ba.get! (off + 6)).toNat
    IDfirstChild := (readU32 ba (off + 8)).toNat
    interval     := {
      min := fun
        | .θ₁ => readI32 ba (off + 12)
        | .φ₁ => readI32 ba (off + 20)
        | .θ₂ => readI32 ba (off + 28)
        | .φ₂ => readI32 ba (off + 36)
        | .α  => readI32 ba (off + 44)
      max := fun
        | .θ₁ => readI32 ba (off + 16)
        | .φ₁ => readI32 ba (off + 24)
        | .θ₂ => readI32 ba (off + 32)
        | .φ₂ => readI32 ba (off + 40)
        | .α  => readI32 ba (off + 48)
    }
    S_index      := ⟨sIdx % 90, Nat.mod_lt _ (by omega)⟩
    P1_index     := (ba.get! (off + 52)).toNat
    P2_index     := (ba.get! (off + 53)).toNat
    P3_index     := (ba.get! (off + 54)).toNat
    Q1_index     := (ba.get! (off + 55)).toNat
    Q2_index     := (ba.get! (off + 56)).toNat
    Q3_index     := (ba.get! (off + 57)).toNat
    sigma_Q      := mkSigmaQ (ba.get! (off + 58)).toNat
    wx_numerator := readI64 ba (off + 60)
    wy_numerator := readI64 ba (off + 68)
    w_denominator := readU64 ba (off + 76)
    r            := readI32 ba (off + 84)
  }

/-! ### Table parsing -/

/-- Parse an entire solution table from binary data. -/
def parseTableBin (ba : ByteArray) : Except String Table := do
  if ba.size < TABLE_HEADER then throw "table: file too small"
  if readU32 ba 0 != TABLE_MAGIC then throw "table: bad magic"
  if readU32 ba 4 != TABLE_VERSION then throw "table: bad version"
  let n := (readU32 ba 8).toNat
  if ba.size < TABLE_HEADER + n * TABLE_ROW_SIZE then throw "table: truncated"
  pure (Array.ofFn fun (i : Fin n) => parseRowBin ba (TABLE_HEADER + i.val * TABLE_ROW_SIZE))

/-! ### Certificate parsing -/

/-- Parse certificate data from binary. Returns (exceeds_ok, localCertData). -/
def parseCertBin (ba : ByteArray) :
    Except String (Array Bool × LocalPrecheckCertificateData) := do
  if ba.size < CERT_HEADER then throw "cert: file too small"
  if readU32 ba 0 != CERT_MAGIC then throw "cert: bad magic"
  if readU32 ba 4 != CERT_VERSION then throw "cert: bad version"
  let n := (readU32 ba 8).toNat
  if ba.size < CERT_HEADER + n * CERT_ROW_SIZE then throw "cert: truncated"
  let base := CERT_HEADER
  let readBool (i : Fin n) (off : Nat) : Bool := ba.get! (base + i.val * CERT_ROW_SIZE + off) != 0
  pure (
    Array.ofFn (readBool · 0),
    { boundR_ok     := Array.ofFn (readBool · 1)
      boundDelta_ok := Array.ofFn (readBool · 2)
      ae1_ok        := Array.ofFn (readBool · 3)
      ae2_ok        := Array.ofFn (readBool · 4)
      span1_ok      := Array.ofFn (readBool · 5)
      span2_ok      := Array.ofFn (readBool · 6)
      be_ok         := Array.ofFn (readBool · 7)
    }
  )

/-! ### Data loading for @[implemented_by]

These unsafe functions read binary files directly. Since Lean's native compiler
evaluates constants as thunks (evaluated once, result cached), the file is only
read once per process even though no explicit caching is used.
-/

/-- Default paths to binary data files. -/
def defaultTablePath : System.FilePath := "external/rupert/data/solution_table.bin"
def defaultCertPath : System.FilePath := "external/rupert/data/cert_data.bin"

/-- Helper: run an IO action unsafely, returning a default on failure. -/
private unsafe def unsafeRunIO {α : Type} (act : IO α) (default : α) : α :=
  match unsafeBaseIO act.toBaseIO with
  | .ok a => a
  | .error _ => default

/-- Load solution table from binary file. -/
unsafe def getLoadedTableImpl : Table :=
  unsafeRunIO (do
    let bytes ← IO.FS.readBinFile defaultTablePath
    IO.ofExcept (parseTableBin bytes)
  ) #[]

/-- Load exceeds_ok array from certificate binary file. -/
unsafe def getLoadedExceedsImpl : Array Bool :=
  unsafeRunIO (do
    let bytes ← IO.FS.readBinFile defaultCertPath
    let (exc, _) ← IO.ofExcept (parseCertBin bytes)
    pure exc
  ) #[]

/-- Load local certificate data from certificate binary file. -/
unsafe def getLoadedLocalCertImpl : LocalPrecheckCertificateData :=
  unsafeRunIO (do
    let bytes ← IO.FS.readBinFile defaultCertPath
    let (_, lc) ← IO.ofExcept (parseCertBin bytes)
    pure lc
  ) { boundR_ok := #[], boundDelta_ok := #[], ae1_ok := #[],
      ae2_ok := #[], span1_ok := #[], span2_ok := #[], be_ok := #[] }

end Solution
