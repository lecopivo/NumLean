import NumLean.Data.FloatArray.TensorOps

open NumLean

def assertFloatArrayData (name : String) (actual : FloatArray) (expected : Array Float) : IO Unit := do
  unless actual.data == expected do
    throw <| IO.userError s!"{name}: expected {reprStr expected}, got {reprStr actual.data}"

def testFill : IO Unit := do
  let counts : Vector Nat 2 := #v[2, 3]
  let dstStrides : Vector Nat 2 := #v[4, 1]
  let dst : FloatArray := FloatArray.mk #[0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]
  let actual := FloatArray.fillTensorSlice counts dst 1 dstStrides 9.5
  assertFloatArrayData "fill strided 2x3 slice" actual
    #[0.0, 9.5, 9.5, 9.5, 4.0, 9.5, 9.5, 9.5, 8.0]

def testCopy : IO Unit := do
  let counts : Vector Nat 2 := #v[2, 2]
  let srcStrides : Vector Nat 2 := #v[5, 2]
  let dstStrides : Vector Nat 2 := #v[3, 1]
  let src : FloatArray := FloatArray.mk
    #[0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0]
  let dst : FloatArray := FloatArray.mk #[100.0, 101.0, 102.0, 103.0, 104.0, 105.0, 106.0]
  let actual := FloatArray.copyTensorSlice counts src 2 srcStrides dst 1 dstStrides
  assertFloatArrayData "copy strided 2x2 slice" actual
    #[100.0, 2.0, 4.0, 103.0, 7.0, 9.0, 106.0]

def testExtract : IO Unit := do
  let counts : Vector Nat 2 := #v[2, 3]
  let srcStrides : Vector Nat 2 := #v[4, 1]
  let src : FloatArray := FloatArray.mk
    #[0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]
  let actual := FloatArray.extractTensorSlice counts src 1 srcStrides
  assertFloatArrayData "extract strided 2x3 slice" actual #[1.0, 2.0, 3.0, 5.0, 6.0, 7.0]

def testOutOfBoundsGuards : IO Unit := do
  let counts : Vector Nat 1 := #v[4]
  let strides : Vector Nat 1 := #v[2]
  let dst : FloatArray := FloatArray.mk #[0.0, 1.0, 2.0, 3.0]
  let filled := FloatArray.fillTensorSlice counts dst 1 strides 8.0
  assertFloatArrayData "fill skips out-of-bounds destinations" filled #[0.0, 8.0, 2.0, 8.0]

  let src : FloatArray := FloatArray.mk #[10.0, 11.0, 12.0, 13.0]
  let extracted := FloatArray.extractTensorSlice counts src 1 strides
  assertFloatArrayData "extract pads out-of-bounds reads" extracted #[11.0, 13.0, 0.0, 0.0]

def testZeroCount : IO Unit := do
  let counts : Vector Nat 2 := #v[2, 0]
  let strides : Vector Nat 2 := #v[4, 1]
  let xs : FloatArray := FloatArray.mk #[1.0, 2.0, 3.0]
  let filled := FloatArray.fillTensorSlice counts xs 0 strides 9.0
  assertFloatArrayData "fill zero-sized slice" filled #[1.0, 2.0, 3.0]
  let extracted := FloatArray.extractTensorSlice counts xs 0 strides
  assertFloatArrayData "extract zero-sized slice" extracted #[]

def runFloatArrayTensorOpsTests : IO Unit := do
  testFill
  testCopy
  testExtract
  testOutOfBoundsGuards
  testZeroCount
  IO.println "FloatArray tensor C ops tests passed"
