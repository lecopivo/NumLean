import NumLean.Data.Prod.Order
import NumLean.Data.HTuple.Order

namespace NumLean

namespace Tests

namespace OrderInstances

example : LinearOrder (LexOrder (Nat × Nat)) := inferInstance
example : LinearOrder (ColexOrder (Nat × Nat)) := inferInstance
example : Preorder (ElementwiseOrder (Nat × Nat)) := inferInstance

example : LinearOrder (LexOrder (HTuple Nat (.prod .leaf .leaf))) := inferInstance
example : LinearOrder (ColexOrder (HTuple Nat (.prod .leaf .leaf))) := inferInstance
example : LE (ElementwiseOrder (HTuple Nat (.prod .leaf .leaf))) := inferInstance
example : LT (ElementwiseOrder (HTuple Nat (.prod .leaf .leaf))) := inferInstance

end OrderInstances

end Tests

end NumLean
