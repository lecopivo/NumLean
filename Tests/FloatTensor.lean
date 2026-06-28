module

public import NumLean
public import NumLean.Data.Scalars.Float64.RealModel
-- public meta import NumLean.Data.FinHTuple.Pretty

@[expose] public section

open NumLean

namespace FloatTensor


/-- info: [2.000000,4.000000,6.000000,8.000000] -/
#guard_msgs in
#eval! ⊞[1.0,2,3,4] + ⊞[1.0,2,3,4]

/-- info: 2.0 • ⊞[1.0, 2, 3, 4] : Float^[4] -/
#guard_msgs in
#check 2.0 • ⊞[1.0,2,3,4]

/-- info: ⊞[1.0, 2, 3, 4] - ⊞[100.0, 0, 0, 0] : Float^[4] -/
#guard_msgs in
#check ⊞[1.0,2,3,4] - ⊞[100.0,0,0,0]

/-- info: ⊞[[1.0, 2], [3, 4]] - ⊞[[100.0, 0], [0, 0]] : Float^[2, 2] -/
#guard_msgs in
#check ⊞[[1.0,2],[3,4]] - ⊞[[100.0,0],[0,0]]

-- missing product of TensorIndexType
/-- info: ⊞[[1.0, 2], [3, 4]] : Float^[2, 2] -/
#guard_msgs in
#check ⊞[[1.0,2],[3,4]]
