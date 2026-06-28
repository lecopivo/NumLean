module

public import Batteries.Data.FloatArray
import all Init.Data.FloatArray.Basic
public import NumLean.Data.Scalars.Float32.Float32Array
public import NumLean.Data.ScalarArrays

@[expose] public section

open NumLean

example : (FloatArray.mk #[1.0, 2.0]).usize = 2 := rfl
example : (Float32Array.empty.push 1).size = 1 := rfl

example : (Int32Array.empty.push 1 |>.push 2).data = #[1, 2] := rfl
example : (Int32Array.empty.push 1 |>.push 2).usize = 2 := rfl
example : (Int32Array.mk #[1, 2, 3]).get! 1 = 2 := rfl
example : ((Int32Array.mk #[1, 2, 3]).set! 1 7).data = #[1, 7, 3] := rfl

example : (Int64Array.empty.push 1 |>.push 2).data = #[1, 2] := rfl
example : (Int64Array.empty.push 1 |>.push 2).usize = 2 := rfl
example : (Int64Array.mk #[1, 2, 3]).get! 1 = 2 := rfl
example : ((Int64Array.mk #[1, 2, 3]).set! 1 7).data = #[1, 7, 3] := rfl

example : (USizeArray.empty.push 1 |>.push 2).data = #[1, 2] := rfl
example : (USizeArray.empty.push 1 |>.push 2).usize = 2 := rfl
example : (USizeArray.mk #[1, 2, 3]).get! 1 = 2 := rfl
example : ((USizeArray.mk #[1, 2, 3]).set! 1 7).data = #[1, 7, 3] := rfl
