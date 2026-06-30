module

public import NumLean.Data.Scalars.Float64.TensorAlgebra

@[expose] public section

namespace NumLean.Tests.Float64TensorAlgebraFailures

set_option backward.do.legacy false

open Tensor VectorType

/--
error: Application type mismatch: The argument
  HTuple.prod j j
has type
  HTuple ℕ (HTuple.Profile.prod rc rc)
but is expected to have type
  HTuple ℕ (HTuple.Profile.prod ra rc)
in the application
  ↑amap (HTuple.prod j j)
---
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
an xn yn : ℕ
ra rc : Rank
rows : Shape ra
cols : Shape rc
alpha beta : Float
A : Float64Vector an
amap : Layout (HTuple.prod rows cols) (h(an))
x : Float64Vector xn
xmap : Layout cols (h(xn))
y✝¹ : Float64Vector yn
ymap : Layout rows (h(yn))
_hymap : FinHTupleMap.Injective ymap
y✝ : Float64Vector yn := y✝¹
i : Shape ra
__h✝¹ : i ∈ 0...rows
y : Float64Vector yn := __s✝¹
acc✝ : Float := 0
j : Shape rc
__h✝ : j ∈ 0...cols
acc : Float := __s✝
⊢ ↑(↑amap sorry) < an
---
error: (kernel) declaration has metavariables 'NumLean.Tests.Float64TensorAlgebraFailures.tensorGemvBadA'
-/
#guard_msgs in
def tensorGemvBadA {an xn yn : Nat} {ra rc : Rank} {rows : Shape ra} {cols : Shape rc}
    (alpha beta : Float)
    (A : Float64Vector an) (amap : Layout (.prod rows cols) h(an))
    (x : Float64Vector xn) (xmap : Layout cols h(xn))
    (y : Float64Vector yn) (ymap : Layout rows h(yn))
    (_hymap : ymap.Injective) : Float64Vector yn := Id.run do
  let mut y := y
  for_all i in 0...rows do
    let mut acc := 0
    for_all j in 0...cols do
      acc := acc + A[amap (j.prod j)] * x[xmap j]
    y[ymap i] := alpha * acc + beta * y[ymap i]
  return y

/--
error: Application type mismatch: The argument
  HTuple.prod j j
has type
  HTuple ℕ (HTuple.Profile.prod rc rc)
but is expected to have type
  HTuple ℕ (HTuple.Profile.prod rr rc)
in the application
  ↑amap (HTuple.prod j j)
---
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
an xn yn : ℕ
rr rc : Rank
rows : Shape rr
cols : Shape rc
alpha : Float
x : Float64Vector xn
xmap : Layout rows (h(xn))
y : Float64Vector yn
ymap : Layout cols (h(yn))
A✝² : Float64Vector an
amap : Layout (HTuple.prod rows cols) (h(an))
_hamap : FinHTupleMap.Injective amap
A✝¹ : Float64Vector an := A✝²
i : Shape rr
__h✝¹ : i ∈ 0...rows
A✝ : Float64Vector an := __s✝¹
j : Shape rc
__h✝ : j ∈ 0...cols
A : Float64Vector an := __s✝
⊢ ↑(↑amap sorry) < an
---
error: (kernel) declaration has metavariables 'NumLean.Tests.Float64TensorAlgebraFailures.tensorGerBadA'
-/
#guard_msgs in
def tensorGerBadA {an xn yn : Nat} {rr rc : Rank} {rows : Shape rr} {cols : Shape rc}
    (alpha : Float)
    (x : Float64Vector xn) (xmap : Layout rows h(xn))
    (y : Float64Vector yn) (ymap : Layout cols h(yn))
    (A : Float64Vector an) (amap : Layout (.prod rows cols) h(an))
    (_hamap : amap.Injective) : Float64Vector an := Id.run do
  let mut A := A
  for_all i in 0...rows do
    for_all j in 0...cols do
      A[amap (j.prod j)] := A[amap (i.prod j)] + alpha * x[xmap i] * y[ymap j]
  return A

/--
error: Application type mismatch: The argument
  HTuple.prod k k
has type
  HTuple ℕ (HTuple.Profile.prod rk rk)
but is expected to have type
  HTuple ℕ (HTuple.Profile.prod ri rk)
in the application
  ↑amap (HTuple.prod k k)
---
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
an bn cn : ℕ
ri rj rk : Rank
is : Shape ri
js : Shape rj
ks : Shape rk
alpha beta : Float
A : Float64Vector an
amap : Layout (HTuple.prod is ks) (h(an))
B : Float64Vector bn
bmap : Layout (HTuple.prod ks js) (h(bn))
C✝² : Float64Vector cn
cmap : Layout (HTuple.prod is js) (h(cn))
_hcmap : FinHTupleMap.Injective cmap
C✝¹ : Float64Vector cn := C✝²
i : Shape ri
__h✝² : i ∈ 0...is
C✝ : Float64Vector cn := __s✝²
j : Shape rj
__h✝¹ : j ∈ 0...js
C : Float64Vector cn := __s✝¹
acc✝ : Float := 0
k : Shape rk
__h✝ : k ∈ 0...ks
acc : Float := __s✝
⊢ ↑(↑amap sorry) < an
---
error: (kernel) declaration has metavariables 'NumLean.Tests.Float64TensorAlgebraFailures.tensorGemmBadA'
-/
#guard_msgs in
def tensorGemmBadA {an bn cn : Nat} {ri rj rk : Rank}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : Float)
    (A : Float64Vector an) (amap : Layout (.prod is ks) h(an))
    (B : Float64Vector bn) (bmap : Layout (.prod ks js) h(bn))
    (C : Float64Vector cn) (cmap : Layout (.prod is js) h(cn))
    (_hcmap : cmap.Injective) : Float64Vector cn := Id.run do
  let mut C := C
  for_all i in 0...is do
    for_all j in 0...js do
      let mut acc := 0
      for_all k in 0...ks do
        acc := acc + A[amap (k.prod k)] * B[bmap (k.prod j)]
      C[cmap (i.prod j)] := alpha * acc + beta * C[cmap (i.prod j)]
  return C

/--
error: Application type mismatch: The argument
  HTuple.prod i j
has type
  HTuple ℕ (HTuple.Profile.prod ri rj)
but is expected to have type
  HTuple ℕ (HTuple.Profile.prod rk rj)
in the application
  ↑bmap (HTuple.prod i j)
---
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
an bn cn : ℕ
ri rj rk : Rank
is : Shape ri
js : Shape rj
ks : Shape rk
alpha beta : Float
A : Float64Vector an
amap : Layout (HTuple.prod is ks) (h(an))
B : Float64Vector bn
bmap : Layout (HTuple.prod ks js) (h(bn))
C✝² : Float64Vector cn
cmap : Layout (HTuple.prod is js) (h(cn))
_hcmap : FinHTupleMap.Injective cmap
C✝¹ : Float64Vector cn := C✝²
i : Shape ri
__h✝² : i ∈ 0...is
C✝ : Float64Vector cn := __s✝²
j : Shape rj
__h✝¹ : j ∈ 0...js
C : Float64Vector cn := __s✝¹
acc✝ : Float := 0
k : Shape rk
__h✝ : k ∈ 0...ks
acc : Float := __s✝
⊢ ↑(↑bmap sorry) < bn
---
error: (kernel) declaration has metavariables 'NumLean.Tests.Float64TensorAlgebraFailures.tensorGemmBadB'
-/
#guard_msgs in
def tensorGemmBadB {an bn cn : Nat} {ri rj rk : Rank}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : Float)
    (A : Float64Vector an) (amap : Layout (.prod is ks) h(an))
    (B : Float64Vector bn) (bmap : Layout (.prod ks js) h(bn))
    (C : Float64Vector cn) (cmap : Layout (.prod is js) h(cn))
    (_hcmap : cmap.Injective) : Float64Vector cn := Id.run do
  let mut C := C
  for_all i in 0...is do
    for_all j in 0...js do
      let mut acc := 0
      for_all k in 0...ks do
        acc := acc + A[amap (i.prod k)] * B[bmap (i.prod j)]
      C[cmap (i.prod j)] := alpha * acc + beta * C[cmap (i.prod j)]
  return C

/--
error: Application type mismatch: The argument
  HTuple.prod j j
has type
  HTuple ℕ (HTuple.Profile.prod rj rj)
but is expected to have type
  HTuple ℕ (HTuple.Profile.prod ri rj)
in the application
  ↑cmap (HTuple.prod j j)
---
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
an bn cn : ℕ
ri rj rk : Rank
is : Shape ri
js : Shape rj
ks : Shape rk
alpha beta : Float
A : Float64Vector an
amap : Layout (HTuple.prod is ks) (h(an))
B : Float64Vector bn
bmap : Layout (HTuple.prod ks js) (h(bn))
C✝² : Float64Vector cn
cmap : Layout (HTuple.prod is js) (h(cn))
_hcmap : FinHTupleMap.Injective cmap
C✝¹ : Float64Vector cn := C✝²
i : Shape ri
__h✝¹ : i ∈ 0...is
C✝ : Float64Vector cn := __s✝²
j : Shape rj
__h✝ : j ∈ 0...js
C : Float64Vector cn := __s✝¹
acc✝ : Float := 0
__s✝ : Float
acc : Float := __s✝
⊢ ↑(↑cmap sorry) < cn
---
error: (kernel) declaration has metavariables 'NumLean.Tests.Float64TensorAlgebraFailures.tensorGemmBadC'
-/
#guard_msgs in
def tensorGemmBadC {an bn cn : Nat} {ri rj rk : Rank}
    {is : Shape ri} {js : Shape rj} {ks : Shape rk}
    (alpha beta : Float)
    (A : Float64Vector an) (amap : Layout (.prod is ks) h(an))
    (B : Float64Vector bn) (bmap : Layout (.prod ks js) h(bn))
    (C : Float64Vector cn) (cmap : Layout (.prod is js) h(cn))
    (_hcmap : cmap.Injective) : Float64Vector cn := Id.run do
  let mut C := C
  for_all i in 0...is do
    for_all j in 0...js do
      let mut acc := 0
      for_all k in 0...ks do
        acc := acc + A[amap (i.prod k)] * B[bmap (k.prod j)]
      C[cmap (j.prod j)] := alpha * acc + beta * C[cmap (i.prod j)]
  return C

end NumLean.Tests.Float64TensorAlgebraFailures
