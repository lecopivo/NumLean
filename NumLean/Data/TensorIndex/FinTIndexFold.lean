import NumLean.Data.TensorIndex.FinTIndexIterator
import NumLean.Data.TensorIndex.IntFinTIndex

namespace NumLean

namespace TensorIndex

namespace FinTIndex

namespace RowMajorLoop

private class Folder (p : HRank) where
  fold {γ : Type u} (shape : Shape p)
    (emit : Nat → FinTIndex shape → γ → Nat × γ) : Nat → γ → Nat × γ

attribute [inline, specialize] Folder.fold

private class NatFolder (p : HRank) where
  fold {γ : Type u} (shape : Shape p)
    (emit : (counter : Nat) → (idx : TIndex Nat p) → TIndex.InBounds shape idx → γ → Nat × γ) :
      Nat → γ → Nat × γ

attribute [inline, specialize] NatFolder.fold

private class IntFolder (p : HRank) where
  fold {γ : Type u} (shape : Shape p)
    (emit : Nat → IntFinTIndex shape → γ → Nat × γ) : Nat → γ → Nat × γ

attribute [inline, specialize] IntFolder.fold

@[inline] private instance : Folder .leaf where
  fold {γ} shape emit counter acc :=
    match shape with
    | .leaf n =>
        let rec @[specialize] loop (i counter : Nat) (acc : γ) : Nat × γ :=
          if hi : i < n then
            let idx : FinTIndex (.leaf n) :=
              { val := .leaf i
                isLt := by simpa [TIndex.InBounds] using hi }
            let (counter', acc') := emit counter idx acc
            loop (i + 1) counter' acc'
          else
            (counter, acc)
        loop 0 counter acc

@[inline] private instance : NatFolder .leaf where
  fold {γ} shape emit counter acc :=
    match shape with
    | .leaf n =>
        let rec @[specialize] loop (i counter : Nat) (acc : γ) : Nat × γ :=
          if hi : i < n then
            let (counter', acc') := emit counter (.leaf i) hi acc
            loop (i + 1) counter' acc'
          else
            (counter, acc)
        loop 0 counter acc

@[inline] private instance : IntFolder .leaf where
  fold {γ} shape emit counter acc :=
    match shape with
    | .leaf n =>
        let rec @[specialize] loop (i counter : Nat) (acc : γ) : Nat × γ :=
          if hi : i < n then
            let idx : IntFinTIndex (.leaf n) :=
              { val := .leaf (i : Int)
                isLt := by
                  simp [TIndex.InBoundsInt]
                  omega }
            let (counter', acc') := emit counter idx acc
            loop (i + 1) counter' acc'
          else
            (counter, acc)
        loop 0 counter acc

@[inline] private instance {p q : HRank} [Folder p] [Folder q] : Folder (.prod p q) where
  fold {γ} shape emit counter acc :=
    match shape with
    | .prod shape₁ shape₂ =>
        let emitLeft (counter : Nat) (idx₁ : FinTIndex shape₁) (acc : γ) : Nat × γ :=
          Folder.fold (p := q) shape₂
            (fun counter idx₂ acc =>
              let idx : FinTIndex (.prod shape₁ shape₂) :=
                { val := .prod idx₁.val idx₂.val
                  isLt := ⟨idx₁.isLt, idx₂.isLt⟩ }
              emit counter idx acc)
            counter acc
        Folder.fold (p := p) shape₁ emitLeft counter acc

@[inline] private instance {p q : HRank} [NatFolder p] [NatFolder q] : NatFolder (.prod p q) where
  fold {γ} shape emit counter acc :=
    match shape with
    | .prod shape₁ shape₂ =>
        let emitLeft (counter : Nat) (idx₁ : TIndex Nat p) (hidx₁ : TIndex.InBounds shape₁ idx₁)
            (acc : γ) : Nat × γ :=
          NatFolder.fold (p := q) shape₂
            (fun counter idx₂ hidx₂ acc => emit counter (.prod idx₁ idx₂) ⟨hidx₁, hidx₂⟩ acc)
            counter acc
        NatFolder.fold (p := p) shape₁ emitLeft counter acc

@[inline] private instance {p q : HRank} [IntFolder p] [IntFolder q] : IntFolder (.prod p q) where
  fold {γ} shape emit counter acc :=
    match shape with
    | .prod shape₁ shape₂ =>
        let emitLeft (counter : Nat) (idx₁ : IntFinTIndex shape₁) (acc : γ) : Nat × γ :=
          IntFolder.fold (p := q) shape₂
            (fun counter idx₂ acc =>
              let idx : IntFinTIndex (.prod shape₁ shape₂) :=
                { val := .prod idx₁.val idx₂.val
                  isLt := ⟨idx₁.isLt, idx₂.isLt⟩ }
              emit counter idx acc)
            counter acc
        IntFolder.fold (p := p) shape₁ emitLeft counter acc

@[inline, specialize] private partial def foldShape {pOut : HRank} {shapeOut : Shape pOut}
    {m : Type u → Type v} [Monad m] {γ : Type u}
    (f : RowMajorItem shapeOut → γ → m γ) : {p : HRank} → (shape : Shape p) →
      (emit : Nat → FinTIndex shape → γ → m (Nat × γ)) → Nat → γ → m (Nat × γ)
  | .leaf, .leaf n, emit, counter, acc =>
      let rec @[specialize] loop (i counter : Nat) (acc : γ) : m (Nat × γ) := do
        if hi : i < n then
          let idx : FinTIndex (.leaf n) :=
            { val := .leaf i
              isLt := by simpa [TIndex.InBounds] using hi }
          let (counter', acc') ← emit counter idx acc
          loop (i + 1) counter' acc'
        else
          pure (counter, acc)
      loop 0 counter acc
  | .prod _ _, .prod shape₁ shape₂, emit, counter, acc =>
      let emitLeft (counter : Nat) (idx₁ : FinTIndex shape₁) (acc : γ) :
          m (Nat × γ) :=
        foldShape f shape₂
          (fun counter idx₂ acc =>
            let idx : FinTIndex (.prod shape₁ shape₂) :=
              { val := .prod idx₁.val idx₂.val
                isLt := ⟨idx₁.isLt, idx₂.isLt⟩ }
            emit counter idx acc)
          counter acc
      foldShape f shape₁ emitLeft counter acc

@[inline, specialize] private partial def foldShapeId {pOut : HRank} {shapeOut : Shape pOut}
    {γ : Type u} (f : RowMajorItem shapeOut → γ → γ) : {p : HRank} → (shape : Shape p) →
      (emit : Nat → FinTIndex shape → γ → Nat × γ) → Nat → γ → Nat × γ
  | .leaf, .leaf n, emit, counter, acc =>
      let rec @[specialize] loop (i counter : Nat) (acc : γ) : Nat × γ :=
        if hi : i < n then
          let idx : FinTIndex (.leaf n) :=
            { val := .leaf i
              isLt := by simpa [TIndex.InBounds] using hi }
          let (counter', acc') := emit counter idx acc
          loop (i + 1) counter' acc'
        else
          (counter, acc)
      loop 0 counter acc
  | .prod _ _, .prod shape₁ shape₂, emit, counter, acc =>
      let emitLeft (counter : Nat) (idx₁ : FinTIndex shape₁) (acc : γ) : Nat × γ :=
        foldShapeId f shape₂
          (fun counter idx₂ acc =>
            let idx : FinTIndex (.prod shape₁ shape₂) :=
              { val := .prod idx₁.val idx₂.val
                isLt := ⟨idx₁.isLt, idx₂.isLt⟩ }
            emit counter idx acc)
          counter acc
      foldShapeId f shape₁ emitLeft counter acc

/-- Standalone row-major fold over bounded tensor indices.

This bypasses the `Iterator`/`IteratorLoop` abstraction and directly runs the structural row-major
loop. It is intended as the low-overhead baseline for tensor loops that need both the flat and
structured index. -/
@[inline, specialize] def foldM {p : HRank} (shape : Shape p)
    {m : Type u → Type v} [Monad m] {γ : Type u} (init : γ)
    (f : RowMajorItem shape → γ → m γ) : m γ := do
  let (_, acc) ← foldShape f shape
    (fun counter idx acc => do
      have hcounter : counter < shape.size := by
        -- The structural traversal emits exactly `shape.size` items.
        sorry
      let item : RowMajorItem shape :=
        { linearIdx := ⟨counter, hcounter⟩
          idx := idx
          toFin_eq := by sorry }
      let acc' ← f item acc
      pure (counter + 1, acc'))
    0 init
  pure acc

/-- Pure `Id` specialization of `foldM`. -/
@[inline, specialize] def fold {p : HRank} (shape : Shape p) {γ : Type u} (init : γ)
    (f : RowMajorItem shape → γ → γ) : γ :=
  let (_, acc) := foldShapeId f shape
    (fun counter idx acc =>
      have hcounter : counter < shape.size := by
        -- The structural traversal emits exactly `shape.size` items.
        sorry
      let item : RowMajorItem shape :=
        { linearIdx := ⟨counter, hcounter⟩
          idx := idx
          toFin_eq := by sorry }
      (counter + 1, f item acc))
    0 init
  acc

/-- Lower-level pure row-major fold that passes the flat and structured indices separately.

This avoids allocating a `RowMajorItem` wrapper in the standalone loop path. -/
@[inline, specialize] def foldIdx {p : HRank} [Folder p] (shape : Shape p) {γ : Type u} (init : γ)
    (f : (linear : Fin shape.size) → FinTIndex shape → γ → γ) : γ :=
  let (_, acc) := Folder.fold (p := p) shape
    (fun counter idx acc =>
      have hcounter : counter < shape.size := by
        -- The structural traversal emits exactly `shape.size` items.
        sorry
      (counter + 1, f ⟨counter, hcounter⟩ idx acc))
    0 init
  acc

/-- Lower-level pure row-major fold that passes a flat natural offset and natural structured index.

This is useful for performance-sensitive code that wants structured coordinates but does not need the
proof-carrying `FinTIndex` wrapper or integer-coordinate representation. -/
@[inline, specialize] def foldNatIdx {p : HRank} [NatFolder p] (shape : Shape p)
    {γ : Type u} (init : γ)
    (f : (linear : Fin shape.size) → (idx : TIndex Nat p) → TIndex.InBounds shape idx → γ → γ) : γ :=
  let (_, acc) := NatFolder.fold (p := p) shape
    (fun counter idx hidx acc =>
      have hcounter : counter < shape.size := by
        -- The structural traversal emits exactly `shape.size` items.
        sorry
      (counter + 1, f ⟨counter, hcounter⟩ idx hidx acc)) 0 init
  acc

@[inline, specialize] private partial def foldIdxRecursiveShape {γ : Type u} :
      {p : HRank} → (shape : Shape p) →
      (emit : Nat → FinTIndex shape → γ → Nat × γ) → Nat → γ → Nat × γ
  | .leaf, .leaf n, emit, counter, acc =>
      let rec @[specialize] loop (i counter : Nat) (acc : γ) : Nat × γ :=
        if hi : i < n then
          let idx : FinTIndex (.leaf n) :=
            { val := .leaf i
              isLt := by simpa [TIndex.InBounds] using hi }
          let (counter', acc') := emit counter idx acc
          loop (i + 1) counter' acc'
        else
          (counter, acc)
      loop 0 counter acc
  | .prod _ _, .prod shape₁ shape₂, emit, counter, acc =>
      let emitLeft (counter : Nat) (idx₁ : FinTIndex shape₁) (acc : γ) : Nat × γ :=
        foldIdxRecursiveShape shape₂
          (fun counter idx₂ acc =>
            let idx : FinTIndex (.prod shape₁ shape₂) :=
              { val := .prod idx₁.val idx₂.val
                isLt := ⟨idx₁.isLt, idx₂.isLt⟩ }
            emit counter idx acc)
          counter acc
      foldIdxRecursiveShape shape₁ emitLeft counter acc

/-- Experimental non-typeclass standalone fold for comparing specialization strategies. -/
@[inline, specialize] def foldIdxRecursive {p : HRank} (shape : Shape p) {γ : Type u} (init : γ)
    (f : (linear : Fin shape.size) → FinTIndex shape → γ → γ) : γ :=
  let (_, acc) := foldIdxRecursiveShape shape
    (fun counter idx acc =>
      have hcounter : counter < shape.size := by
        -- The structural traversal emits exactly `shape.size` items.
        sorry
      (counter + 1, f ⟨counter, hcounter⟩ idx acc))
    0 init
  acc

@[inline, specialize] private partial def foldNatIdxRecursiveShape {γ : Type u} :
      {p : HRank} → (shape : Shape p) →
      (emit : (counter : Nat) → (idx : TIndex Nat p) → TIndex.InBounds shape idx → γ → Nat × γ) →
      Nat → γ → Nat × γ
  | .leaf, .leaf n, emit, counter, acc =>
      let rec @[specialize] loop (i counter : Nat) (acc : γ) : Nat × γ :=
        if hi : i < n then
          let (counter', acc') := emit counter (.leaf i) hi acc
          loop (i + 1) counter' acc'
        else
          (counter, acc)
      loop 0 counter acc
  | .prod _ _, .prod shape₁ shape₂, emit, counter, acc =>
      let emitLeft (counter : Nat) (idx₁ : TIndex Nat _) (hidx₁ : TIndex.InBounds shape₁ idx₁)
          (acc : γ) : Nat × γ :=
        foldNatIdxRecursiveShape shape₂
          (fun counter idx₂ hidx₂ acc => emit counter (.prod idx₁ idx₂) ⟨hidx₁, hidx₂⟩ acc)
          counter acc
      foldNatIdxRecursiveShape shape₁ emitLeft counter acc

/-- Experimental non-typeclass raw Nat-coordinate fold for comparing specialization strategies. -/
@[inline, specialize] def foldNatIdxRecursive {p : HRank} (shape : Shape p)
    {γ : Type u} (init : γ)
    (f : (linear : Fin shape.size) → (idx : TIndex Nat p) → TIndex.InBounds shape idx → γ → γ) : γ :=
  let (_, acc) := foldNatIdxRecursiveShape shape
    (fun counter idx hidx acc =>
      have hcounter : counter < shape.size := by
        -- The structural traversal emits exactly `shape.size` items.
        sorry
      (counter + 1, f ⟨counter, hcounter⟩ idx hidx acc)) 0 init
  acc

/-- Lower-level pure row-major fold that passes the old integer-coordinate bounded tensor index. -/
@[inline, specialize] def foldIntFinIdx {p : HRank} [IntFolder p] (shape : Shape p)
    {γ : Type u} (init : γ)
    (f : (linear : Fin shape.size) → IntFinTIndex shape → γ → γ) : γ :=
  let (_, acc) := IntFolder.fold (p := p) shape
    (fun counter idx acc =>
      have hcounter : counter < shape.size := by
        -- The structural traversal emits exactly `shape.size` items.
        sorry
      (counter + 1, f ⟨counter, hcounter⟩ idx acc)) 0 init
  acc

end RowMajorLoop

end FinTIndex
end TensorIndex
end NumLean
