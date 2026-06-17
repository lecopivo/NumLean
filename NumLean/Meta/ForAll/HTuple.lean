import NumLean.Data.HTuple.RangeIterator
import NumLean.Meta.ForAll.Basic

public section

namespace NumLean
namespace Meta.ForAll

@[always_inline, inline] instance {α : Type u} [LE α] [LT α] [DecidableLT α]
    [Std.PRange.UpwardEnumerable α] [Std.PRange.LawfulUpwardEnumerable α]
    [Std.PRange.LawfulUpwardEnumerableLE α] [Std.PRange.LawfulUpwardEnumerableLT α]
    [Std.Rxo.IsAlwaysFinite α]
    [Std.Iterators.Finite (Std.Rxo.Iterator α) Id] {p : HTuple.Profile}
    [HTuple.Range.FoldProfile p]
    {β : Type v} :
    ForAllIn' (Std.Rco (HTuple α p)) (HTuple α p) β HTuple.Range.instMembershipRcoHTuple where
  forAllIn' xs init f :=
    HTuple.Range.foldRange xs init f

end Meta.ForAll
end NumLean
