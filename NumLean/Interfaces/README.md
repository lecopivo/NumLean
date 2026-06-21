# Namind convention


  - `XOps A` means that type `A` provides same operations as `X`
  - `XArrayOps As` means that `As` provides array bulk `X` operations
  - `XTensorOps As` means that `As` provides tensor bulk `X` operations
    - if there operations are purely algorithimical, like copying data around then they are usually required to be lawful
    - if the operations are mathematical like addition then then are not required to be lawful and a separate class is usually created
  - `LawfulXOps A` means that `X` like-operations on `A` behaves as expected
