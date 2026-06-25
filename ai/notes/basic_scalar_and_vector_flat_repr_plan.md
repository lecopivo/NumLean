# Basic Scalar + Vector Flat-Repr Plan

    The goal is to provide relavent implementations of interfaces for basic types like Float32, Float, Complex32, Complex64, UInt8
    
    All the code should live in NumLean/Data/Scalars/ The target directory structure is following for Float and analogous for other types:
    
    Float/Basic.lean - what ever is missing for the basic defitions. Define Complex* as two field structure (re im : Float*) 
         /FloatVector.lean - size annotated FloatArray. For Complex* do not define Complex*Array, just define Complex*Vector directly and store its data in Float*Array with condition that data.size = 2*n. For UInt8 wrap ByteArray into size annotated structure and call it ByteVector.
         /Algebra.lean - provide an instance of the strongest class that makes sense - ROps for Float*, RCOps for Complex*, and Semiring for UInt8
         /VectorType.lean - show that FloatVector is a `VectoryType FloatVector Float`
         /HasFlatRepr.lean - show that `HasDefaultFlatRepr Float FloatVector 1` and `HasFlatRepr Float ByteVector 8`, For Complex* do `HasDefaultFlatRepr Complex32 Complex32Vector 1`, `HasFlatRepr Float32 Complex32Vector 2` , `HasFlatRepr Float32 ByteVector 8` similar for the 64-bit version Float. For UInt8 do only `HasDefaultflatrepr UInt8 ByteVector 1`
         
