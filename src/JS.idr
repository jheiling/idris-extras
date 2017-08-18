module JS

%default total
%access export



%inline
JsTy : Type -> Type
JsTy = FTy FFI_JS []

%inline
js : (fname : String) -> (ty : Type) -> {auto fty : JsTy ty} -> ty
js fname ty = foreign FFI_JS fname ty

object : JS_IO Ptr
object = js "{}" (JS_IO Ptr)
