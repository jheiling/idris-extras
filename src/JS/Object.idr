module JS.Object

import JS

%default total
%access public export



data Object = MkObject Ptr

Cast Object Ptr where
    cast (MkObject ptr) = ptr



utEmpty : JS_IO Ptr
utEmpty = js "{}" (JS_IO Ptr)



fromUt : JS_IO Ptr -> JS_IO Object
fromUt obj = pure $ MkObject !obj

empty : JS_IO Object
empty = fromUt utEmpty
