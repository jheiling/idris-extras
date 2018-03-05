module Js.DOM

%default total



public export
data Element = MkElement Ptr

export
Cast Element Ptr where
    cast (MkElement ptr) = ptr
