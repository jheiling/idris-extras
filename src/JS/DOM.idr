module JS.DOM

%default total
%access public export



data Element = MkElement Ptr

Cast Element Ptr where
    cast (MkElement ptr) = ptr
