module JS.Object

import JS

%default total
%access export



public export
data Object = MkObject Ptr



public export
Cast Object Ptr where
    cast (MkObject ptr) = ptr

public export
Cast (JS_IO Ptr) (JS_IO Object) where
    cast o = pure $ MkObject !o



%inline
empty : JS_IO Object
empty = cast $ js "{}" (JS_IO Ptr)

%inline
setString : (member : String) -> (value : String) -> (object : Object) -> JS_IO ()
setString member value = js "%2[%0] = %1" (String -> String -> Ptr -> JS_IO ()) member value . cast

%inline
setInt : (member : String) -> (value : Int) -> (object : Object) -> JS_IO ()
setInt member value = js "%2[%0] = %1" (String -> Int -> Ptr -> JS_IO ()) member value . cast

%inline
setNat : (member : String) -> (value : Nat) -> (object : Object) -> JS_IO ()
setNat member value = setInt member $ cast value

%inline
setDouble : (member : String) -> (value : Double) -> (object : Object) -> JS_IO ()
setDouble member value = js "%2[%0] = %1" (String -> Double -> Ptr -> JS_IO ()) member value . cast

%inline
setBool : (member : String) -> (value : Bool) -> (object : Object) -> JS_IO ()
setBool member False = js "%1[%0] = false" (String -> Ptr -> JS_IO ()) member . cast
setBool member True = js "%1[%0] = true" (String -> Ptr -> JS_IO ()) member . cast
