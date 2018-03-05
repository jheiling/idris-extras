module Js.Object

import Control.Monad.Syntax
import Js

%default total
%access export



public export
data Object = MkObject Ptr

public export
interface Member a where
    get : (member : String) -> (object : Object) -> JS_IO a
    set : (member : String) -> (value : a) -> (object : Object) -> JS_IO ()



Cast Object Ptr where
    cast (MkObject ptr) = ptr

Cast (JS_IO Ptr) (JS_IO Object) where
    cast o = pure $ MkObject !o

Member Nat where
    get member = js "%1[%0]" (String -> Ptr -> JS_IO Int) member . cast >=> pure . cast
    set member value = js "%2[%0] = %1" (String -> Int -> Ptr -> JS_IO ()) member (cast value) . cast

Member Int where
    get member = js "%1[%0]" (String -> Ptr -> JS_IO Int) member . cast
    set member value = js "%2[%0] = %1" (String -> Int -> Ptr -> JS_IO ()) member value . cast

Member Double where
    get member = js "%1[%0]" (String -> Ptr -> JS_IO Double) member . cast
    set member value = js "%2[%0] = %1" (String -> Double -> Ptr -> JS_IO ()) member value . cast

Member String where
    get member = js "%1[%0]" (String -> Ptr -> JS_IO String) member . cast
    set member value = js "%2[%0] = %1" (String -> String -> Ptr -> JS_IO ()) member value . cast



%inline
empty : JS_IO Object
empty = cast $ js "{}" (JS_IO Ptr)

%inline
setBool : (member : String) -> (value : Bool) -> (object : Object) -> JS_IO ()
setBool member False = js "%1[%0] = false" (String -> Ptr -> JS_IO ()) member . cast
setBool member True = js "%1[%0] = true" (String -> Ptr -> JS_IO ()) member . cast
