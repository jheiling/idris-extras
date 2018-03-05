module Js.Array

import Control.Monad.Syntax

import Js
import Data.Foldable.Extras

%default total
%access public export



data Array = MkArray Ptr

Cast Array Ptr where
    cast (MkArray ptr) = ptr



%inline
empty : JS_IO Array
empty = pure $ MkArray !(js "[]" (JS_IO Ptr))

%inline
jsAppend : (ty : Type) -> {auto fty : FTy FFI_JS [] ty} -> ty
jsAppend ty = js "%1.push(%0)" ty

%inline
appendString : (value : String) -> (array : Array) -> JS_IO ()
appendString value = jsAppend (String -> Ptr -> JS_IO ()) value . cast

%inline
appendPtr : (value : Ptr) -> (array : Array) -> JS_IO ()
appendPtr value = jsAppend (Ptr -> Ptr -> JS_IO ()) value . cast

%inline
fromPtrFoldable : Foldable f => f Ptr -> JS_IO Array
fromPtrFoldable xs = do array <- empty
                        iter (flip appendPtr array) xs
                        pure array
