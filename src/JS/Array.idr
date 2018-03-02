module JS.Array

import Control.Monad.Syntax

import JS
import Data.Foldable.Extras

%default total
%access public export



data Array = MkArray Ptr

Cast Array Ptr where
    cast (MkArray ptr) = ptr



utEmpty : JS_IO Ptr
utEmpty = js "[]" (JS_IO Ptr)

jsAppend : (ty : Type) -> {auto fty : FTy FFI_JS [] ty} -> ty
jsAppend ty = js "%1.push(%0)" ty

utAppendString : (value : String) -> (array : Ptr) -> JS_IO ()
utAppendString = jsAppend (String -> Ptr -> JS_IO ())

utAppendPtr : (value : Ptr) -> (array : Ptr) -> JS_IO ()
utAppendPtr = jsAppend (Ptr -> Ptr -> JS_IO ())

utFromPtrFoldable : Foldable f => f Ptr -> JS_IO Ptr
utFromPtrFoldable xs = do arr <- utEmpty
                          iter (flip utAppendPtr arr) xs
                          pure arr



fromUt : JS_IO Ptr -> JS_IO Array
fromUt arr = pure $ MkArray !arr

empty : JS_IO Array
empty = fromUt utEmpty

appendString : (value : String) -> (array : Array) -> JS_IO ()
appendString value = utAppendString value . cast

appendPtr : (value : Ptr) -> (array : Array) -> JS_IO ()
appendPtr value = utAppendPtr value . cast

fromPtrFoldable : Foldable f => f Ptr -> JS_IO Array
fromPtrFoldable = utFromPtrFoldable >=> (pure . MkArray)
