module JS.DOM.Document

import Control.Monad.Syntax
import JS
import JS.DOM

%default total
%access export



getElement : (id : String) -> JS_IO Element
getElement = js "document.getElementById(%0)" (String -> JS_IO Ptr) >=> pure . MkElement

write : String -> JS_IO ()
write = js "document.write(%0)" (String -> JS_IO ())
