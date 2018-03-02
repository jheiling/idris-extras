module JS.DOM.Document

import JS
import JS.DOM
import Control.Monad.Extras

%default total
%access export



utGetElement : (id : String) -> JS_IO Ptr
utGetElement = js "document.getElementById(%0)" (String -> JS_IO Ptr)



getElement : (id : String) -> JS_IO Element
getElement = utGetElement >=> (pure . MkElement)

write : String -> JS_IO ()
write = js "document.write(%0)" (String -> JS_IO ())
