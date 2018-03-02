module JS.Node.Module

import JS

%default total
%access export



dir : JS_IO String
dir = js "__dirname" (JS_IO String)

path : JS_IO String
path = js "__filename" (JS_IO String)
