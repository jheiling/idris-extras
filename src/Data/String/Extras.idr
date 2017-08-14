module Data.String.Extras

import Data.Vect

%default total
%access export



unsplit : String -> List String -> String
unsplit s [] = ""
unsplit s (x :: []) = x
unsplit s (x :: xs) = x ++ s ++ unsplit s xs
