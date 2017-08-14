module Data.Vect.Extras

import Data.Vect
import Data.Vect.Views

%default total
%access export



foldrM :  Monad m => (func: elem -> acc -> m acc) -> (init : acc) -> (input : Vect n elem) -> m acc
foldrM func init input with (snocVect input)
  foldrM _ init [] | Empty = pure init
  foldrM func init (xs ++ [x]) | Snoc rec = do res <- func x init
                                               foldrM func res xs | rec

mapM : Monad m => (func : elem -> m r) -> (input : Vect n elem) -> m (Vect n r)
mapM = helper []
where helper :  Monad m => Vect n r -> (elem -> m r) ->  Vect n' elem -> m (Vect (n + n') r)
      helper {n} acc func [] = rewrite plusZeroRightNeutral n in pure acc
      helper {n} {n' = S k} acc func (x :: xs) = rewrite sym $ plusSuccRightSucc n k in
                                                 do res <- func x
                                                    helper (res :: acc) func xs
