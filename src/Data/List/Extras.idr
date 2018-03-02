module Data.List.Extras

import Data.List.Views

%default total
%access export



foldrM :  Monad m => (func : elem -> acc -> m acc) -> (init : acc) -> (input : List elem) -> m acc
foldrM func init input with (snocList input)
    foldrM _ init [] | Empty = pure init
    foldrM func init (xs ++ [x]) | Snoc rec = foldrM func !(func x init) xs | rec

mapM : Monad m => (func : elem -> m r) -> (input : List elem) -> m (List r)
mapM func = foldrM (\x, acc => liftA (:: acc) (func x)) []
