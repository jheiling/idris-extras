module Control.Monad.Extras

%default total
%access export



infixl 5 >=>

(>=>) : Monad m => (a -> m b) -> (b -> m c) -> a -> m c
(>=>) f g x = f x >>= g
