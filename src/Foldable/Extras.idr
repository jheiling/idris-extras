module Foldable.Extras

%default total
%access export



iter : Foldable t => Monad m => (a -> m ()) -> t a -> m ()
iter f = foldlM (\(), x => f x) ()
