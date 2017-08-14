module Either.Extras

%default total
%access export



toEither : (input : Bool) -> (left : Lazy l) -> (right : Lazy r) -> Either l r
toEither False left _ = Left left
toEither True _ right = Right right

|||Maps func over l if input is Left l.
mapLeft : (func : Lazy (l -> l')) -> (input : Either l r) -> Either l' r
mapLeft func (Left l) = Left $ func l
mapLeft _ (Right r) = Right r

|||Maps either funcl or funcr over input.
mapEither : (funcl : Lazy (l -> l')) -> (funcr : Lazy (r -> r')) -> (input : Either l r) -> Either l' r'
mapEither funcl _ (Left l) = Left $ funcl l
mapEither _ funcr (Right r) = Right $ funcr r
