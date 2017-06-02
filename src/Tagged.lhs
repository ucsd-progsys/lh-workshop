\begin{code}
module Tagged where 

import Prelude hiding (print)

data User = Chair | Alice | Bob | Default
   deriving (Show, Eq)

-- | Value tagged with a policy  

{-@ data Tagged a <p :: User -> Bool> = Tagged (content :: a) @-}
data Tagged a = Tagged a

{-@ data variance Tagged  covariant contravariant @-}

instance Functor Tagged where
  fmap f (Tagged x) = Tagged (f x)

instance Applicative Tagged where
  pure  = Tagged
  -- f (a -> b) -> f a -> f b 
  (Tagged f) <*> (Tagged x) = Tagged (f x)

instance Monad Tagged where
  return x = Tagged x
  (Tagged x) >>= f = f x 
  (Tagged _) >>  t = t  
  fail          = error

{-@ instance Monad Tagged where 
     >>= :: forall <p :: User -> Bool, f:: a -> b -> Bool>. 
            x:Tagged <p> a
         -> (u:a -> Tagged <p> (b <f u>))
         -> Tagged <p> (b<f (content x)>); 
     >>  :: x:Tagged a
         -> Tagged b
         -> Tagged b;
     return :: forall <p :: User -> Bool>. a -> Tagged <p> a 
  @-}

{-@ liftM :: forall a b <p :: User -> Bool, f:: a -> b -> Bool>.
                x: Tagged <p> a
                -> (u:a -> b<f u>)
                -> Tagged <p> (b<f (content x)>)
@-}
liftM :: Tagged a -> (a -> b) -> Tagged b
liftM x f =  x >>= (\x' -> return (f x'))

--{-@ lift :: forall a b <p :: User -> Bool, f:: a -> b -> Bool>.
--                (u:a -> b<f u>)
--                -> x: Tagged <p> a
--                -> Tagged <p> (b<f (content x)>)
-- @-}
--lift :: (a -> b) -> Tagged a -> Tagged b
--lift f x = bind x (\x' -> ret (f x'))

--liftM2 :: (a -> b -> c) -> Tagged a -> Tagged b -> Tagged c
--liftM2 f x y = bind x (\x' -> bind y (\y' -> ret (f x' y')))  

data PaperId
data World

{- Sensitive data and policies -}
   
-- | Current session user
{-@ measure sessionUser :: World -> User @-}
sessionUser = Alice
{-@ assume getSessionUser :: w:World -> {u:User | u == sessionUser w} @-}
getSessionUser :: World -> User
getSessionUser w = Alice

-- | PC chair (public)
{-@ measure chair :: World -> User @-}
chair = Chair

{-@ assume getChair :: Tagged {v:User | v == Chair} @-}
getChair :: Tagged User
getChair = Tagged Chair

-- | Paper title (public)
getTitle :: PaperId -> Tagged String
getTitle pid = Tagged "Waow" -- hack for now

-- | Paper authors (visible only to the chair)
{-@ getAuthors ::  pid : PaperId -> Tagged <{\u -> u == Chair}> [User]  @-}
getAuthors :: PaperId -> Tagged [User]
getAuthors pid = Tagged [Alice, Bob] -- hack for now
defaultPaperAuthors = [Default]

print :: Tagged User -> Tagged String -> IO ()
{-@ print :: forall <p :: User -> Bool>. 
             viewer:Tagged <p> (User<p>) 
          -> msg:Tagged <p> String 
          -> IO () @-}
print = undefined


-- This is a bad type because p is at the same time co- anc contra- variant
-- so putting it on the result type creates inconsistencies.
{- getCurrentUser :: forall <p :: User -> Bool>.
                      w:World -> Tagged <p> (User<p>) @-}

{-@ measure currentUser :: World -> User @-}
{- getCurrentUser :: w:World -> Tagged {v:User | v == currentUser w }@-}                      
getCurrentUser :: Tagged User 
getCurrentUser = undefined 


{-@ whenUserIsChair ::forall <p :: User -> Bool>.  Tagged <{\v -> v == Chair}>[a] -> Tagged <p> [a] @-}
whenUserIsChair :: Tagged [a] -> Tagged [a]
whenUserIsChair t = do 
  u <- getCurrentUser 
  if u == Chair then t else return [] 
\end{code}
