module Export17(Hello(Empt), Listt2(Empt)) where

f :: Int
f = 4

(/**) :: a -> Int -> Int
_ /** z = 2 * g * z -- 12 * z
  where
    g = 3 * k -- 6
      where
        k = 3

infixr 6 /**

data Listt a = a :> a | Empt

data Listt2 a = a :>< a | Empty

data Listt3 a = a :>>< a | Emptyy

type Hello = Int