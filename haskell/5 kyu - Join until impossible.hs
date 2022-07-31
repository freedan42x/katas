{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, UndecidableInstances, GADTs #-}
module Join (jojo) where


class Jotaro a b where
  jojo :: Maybe a -> Maybe b

instance {-# OVERLAPS #-} (a ~ b) => Jotaro a b where
  jojo = id

instance Jotaro a b => Jotaro (Maybe a) b where
  jojo (Just x) = jojo x
  jojo _        = Nothing
