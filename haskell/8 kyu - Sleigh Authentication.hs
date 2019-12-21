module SleighAuthentication where

authenticate :: String -> String -> Bool
authenticate a b = "Santa ClausHo Ho Ho!" == (++) a b
