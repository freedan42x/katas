module RemoveUrlAnchor where

removeUrlAnchor :: String -> String
removeUrlAnchor = takeWhile (/= '#')
