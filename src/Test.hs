
main :: IO ()
main =
    do  s <- getLineEdit "Test> "
	putStrLn s
	if s==""
	    then return ()
	    else main

getLineEdit :: String -> IO String
getLineEdit prompt =
    do  putStr prompt
	getLine