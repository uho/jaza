module MyDebug
where
import Debug.Trace

debug msg list value = value
--debug msg list value = trace ("\n" ++ msg ++ "<<" ++ dumpList list ++ ">>\n") value

debug2 msg list value = value
--debug2 msg list value = trace ("\n" ++ msg ++ "<<<" ++ dumpList list ++ ">>>\n") value

dumpList [] = "\n"
dumpList es = concat ["\t" ++ show e ++ "\n" | e <- es]
