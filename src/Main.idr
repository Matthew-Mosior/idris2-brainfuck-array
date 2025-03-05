module Main

import Data.String
import Data.Array.Core as Array
import Data.Array.Index
import Data.Array.Mutable
import Data.Bits as B
import Data.Linear.Ref1
import Data.Linear.Traverse1
import Network.Socket as Skt
import System as Sys
import System.File as F
import System.File.Process as SFP

%foreign "scheme:(lambda (a x) (vector-ref a x))"
prim__arrget : AnyPtr -> Integer -> AnyPtr

%foreign "scheme:(lambda (a x v) (vector-set! a x v))"
prim__arrset : AnyPtr -> Integer -> AnyPtr -> PrimIO ()
                
%inline
arrget : MArray s n a -> Integer -> F1 s a
arrget arr n t = believe_me (prim__arrget (believe_me arr) n) # t

%inline
arrset : MArray s n a -> Integer -> a -> F1 s ()
arrset arr n v = ffi (prim__arrset (believe_me arr) n (believe_me v))

%inline
arrmod : MArray s n a -> Integer -> (a -> a) -> F1 s ()
arrmod arr n f t =
  let v # t := arrget arr n t
   in arrset arr n (f v) t

data Op =
    Inc
  | Dec
  | MovL
  | MovR
  | Print
  | Loop (List Op)

parse : List Char -> List Op
parse cs =
  let (_, ops) = go [<] cs
    in ops
  where
    go :  SnocList Op -> List Char -> (List Char, List Op)
    go acc  []       = ([], acc <>> [])
    go acc (c :: cs) =
      case c of
        '+' => go (acc :< Inc) cs
        '-' => go (acc :< Dec) cs
        '>' => go (acc :< MovR) cs
        '<' => go (acc :< MovL) cs
        '.' => go (acc :< Print) cs
        '[' => let (cs', body) = go [<] cs
                 in go (acc :< Loop body) cs'
        ']' => (cs, acc <>> [])
        _   => go acc cs

record Printer where
  constructor P
  sum1  : IORef Integer
  sum2  : IORef Integer
  quiet : Bool

printer : Bool -> F1 World Printer
printer q t =
  let s1 # t := ref1 0 t
      s2 # t := ref1 0 t
   in P s1 s2 q # t

write : Printer -> Integer -> F1' World
write (P sm1 sm2 q) n t =
  case q of
    True  =>
      let sum1 # t := read1 sm1 t
          sum2 # t := read1 sm2 t
          s1       := mod (sum1 + n) 255
          s2       := mod (s1 + sum2) 255
          _ # t    := write1 sm1 s1 t
        in write1 sm2 s2 t
    False =>
      let _ # t := ioToF1 (putStr $ singleton (cast n)) t
        in ioToF1 (SFP.fflush stdout) t

getChecksum : Printer -> F1 World Integer
getChecksum (P s1 s2 _) t =
  let sum1' # t := read1 s1 t
      sum2' # t := read1 s2 t
    in ((sum2' `shiftL` 8) .|. sum1') # t

record Tape where
  constructor T
  {size : Nat}
  arr   : IOArray size Integer
  pos   : Integer

%inline
predFin : Fin n -> Fin n
predFin FZ     = FZ
predFin (FS k) = weaken k

incPos : Fin n -> Fin (n+n)
incPos n = believe_me (FS n)

parameters (p : Printer)

  covering
  runBF : {n : _} -> List Op -> Integer -> IOArray n Integer -> F1 World Tape
  runBF []             pos arr t = T arr pos # t
  runBF os@(op :: ops) pos arr t =
    case op of
      Inc  => let _ # t := arrmod arr pos (+1) t
                in runBF ops pos arr t
      Dec  => let _ # t := arrmod arr pos (\x => x-1) t
                in runBF ops pos arr t
      MovL => runBF ops (pos - 1) arr t
      MovR =>
        let p2 := pos+1
          in case prim__lt_Integer p2 (cast n) of
               0 => let arr2 # t := mgrow arr n 0 t
                      in runBF ops p2 arr2 t
               _ => runBF ops p2 arr t
      Print     =>
        let x # t := arrget arr pos t
            _ # t := write p x t
          in runBF ops pos arr t
      Loop body =>
        let v # t := arrget arr pos t
          in case v of
               0 => runBF ops pos arr t
               _ => let T arr2 pos2 # t := runBF body pos arr t
                      in runBF os pos2 arr2 t

src : String
src =  "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++."

verify : F1 World (Either String ())
verify t =
  let p1    # t := printer True t
      p2    # t := printer True t
      arr   # t := marray1 1 0 t
      _     # t := runBF p1 (parse $ unpack src) 0 arr t
      left  # t := getChecksum p1 t
      _     # t := traverse1_ (\c => write p2 $ (cast $ ord c)) (fastUnpack "Hello World!\n") t
      right # t := getChecksum p2 t
    in case left == right of
         True  => Right () # t
         False => Left (show left ++ " != " ++ show right) # t

partial
notify : String -> IO ()
notify msg = do
  Right skt <- socket AF_INET Stream 0
    | Left err => die $ "Error in call to socket: " ++ show err
  _ <- connect skt (Hostname "localhost") 9001
  Right _ <- send skt msg
    | Left err => die $ "Error in call to send: " ++ show err
  close skt

covering
main1 : F1' World
main1 t =
  let Right ()  # t := verify t | Left err # t => ioToF1 (die err) t
      [_, fn]   # t := ioToF1 getArgs t | as # t => ioToF1 (die "invalid args: \{show as}") t
      Right src # t := ioToF1 (readFile fn) t
        | Left err # t => ioToF1 (die $ "Error reading file: " ++ show err) t
      ops           :=  parse $ fastUnpack src 
      quiet     # t := ioToF1 (getEnv "QUIET") t
      pid       # t := ioToF1 getPID t
      ops           := parse $ unpack src
      _         # t := ioToF1 (notify $ "Idris (Array)\t" ++ show pid) t
    in case quiet of
         Just _  =>
           let p1    # t := printer True t
               arr   # t := marray1 1 0 t
               _     # t := runBF p1 ops 0 arr t
               check # t := getChecksum p1 t
               _     # t := ioToF1 (notify "stop") t
             in ioToF1 (putStrLn $ "Output checksum: " ++ show check) t
         Nothing =>
           let p1  # t := printer False t
               arr # t := marray1 1 0 t
               _   # t := runBF p1 ops 0 arr  t
             in ioToF1 (notify "stop") t

covering
main : IO ()
main = runIO main1
