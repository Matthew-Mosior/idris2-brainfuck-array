module Main

import Data.Array.Core
import Data.Array.Index
import Data.Array.Mutable
import Data.Bits as B
import Network.Socket as Skt
import System as Sys
import System.File as F
import System.File.Process as SFP
import Syntax.T1

data IncType =
    PositiveInc
  | NegativeInc
                
data MoveType =
    PositiveMove
  | NegativeMove

data Op =
    Inc IncType Nat
  | Move MoveType Nat
  | Print
  | Loop (List Op)

{-
data Tape : Nat -> Type where
  MkTape :  (tapedata : MArray n Nat)
         -> (tapepos  : Nat)
         -> Tape n
-}
record Tape (n : Nat) where
  constructor MkTape
  tapedata : MArray n Nat
  tapepos  : Nat
--  {auto 0 lt : LT tapepos n}
--  {auto 0 lte : LTE tapepos n}

data Printer : Type where
  MkPrinter :  (sum1 : Nat)
            -> (sum2 : Nat)
            -> (quiet : Bool)
            -> Printer

write :  Printer
      -> Nat
      -> IO Printer
write p@(MkPrinter sum1' sum2' quiet') n =
  case quiet' of
    True  =>
      let s1 = mod (sum1' `plus` n) 255
          s2 = mod (s1 `plus` sum2') 255
        in pure $
             MkPrinter s1 s2 True
    False => do
      putStr $ fastPack $ ((chr $ (the Int (cast n))) :: Nil)
      SFP.fflush stdout
      pure p

getChecksum :  Printer
            -> Nat
getChecksum (MkPrinter sum1' sum2' _) =
  integerToNat
    (((natToInteger sum2') `shiftL` 8) .|. (natToInteger sum1'))

parameters {n : Nat}
           (tape : Tape n)
           {0 rs : Resources}
           {auto 0 p : Res tape.tapedata rs}

  current :  {auto 0 _ : LT tape.tapepos n}
          -> F1 rs Nat
  current t =
    getNat tape.tapedata tape.tapepos t

  inc :  (delta : Nat)
      -> IncType
      -> {auto 0 _ : LT tape.tapepos n}
      -> F1' rs
  inc delta PositiveInc t =
    let prev # t := getNat tape.tapedata tape.tapepos t
      in setNat tape.tapedata tape.tapepos (prev `plus` delta) t
  inc delta NegativeInc t =
    let prev # t := getNat tape.tapedata tape.tapepos t
      in setNat tape.tapedata tape.tapepos (prev `minus` delta) t

  move :  (m : Nat)
       -> MoveType
       -> A1 [] (Tape n)
  move m PositiveMove =
    let tapepos' = tape.tapepos `plus` m
      in case tapepos' < n of
           True  =>
             pure $ MkTape tape.tapedata tapepos'
           False =>
             let tapedata' # t := mgrow1 tape.tapedata m 0
               in A (MkTape tapedata' tapepos') t
  move m NegativeMove =
    let tapepos' = tape.tapepos `minus` m
      in case tapepos' < n of
           True  =>
             pure $ MkTape tape.tapedata tapepos'
           False =>
             let tapedata' # t := mgrow1 tape.tapedata m 0
               in A (MkTape tapedata' tapepos') t

parse :  List Char
      -> List Op
parse cs =
  let (_, ops) = loop (cs, [])
    in ops
  where
    loop :  (List Char, List Op)
         -> (List Char, List Op)
    loop (Nil, acc)     = (Nil, reverse acc)
    loop (c :: cs, acc) = case c of
      '+' => loop (cs, (Inc PositiveInc 1) :: acc)
      '-' => loop (cs, (Inc NegativeInc 1) :: acc)
      '>' => loop (cs, (Move PositiveMove 1)  :: acc)
      '<' => loop (cs, (Move NegativeMove 1) :: acc)
      '.' => loop (cs, Print :: acc)
      '[' => let (cs', body) = loop (cs, []) in loop (cs', Loop body :: acc)
      ']' => (cs, reverse acc)
      _   => loop (cs, acc)

partial
run :  List Op
    -> Tape
    -> Printer
    -> IO (Tape, Printer)
run Nil         tape p =
  pure (tape, p)
run (op :: ops) tape p =
  case op of
    (Inc PositiveInc d)   =>
      run ops (inc d PositiveInc tape) p
    (Inc NegativeInc d)   =>
      run ops (inc d NegativeInc tape) p
    (Move PositiveMove m) =>
      run ops (move m PositiveMove tape) p
    (Move NegativeMove m) =>
      run ops (move m NegativeMove tape) p
    Print                 => do
      let x = current tape
      newp <- write p x
      run ops tape newp
    Loop body             => do
      case current tape of
        Z =>
          run ops tape p
        _ => do
          (tape', p') <- run body tape p
          run (op :: ops) tape' p'

verify : IO (Either String ())
verify = do
  let src      = "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++."
      ops      = parse $ fastUnpack src
      empty    = fill 1 0
      pempty   = MkPrinter Z Z True
  (_, pleft)   <- run ops
                      (MkTape empty Z)
                      pempty
  let left     = getChecksum pleft
  pright       <- foldlM (\p, c => write p $ the Nat (cast $ ord c))
                         pempty
                         (fastUnpack "Hello World!\n")
  let right    = getChecksum pright
  case left == right of
    True  =>
      pure $ Right ()
    False =>
      pure $ Left $ show left ++ " != " ++ show right

partial
notify : String -> IO ()
notify msg = do
  Right skt <- socket AF_INET Stream 0
    | Left err => die $ "Error in call to socket: " ++ show err
  _ <- connect skt (Hostname "localhost") 9001
  Right _ <- send skt msg
    | Left err => die $ "Error in call to send: " ++ show err
  close skt

partial
main : IO ()
main = do
  Right () <- verify
    | Left err => die err
  [_, fn]   <- getArgs
  Right src <- readFile fn
    | Left err => die $ "Error reading file: " ++ show err
  quiet     <- getEnv "QUIET"
  pid       <- getPID
  notify $ "Idris (Array)\t" ++ show pid
  case quiet of
    Just _  => do
      let ops   = parse $ fastUnpack src
      (_, newp) <- run ops (MkTape (fill 1 0) Z) (MkPrinter Z Z True)
      notify "stop"
      putStrLn $ "Output checksum: " ++ show (getChecksum newp)
    Nothing => do
      let ops   = parse $ fastUnpack src
      (_, newp) <- run ops (MkTape (fill 1 0) Z) (MkPrinter Z Z False)
      notify "stop"
