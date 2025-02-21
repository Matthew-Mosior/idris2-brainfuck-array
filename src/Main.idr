module Main

import Data.Array.Core as Array
import Data.Array.Index
import Data.Array.Mutable
import Data.Bits as B
import Data.Linear.Ref1
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
{-
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
    let prev # t := current t
      in setNat tape.tapedata tape.tapepos (prev `plus` delta) t
  inc delta NegativeInc t =
    let prev # t := current t
      in setNat tape.tapedata tape.tapepos (prev `minus` delta) t

  move :  (m : Nat)
       -> MoveType
--       -> Either (Tape n) (A1 [] (Tape n))
--       -> (1 t : T1 [tape.tapedata])
--       -> F1 rs (Tape n)
       -> F1 rs (Either (Tape n) (Tape (m + n)))
  move m PositiveMove t =
    let tapepos' = tape.tapepos `plus` m
      in case tapepos' < n of
           True  =>
             let tapedata' # t := mgrow tape.tapedata m 0 t
               in T1.pure $ Right $ MkTape tapedata' tapepos' t
             --Left $ MkTape tape.tapedata tapepos' t
             --Left $ MkTape tape.tapedata tapepos' # t
             --let tape' # t := MkTape tape.tapedata tapepos' t
             --  in Left $ tape' # t
             --Left $ MkTape tape.tapedata tapepos' t
           False =>
             let tapedata' # t := mgrow1 tape.tapedata m 0 t
               in Right $ MkTape tapedata' tapepos' t
  move m NegativeMove t =
    let tapepos' = tape.tapepos `minus` m
      in case tapepos' < n of
           True  =>
             Left $ pure $ MkTape tape.tapedata tapepos'
           False =>
             let tapedata' # t := mgrow1 tape.tapedata m 0 t
               in Right $ MkTape tapedata' tapepos' # t
-}

record Tape where
  constructor T
  {size : Nat}
  arr   : MArray size Nat
  pos   : Fin size

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

0 finMinusLT : (x : Fin n) -> (m : Nat) -> LT (finToNat x `minus` m) n
finMinusLT FZ     m = %search
finMinusLT (FS x) m = ?finMinusLT_rhs_1

--0 finPlusLT : (x : Fin v) -> (m : Nat) -> LT (finToNat x `plus` m) n
--finPlusLT FZ     m = %search
--finPlusLT (FS x) m = %search -- ?finPlusLT_rhs_1

%inline
current : (tp : Tape) -> F1 [tp.arr] Nat
current tp = get tp.arr tp.pos

inc : (delta : Nat) -> IncType -> (tp : Tape) -> F1' [tp.arr]
inc delta PositiveInc tp = modify tp.arr tp.pos (+ delta)
inc delta NegativeInc tp = modify tp.arr tp.pos (`minus` delta)

minus : Fin n -> Nat -> Fin n
minus x m = natToFinLT (finToNat x `minus` m) @{finMinusLT _ _}

plus : {n : _} -> Fin n -> (m : Nat) -> Either (Fin n) (Fin (m+n))
plus x m =
  case tryNatToFin (finToNat x + m) of
    Just y  => Left y
    Nothing => Right $ natToFinLT (finToNat x + m) @{?bar}-- @{finPlusLT _ _}

move :  (m : Nat)
     -> MoveType
     -> (tp : Tape)
     -> (1 t : T1 [tp.arr])
     -> Res1 Tape (\x => [x.arr])
move m NegativeMove (T arr pos) t = T arr (pos `minus` m) # t
move m PositiveMove (T arr pos) t =
  case plus pos m of
    Left  p2 => T arr p2 # t
    Right p2 =>
      let arr2 # t := mgrow1 arr m 0 t
        in T arr2 p2 # t

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
run' :  List Op
     -> (tp : Tape)
     -> (p : Printer)
--    -> F1 [IO Tape] (Tape, Printer)
     -> (1 t : T1 [tp.arr])
     -> Res1 (Tape, Printer) (\x => [x.arr]) --(Tape, Printer)
--     -> IO (Tape, Printer)
--     -> (1 t' : T1 [p])
--     -> Res1 (Tape, Printer) (\x => [])
--     -> F1 [] (Tape, Printer)
--    -> IO (Tape, Printer)
--    -> (1 t : T1 [tp.arr])
--    -> Res1 Tape (\x => [x.arr])
run' Nil         tp p t =
  (tp, p) # t
run' (op :: ops) tp p t =
  case op of
    (Inc PositiveInc d)   =>
      let _ # t := inc d PositiveInc tp t
        in run' ops tp p t
      --run' ops (inc d PositiveInc tp) p t
    (Inc NegativeInc d)   =>
      let _ # t := inc d NegativeInc tp t
        in run' ops tp p t
    (Move PositiveMove m) =>
      let tp' # t := move m PositiveMove tp t
        in run' ops tp' p t
      --run' ops (move m PositiveMove tp) p t
      --run' ops !(runIO $ move m PositiveMove tp) p t
    (Move NegativeMove m) =>
      let tp' # t := move m NegativeMove tp t
        in run' ops tp p t
      --run' ops (move m NegativeMove tp) p t
      --run' ops !(runIO $ move m NegativeMove tp) p t
    Print                 => -- T1.do
      let x # t := current tp t
      --newp      <- write p x
        in run' ops tp !(write p x) t
    Loop body             => --T1.do
      case current tp of
        Z =>
          run' ops tp p t
        _ => T1.do
          (tp', p') <- run' body tp p t
          run' (op :: ops) tp' p' t

verify : IO (Either String ())
verify = do
  let src      = "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++."
  --    ops      = parse $ fastUnpack src
  --    empty    = fill 1 0
      pempty   = MkPrinter Z Z True
  --(_, pleft)   <- run' ops
  --                     (MkTape empty Z)
  --                     pempty
  pleft <-
    pure $ run1 $ \t =>
      let ops             = parse $ fastUnpack src
          tape       # t := newMArray 1 Z t
          (_, pleft) # t := run' ops (T tape FZ) (MkPrinter Z Z True) t
        in pleft # t
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
      --let ops   = parse $ fastUnpack src
      --(_, newp) <- run ops (MkTape (fill 1 0) Z) (MkPrinter Z Z True)
      --(_, newp) <- run ops (T (newMArray 1 0) FZ) (MkPrinter Z Z True)
      --(_, newp) <- unsafeCreate 0 (run ops (MkPrinter Z Z True))
      newp <-
        runIO $ \t =>
          let ops            = parse $ fastUnpack src
              tape      # t := newMArray 1 Z t
              (_, newp) # t := run' ops (T tape FZ) (MkPrinter Z Z True) t
              _         # t := Array.release tape t
            in newp # t
          --    newp # t := run' ops (T tape FZ) (MkPrinter Z Z True) t
          --  in newp # t
      notify "stop"
      putStrLn $ "Output checksum: " ++ show (getChecksum newp)
    Nothing => do
      --let ops   = parse $ fastUnpack src
      newp <-
        runIO $ \t =>
          let ops            = parse $ fastUnpack src
              tape      # t := newMArray 1 Z t
              (_, newp) # t := run' ops (T tape FZ) (MkPrinter Z Z True) t
            in newp # t
      notify "stop"
