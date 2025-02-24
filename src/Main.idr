module NMain

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

%hide System.run
%hide Data.Array.Index.inc

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

record Tape where
  constructor MkTape
  {size : Nat}
  arr   : IOArray size Nat
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
current : (tp : Tape) -> F1 World Nat
current tp = get tp.arr tp.pos

inc : (delta : Nat) -> IncType -> (tp : Tape) -> F1' World
inc delta PositiveInc tp = modify tp.arr tp.pos (+ delta)
inc delta NegativeInc tp = modify tp.arr tp.pos (`minus` delta)

--inc : {size : Nat} -> (delta : Nat) -> IncType -> MArray s size Nat -> Fin size -> F1' s
--inc delta PositiveInc arr pos = modify arr pos (+ delta)
--inc delta NegativeInc arr pos = modify arr pos (`minus` delta)

minus : Fin n -> Nat -> Fin n
minus x m = natToFinLT (finToNat x `minus` m) @{finMinusLT _ _}

plus : {n : _} -> Fin n -> (m : Nat) -> Either (Fin n) (Fin (m+n))
plus x m =
  case tryNatToFin (finToNat x + m) of
    Just y  => Left y
    Nothing => Right $ natToFinLT (finToNat x + m) @{?bar} -- @{finPlusLT _ _}

move :  (m : Nat)
     -> MoveType
     -> (tp : Tape)
     -> F1 World Tape
move m NegativeMove (MkTape arr pos) t = MkTape arr (pos `minus` m) # t
move m PositiveMove (MkTape arr pos) t =
  case plus pos m of
    Left  p2 => MkTape arr p2 # t
    Right p2 =>
      let arr2 # t := mgrow arr m 0 t
        in MkTape arr2 p2 # t

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
      '[' => let (cs', body) = loop (cs, [])
               in loop (cs', Loop body :: acc)
      ']' => (cs, reverse acc)
      _   => loop (cs, acc)

partial
run :  List Op
    -> (tp : Tape)
    -> (p : Printer)
    -> IO (Tape, Printer)
run Nil         tp p =
  pure (tp, p)
run (op :: ops) tp p =
  case op of
    (Inc PositiveInc d)   => do
      () <- runIO (inc d PositiveInc tp)
      run ops tp p
    (Inc NegativeInc d)   => do
      () <- runIO (inc d NegativeInc tp)
      run ops tp p
    (Move PositiveMove m) => do
      tp' <- runIO (move m PositiveMove tp)
      run ops tp' p
    (Move NegativeMove m) => do
      tp' <- runIO (move m NegativeMove tp)
      run ops tp' p
    Print                 => do
      x <- runIO (current tp)
      run ops tp !(write p x)
    Loop body             =>
      case !(runIO (current tp)) of
        Z =>
          run ops tp p
        _ => do
          (tp', p') <- run body tp p
          run (op :: ops) tp' p'

verify : IO (Either String ())
verify = do
  let src      = "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++."
      ops      = parse $ fastUnpack src
      pempty   = MkPrinter Z Z True
  pleft <- do
    tape       <- marray 1 Z
    (_, pleft) <- run ops (MkTape tape FZ) (MkPrinter Z Z True)
    pure pleft
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
  let ops   =  parse $ fastUnpack src 
  quiet     <- getEnv "QUIET"
  pid       <- getPID
  notify $ "Idris (Array)\t" ++ show pid
  case quiet of
    Just _  => do
      tape      <- marray 1 Z 
      (_, newp) <- run ops (MkTape tape FZ) (MkPrinter Z Z True)
      notify "stop"
      putStrLn $ "Output checksum: " ++ show (getChecksum newp)
    Nothing => do
      tape      <- marray 1 Z
      (_, newp) <- run ops (MkTape tape FZ) (MkPrinter Z Z True)
      notify "stop"
