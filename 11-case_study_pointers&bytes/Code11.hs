{-@ LIQUID "--no-termination" @-}
module Code11 where

import Prelude hiding (null)

import Data.Word
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr
import Foreign.Storable
import System.IO.Unsafe
import Data.ByteString.Internal (c2w, w2c)

{-@ type TRUE = {b:_ | b}@-}

{-@ ignore chop' @-}
chop'     :: String -> Int -> String
chop' s n = s'
  where
    b     = pack s          -- down to low-level
    b'    = unsafeTake n b  -- grab n chars
    s'    = unpack b'       -- up to high-level

{-@ GHC.ForeignPtr.mallocForeignPtrBytes :: n:Nat -> IO ({v:ForeignPtr a | fplen v = n}) @-}

zero4 = do fp <- mallocForeignPtrBytes 4
           withForeignPtr fp $ \p -> do
             poke (p `plusPtr` 0) zero
             poke (p `plusPtr` 1) zero
             poke (p `plusPtr` 2) zero
             poke (p `plusPtr` 3) zero
           return fp
        where
           zero = 0 :: Word8

{-@ fail zero4' @-}
zero4' = do fp <- mallocForeignPtrBytes 4
            withForeignPtr fp $ \p -> do
              poke (p `plusPtr` 0) zero
              poke (p `plusPtr` 1) zero
              poke (p `plusPtr` 2) zero
              poke (p `plusPtr` 8) zero
            return fp
         where
            zero = 0 :: Word8

zero3 = do fp <- mallocForeignPtrBytes 4
           withForeignPtr fp $ \p -> do
             poke (p `plusPtr` 0) zero
             poke (p `plusPtr` 1) zero
             poke (p `plusPtr` 2) zero
           return fp
        where
           zero = 0 :: Word8

{-@ fail exBad @-}
exBad = do fp <- mallocForeignPtrBytes 4
           withForeignPtr fp $ \p -> do
             poke (p `plusPtr` 0) zero
             poke (p `plusPtr` 1) zero
             poke (p `plusPtr` 2) zero
             poke (p `plusPtr` 5) zero     -- LH complains
           return fp
        where
           zero = 0 :: Word8

data ByteString = BS {
    bPtr :: ForeignPtr Word8
  , bOff :: !Int
  , bLen :: !Int
  }

{-@ data ByteString = BS {
      bPtr :: ForeignPtr Word8
    , bOff :: {v:Nat| v        <= fplen bPtr}
    , bLen :: {v:Nat| v + bOff <= fplen bPtr}
    }
  @-}

{-@ type ByteStringN N = {v:ByteString | bLen v = N} @-}

{-@ good1 :: IO (ByteStringN 5) @-}
good1 = do fp <- mallocForeignPtrBytes 5
           return (BS fp 0 5)

{-@ good2 :: IO (ByteStringN 2) @-}
good2 = do fp <- mallocForeignPtrBytes 5
           return (BS fp 3 2)

bad1 = do fp <- mallocForeignPtrBytes 3
          return (BS fp 0 3)

bad2 = do fp <- mallocForeignPtrBytes 3
          return (BS fp 2 1)

{-@ create :: n:Nat -> (PtrN Word8 n -> IO ()) -> ByteStringN n @-}
create :: Int -> (Ptr Word8 -> IO ()) -> ByteString
create n fill = unsafePerformIO $ do
  fp  <- mallocForeignPtrBytes n
  withForeignPtr fp fill
  return (BS fp 0 n)

bsGHC = create 3 $ \p -> do
  poke (p `plusPtr` 0) (c2w 'G')
  poke (p `plusPtr` 1) (c2w 'H')
  poke (p `plusPtr` 2) (c2w 'C')

{-@ pack :: str:String -> ByteStringN {len str} @-}
pack str      = create n $ \p -> go p xs
  where
  n           = length str
  xs          = map c2w str
  {-@ go :: p:Ptr a -> {xs:_ | plen p = len xs} -> IO ()@-}
  go p (x:xs) = poke p x >> go (plusPtr p 1) xs
  go _ []     = return  ()

{-@ prop_pack_length  :: String -> TRUE @-}
prop_pack_length xs   = bLen (pack xs) == length xs

packEx str     = create n $ \p -> pLoop p xs
  where
  n            = length str
  xs           = map c2w str

{-@ pLoop      :: (Storable a) => p:Ptr a -> {xs:[a] | plen p = len xs} -> IO () @-}
pLoop p (x:xs) = poke p x >> pLoop (plusPtr p 1) xs
pLoop _ []     = return ()

{-@ unsafeTake :: n:Nat -> b:{v:_ | bLen v >= n} -> ByteStringN n @-}
unsafeTake n (BS x s _) = BS x s n

{-@ unsafeDrop :: n:Nat -> b:{v:_ | bLen v >= n} -> ByteStringN {bLen b - n} @-}
unsafeDrop n (BS x s l) = BS x (s + n) (l - n)

{-@ unpack :: bs:ByteString -> {v:_ | bLen bs = len v} @-}
unpack              :: ByteString -> String
unpack (BS _  _ 0)  = []
unpack (BS ps s l)  = unsafePerformIO
                        $ withForeignPtr ps
                        $ \p -> go (p `plusPtr` s) (l - 1) []
  where
    {-@ go     :: p:_ -> {n:Nat | n < plen p} -> acc:_ -> IO {v:_ | len v = n + len acc + 1} @-}
    go :: Ptr Word8 -> Int -> String -> IO String
    go p 0 acc = peekAt p 0 >>= \e -> return (w2c e : acc)
    go p n acc = peekAt p n >>= \e -> go p (n-1) (w2c e : acc)

    {-@ peekAt :: p:_ -> {n:Nat | n < plen p} -> _ @-}
    peekAt p n = peek (p `plusPtr` n)

{-@ prop_unpack_length :: ByteString -> TRUE @-}
prop_unpack_length b   = bLen b == length (unpack b)

{-@ chop :: s:String -> n:BNat (len s) -> {v:_ | n = len v} @-}
chop s n = s'
  where
    b    = pack s          -- down to low-level
    b'   = unsafeTake n b  -- grab n chars
    s'   = unpack b'       -- up to high-level

{-@ ignore demo @-}
demo     = [ex6, ex30]
  where
    ex   = ['L','I','Q','U','I','D']
    ex6  = chop ex 6   -- accepted by LH
    ex30 = chop ex 30  -- rejected by LH

{-@ prop_chop_length  :: String -> Nat -> TRUE @-}
prop_chop_length s n
  | n <= length s     = length (chop s n) == n
  | otherwise         = True

safeChop      :: String -> Int -> String
safeChop str n
  | ok        = chop str n
  | otherwise = ""
  where
    ok        = 0 <= n && n <= length str

queryAndChop  :: IO String
queryAndChop  = do putStrLn "Give me a string:"
                   str  <-  getLine
                   putStrLn "Give me a number:"
                   ns   <-  getLine
                   let n =  read ns :: Int
                   return $ safeChop str n

{-@ predicate Null B  = bLen B == 0                   @-}
{-@ type ByteStringNE = {v:ByteString | not (Null v)} @-}

{-@ null :: b:_ -> {v:Bool | v <=> Null b} @-}
null (BS _ _ l) = l == 0


{-@ unsafeHead :: ByteStringNE -> Word8 @-}
unsafeHead :: ByteString -> Word8
unsafeHead (BS x s _) = unsafePerformIO $
                          withForeignPtr x $ \p ->
                            peekByteOff p s

{-@ unsafeTail :: b:ByteStringNE -> ByteStringN {bLen b -1} @-}
unsafeTail (BS ps s l) = BS ps (s + 1) (l - 1)

{-@ group :: b:_ -> {v: [ByteStringNE] | bsLen v = bLen b} @-}
group :: ByteString -> [ByteString]
group xs
    | null xs   = []
    | otherwise = let  y        = unsafeHead xs
                       (ys, zs) = spanByte y (unsafeTail xs)
                  in (y `cons` ys) : group zs

{-@ measure bsLen @-}
bsLen        :: [ByteString] -> Int
bsLen []     = 0
bsLen (b:bs) = bLen b + bsLen bs

{-@ assume spanByte :: Word8 -> b:ByteString -> ByteString2 b @-}
spanByte :: Word8 -> ByteString -> (ByteString, ByteString)
spanByte c ps@(BS x s ln)
  = unsafePerformIO
      $ withForeignPtr x $ \p ->
         go (p `plusPtr` s) 0
  where
    {-@ go :: {p:Ptr a | ln <= plen p} -> {v:Nat | v <= ln} -> _ @-}
    go p i
      | i >= ln   = return (ps, empty)
      | otherwise = do c' <- peekByteOff p i
                       if c /= c'
                         then return (splitAt i)
                         else go p (i+1)
    splitAt i     = (unsafeTake i ps, unsafeDrop i ps)

{-@ type ByteString2 B
      = {v:_ | bLen (fst v) + bLen (snd v) = bLen B} @-}

{-@ unsafeCreate :: l:Nat -> (PtrN Word8 l -> IO ()) -> ByteStringN l @-}
unsafeCreate n f = create' n f

{-@ cons :: Word8 -> b:ByteString -> {v:ByteStringNE | bLen v = bLen b + 1} @-}
cons :: Word8 -> ByteString -> ByteString
cons c (BS x s l) = unsafeCreate (l+1) $ \p -> withForeignPtr x $ \f -> do
        poke p c
        memcpy (p `plusPtr` 1) (f `plusPtr` s) (fromIntegral l)

{-@ empty :: {v:ByteString | bLen v = 0} @-}
empty :: ByteString
empty = BS nullForeignPtr 0 0


{-@ assume
    c_memcpy :: dst:PtrV Word8
             -> src:PtrV Word8
             -> size:{CSize | size <= plen src && size <= plen dst}
             -> IO (Ptr Word8)
  @-}
foreign import ccall unsafe "string.h memcpy" c_memcpy
    :: Ptr Word8 -> Ptr Word8 -> CSize -> IO (Ptr Word8)

{-@ memcpy :: dst:PtrV Word8
           -> src:PtrV Word8
           -> size:{CSize | size <= plen src && size <= plen dst}
           -> IO ()
  @-}
memcpy :: Ptr Word8 -> Ptr Word8 -> CSize -> IO ()
memcpy p q s = c_memcpy p q s >> return ()

{-@ assume nullForeignPtr :: {v: ForeignPtr Word8 | fplen v = 0} @-}
nullForeignPtr :: ForeignPtr Word8
nullForeignPtr = unsafePerformIO $ newForeignPtr_ nullPtr
{-# NOINLINE nullForeignPtr #-}

{-@ create' :: n:Nat -> (PtrN Word8 n -> IO ()) -> ByteStringN n @-}
create' :: Int -> (Ptr Word8 -> IO ()) -> ByteString
create' n fill = unsafePerformIO $ do
  fp  <- mallocForeignPtrBytes n
  withForeignPtr fp fill
  return (BS fp 0 n)
