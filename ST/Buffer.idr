module ST.Buffer

import Control.ST
import Control.Catchable
import Control.IOExcept
import Data.Buffer

%default total

public export
interface BufferST (m : Type -> Type) where
  STBuffer : Type
  createBuffer : Nat -> ST m (Maybe Var) [addIfJust STBuffer]
  writeChunk : (chunk : ty) -> Nat -> (Buffer -> Int -> ty -> IO ()) -> (store : Var) -> ST m () [store ::: STBuffer]

  writeString : String -> (store : Var) -> ST m () [store ::: STBuffer]
  writeString str store = writeChunk str (length str) setString  store

  writeInt : Int -> (store : Var) -> ST m () [store ::: STBuffer]
  writeInt num store = writeChunk num 4 setInt store

  writeByte : Bits8 -> (store : Var) -> ST m () [store ::: STBuffer]
  writeByte byte store = writeChunk byte 1 setByte store

  writeBytes : List Bits8 -> (store : Var) -> ST m () [store ::: STBuffer]
  writeBytes [] store = pure ()
  writeBytes (b :: bytes) store = writeByte b store >>= \t => writeBytes bytes store

  destroyBuffer : (store : Var) -> ST m () [remove store STBuffer]

  toBuffer : (store : Var) -> ST m Buffer [store ::: STBuffer]
  toBufferWithCount : (store : Var) -> ST m (Buffer, Nat) [store ::: STBuffer]

public export
BufferST IO where
  STBuffer = State (Buffer, Nat)
  createBuffer initSize =
    do bufM <- lift $ newBuffer (cast initSize)
       case bufM of
         Nothing => pure Nothing
         Just buf => do store <- new (buf, 0)
                        pure $ Just store

  destroyBuffer store = delete store

  writeChunk str move fn bufst =
    do (buf, pos) <- read bufst
       lift $ fn buf (cast pos) str
       write bufst (buf, pos + move)
       pure ()

  toBuffer store = do (buf, num) <- read store
                      pure buf
  toBufferWithCount store = read store

