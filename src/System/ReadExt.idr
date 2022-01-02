module System.ReadExt

import Data.Fuel
import Data.Vect
import System.File

%default total

public export
data FileErrorExt
  = SysFileError FileError
  | HitLimit

export
implementation Show FileErrorExt where
  show (SysFileError err) = show err
  show HitLimit = "Hit line limit: file is too large"

-- TODO: leaves the strings with trailing \n... trim?
export
readFileWithLimit : String -> IO (Either FileErrorExt (List String))
readFileWithLimit fname
  = do Right (isOk, contents) <- readFilePage 0 (Fuel.limit 10000) fname
             | Left err => pure $ Left (SysFileError err)
       pure $ if isOk
              then Right contents
              else Left HitLimit

export
readLinesOnto' : HasIO io => (acc : (p ** Vect p String)) ->
                             (fuel : Fuel) ->
                             (h : File) ->
                             io (Either FileError (Bool, (q ** Vect q String)))
readLinesOnto' (p ** vect) Dry h = pure (Right (False, (p ** reverse vect)))
readLinesOnto' (p ** vect) (More fuel) h
  = do False <- fEOF h
         | True => pure $ Right (True, (p ** reverse vect))
       (fGetLine h >>= \str => readLinesOnto' ((S p) ** (str :: vect)) fuel h) @{Monad.Compose}

export
readFilePage' : HasIO io => (until : Fuel) ->
                            (fname :  String) ->
                            io (Either FileError (Bool, (q ** Vect q String)))
readFilePage' fuel fname
  = withFile fname Read pure $
      readLinesOnto' (0 ** []) fuel

export
readFileWithLimit' : HasIO io => String -> io (Either FileErrorExt (q ** Vect q String))
readFileWithLimit' fname
  = do Right (isOk, contents) <- readFilePage' (Fuel.limit 10000) fname
             | Left err => pure $ Left (SysFileError err)
       pure $ if isOk
              then Right contents
              else Left HitLimit
