module System.ReadExt

import Data.Fuel
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
