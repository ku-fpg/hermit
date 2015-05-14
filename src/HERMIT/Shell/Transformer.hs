module HERMIT.Shell.Transformer where
        
import HERMIT.Kure

class Transformer f where
   toTransformH :: f a b -> TransformH a b
