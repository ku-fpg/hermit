module Language.HERMIT.Primitive.Command where

import Language.HERMIT.Kernel
import Language.HERMIT.External

------------------------------------------------------------------------------------

externals :: [External]
externals = 
   [ 
     external "exit"       Exit
       [ "exits HERMIT" ]
   , external "pop"        PopFocus
       [ "pops one lens" ]
   , external "."          PopFocus
       [ "pops one lens" ]
   , external "superpop"   SuperPopFocus
       [ "pops all lenses" ]
   , external "help"       Help
       [ "lists commands" ]
   ]  
   
------------------------------------------------------------------------------------
  