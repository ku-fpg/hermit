module Language.HERMIT.Primitive.Command where

import Language.HERMIT.Kernel
import Language.HERMIT.External

------------------------------------------------------------------------------------

externals :: [External]
externals =
   [
     external "exit"            Exit
       [ "exits HERMIT" ]
   , external "pop"             PopFocus
       [ "pops one lens" ]
   , external "."               PopFocus
       [ "pops one lens" ]
   , external "superpop"        SuperPopFocus
       [ "pops all lenses" ]
   , external "help [category]" (Help Nothing)
       [ "lists commands"
       , ""
       , "optionally, specify a command category"
       , "use 'help list' to see a list of categories"  ]
   ]

------------------------------------------------------------------------------------

