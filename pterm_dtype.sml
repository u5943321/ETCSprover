structure pterm_dtype = 
struct
datatype psort = pob
               | par of pterm * pterm
               | psvar of string
and pterm =
          ptUVar of string 
         | pVar of string * psort
         | pFun of string * pterm list
         | pAnno of pterm * psort
datatype pform =
         pPred of string * pterm list
         | pConn of string * pform list
         | pQuant of string * string * psort * pform;  

end


