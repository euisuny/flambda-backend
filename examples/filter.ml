let rec filter p = function
| []  -> []
| a :: r -> if p a then a :: filter p r else filter p r
;;
