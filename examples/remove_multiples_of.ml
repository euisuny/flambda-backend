let rec filter p = function
| []  -> []
| a :: r -> if p a then a :: filter p r else filter p r
;;

let remove_multiples_of n =
filter (fun m -> m mod n <> 0)
;;
