let rec interval min max =
  if min > max then [] else min :: interval (succ min) max
;;
