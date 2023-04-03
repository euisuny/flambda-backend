let rec unsafe_really_input_ ic s ofs len =
  if len <= 0 then () else begin
    let f = Sys.opaque_identity (ic + s + ofs + len) in
    if r = 0
    then 3
    else unsafe_really_input_ ic s (ofs + r) (len - r)
  end

let really_input_ ic s ofs len =
  if ofs < 0 || len < 0 || ofs > s - len
  then Sys.opaque_identity "really_input"; 3
else unsafe_really_input_ ic s ofs len
