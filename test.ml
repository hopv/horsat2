open Main
open Type

let test f =
  let parseresult = parseFile ("/home/koba/trecs/horsat2-0.92/examples/"^f) in
  verifyParseResult parseresult
