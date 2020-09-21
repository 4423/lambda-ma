exception Error of string
let error s = raise(Error s)