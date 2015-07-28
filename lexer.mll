{
  open Parser
  exception Eof
}
rule token = parse
    [' ' '\t']  { token lexbuf }
  | ';'                 { SEQ }
  | '+' | 'U'           { CHOICE }
  | '*'                 { ITER }
  | "||"                { CPAR }
  | '?'                 { TEST }
  | 'F'("alse")? | "⊥"  { BOT }
  | 'T'("rue")?  | "⊤"  { TOP }
  | '~' | '!' | "¬"     { NEG }
  | '&' | "∧"           { CONJ }
  | '|' | "∨"           { DISJ }
  | "=>" |"->" | "→"    { IMP }
  | "<=>" |"<->"        { EQUIV }
  | '<'                 { DIAM_O }
  | '>'                 { DIAM_C }
  | '['                 { BOX_O }
  | ']'                 { BOX_C }
  | '('                 { PAREN_O }
  | ')'                 { PAREN_C }
  | '\n'                { EOL }
  | ['A'-'Z' 'a'-'z' '0'-'9' '_' '\''] + as id
                        { IDENT id }
  | eof                 { raise Eof }
