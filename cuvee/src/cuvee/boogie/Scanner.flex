package cuvee.boogie;

%%

%public
%class Scanner
%function next
%type easyparse.Token

%line
%column

%{
    public final String yytext(int start, int end) {
        int length = zzMarkedPos-zzStartRead;
        return new String( zzBuffer, zzStartRead + start, length - start + end );
    }
%}

nl = \r|\n|\r\n
ws = {nl} | [ \t\f]

number  = [1-9][0-9]* | 0

kw = "function" | "axiom" | "const" | "lemma" | "data" | "abstractions" | "contract" | "type" | "procedure" | "where"
   | "(" | ")" | "[" | "]" | "::" | [;,:{}] | ":="
   | "bool" | "int" | "real" | "=" | "|"
   | "var" | "call" | "invariant" | "summary" | "assume" | "assert" | "havoc" | "requires" | "ensures" | "modifies" | "returns" | "decreases"
   | "while" | "if" | "else" | "break" | "return"
   | "proof" | "sorry" | "show" | "then" | "case" | "free lemma" | "goal"
   | "induction" | "unfold" | "at" | "=>" | "end" | "auto" | "noauto"
   | "in" | "out" | "inout"

id = [a-zA-Z_][a-zA-Z0-9⁰-⁹₀-₉_~#$.?]* | "seq.++"
op = [+\-*/%] | "&&" | "||" | "==>" | "<==>" | "!"
   | "==" | "!=" | "<=" | "<" | ">" | ">="

quant = "forall" | "exists"
loc = "old" | "final" | "earlier"

%%

<YYINITIAL> {

{ws}+ {}
"//" .* {nl} {}

{kw}        { return Parser.kw(yytext()); }
\" ~ \"     { return Parser.string().apply(yytext(+1,-1)); }
{quant}     { return Parser.quant().apply(yytext()); }
{loc}       { return Parser.loc().apply(yytext()); }
{number}    { return Parser.number().apply(yytext()); }
{id}        { return Parser.id().apply(yytext()); }
{op}        { return Parser.op().apply(yytext()); }

[^]         { throw new RuntimeException("unexpected character '" + yytext() + "' at " + yyline + ":" + yycolumn); }

}
