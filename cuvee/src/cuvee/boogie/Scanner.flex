package cuvee.boogie;

%%

%public
%class Scanner
%function next
%type arse.Token

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

kw = "function" | "axiom" | "const" | "lemma" | "data" | "type"
   | "(" | ")" | "[" | "]" | "::" | [;,:{}]
   | "bool" | "int" | "real" | "=" | "|"
   | "proof" | "sorry" | "induction" | "->"

id = [a-zA-Z][a-zA-Z0-9]*
op = [+\-*/%] | "&&" | "||" | "==>" | "<==>" | "!"
   | "==" | "!=" | "<=" | "<" | ">" | ">="

quant = "forall" | "exists"

%%

<YYINITIAL> {

{ws}+ {}
"//" .* {nl} {}

{kw}        { return Parser.kw(yytext()); }
\" ~ \"     { return Parser.string().apply(yytext(+1,-1)); }
{quant}     { return Parser.quant().apply(yytext()); }
{number}    { return Parser.number().apply(yytext()); }
{id}        { return Parser.id().apply(yytext()); }
{op}        { return Parser.op().apply(yytext()); }

[^]         { throw new RuntimeException("unexpected character '" + yytext() + "' at " + yyline + ":" + yycolumn); }

}
