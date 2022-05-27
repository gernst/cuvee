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

name    = [a-zA-Z][a-zA-Z0-9]*
number  = [1-9][0-9]* | 0

kw = "function" | "axiom" | "const" | "data" | "type"
   | "(" | ")" | "[" | "]" | "::" | [;,:<>{}]
   | "bool" | "int" | "real"

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
{name}      { return Parser.name().apply(yytext()); }
{op}        { return Parser.opname().apply(yytext()); }

[^]         { throw new RuntimeException("unexpected character '" + yytext() + "' at " + yyline + ":" + yycolumn); }

}
