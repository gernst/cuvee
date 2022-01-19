package cuvee.sexpr;

%%

%public
%class Scanner
%function next
%type arse.Token

%eofval{
    return Expr.eof();
%eofval}

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

// printable = [\u0020-\u007E] | [\u0080-\uFFFF]
digit   = [0-9]
letter  = [a-zA-Z]
extra   = [~!@$%&*_+=<>.?/] | "-" | "^"

num     = [1-9]{digit}* | 0
dec     = num "\." 0* num
hex     = "0x" [0-9a-fA-F]+
bin     = "#b" [01]+

symbol0 = {letter} | {extra}
symbol1 = {letter} | {extra} | {digit}
symbol  = {symbol0} {symbol1}*

quoted  = \| ~ \|

kw      = ":" {symbol}

%%

<YYINITIAL> {

{ws}+ {}
";" .* {nl} {}

"("         { return Expr.lp();   }
")"         { return Expr.rp();   }

\" ~ \"
            { return new Lit.str(yytext(+1,-1)); }

{num}       { return new Lit.num(yytext()); }
{dec}       { return new Lit.dec(yytext()); }
{hex}       { return new Lit.hex(yytext(+2,0)); }
{bin}       { return new Lit.bin(yytext(+2,0)); }

{symbol}    { return new Id(yytext()); }
{quoted}    { return new Id(yytext(+1,-1)); }
{kw}        { return new Kw(yytext(+1,0));  }

/* {any} ({printable} - {ws})
            { throw new RuntimeException("unexpected character '" + yytext() + "'"); } */

[^]         { throw new RuntimeException("unexpected character '" + yytext() + "' at " + yyline + ":" + yycolumn); }

}
