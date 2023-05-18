MODULE M2S; (*NW 17.8.83 / 25.6.86 / 31.12.91*)
  IMPORT Texts, Viewers, Oberon, MenuViewers, TextFrames;

  CONST KW = 42; (*number of keywords*)

    null = 0; times = 1; slash = 2; div = 3; mod = 4; and = 5;
    plus = 6; minus = 7; or = 8;
    eql = 9; neq = 10; lss = 11; leq = 12; gtr = 13; geq = 14; in = 15;
    arrow = 16; period = 17; comma = 18; colon = 19; ellipsis = 20; rparen = 21; rbrak = 22; rbrace = 23;
    of = 24; then = 25; do = 26; to = 27; by = 28; 
    lparen = 29; lbrak = 30; lbrace = 31; not = 32; becomes = 33; number = 34; string = 35; ident = 36;
    semicolon = 37; bar = 38; end = 39; else = 40; elsif = 41; until = 42;
    if = 43; while = 44; repeat = 45; loop = 46; with = 47; exit = 48; return = 49; case = 50; for = 51;
    array = 52; pointer = 53; record = 54; set = 55;
    begin = 56; code = 57; const = 58; type = 59; var = 60; forward = 61; procedure = 62; module = 63;
    definition = 64; implementation = 65; export = 66; qualified = 67; from = 68; import = 69; eof = 70;

  VAR id*: ARRAY 64 OF CHAR;
    scanerr*: BOOLEAN;
    ch: CHAR;      (*current character*)
    K, L: INTEGER;
    lastpos: LONGINT; (*error position in source file*)
    T: Texts.Text;    (*output text*)
    R: Texts.Reader;
    W, WL: Texts.Writer;
    lead: ARRAY 128 OF CHAR;
    keyTab: ARRAY KW OF
                RECORD sym: INTEGER;
                  id: ARRAY 16 OF CHAR
                END;
    Symbol: ARRAY 71, 16 OF CHAR;

  PROCEDURE Mark*(n: INTEGER);
    VAR pos: LONGINT;
  BEGIN scanerr := TRUE; pos := Texts.Pos(R);
    IF lastpos + 10 < pos THEN
      Texts.WriteString(WL, "  pos");
      Texts.WriteInt(WL, pos, 6); Texts.WriteString(WL, "  err"); Texts.WriteInt(WL, n, 4);
      Texts.WriteLn(WL); Texts.Append(Oberon.Log, WL.buf); lastpos := pos
    END
  END Mark;

  PROCEDURE String(tch: CHAR);
  BEGIN K := 0;
    LOOP Texts.Read(R, ch);
      IF ch = tch THEN EXIT END ;
      IF ch < " " THEN Mark(3); EXIT END ;
      IF K < 63 THEN id[K] := ch; INC(K) ELSE Mark(212); K := 0 END
    END ;
    Texts.Read(R, ch)
  END String;

  PROCEDURE Identifier(VAR sym: INTEGER);
    VAR k, l, m: INTEGER;
  BEGIN K := 0;
    REPEAT id[K] := ch; INC(K); Texts.Read(R, ch)
    UNTIL (ch < "0") OR ("9" < ch) & (CAP(ch) < "A") OR ("Z" < CAP(ch));
    id[K] := 0X;
    k := 0; l := KW;
    REPEAT m := (k + l) DIV 2;
      IF id <= keyTab[m].id THEN l := m ELSE k := m + 1 END
    UNTIL k >= l;
    IF (k < KW) & (id =  keyTab[k].id) THEN sym := keyTab[k].sym
    ELSE sym := ident
    END
  END Identifier;

  PROCEDURE Number;
    VAR i, j: INTEGER; d, intval: LONGINT; lastCh: CHAR;
      dig: ARRAY 10 OF LONGINT;

    PROCEDURE hex(d: LONGINT);
    BEGIN
      IF d < 10 THEN id[i] := CHR(d + 30H) ELSE id[i] := CHR(d + 37H) END ;
      INC(i)
    END hex;

  BEGIN K := 0;
    REPEAT id[K] := ch; INC(K); Texts.Read(R, ch)
    UNTIL (ch < "0") OR ("9" < ch) & (CAP(ch) < "A") OR ("Z" < CAP(ch));
    lastCh := ch;
    IF ch = "." THEN Texts.Read(R, ch);
      IF ch = "." THEN lastCh := 0X; ch := 7FX END
    END ;
    IF lastCh = "." THEN (*decimal point*)
      id[K] := "."; INC(K);
      WHILE ("0" <= ch) & (ch <= "9") DO (*read fraction*)
        id[K] := ch; INC(K); Texts.Read(R, ch)
      END ;
      IF ch = "E" THEN
        id[K] := ch; INC(K); Texts.Read(R, ch);
        IF (ch = "-") OR (ch = "+") THEN id[K] := ch; INC(K); Texts.Read(R, ch) END ;
        WHILE ("0" <= ch) & (ch <= "9") DO (*read exponent*)
          id[K] := ch; INC(K); Texts.Read(R, ch)
        END
      END
    ELSE (*integer*)
      lastCh := id[K-1];
      IF lastCh = "B" THEN (*octal*)
        DEC(K); intval := 0; j := 0;
        WHILE j < K DO
          d := ORD(id[j]) - 30H; intval := intval*8 + d; INC(j)
        END ;
        i := 0; j := 0;
        REPEAT dig[j] := intval MOD 10H; INC(j); intval := intval DIV 10H
        UNTIL intval = 0;
        IF dig[j-1] >= 10 THEN id[0] := "0"; i := 1 END ;
        REPEAT DEC(j); hex(dig[j]) UNTIL j = 0;
        id[i] := "H"; INC(i); id[i] := 0X; K := i
      ELSIF lastCh = "D" THEN DEC(K)
      ELSIF lastCh = "C" THEN
        DEC(K); intval := 0; i := 0; j := 0;
        WHILE j < K DO
          d := ORD(id[j]) - 30H; intval := intval*8 + d; INC(j)
        END ;
        IF intval >= 160 THEN id[0] := "0"; i := 1 END ;
        hex(intval DIV 10H); hex(intval MOD 10H);
        id[i] := "X"; INC(i); id[i] := 0X; K := i
      END
    END
  END Number;

  PROCEDURE Get*(VAR sym: INTEGER);
    VAR xch: CHAR; i: INTEGER;

    PROCEDURE Comment;
    BEGIN lead[L] := "("; INC(L); lead[L] := "*"; INC(L); Texts.Read(R, ch);
      REPEAT
        WHILE (ch # "*") & (ch > 0X) DO
          IF ch = "(" THEN Texts.Read(R, ch);
            IF ch = "*" THEN Comment END
          ELSE lead[L] := ch; INC(L); Texts.Read(R, ch)
          END
        END ;
        lead[L] := ch; INC(L); Texts.Read(R, ch)
      UNTIL (ch = ")") OR (ch = 0X);
      IF ch > 0X THEN lead[L] := ch; INC(L); Texts.Read(R, ch) ELSE Mark(42) END
    END Comment;

  BEGIN L := 0;
    LOOP
      IF (ch <= " ") OR (ch > 7FX) THEN
        IF ch = 0X THEN ch := " "; EXIT
        ELSE lead[L] := ch; INC(L); Texts.Read(R, ch)
        END ;
      ELSE EXIT
      END
    END ;
    CASE ch OF   (* " " <= ch <= 7FX *)
        " "  : sym := eof; ch := 0X |
        "!"  : sym := null; Texts.Read(R, ch) |
        22X  : String(22X); sym := string |
        "#"  : sym := neq; Texts.Read(R, ch)  |
        "$"  : sym := null; Texts.Read(R, ch) |
        "%"  : sym := null; Texts.Read(R, ch) |
        "&"  : sym := and; Texts.Read(R, ch)  |
        "'"  : String("'"); sym := string |
        "("  : Texts.Read(R, ch);
               IF ch = "*" THEN Comment; Get(sym)
                 ELSE sym := lparen
               END |
        ")"  : sym := rparen; Texts.Read(R, ch)|
        "*"  : sym := times; Texts.Read(R, ch) |
        "+"  : sym := plus; Texts.Read(R, ch)  |
        ","  : sym := comma; Texts.Read(R, ch) |
        "-"  : sym := minus; Texts.Read(R, ch) |
        "."  : Texts.Read(R, ch);
               IF ch = "." THEN Texts.Read(R, ch); sym := ellipsis
                 ELSE sym := period
               END |
        "/"  : sym := slash; Texts.Read(R, ch) |
        "0".."9": Number; sym := number |
        ":"  : Texts.Read(R, ch);
              IF ch = "=" THEN Texts.Read(R, ch); sym := becomes
                ELSE sym := colon
              END |
        ";"  : sym := semicolon; Texts.Read(R, ch) |
        "<"  : Texts.Read(R, ch);
              IF ch = "=" THEN Texts.Read(R, ch); sym := leq
                ELSIF ch = ">" THEN Texts.Read(R, ch); sym := neq
                ELSE sym := lss
              END |
        "="  : sym := eql; Texts.Read(R, ch)   |
        ">"  : Texts.Read(R, ch);
              IF ch = "=" THEN Texts.Read(R, ch); sym := geq
                ELSE sym := gtr
              END |
        "?"  : sym := null; Texts.Read(R, ch)  |
        "@"  : sym := null; Texts.Read(R, ch)  |
        "A".."Z": Identifier(sym) |
        "["  : sym := lbrak; Texts.Read(R, ch) |
        "\"  : sym := null; Texts.Read(R, ch)  |
        "]"  : sym := rbrak; Texts.Read(R, ch) |
        "^"  : sym := arrow; Texts.Read(R, ch) |
        "_"  : sym := becomes; Texts.Read(R, ch)  |
        "`"  : sym := null; Texts.Read(R, ch)  |
        "a".."z": Identifier(sym) |
        "{"  : sym := lbrace; Texts.Read(R, ch)|
        "|"  : sym := bar; Texts.Read(R, ch)   |
        "}"  : sym := rbrace; Texts.Read(R, ch)|
        "~"  : sym := not; Texts.Read(R, ch)   |
        7FX : sym := ellipsis; Texts.Read(R, ch)
    END
  END Get;

  PROCEDURE OutLead*;
    VAR i: INTEGER;
  BEGIN i := 0;
    WHILE i < L DO Texts.Write(W, lead[i]); INC(i) END
  END OutLead;

  PROCEDURE OutId*;
    VAR i: INTEGER;
  BEGIN i := 0;
    WHILE i < L DO Texts.Write(W, lead[i]); INC(i) END ;
    i := 0;
    WHILE i < K DO Texts.Write(W, id[i]); INC(i) END
  END OutId;

  PROCEDURE OutStr*;
    VAR i: INTEGER;
  BEGIN i := 0;
    WHILE i < L DO Texts.Write(W, lead[i]); INC(i) END ;
    Texts.Write(W, 22X); i := 0;
    WHILE i < K DO Texts.Write(W, id[i]); INC(i) END ;
    Texts.Write(W, 22X)
  END OutStr;

  PROCEDURE OutCh*(ch: CHAR);
  BEGIN Texts.Write(W, ch)
  END OutCh;

  PROCEDURE OutLit*(s: ARRAY OF CHAR);
    VAR i: INTEGER;
  BEGIN i := 0;
    WHILE s[i] > 0X DO Texts.Write(W, s[i]); INC(i) END
  END OutLit;

  PROCEDURE OutInt*(n: INTEGER);
  BEGIN Texts.WriteInt(W, n, 1)
  END OutInt;

  PROCEDURE OutLn*;
  BEGIN Texts.WriteLn(W); Texts.Write(W, 9X)
  END OutLn;

  PROCEDURE Out*(sym: INTEGER);
    VAR i: INTEGER; ch: CHAR;
  BEGIN i := 0;
    WHILE i < L DO Texts.Write(W, lead[i]); INC(i) END ;
    i := 0;
    LOOP ch := Symbol[sym, i];
      IF ch > 0X THEN Texts.Write(W, ch); INC(i) ELSE EXIT END
    END
  END Out;

  PROCEDURE Open*(source: Texts.Text; pos: LONGINT);
  BEGIN ch := " "; scanerr := FALSE; lastpos := -8; Texts.OpenReader(R, source, pos)
  END Open;

  PROCEDURE OpenViewer*(VAR name: ARRAY OF CHAR);
    VAR V: Viewers.Viewer; X, Y: INTEGER;
  BEGIN T := TextFrames.Text(""); Oberon.AllocateUserViewer(0, X, Y);
    V := MenuViewers.New(
        TextFrames.NewMenu(name, "System.Close  System.Copy  System.Grow  Edit.Search  Edit.Store"),
        TextFrames.NewText(T, 0), TextFrames.menuH, X, Y);
  END OpenViewer;

  PROCEDURE Close*;
  BEGIN Texts.Append(T, W.buf)
  END Close;
  
  PROCEDURE EnterKW(sym: INTEGER; id: ARRAY OF CHAR);
  BEGIN
    keyTab[K].sym := sym; COPY(id, keyTab[K].id); INC(K); COPY(id, Symbol[sym])
  END EnterKW;
  
BEGIN K := 0;
  EnterKW(and,"AND");
  EnterKW(array,"ARRAY");
  EnterKW(begin,"BEGIN");
  EnterKW(by,"BY");
  EnterKW(case,"CASE");
  EnterKW(code,"CODE");
  EnterKW(const,"CONST");
  EnterKW(definition,"DEFINITION");
  EnterKW(div,"DIV");
  EnterKW(do,"DO");
  EnterKW(else,"ELSE");
  EnterKW(elsif,"ELSIF");
  EnterKW(end,"END");
  EnterKW(exit,"EXIT");
  EnterKW(export,"EXPORT");
  EnterKW(for,"FOR");
  EnterKW(forward,"FORWARD");
  EnterKW(from,"FROM");
  EnterKW(if,"IF");
  EnterKW(implementation,"IMPLEMENTATION");
  EnterKW(import,"IMPORT");
  EnterKW(in,"IN");
  EnterKW(loop,"LOOP");
  EnterKW(mod,"MOD");
  EnterKW(module,"MODULE");
  EnterKW(not,"NOT");
  EnterKW(of,"OF");
  EnterKW(or,"OR");
  EnterKW(pointer,"POINTER");
  EnterKW(procedure,"PROCEDURE");
  EnterKW(qualified,"QUALIFIED");
  EnterKW(record,"RECORD");
  EnterKW(repeat,"REPEAT");
  EnterKW(return,"RETURN");
  EnterKW(set,"SET");
  EnterKW(then,"THEN");
  EnterKW(to,"TO");
  EnterKW(type,"TYPE");
  EnterKW(until,"UNTIL");
  EnterKW(var,"VAR");
  EnterKW(while,"WHILE");
  EnterKW(with,"WITH");
  Symbol[1, 0] := "*";
  Symbol[2,0] := "/";
  Symbol[5,0] := "&"; Symbol[5,1] := 0X;
  Symbol[6,0] := "+";
  Symbol[7,0] := "-";
  Symbol[9,0] := "=";
  Symbol[10,0] := "#";
  Symbol[11,0] := "<";
  Symbol[12] := "<=";
  Symbol[13,0] := ">";
  Symbol[14] := ">=";
  Symbol[16,0] := "^";
  Symbol[17,0] := ".";
  Symbol[18,0] := ",";
  Symbol[19,0] := ":";
  Symbol[20] := "..";
  Symbol[21,0] := ")";
  Symbol[22,0] := "]";
  Symbol[23,0] := "}";
  Symbol[29,0] := "(";
  Symbol[30,0] := "[";
  Symbol[31,0] := "{";
  Symbol[32,0] := "~"; Symbol[32,1] := 0X;
  Symbol[33] := ":=";
  Symbol[37,0] := ";";
  Symbol[38,0] := "|";
  Texts.OpenWriter(W); Texts.OpenWriter(WL)
END M2S.
