MODULE Modula;   (*NW 14.12.91 / 31.12.91*)
  IMPORT Viewers, Texts, Oberon, TextFrames, M2S;

  CONST Const = 0; Typ = 1; Var = 2; Proc = 3; Module = 4; Head = 5;

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

  TYPE Object = POINTER TO ObjDesc;
    ObjDesc = RECORD
        name: ARRAY 32 OF CHAR;
        class: INTEGER;
        exported: BOOLEAN;
        mod, next, dsc: Object
      END ;

  VAR sym: INTEGER;
    isdef, isimp: BOOLEAN;
    topScope, undefobj, universe: Object;

  PROCEDURE^ Type;
  PROCEDURE^ Expression;
  PROCEDURE^ Block(level: INTEGER);

  PROCEDURE This(VAR name: ARRAY OF CHAR): Object;
    VAR obj, head: Object;
  BEGIN head := topScope;
    LOOP obj := head.next;
      WHILE (obj # NIL) & (obj.name # name) DO obj := obj.next END ;
      IF obj # NIL THEN EXIT END ;
      head := head.dsc;
      IF head = NIL THEN obj := undefobj; M2S.Mark(0); COPY(name, obj.name); EXIT END
    END ;
    RETURN obj
  END This;

  PROCEDURE ThisOne(VAR name: ARRAY OF CHAR): Object;
    VAR obj, head: Object;
  BEGIN obj := topScope.next;
    WHILE (obj # NIL) & (obj.name # name) DO obj := obj.next END ;
    RETURN obj
  END ThisOne;

  PROCEDURE Insert(VAR name: ARRAY OF CHAR; class: INTEGER);
    VAR obj, new: Object;
  BEGIN NEW(new);
    new.dsc := NIL; new.next := topScope.next; new.mod := NIL; new.exported := isdef;
    COPY(name, new.name); new.class := class; topScope.next := new
  END Insert;

  PROCEDURE OpenScope;
    VAR head: Object;
  BEGIN NEW(head);
    head.class := Head; head.dsc := topScope; head.next := NIL; topScope := head
  END OpenScope;

  PROCEDURE CloseScope;
  BEGIN topScope := topScope.dsc
  END CloseScope;

  PROCEDURE CheckSym(s, n: INTEGER);
  BEGIN M2S.Out(s);
    IF sym = s THEN M2S.Get(sym) ELSE M2S.Mark(n) END
  END CheckSym;

  PROCEDURE qualident(VAR obj: Object);
  BEGIN (*sym = ident*)
    M2S.OutLead; obj := This(M2S.id); M2S.Get(sym);
    WHILE (sym = period) & (obj # NIL) & (obj.class = Module) DO
      M2S.OutId; M2S.Out(sym); M2S.Get(sym);
      IF sym = ident THEN
        obj := This(M2S.id); M2S.Get(sym)
      ELSE M2S.Mark(10)
      END
    END
  END qualident;

  PROCEDURE makeid(obj: Object);
  BEGIN
    IF obj # NIL THEN
      IF obj.mod # NIL THEN M2S.OutLit(obj.mod.name); M2S.OutCh(".") END ;
      M2S.OutLit(obj.name)
    END
  END makeid;

  PROCEDURE CaseLabelList;
  BEGIN
    LOOP Expression;
      IF sym = ellipsis THEN
        M2S.Out(sym); M2S.Get(sym); Expression
      END ;
      IF sym = comma THEN M2S.Out(sym); M2S.Get(sym) ELSE EXIT END
    END
  END CaseLabelList;

  PROCEDURE Subrange;
  BEGIN 
    REPEAT M2S.Get(sym) UNTIL sym = rbrak;
    M2S.OutLit(" INTEGER"); M2S.Get(sym)
  END Subrange;

  PROCEDURE CheckId;
    VAR obj: Object;
  BEGIN
    IF M2S.id = "CARDINAL" THEN
      M2S.OutLit(" INTEGER"); M2S.Get(sym);
      IF sym = lbrak THEN
        REPEAT M2S.Get(sym) UNTIL sym = rbrak;
        M2S.Get(sym)
      END
    ELSIF M2S.id = "BITSET" THEN M2S.OutLit(" SET"); M2S.Get(sym)
    ELSE qualident(obj);
      IF sym = lbrak THEN Subrange ELSE makeid(obj) END
    END
  END CheckId;

  PROCEDURE SimpleType;
    VAR n: INTEGER;
  BEGIN
    IF sym = ident THEN CheckId
    ELSIF sym = lparen THEN
      M2S.Get(sym); M2S.OutLit(" INTEGER;"); M2S.OutLn; M2S.OutLit("CONST "); n := 0;
      LOOP
        IF sym = ident THEN
          Insert(M2S.id, Const);
          M2S.OutId; M2S.OutLit(" = "); M2S.OutInt(n);
          INC(n); M2S.Get(sym)
        ELSE M2S.Mark(10)
        END ;
        IF sym = comma THEN M2S.Out(semicolon); M2S.Get(sym) ELSE EXIT END
      END ;
      M2S.Get(sym)
    ELSIF sym = lbrak THEN Subrange
    ELSE M2S.Mark(32)
    END
  END SimpleType;

  PROCEDURE FieldListSequence;
    VAR obj: Object;

    PROCEDURE VariantPart;
    BEGIN
      LOOP
        IF sym < bar THEN
          WHILE sym # colon DO M2S.Get(sym) END ;
          M2S.Get(sym); FieldListSequence
        END ;
        IF sym = bar THEN M2S.OutCh(";"); M2S.Get(sym) ELSE EXIT END
      END ;
      IF sym = else THEN M2S.OutCh(";"); M2S.Get(sym); FieldListSequence END
    END VariantPart;

  BEGIN
    IF (sym = ident) OR (sym = case) THEN
      LOOP
        IF sym = ident THEN
          LOOP
            IF sym = ident THEN
              M2S.OutId; M2S.Get(sym)
            ELSE M2S.Mark(10)
            END ;
            IF sym = comma THEN M2S.Out(sym); M2S.Get(sym) ELSE EXIT END
          END ;
          CheckSym(colon, 13); Type
        ELSIF sym = case THEN
          M2S.Get(sym);
          IF sym = ident THEN
            M2S.OutId; M2S.Get(sym)
          END ;
          CheckSym(colon, 13);
          IF sym = ident THEN qualident(obj); makeid(obj) ELSE M2S.Mark(10) END ;
          IF sym = of THEN M2S.OutCh(";"); M2S.Get(sym) ELSE M2S.Mark(24) END ;
          VariantPart;
          IF sym = end THEN M2S.Get(sym) ELSE M2S.Mark(20) END
        END ;
        IF sym = semicolon THEN M2S.Out(sym); M2S.Get(sym) ELSE EXIT END
      END
    END
  END FieldListSequence;

  PROCEDURE FormalType;
  BEGIN
    IF sym = array THEN
      M2S.Out(sym); M2S.Get(sym); CheckSym(of, 23);
      IF sym = ident THEN CheckId END
    ELSIF sym = ident THEN CheckId
    ELSE M2S.Mark(10)
    END
  END FormalType;

  PROCEDURE FormalTypeList;
    VAR obj: Object;
  BEGIN
    IF (sym = ident) OR (sym = var) OR (sym = array) THEN
      LOOP
        IF sym = var THEN M2S.Get(sym) END ;
        FormalType;
        IF sym = comma THEN M2S.Out(sym); M2S.Get(sym) ELSE EXIT END
      END
    END ;
    CheckSym(rparen, 15);
    IF sym = colon THEN
      M2S.Out(sym); M2S.Get(sym);
      IF sym = ident THEN qualident(obj); makeid(obj) ELSE M2S.Mark(10) END
    END
  END FormalTypeList;

  PROCEDURE ArrayType;
    VAR obj: Object;
  BEGIN
    IF sym = ident THEN qualident(obj); makeid(obj)
    ELSIF sym = lbrak THEN
      REPEAT M2S.Get(sym) UNTIL sym = rbrak;
      M2S.Get(sym)
    END ;
    IF sym = of THEN
      M2S.Out(sym); M2S.Get(sym); Type
    ELSIF sym = comma THEN
      M2S.Out(sym); M2S.Get(sym); ArrayType
    ELSE M2S.Mark(23)
    END
  END ArrayType;

  PROCEDURE Type;
    VAR obj: Object;
  BEGIN
    IF sym < lparen THEN M2S.Mark(33);
      REPEAT M2S.Get(sym) UNTIL sym >= lparen
    END ;
    IF sym = array THEN
      M2S.Out(sym); M2S.Get(sym); ArrayType
    ELSIF sym = record THEN
      M2S.Out(sym); M2S.Get(sym); OpenScope;
      FieldListSequence;
      CheckSym(end, 20); CloseScope
    ELSIF sym = set THEN
      M2S.Out(sym);
      REPEAT M2S.Get(sym) UNTIL sym = semicolon
    ELSIF sym = pointer THEN
      M2S.Out(sym); M2S.Get(sym); CheckSym(to, 24);
      IF sym = ident THEN qualident(obj); makeid(obj)
      ELSE Type
      END
    ELSIF sym = procedure THEN
      M2S.Out(sym); M2S.Get(sym);
      IF sym = lparen THEN
        M2S.Out(sym); M2S.Get(sym); FormalTypeList
      END
    ELSE SimpleType
    END ;
    IF (sym < semicolon) OR (else < sym) THEN M2S.Mark(34);
      WHILE (sym < ident) OR (else < sym) & (sym < begin) DO M2S.Get(sym) END
    END
  END Type;


  PROCEDURE selector;
  BEGIN
    LOOP
      IF sym = lbrak THEN M2S.Out(sym); M2S.Get(sym);
        LOOP Expression;
          IF sym = comma THEN M2S.Out(sym); M2S.Get(sym) ELSE EXIT END
        END ;
        CheckSym(rbrak, 16)
      ELSIF sym = period THEN
        M2S.Out(sym); M2S.Get(sym);
        IF sym = ident THEN M2S.OutId; M2S.Get(sym)
        ELSE M2S.Mark(10)
        END
      ELSIF sym = arrow THEN
        M2S.Get(sym);
        IF sym # period THEN M2S.Out(arrow) END
      ELSE EXIT
      END
    END
  END selector;

  PROCEDURE ActualParameters;
  BEGIN
    IF sym # rparen THEN
      LOOP Expression;
        IF sym = comma THEN M2S.Out(sym); M2S.Get(sym) ELSE EXIT END
      END
    END
  END ActualParameters;

  PROCEDURE Element;
  BEGIN Expression;
    IF sym = ellipsis THEN
      M2S.Out(sym); M2S.Get(sym); Expression
    END ;
  END Element;

  PROCEDURE Sets;
  BEGIN 
    IF sym # rbrace THEN
      Element;
      LOOP
        IF sym = comma THEN M2S.Out(sym); M2S.Get(sym) ELSE EXIT END ;
        Element
      END
    END ;
    CheckSym(rbrace, 17)
  END Sets;

  PROCEDURE Factor;
    VAR obj: Object;
  BEGIN
    IF sym < lparen THEN M2S.Mark(31);
      REPEAT M2S.Get(sym) UNTIL sym >= lparen
    END ;
    IF sym = ident THEN
      qualident(obj);
      IF obj.class = Typ THEN
        M2S.Get(sym); Expression; M2S.Get(sym)
      ELSE makeid(obj);
        IF sym = lbrace THEN M2S.Out(sym); M2S.Get(sym); Sets
        ELSE selector;
          IF sym = lparen THEN
            M2S.Get(sym); M2S.Out(lparen); ActualParameters; CheckSym(rparen, 15)
          END
        END
      END
    ELSIF sym = number THEN M2S.OutId; M2S.Get(sym)
    ELSIF sym = string THEN  M2S.OutStr; M2S.Get(sym)
    ELSIF sym = lparen THEN
      M2S.Out(lparen); M2S.Get(sym); Expression; CheckSym(rparen, 15)
    ELSIF sym = lbrace THEN M2S.Out(sym); M2S.Get(sym); Sets
    ELSIF sym = not THEN M2S.Out(sym); M2S.Get(sym); Factor
    ELSE M2S.Mark(31)
    END
  END Factor;

  PROCEDURE Term;
  BEGIN Factor;
    WHILE (times <= sym) & (sym <= and) DO
      M2S.Out(sym); M2S.Get(sym); Factor
    END
  END Term;

  PROCEDURE SimpleExpression;
  BEGIN
    IF (sym = minus) OR (sym = plus) THEN
      M2S.Out(sym); M2S.Get(sym)
    END ;
    Term;
    WHILE (plus <= sym) & (sym <= or) DO
      M2S.Out(sym); M2S.Get(sym); Term
    END
  END SimpleExpression;

  PROCEDURE Expression;
  BEGIN SimpleExpression;
    IF (eql <= sym) & (sym <= in) THEN
      M2S.Out(sym); M2S.Get(sym); SimpleExpression
    END
  END Expression;

  PROCEDURE Priority;
  BEGIN
    IF sym = lbrak THEN
      REPEAT M2S.Get(sym) UNTIL sym = rbrak;
      M2S.Get(sym)
    END
  END Priority;

  PROCEDURE ImportList;
  BEGIN
    LOOP
      IF sym = ident THEN
        M2S.Get(sym)
      ELSE M2S.Mark(10)
      END ;
      IF sym = comma THEN M2S.Get(sym)
      ELSIF sym = ident THEN M2S.Mark(11)
      ELSE EXIT
      END
    END ;
    M2S.Get(sym)
  END ImportList;

  PROCEDURE ExportList;
  BEGIN
    LOOP
      IF sym = ident THEN M2S.Get(sym)
      ELSE M2S.Mark(10)
      END ;
      IF sym = comma THEN M2S.Get(sym)
      ELSE EXIT
      END
    END ;
    M2S.Get(sym)
  END ExportList;

  PROCEDURE FormalParameters;
  BEGIN
    IF (sym = ident) OR (sym = var) THEN
      LOOP 
        IF sym = var THEN M2S.Out(sym); M2S.Get(sym) END ;
        LOOP
          IF sym = ident THEN Insert(M2S.id, Var); M2S.OutId; M2S.Get(sym) ELSE M2S.Mark(10) END ;
          IF sym = comma THEN M2S.Out(sym); M2S.Get(sym) ELSE EXIT END
        END ;
        CheckSym(colon, 13); FormalType;
        IF sym = semicolon THEN M2S.Out(sym); M2S.Get(sym) ELSE EXIT END
      END
    END ;
    CheckSym(rparen, 15)
  END FormalParameters;

  PROCEDURE ProcedureDeclaration(level: INTEGER);
    VAR obj: Object;
  BEGIN
    IF isdef THEN
      M2S.Get(sym); Insert(M2S.id, Proc);
      REPEAT M2S.Get(sym) UNTIL sym = semicolon;
      M2S.Get(sym)
    ELSE M2S.Out(sym); M2S.Get(sym); M2S.OutId;
      IF (level = 0) & (ThisOne(M2S.id) # NIL) THEN M2S.OutCh("*") ELSE Insert(M2S.id, Proc) END ;
      M2S.Get(sym); OpenScope;
      IF sym = lparen THEN
        M2S.Out(sym); M2S.Get(sym); FormalParameters;
        IF sym = colon THEN
          M2S.Out(sym); M2S.Get(sym);
          IF sym = ident THEN qualident(obj); makeid(obj) ELSE M2S.Mark(10) END
        END
      END ;
      CheckSym(semicolon, 12);
      IF sym = code THEN M2S.Get(sym);
      ELSIF sym = forward THEN M2S.OutCh("^"); M2S.Get(sym); M2S.Get(sym)
      ELSE Block(level+1)
      END ;
      CheckSym(semicolon, 12); CloseScope
    END
  END ProcedureDeclaration;

  PROCEDURE ModuleDeclaration(level: INTEGER);
  BEGIN M2S.Get(sym); M2S.Get(sym);
    Insert(M2S.id, Module); Priority; M2S.Get(sym);
    WHILE (sym = from) OR (sym = import) DO
      IF sym = from THEN M2S.Get(sym);
        IF sym = ident THEN M2S.Get(sym)
        ELSE M2S.Mark(10)
        END ;
        M2S.Get(sym)
      ELSE M2S.Get(sym)
      END ;
      ImportList
    END ;
    IF sym = export THEN M2S.Get(sym);
      IF sym = qualified THEN M2S.Get(sym) END ;
      ExportList
    END ;
    Block(level);
    M2S.Get(sym)
  END ModuleDeclaration;


  PROCEDURE Block(level: INTEGER);

  PROCEDURE StatSeq;
    VAR obj: Object;
  BEGIN
    LOOP
      IF sym < ident THEN M2S.Mark(35);
        REPEAT M2S.Get(sym) UNTIL sym >= ident
      END ;
      IF sym = ident THEN
        qualident(obj); makeid(obj); selector;
        IF sym = becomes THEN M2S.Out(sym); M2S.Get(sym); Expression
        ELSIF sym = lparen THEN
          M2S.Out(sym); M2S.Get(sym); ActualParameters; CheckSym(rparen, 15)
        END
      ELSIF sym = if THEN
        M2S.Out(sym); M2S.Get(sym); Expression;
        CheckSym(then, 27); StatSeq;
        WHILE sym = elsif DO
          M2S.Out(sym); M2S.Get(sym); Expression;
          CheckSym(then, 27); StatSeq
        END ; 
        IF sym = else THEN M2S.Out(sym); M2S.Get(sym); StatSeq END ;
        CheckSym(end, 20)
      ELSIF sym = case THEN
        M2S.Out(sym); M2S.Get(sym); Expression; CheckSym(of, 23);
        LOOP
          IF sym < bar THEN
            CaseLabelList;
            CheckSym(colon, 13); StatSeq
          END ;
          IF sym = bar THEN M2S.Out(sym); M2S.Get(sym) ELSE EXIT END
        END ;
        IF sym = else THEN M2S.Out(sym); M2S.Get(sym); StatSeq END ;
        CheckSym(end, 20)
      ELSIF sym = while THEN
        M2S.Out(sym); M2S.Get(sym); Expression;
        CheckSym(do, 25); StatSeq; CheckSym(end, 20)
      ELSIF sym = repeat THEN
        M2S.Out(sym); M2S.Get(sym); StatSeq;
        IF sym = until THEN M2S.Out(sym); M2S.Get(sym); Expression ELSE M2S.Mark(26) END
      ELSIF sym = loop THEN
        M2S.Out(sym); M2S.Get(sym); StatSeq; CheckSym(end, 20)
      ELSIF sym = for THEN
        M2S.Out(sym); M2S.Get(sym);
        IF sym = ident THEN M2S.OutId; M2S.Get(sym) ELSE M2S.Mark(10) END ;
        IF sym = becomes THEN M2S.Out(sym); M2S.Get(sym) ELSE M2S.Mark(19) END ;
        Expression;
        CheckSym(to, 24); Expression;
        IF sym = by THEN M2S.Out(sym); M2S.Get(sym); Expression END ;
        CheckSym(do, 25); StatSeq; CheckSym(end, 20)
      ELSIF sym = with THEN
        M2S.OutLead;
        REPEAT M2S.Get(sym) UNTIL sym = do;
        M2S.Get(sym); StatSeq; M2S.Get(sym)
      ELSIF sym = exit THEN M2S.Out(sym); M2S.Get(sym)
      ELSIF sym = return THEN M2S.Out(sym); M2S.Get(sym);
        IF sym < semicolon THEN Expression END
      END ;
      IF sym = semicolon THEN M2S.Out(sym); M2S.Get(sym)
      ELSIF (sym <= ident) OR (if <= sym) & (sym <= for) THEN M2S.Mark(12)
      ELSE EXIT
      END
    END
  END StatSeq;

  BEGIN (*Block*)
    LOOP
      IF sym = const THEN
        M2S.Out(sym); M2S.Get(sym);
        WHILE sym = ident DO
          M2S.OutId; Insert(M2S.id, Const); M2S.Get(sym);
          IF isdef THEN M2S.OutCh("*") END ;
          IF sym = eql THEN M2S.Out(sym); M2S.Get(sym); Expression ELSE M2S.Mark(18) END ;
          CheckSym(semicolon, 12)
        END
      ELSIF sym = type THEN
        M2S.Out(sym); M2S.Get(sym);
        WHILE sym = ident DO
          M2S.OutId; Insert(M2S.id, Typ); M2S.Get(sym);
          IF isdef THEN M2S.OutCh("*") END ;
          IF sym = eql THEN M2S.Out(sym); M2S.Get(sym); Type END ;
          CheckSym(semicolon, 12)
        END
      ELSIF sym = var THEN
        M2S.Out(sym); M2S.Get(sym);
        WHILE sym = ident DO
          LOOP
            IF sym = ident THEN
              M2S.OutId; Insert(M2S.id, Var); M2S.Get(sym);
              IF isdef THEN M2S.OutCh("*") END
            ELSE M2S.Mark(10)
            END ;
            IF sym = comma THEN M2S.Out(sym); M2S.Get(sym) ELSE EXIT END
          END ;
          CheckSym(colon, 13); Type; CheckSym(semicolon, 12)
        END
      ELSIF sym = procedure THEN ProcedureDeclaration(level)
      ELSIF sym = module THEN ModuleDeclaration(level)
      ELSE
        IF (sym # begin) & (sym # end) THEN M2S.Mark(36);
          REPEAT M2S.Get(sym) UNTIL (sym >= begin) OR (sym = end)
        END ;
        IF (sym <= begin) OR (sym = eof) THEN EXIT END
      END
    END ;

    IF ~isdef THEN
      IF sym = begin THEN
        M2S.Out(sym); M2S.Get(sym); StatSeq;
      END ;
      CheckSym(end, 20);
      IF sym = ident THEN M2S.OutId; M2S.Get(sym) ELSE M2S.Mark(10) END
    END
  END Block;

  PROCEDURE CompilationUnit(VAR name: ARRAY OF CHAR);
    VAR mod: Object; first: BOOLEAN;
  BEGIN isdef := FALSE; isimp := FALSE; M2S.Get(sym);
    IF sym = definition THEN isdef := TRUE; M2S.Get(sym)
    ELSIF sym = implementation THEN isimp := TRUE; M2S.Get(sym)
    END ;
    IF sym = module THEN
      IF ~isimp THEN
        M2S.OpenViewer(name); M2S.Out(sym); M2S.Get(sym); M2S.OutId; M2S.Get(sym); Priority;
        CheckSym(semicolon, 12); topScope := universe; OpenScope
      ELSE M2S.Get(sym); (*modid*); M2S.Get(sym); M2S.Get(sym)
      END ;
        first := TRUE;
        WHILE (sym = from) OR (sym = import) DO
          IF first THEN first := FALSE; M2S.Out(import) ELSE M2S.OutCh(",") END ;
          IF sym = from THEN
            M2S.Get(sym);
            IF sym = ident THEN
              M2S.OutId; Insert(M2S.id, Module); mod := topScope.next; M2S.Get(sym)
            ELSE M2S.Mark(36)
            END ;
            M2S.Get(sym);
            LOOP
              IF sym = ident THEN
                Insert(M2S.id, Var); topScope.next.mod := mod; M2S.Get(sym)
              ELSE M2S.Mark(36)
              END ;
              IF sym = comma THEN M2S.Get(sym) ELSIF sym # ident THEN EXIT END
            END ;
            M2S.Get(sym)
          ELSE (*sym = import*) M2S.Get(sym);
            LOOP
              IF sym = ident THEN
                M2S.OutId; Insert(M2S.id, Module); M2S.Get(sym)
              ELSE M2S.Mark(36)
              END ;
              IF sym = comma THEN M2S.Out(sym); M2S.Get(sym) ELSIF sym # ident THEN EXIT END
            END ;
            M2S.Get(sym)
          END
        END ;
        IF ~first THEN M2S.OutCh(";") END ;
        IF sym = export THEN
          M2S.Get(sym); M2S.Mark(38);
          WHILE sym # semicolon DO M2S.Get(sym) END ;
          M2S.Get(sym)
        END ;
        Block(0);
        IF ~isdef THEN CheckSym(period, 17); CloseScope END ;
    ELSE M2S.Mark(28)
    END
  END CompilationUnit;

  PROCEDURE Convert*;
    VAR i: INTEGER;
      v: Viewers.Viewer;
      T: Texts.Text;
      S: Texts.Scanner;
  BEGIN v := Oberon.MarkedViewer();
    IF (v.dsc # NIL) & (v.dsc.next IS TextFrames.Frame) THEN
      Texts.OpenScanner(S, v.dsc(TextFrames.Frame).text, 0); Texts.Scan(S);
      IF S.class = Texts.Name THEN i := S.len;
        WHILE (i > 0) & (S.s[i] # ".") DO DEC(i) END ;
        INC(i); S.s[i] := "M"; INC(i); S.s[i] := "o";
        INC(i); S.s[i] := "d"; INC(i); S.s[i] := 0X;
        M2S.Open(v.dsc.next(TextFrames.Frame).text, 0);
        CompilationUnit(S.s); M2S.Close
      END
    END
  END Convert;

  PROCEDURE Enter(name: ARRAY OF CHAR; class: INTEGER);
    VAR obj: Object;
  BEGIN NEW(obj); COPY(name, obj.name); obj.class := class; obj.next := topScope.next;
    obj.dsc := NIL; topScope.next := obj
  END Enter;

BEGIN OpenScope;
  Enter("PROC", 1);
  Enter("TRUNC", 4);
  Enter("FLOAT", 4);
  Enter("VAL", 4);
  Enter("SIZE", 4);
  Enter("HIGH", 4);
  Enter("EXCL", 4);
  Enter("HALT", 4);
  Enter("INCL", 4);
  Enter("ORD", 4);
  Enter("ODD", 4);
  Enter("MAX", 4);
  Enter("MIN", 4);
  Enter("CHR", 4);
  Enter("ABS", 4);
  Enter("CAP", 4);
  Enter("DEC", 4);
  Enter("INC", 4);
  Enter("LONGINT", 1);
  Enter("BITSET", 1);
  Enter("CARDINAL", 1);
  Enter("INTEGER", 1);
  Enter("BOOLEAN", 1);
  Enter("FALSE", 0);
  Enter("TRUE", 0);
  Enter("CHAR", 1);
  Enter("REAL", 1);
  Enter("NIL", 0);
  universe := topScope;
  NEW(undefobj); undefobj.name := "UNDEF"; undefobj.class := Var
END Modula.
