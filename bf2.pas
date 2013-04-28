{$RANGECHECKS OFF}
{$OVERFLOWCHECKS OFF}
{$PACKENUM 1}
{$M 16777216,33554432}

PROGRAM boolean_functions;

(*
 * Copyright (c) 1988-2007 Antonio Costa.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms are permitted
 * provided that the above copyright notice and this paragraph are
 * duplicated in all such forms and that any documentation,
 * advertising materials, and other materials related to such
 * distribution and use acknowledge that the software was developed
 * by Antonio Costa. The name of the author may not be used to endorse
 * or promote products derived from this software without specific
 * prior written permission.
 * THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE IMPLIED
 * WARRANTIES OF MERCHANTIBILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 *)
(*
   BOOLEAN FUNCTIONS - QUINE McCLUSKEY MINIMIZATION

   Version 12.3 - Global Outputs

   Made by    : ANTONIO COSTA, PORTO, DECEMBER 1986
   Modified by: ANTONIO COSTA, PORTO, AUGUST 2007
*)

LABEL
  end_of_program;

CONST
  variable_max=16;
  multiple_max=16;

  term_max=65536;
  prime_max=131072; (* NOTE: Value bellow specification *)
  cube_max=131072;  (* NOTE: Value bellow specification *)

  count1_max=12870;
  count2_max=2018016;

  product_max=65536; (* NOTE: Value bellow specification *)

  char_max=5;

  line_max=(5+char_max)*SUCC(variable_max);

  space=' ';
  tab=CHR(9);
  marker='#';

  assign_op='=';
  invert_op='/';
  or_op='+';
  and_op='*';

  high='H';
  low='L';
  zero='0';
  one='1';
  dont_care='X';

  common1_name='TERM_';
  common2_name='PRIME_';
  common2_len=LENGTH(common2_name);

TYPE
  signal=RECORD
           state:BOOLEAN;
           name:STRING[char_max]
         END;

  input_value=(sN,s0,s1,sX);
  input_code=PACKED ARRAY[1..variable_max] OF input_value;
  output_code=PACKED ARRAY[1..multiple_max] OF BOOLEAN;
  pointer=0..prime_max;
  pointer_table=PACKED ARRAY[1..product_max] OF pointer;

VAR
  (* global variables *)
  inpsignal:ARRAY[1..variable_max] OF signal;
  outsignal:ARRAY[1..multiple_max] OF signal;
  outlevel:PACKED ARRAY[1..multiple_max] OF BOOLEAN;
  termtotal:PACKED ARRAY[0..multiple_max] OF 0..term_max;
  mterm:PACKED ARRAY[1..term_max] OF input_code;
  check:PACKED ARRAY[1..term_max] OF output_code;
  primeimp:PACKED ARRAY[0..prime_max] OF input_code;
  outcode:PACKED ARRAY[0..prime_max] OF output_code;
  essential:PACKED ARRAY[1..prime_max] OF BOOLEAN;
  petrick:PACKED ARRAY[1..prime_max] OF pointer;
  count:pointer_table;
  i,j,k,l,m,n,o:LONGINT;
  variable,multiple,term,prime,product:LONGINT;
  flag1,flag2,table_flag,stats_flag:BOOLEAN;
  equat_flag:LONGINT;

  (* "generate_primes" variables *)
  outcode1,outcode2:PACKED ARRAY[1..cube_max] OF output_code;

  runtime_error_flag:BOOLEAN;

PROCEDURE exit_proc;

BEGIN
IF runtime_error_flag THEN
  BEGIN
  WRITELN;
  WRITELN('***** RUNTIME ERROR: too much data or out of memory');
  WRITELN
  END;
ExitCode:=0;
ErrorAddr:=NIL
END;

FUNCTION max(A,B:LONGINT):LONGINT;

BEGIN
IF A>B THEN
  max:=A
ELSE
  max:=B
END;

PROCEDURE runtime_abort(error:LONGINT);

BEGIN
WRITELN;
WRITE('***** RUNTIME ERROR: ');
CASE error OF
  1:
    WRITELN('too many sub-cubes');
  2:
    WRITELN('too many prime imps');
  3:
    WRITELN('too many petrick products')
  END;
WRITELN;
GOTO end_of_program
END;

PROCEDURE input_data;

VAR
  inpterm,temp:PACKED ARRAY[1..term_max] OF input_code;
  code01,codeX:PACKED ARRAY[0..term_max] OF output_code;
  termtable:PACKED ARRAY[1..term_max] OF BOOLEAN;
  ones:PACKED ARRAY[1..term_max] OF 0..variable_max;
  group:PACKED ARRAY[0..variable_max] OF 0..count1_max;
  lin,col:LONGINT;
  c:CHAR;

PROCEDURE input_abort(error:LONGINT);

BEGIN
WRITE('***** INPUT ERROR: ');
CASE error OF
  0:
    WRITE('unable to read input');
  1:
    WRITE('no block marker [',marker,'] found');
  2:
    WRITE('illegal input variable');
  3:
    WRITE('too many input variables');
  4:
    WRITE('illegal output variable');
  5:
    WRITE('too many output variables');
  6:
    WRITE('wrong mode option');
  7:
    WRITE('wrong table option');
  8:
    WRITE('wrong equations option');
  9:
    WRITE('wrong statistics option');
  10:
    WRITE('illegal input term definition');
  11:
    WRITE('illegal output term definition')
  END;
IF error>0 THEN
  WRITE(' (line ',lin:0,', column ',col:0,')');
WRITELN;
GOTO end_of_program
END;

PROCEDURE read_ch(VAR ch:CHAR;error:LONGINT);

BEGIN
IF EOF OR EOLN THEN
  input_abort(error);
READ(ch);
col:=SUCC(col)
END;

PROCEDURE read_ln(error:LONGINT);

BEGIN
IF EOF THEN
  input_abort(error);
READLN;
col:=0;
lin:=SUCC(lin)
END;

FUNCTION uppercase(ch:CHAR):CHAR;

BEGIN
IF ch IN ['a'..'z'] THEN
  uppercase:=CHR(ORD('A')+ORD(ch)-ORD('a'))
ELSE
  uppercase:=ch
END;

PROCEDURE skip_comments(flag:BOOLEAN;error:LONGINT);

BEGIN
IF flag THEN
  read_ln(error);
REPEAT
  WHILE EOLN DO
    read_ln(error);
  read_ch(c,error);
  read_ln(error)
UNTIL c=marker
END;

PROCEDURE get_signal(VAR s:signal;error:LONGINT);

BEGIN
WITH s DO
  BEGIN
  name:='';
  WHILE c IN [space,tab] DO
    read_ch(c,error);
  WHILE NOT (c IN [space,tab]) OR (name='') DO
    BEGIN
    IF LENGTH(name)<char_max THEN
    IF uppercase(c) IN ['A'..'Z','0'..'9'] THEN
       name:=name+c;
    read_ch(c,error)
    END;
  REPEAT
    read_ch(c,error);
    c:=uppercase(c)
  UNTIL c IN [low,high];
  state:=c=high
  END
END;

FUNCTION term_value:LONGINT;

VAR
  value,weight,z:LONGINT;

BEGIN
value:=1;
weight:=1;
FOR z:=1 TO variable DO
  BEGIN
  IF temp[j,z]=s1 THEN
    value:=value+weight;
  weight:=2*weight
  END;
term_value:=value
END;

FUNCTION valid_output:BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

BEGIN
z:=0;
REPEAT
  z:=SUCC(z);
  flag:=code01[j,z]
UNTIL (z=multiple) OR flag;
valid_output:=flag
END;

BEGIN
lin:=1;
col:=0;
skip_comments(FALSE,1);
variable:=0;
read_ch(c,2);
REPEAT
  variable:=SUCC(variable);
  IF variable>variable_max THEN
    input_abort(3);
  get_signal(inpsignal[variable],2);
  read_ln(1);
  read_ch(c,1)
UNTIL c=marker;
read_ln(4);
multiple:=0;
read_ch(c,4);
REPEAT
  multiple:=SUCC(multiple);
  IF multiple>multiple_max THEN
    input_abort(5);
  get_signal(outsignal[multiple],4);
  REPEAT
    read_ch(c,4)
  UNTIL c IN [zero,one];
  outlevel[multiple]:=c=one;
  read_ln(1);
  read_ch(c,1)
UNTIL c=marker;
read_ln(6);
REPEAT
  read_ch(c,6)
UNTIL c IN [zero..'6'];
flag1:=c<>zero;
o:=ORD(c)-ORD(zero);
read_ln(7);
REPEAT
  read_ch(c,7)
UNTIL c IN [zero,one];
table_flag:=c=one;
read_ln(8);
REPEAT
  read_ch(c,8)
UNTIL c IN [zero..'4'];
equat_flag:=ORD(c)-ORD(zero);
read_ln(9);
REPEAT
  read_ch(c,9)
UNTIL c IN [zero,one];
stats_flag:=c=one;
skip_comments(TRUE,1);
FOR i:=1 TO 2**variable DO
  termtable[i]:=FALSE;
FOR i:=0 TO variable DO
  group[i]:=0;
WHILE NOT EOF DO
  BEGIN
  n:=0;
  FOR j:=1 TO variable DO
    BEGIN
    REPEAT
      read_ch(c,10);
      c:=uppercase(c)
    UNTIL c IN [zero,one,dont_care];
    CASE c OF
      zero:
        temp[1,j]:=s0;
      one:
        temp[1,j]:=s1;
      dont_care:
        BEGIN
        temp[1,j]:=sX;
        n:=SUCC(n)
        END
      END
    END;
  FOR j:=1 TO multiple DO
    BEGIN
    REPEAT
      read_ch(c,11);
      c:=uppercase(c)
    UNTIL c IN [zero,one,dont_care];
    IF outlevel[j] THEN
      code01[0,j]:=c<>zero
    ELSE
      code01[0,j]:=c<>one;
    codeX[0,j]:=c<>dont_care
    END;
  i:=1;
  FOR j:=1 TO n DO
    BEGIN
    k:=i;
    FOR l:=1 TO k DO
      BEGIN
      m:=1;
      WHILE temp[l,m]<>sX DO
        m:=SUCC(m);
      i:=SUCC(i);
      temp[l,m]:=s0;
      temp[i]:=temp[l];
      temp[i,m]:=s1
      END
    END;
  FOR j:=1 TO i DO
    BEGIN
    k:=term_value;
    IF flag1 AND termtable[k] THEN
    FOR l:=1 TO multiple DO
    CASE o OF
      1:
        BEGIN
        code01[k,l]:=code01[k,l] AND code01[0,l];
        codeX[k,l]:=codeX[k,l] AND codeX[0,l] OR NOT code01[k,l]
                    OR NOT code01[0,l]
        END;
      2:
        BEGIN
        code01[k,l]:=code01[k,l] AND code01[0,l];
        codeX[k,l]:=codeX[k,l] OR codeX[0,l]
        END;
      3:
        BEGIN
        code01[k,l]:=code01[k,l] AND code01[0,l] OR NOT codeX[k,l]
                     OR NOT codeX[0,l];
        codeX[k,l]:=codeX[k,l] AND codeX[0,l]
        END;
      4:
        BEGIN
        code01[k,l]:=code01[k,l] OR code01[0,l];
        codeX[k,l]:=codeX[k,l] AND codeX[0,l]
        END;
      5:
        BEGIN
        code01[k,l]:=code01[k,l] AND code01[0,l] OR code01[k,l]
                     AND codeX[k,l] OR code01[0,l] AND codeX[0,l];
        codeX[k,l]:=codeX[k,l] OR codeX[0,l]
        END;
      6:
        BEGIN
        code01[k,l]:=code01[k,l] OR code01[0,l];
        codeX[k,l]:=codeX[k,l] AND codeX[0,l] OR code01[k,l] AND codeX[k,l]
                    OR code01[0,l] AND codeX[0,l]
        END
      END
    ELSE
      BEGIN
      IF NOT termtable[k] THEN
        BEGIN
        termtable[k]:=TRUE;
        inpterm[k]:=temp[j];
        l:=0;
        FOR m:=1 TO variable DO
        IF inpterm[k,m]=s1 THEN
          l:=SUCC(l);
        ones[k]:=l;
        group[l]:=SUCC(group[l])
        END;
      code01[k]:=code01[0];
      codeX[k]:=codeX[0]
      END
    END;
  read_ln(11)
  END;
IF stats_flag THEN
FOR i:=1 TO multiple DO
  termtotal[i]:=0;
term:=0;
FOR i:=0 TO variable DO
  BEGIN
  j:=0;
  WHILE group[i]>0 DO
    BEGIN
    j:=SUCC(j);
    IF termtable[j] THEN
    IF ones[j]=i THEN
      BEGIN
      IF valid_output THEN
        BEGIN
        term:=SUCC(term);
        mterm[term]:=inpterm[j];
        outcode[term]:=code01[j];
        IF stats_flag THEN
        FOR k:=1 TO multiple DO
        IF outcode[term,k] THEN
          termtotal[k]:=SUCC(termtotal[k]);
        check[term]:=codeX[j]
        END;
      group[i]:=PRED(group[i]);
      termtable[j]:=FALSE
      END
    END
  END
END;

PROCEDURE generate_primes;

VAR
  term1,term2:PACKED ARRAY[1..cube_max] OF input_code;
  ones1,ones2:PACKED ARRAY[0..cube_max] OF 0..variable_max;
  group1,group2:PACKED ARRAY[0..variable_max] OF 0..count2_max;
  (* outcode1,outcode2:PACKED ARRAY[1..cube_max] OF output_code; *)
  primeflag1,primeflag2:PACKED ARRAY[1..cube_max] OF BOOLEAN;

FUNCTION terms_combine:BOOLEAN;

VAR
  diff,z:LONGINT;

BEGIN
diff:=0;
z:=0;
REPEAT
  z:=SUCC(z);
  IF term1[l,z]<>term1[m,z] THEN
    diff:=SUCC(diff)
UNTIL (z=variable) OR (diff>1);
terms_combine:=diff=1
END;

FUNCTION groups_combine:BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

BEGIN
z:=0;
REPEAT
  z:=SUCC(z);
  flag:=(group1[PRED(z)]>0) AND (group1[z]>0)
UNTIL (z=variable) OR flag;
groups_combine:=flag
END;

FUNCTION common_output:BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

BEGIN
z:=0;
REPEAT
  z:=SUCC(z);
  flag:=outcode1[l,z] AND outcode1[m,z]
UNTIL (z=multiple) OR flag;
common_output:=flag
END;

FUNCTION different_output(x:output_code):BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

BEGIN
z:=0;
REPEAT
  z:=SUCC(z);
  flag:=outcode2[j,z]<>x[z]
UNTIL (z=multiple) OR flag;
different_output:=flag
END;

FUNCTION found_before:BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

FUNCTION equal_input:BOOLEAN;

VAR
  flag:BOOLEAN;
  w:LONGINT;

BEGIN
w:=0;
REPEAT
  w:=SUCC(w);
  flag:=term2[j,w]<>term2[z,w]
UNTIL (w=variable) OR flag;
equal_input:=NOT flag
END;

BEGIN
IF j=1 THEN
  found_before:=FALSE
ELSE
  BEGIN
  z:=0;
  REPEAT
    z:=SUCC(z);
    flag:=equal_input
  UNTIL (z=PRED(j)) OR flag;
  found_before:=flag
  END
END;

BEGIN
FOR i:=0 TO variable DO
  group1[i]:=0;
FOR i:=1 TO term DO
  BEGIN
  term1[i]:=mterm[i];
  o:=0;
  FOR j:=1 TO variable DO
  IF term1[i,j]=s1 THEN
    o:=SUCC(o);
  ones1[i]:=o;
  group1[o]:=SUCC(group1[o]);
  outcode1[i]:=outcode[i];
  primeflag1[i]:=TRUE;
  FOR j:=1 TO multiple DO
    check[i,j]:=check[i,j] AND outcode[i,j]
  END;
ones1[0]:=0;
ones2[0]:=0;
i:=term;
prime:=0;
flag1:=groups_combine;
WHILE flag1 DO
  BEGIN
  FOR l:=0 TO variable DO
    group2[l]:=0;
  j:=0;
  k:=1;
  FOR l:=1 TO i-group1[ones1[i]] DO
    BEGIN
    IF (ones1[l]>ones1[PRED(l)]) OR (l=1) THEN
      BEGIN
      k:=k+group1[ones1[l]];
      o:=PRED(k)+group1[SUCC(ones1[l])]
      END;
    FOR m:=k TO o DO
    IF common_output THEN
    IF terms_combine THEN
      BEGIN
      j:=SUCC(j);
      IF j>cube_max THEN
        runtime_abort(1);
      term2[j]:=term1[l];
      n:=1;
      WHILE term1[l,n]=term1[m,n] DO
        n:=SUCC(n);
      term2[j,n]:=sX;
      outcode2[j]:=outcode1[l];
      FOR n:=1 TO multiple DO
        outcode2[j,n]:=outcode2[j,n] AND outcode1[m,n];
      primeflag1[l]:=primeflag1[l] AND different_output(outcode1[l]);
      primeflag1[m]:=primeflag1[m] AND different_output(outcode1[m]);
      IF found_before THEN
        j:=PRED(j)
      ELSE
        BEGIN
        ones2[j]:=ones1[l];
        group2[ones2[j]]:=SUCC(group2[ones2[j]]);
        primeflag2[j]:=TRUE
        END
      END;
    IF primeflag1[l] THEN
      BEGIN
      prime:=SUCC(prime);
      IF prime>prime_max THEN
        runtime_abort(2);
      primeimp[prime]:=term1[l];
      outcode[prime]:=outcode1[l]
      END
    END;
  FOR l:=k TO i DO
  IF primeflag1[l] THEN
    BEGIN
    prime:=SUCC(prime);
    IF prime>prime_max THEN
      runtime_abort(2);
    primeimp[prime]:=term1[l];
    outcode[prime]:=outcode1[l]
    END;
  i:=j;
  IF i>0 THEN
    BEGIN
    term1:=term2;
    outcode1:=outcode2;
    group1:=group2;
    flag1:=groups_combine;
    IF flag1 THEN
      BEGIN
      ones1:=ones2;
      primeflag1:=primeflag2
      END
    END
  ELSE
    flag1:=FALSE
  END;
FOR j:=1 TO i DO
  BEGIN
  prime:=SUCC(prime);
  IF prime>prime_max THEN
    runtime_abort(2);
  primeimp[prime]:=term1[j];
  outcode[prime]:=outcode1[j]
  END;
WRITELN('Total Prime Imps      : ',prime:0)
END;

PROCEDURE reduce_primes;

VAR
  removed:PACKED ARRAY[1..prime_max] OF BOOLEAN;
  repeated:PACKED ARRAY[1..prime_max] OF 0..product_max;
  flag3:BOOLEAN;

FUNCTION in_column(x:LONGINT):BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

BEGIN
z:=0;
REPEAT
  z:=SUCC(z);
  flag:=check[x,z]
UNTIL (z=multiple) OR flag;
in_column:=flag
END;

FUNCTION in_table(x,y:LONGINT):BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

BEGIN
IF in_column(y) THEN
  BEGIN
  z:=0;
  REPEAT
    z:=SUCC(z);
    flag:=(primeimp[x,z]<>sX) AND (primeimp[x,z]<>mterm[y,z])
  UNTIL (z=variable) OR flag;
  in_table:=NOT flag
  END
ELSE
  in_table:=FALSE
END;

FUNCTION equal_output:BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

BEGIN
z:=0;
REPEAT
  z:=SUCC(z);
  flag:=outcode[i,z] AND NOT outcode[j,z]
UNTIL (z=multiple) OR flag;
equal_output:=NOT flag
END;

FUNCTION less_cost:BOOLEAN;

VAR
  diff,z:LONGINT;

BEGIN
diff:=0;
FOR z:=1 TO variable DO
  BEGIN
  IF primeimp[i,z]=sX THEN
    diff:=SUCC(diff);
  IF primeimp[j,z]=sX THEN
    diff:=PRED(diff)
  END;
less_cost:=diff<=0
END;

FUNCTION covers:BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

BEGIN
z:=0;
REPEAT
  z:=SUCC(z);
  flag:=in_table(i,z) AND NOT in_table(j,z)
UNTIL (z=term) OR flag;
covers:=NOT flag
END;

BEGIN
FOR i:=1 TO prime DO
  BEGIN
  essential[i]:=FALSE;
  removed[i]:=FALSE
  END;
REPEAT
  FOR i:=1 TO multiple DO
  FOR j:=1 TO term DO
  IF check[j,i] THEN
    BEGIN
    k:=0;
    l:=0;
    REPEAT
      k:=SUCC(k);
      IF NOT removed[k] AND outcode[k,i] AND in_table(k,j) THEN
        BEGIN
        l:=SUCC(l);
        o:=k
        END
    UNTIL (l=2) OR (k=prime);
    IF l=0 THEN
      check[j,i]:=FALSE
    ELSE
    IF l=1 THEN
      BEGIN
      essential[o]:=TRUE;
      removed[o]:=TRUE;
      FOR m:=1 TO term DO
      IF in_table(o,m) THEN
      FOR n:=1 TO multiple DO
      IF outcode[o,n] THEN
        check[m,n]:=FALSE
      END
    END;
  i:=0;
  REPEAT
    i:=SUCC(i);
    flag1:=in_column(i)
  UNTIL (i=term) OR flag1;
  flag2:=FALSE;
  IF flag1 THEN
    BEGIN
    FOR i:=1 TO prime DO
    IF NOT removed[i] THEN
      BEGIN
      j:=0;
      REPEAT
        j:=SUCC(j);
        flag3:=in_table(i,j)
      UNTIL (j=term) OR flag3;
      removed[i]:=NOT flag3
      END;
    FOR i:=1 TO prime DO
    IF NOT removed[i] THEN
      BEGIN
      flag3:=FALSE;
      j:=0;
      REPEAT
        j:=SUCC(j);
        IF (j<>i) AND NOT removed[j] THEN
        IF equal_output THEN
        IF less_cost THEN
        IF covers THEN
          BEGIN
          removed[i]:=TRUE;
          flag2:=TRUE;
          flag3:=TRUE
          END
      UNTIL (j=prime) OR flag3
      END
    END
UNTIL NOT flag2;
n:=0;
FOR i:=1 TO prime DO
IF essential[i] THEN
  n:=SUCC(n);
WRITELN('1st reduced Prime Imps: ',n:0);
n:=0;
WHILE flag1 DO
  BEGIN
  flag1:=FALSE;
  flag2:=FALSE;
  FOR i:=1 TO prime DO
    repeated[i]:=0;
  FOR i:=1 TO term DO
  IF in_column(i) THEN
  FOR j:=1 TO multiple DO
  IF check[i,j] THEN
  FOR k:=1 TO prime DO
  IF NOT removed[k] AND outcode[k,j] AND in_table(k,i) THEN
    BEGIN
    repeated[k]:=SUCC(repeated[k]);
    flag2:=TRUE
    END;
  IF flag2 THEN
    BEGIN
    i:=2;
    j:=-1;
    FOR k:=1 TO prime DO
    IF repeated[k]>i THEN
      BEGIN
      i:=repeated[k];
      o:=k;
      flag1:=TRUE
      END
    ELSE
    IF repeated[k]=i THEN
      BEGIN
      l:=0;
      FOR m:=1 TO variable DO
      IF primeimp[k,m]=sX THEN
        l:=SUCC(l);
      IF l>j THEN
        BEGIN
        o:=k;
        j:=l;
        flag1:=TRUE
        END
      END;
    IF flag1 THEN
      BEGIN
      n:=SUCC(n);
      essential[o]:=TRUE;
      removed[o]:=TRUE;
      FOR i:=1 TO term DO
      IF in_table(o,i) THEN
      FOR j:=1 TO multiple DO
      IF outcode[o,j] THEN
        check[i,j]:=FALSE
      END
    END
  END;
WRITELN('2nd reduced Prime Imps: ',n:0);
product:=0;
IF flag2 THEN
  BEGIN
  i:=1;
  FOR j:=1 TO term DO
  IF in_column(j) THEN
  FOR k:=1 TO multiple DO
  IF check[j,k] THEN
    BEGIN
    product:=SUCC(product);
    IF product>product_max THEN
      runtime_abort(3);
    count[product]:=0;
    FOR l:=1 TO prime DO
    IF NOT removed[l] AND outcode[l,k] AND in_table(l,j) THEN
      BEGIN
      count[product]:=SUCC(count[product]);
      petrick[i]:=l;
      i:=SUCC(i)
      END
    END
  END;
WRITELN('3rd reduced Prime Imps: ',product:0)
END;

PROCEDURE petrick_primes;

VAR
  best:pointer;

BEGIN
m:=0;
FOR i:=1 TO product DO
  BEGIN
  n:=-1;
  FOR j:=1 TO count[i] DO
    BEGIN
    m:=SUCC(m);
    o:=petrick[m];
    k:=0;
    l:=0;
    REPEAT
      k:=SUCC(k);
      IF primeimp[o,k]=sX THEN
        l:=SUCC(l)
    UNTIL k>=variable-max(n-l,0);
    IF l>n THEN
      BEGIN
      n:=l;
      best:=o
      END
    END;
  essential[best]:=TRUE
  END
END;

PROCEDURE simplify_primes;

VAR
  termtable:PACKED ARRAY[1..term_max] OF BOOLEAN;
  bit01,bitX:PACKED ARRAY[1..variable_max] OF BOOLEAN;

FUNCTION common_terms:BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

BEGIN
z:=0;
REPEAT
  z:=SUCC(z);
  flag:=(primeimp[i,z]<>sX) AND (primeimp[k,z]<>sX) AND (primeimp[i,z]<>primeimp[k,z])
UNTIL (z=variable) OR flag;
common_terms:=NOT flag
END;

PROCEDURE set_up(x:input_code);

VAR
  z:LONGINT;

BEGIN
flag2:=TRUE;
FOR z:=1 TO variable DO
CASE x[z] OF
  s0:
    BEGIN
    bit01[z]:=FALSE;
    bitX[z]:=FALSE
    END;
  s1:
    BEGIN
    bit01[z]:=TRUE;
    bitX[z]:=FALSE
    END;
  sX:
    BEGIN
    bit01[z]:=FALSE;
    bitX[z]:=TRUE;
    flag2:=FALSE
    END
  END
END;

FUNCTION term_value:LONGINT;

VAR
  value,weight,z:LONGINT;

BEGIN
value:=1;
weight:=1;
FOR z:=1 TO variable DO
  BEGIN
  IF bit01[z] THEN
    value:=value+weight;
  weight:=2*weight
  END;
term_value:=value
END;

PROCEDURE next_term;

VAR
  z:LONGINT;

BEGIN
z:=0;
REPEAT
  z:=SUCC(z);
  IF bitX[z] THEN
    BEGIN
    bit01[z]:=NOT bit01[z];
    flag2:=bit01[z]
    END
UNTIL (z=variable) OR flag2
END;

PROCEDURE fill_termtable;

BEGIN
set_up(primeimp[k]);
IF flag2 THEN
  termtable[term_value]:=TRUE
ELSE
REPEAT
  termtable[term_value]:=TRUE;
  flag2:=FALSE;
  next_term
UNTIL NOT flag2
END;

FUNCTION redundant:BOOLEAN;

VAR
  flag:BOOLEAN;

BEGIN
set_up(primeimp[i]);
IF flag2 THEN
  redundant:=TRUE
ELSE
  BEGIN
  REPEAT
    flag2:=FALSE;
    flag:=termtable[term_value];
    IF flag THEN
      next_term
  UNTIL NOT flag OR NOT flag2;
  redundant:=flag
  END
END;

BEGIN
n:=0;
FOR i:=1 TO prime DO
IF essential[i] THEN
  BEGIN
  flag1:=FALSE;
  FOR j:=1 TO multiple DO
  IF outcode[i,j] THEN
    BEGIN
    flag2:=FALSE;
    k:=0;
    REPEAT
      k:=SUCC(k);
      IF (i<>k) AND essential[k] AND outcode[k,j] THEN
      IF common_terms THEN
        BEGIN
        FOR o:=1 TO 2**variable DO
          termtable[o]:=FALSE;
        fill_termtable;
        flag2:=redundant
        END
    UNTIL (k=prime) OR flag2;
    outcode[i,j]:=NOT flag2;
    flag1:=flag1 OR NOT flag2
    END;
  essential[i]:=flag1;
  IF NOT flag1 THEN
    n:=SUCC(n)
  END;
WRITELN('<Redundant> Prime Imps: ',n:0)
END;

PROCEDURE sort_primes;

FUNCTION reverse_order:BOOLEAN;

VAR
  flag:BOOLEAN;
  diff,z:LONGINT;

BEGIN
diff:=0;
FOR z:=1 TO multiple DO
  BEGIN
  IF outcode[j,z] THEN
    diff:=SUCC(diff);
  IF outcode[SUCC(j),z] THEN
    diff:=PRED(diff)
  END;
IF diff<>0 THEN
  reverse_order:=diff<0
ELSE
  BEGIN
  z:=0;
  REPEAT
    z:=SUCC(z);
    flag:=outcode[j,z]<>outcode[SUCC(j),z]
  UNTIL (z=multiple) OR flag;
  reverse_order:=flag AND NOT outcode[j,z]
  END
END;

BEGIN
i:=0;
FOR j:=1 TO prime DO
IF essential[j] THEN
  BEGIN
  i:=SUCC(i);
  primeimp[i]:=primeimp[j];
  outcode[i]:=outcode[j]
  END;
prime:=i;
FOR i:=1 TO prime DIV 2 DO
  BEGIN
  j:=SUCC(prime)-i;
  primeimp[0]:=primeimp[i];
  outcode[0]:=outcode[i];
  primeimp[i]:=primeimp[j];
  outcode[i]:=outcode[j];
  primeimp[j]:=primeimp[0];
  outcode[j]:=outcode[0]
  END;
FOR i:=1 TO PRED(prime) DO
FOR j:=1 TO prime-i DO
IF reverse_order THEN
  BEGIN
  k:=SUCC(j);
  primeimp[0]:=primeimp[k];
  outcode[0]:=outcode[k];
  primeimp[k]:=primeimp[j];
  outcode[k]:=outcode[j];
  primeimp[j]:=primeimp[0];
  outcode[j]:=outcode[0]
  END;
WRITELN('<Essential> Prime Imps: ',prime:0)
END;

PROCEDURE output_data;

VAR
  flag3:BOOLEAN;

PROCEDURE truth_table;

BEGIN
WRITELN('##### Truth Table');
WRITELN;
IF prime>0 THEN
  BEGIN
  FOR i:=1 TO prime DO
    BEGIN
    FOR j:=1 TO variable DO
    CASE primeimp[i,j] OF
      s0:
        WRITE(zero);
      s1:
        WRITE(one);
      sX:
        WRITE(dont_care)
      END;
    WRITE(space);
    FOR j:=1 TO multiple DO
    IF outlevel[j]=outcode[i,j] THEN
      WRITE(one)
    ELSE
      WRITE(zero);
    WRITELN
    END
  END
ELSE
  WRITELN('None');
WRITELN
END;

PROCEDURE equations;

VAR
  common1,common2,primetable:PACKED ARRAY[1..prime_max] OF pointer;

FUNCTION prime_pointer:LONGINT;

VAR
  order,order_max,p,z:LONGINT;

FUNCTION prime_order(p:LONGINT):LONGINT;

VAR
  order,z:LONGINT;

BEGIN
order:=variable;
FOR z:=1 TO variable DO
IF primeimp[p,z]=sX THEN
  order:=PRED(order);
prime_order:=order
END;

FUNCTION covers_prime(p:LONGINT):BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

BEGIN
z:=0;
REPEAT
  z:=SUCC(z);
  flag:=(primeimp[p,z]<>sX) AND (primeimp[p,z]<>primeimp[j,z])
UNTIL (z=variable) OR flag;
covers_prime:=NOT flag
END;

BEGIN
prime_pointer:=0;
order:=PRED(prime_order(j));
IF order>1 THEN
  BEGIN
  order_max:=1;
  z:=0;
  REPEAT
    z:=SUCC(z);
    IF z<>j THEN
    IF covers_prime(z) THEN
    IF prime_order(z)>order_max THEN
      BEGIN
      order_max:=prime_order(z);
      p:=z
      END
  UNTIL (z=prime) OR (order=order_max);
  IF order_max>1 THEN
    prime_pointer:=p
  END
END;

FUNCTION common_outputs:BOOLEAN;

VAR
  flag:BOOLEAN;
  x,z:LONGINT;

BEGIN
flag:=FALSE;
x:=0;
REPEAT
  x:=SUCC(x);
  IF outcode[j,x] THEN
    BEGIN
    z:=x;
    REPEAT
      z:=SUCC(z);
      flag:=outcode[j,z]
    UNTIL (z=multiple) OR flag
  END
UNTIL (x=PRED(multiple)) OR flag;
common_outputs:=flag
END;

FUNCTION different_outputs:BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

BEGIN
IF j=1 THEN
  different_outputs:=TRUE
ELSE
  BEGIN
  z:=0;
  REPEAT
    z:=SUCC(z);
    flag:=outcode[j,z]<>outcode[PRED(j),z]
  UNTIL (z=multiple) OR flag;
  different_outputs:=flag
  END
END;

BEGIN
WRITE('##### Boolean Equation');
IF multiple>1 THEN
  WRITELN('s');
FOR i:=1 TO prime DO
  common1[i]:=0;
IF equat_flag>=3 THEN
  BEGIN
  i:=0;
  FOR j:=1 TO prime DO
    BEGIN
    k:=prime_pointer;
    primetable[j]:=k;
    IF k<>0 THEN
    IF common1[k]=0 THEN
      BEGIN
      i:=SUCC(i);
      common1[k]:=i;
      WRITELN;
      WRITE(common1_name,i:0,assign_op);
      flag3:=FALSE;
      FOR l:=1 TO variable DO
      WITH inpsignal[l] DO
      IF primeimp[k,l] IN [s0,s1] THEN
        BEGIN
        IF flag3 THEN
          WRITE(and_op);
        IF (primeimp[k,l]=s0)=state THEN
          WRITE(invert_op);
        WRITE(name);
        flag3:=TRUE
        END;
      WRITELN
      END
    END;
  WRITELN;
  IF i=0 THEN
    WRITE('No')
  ELSE
    WRITE(i:0);
  WRITE(' Term Common Expression');
  IF i<>1 THEN
    WRITELN('s')
  END
ELSE
FOR i:=1 TO prime DO
  primetable[i]:=0;
IF equat_flag>=2 THEN
  BEGIN
  i:=0;
  j:=1;
  WHILE (j<=prime) AND common_outputs DO
    BEGIN
    IF (equat_flag<=3) OR different_outputs THEN
      BEGIN
      i:=SUCC(i);
      WRITELN;
      WRITE(common2_name,i:0,assign_op);
      k:=common2_len+SUCC(TRUNC(LN(i)/LN(10)))
      END
    ELSE
      WRITE(space:k,or_op);
    common2[j]:=i;
    IF common1[j]<>0 THEN
      WRITE(common1_name,common1[j]:0)
    ELSE
    IF primetable[j]<>0 THEN
      BEGIN
      m:=primetable[j];
      WRITE(common1_name,common1[m]:0);
      FOR l:=1 TO variable DO
      IF primeimp[j,l]<>primeimp[m,l] THEN
      WITH inpsignal[l] DO
      IF primeimp[j,l] IN [s0,s1] THEN
        BEGIN
        WRITE(and_op);
        IF (primeimp[j,l]=s0)=state THEN
          WRITE(invert_op);
        WRITE(name)
        END
      END
    ELSE
      BEGIN
      l:=0;
      REPEAT
        l:=SUCC(l);
        flag2:=primeimp[j,l]<>sX
      UNTIL (l=variable) OR flag2;
      IF flag2 THEN
        BEGIN
        flag3:=FALSE;
        FOR l:=1 TO variable DO
        WITH inpsignal[l] DO
        IF primeimp[j,l] IN [s0,s1] THEN
          BEGIN
          IF flag3 THEN
            WRITE(and_op);
          IF (primeimp[j,l]=s0)=state THEN
            WRITE(invert_op);
          WRITE(name);
          flag3:=TRUE
          END
        END
      ELSE
        WRITE(one)
      END;
    j:=SUCC(j);
    WRITELN
    END;
  FOR k:=j TO prime DO
    common2[k]:=0;
  WRITELN;
  IF i=0 THEN
    WRITE('No')
  ELSE
    WRITE(i:0);
  WRITE(' Prime Imps Common Expression');
  IF i<>1 THEN
    WRITELN('s')
  END
ELSE
FOR i:=1 TO prime DO
  common2[i]:=0;
FOR i:=1 TO multiple DO
  BEGIN
  WRITELN;
  WITH outsignal[i] DO
    BEGIN
    IF outlevel[i]=state THEN
      k:=LENGTH(name)
    ELSE
      BEGIN
      WRITE(invert_op);
      k:=SUCC(LENGTH(name))
      END;
    WRITE(name,assign_op)
    END;
  flag1:=TRUE;
  flag2:=TRUE;
  j:=0;
  REPEAT
    j:=SUCC(j);
    IF outcode[j,i] THEN
    IF common2[j]=0 THEN
      BEGIN
      IF NOT flag1 THEN
        BEGIN
        WRITELN;
        WRITE(space:k,or_op)
        END;
      flag1:=FALSE;
      IF common1[j]<>0 THEN
        WRITE(common1_name,common1[j]:0)
      ELSE
      IF primetable[j]<>0 THEN
        BEGIN
        m:=primetable[j];
        WRITE(common1_name,common1[m]:0);
        FOR l:=1 TO variable DO
        IF primeimp[j,l]<>primeimp[m,l] THEN
        WITH inpsignal[l] DO
        IF primeimp[j,l] IN [s0,s1] THEN
          BEGIN
          WRITE(and_op);
          IF (primeimp[j,l]=s0)=state THEN
            WRITE(invert_op);
          WRITE(name)
          END
        END
      ELSE
        BEGIN
        l:=0;
        REPEAT
          l:=SUCC(l);
          flag2:=primeimp[j,l]<>sX
        UNTIL (l=variable) OR flag2;
        IF flag2 THEN
          BEGIN
          flag3:=FALSE;
          FOR l:=1 TO variable DO
          WITH inpsignal[l] DO
          IF primeimp[j,l] IN [s0,s1] THEN
            BEGIN
            IF flag3 THEN
              WRITE(and_op);
            IF (primeimp[j,l]=s0)=state THEN
              WRITE(invert_op);
            WRITE(name);
            flag3:=TRUE
            END
          END
        ELSE
          WRITE(one)
        END
      END
    ELSE
    IF j=1 THEN
      BEGIN
      IF NOT flag1 THEN
        BEGIN
        WRITELN;
        WRITE(space:k,or_op)
        END;
      flag1:=FALSE;
      WRITE(common2_name,1:0)
      END
    ELSE
    IF common2[j]<>common2[PRED(j)] THEN
      BEGIN
      IF NOT flag1 THEN
        BEGIN
        WRITELN;
        WRITE(space:k,or_op)
        END;
      flag1:=FALSE;
      WRITE(common2_name,common2[j]:0)
      END
  UNTIL (j=prime) OR NOT flag2;
  IF flag1 THEN
    WRITE(zero);
  WRITELN
  END;
WRITELN
END;

PROCEDURE statistics;

VAR
  primetotal:PACKED ARRAY[0..variable_max] OF 0..cube_max;

FUNCTION output_order:LONGINT;

VAR
  order,z:LONGINT;

BEGIN
order:=0;
FOR z:=1 TO multiple DO
IF outcode[l,z] THEN
  order:=SUCC(order);
output_order:=order
END;

FUNCTION prime_order:LONGINT;

VAR
  order,z:LONGINT;

BEGIN
order:=variable;
FOR z:=1 TO variable DO
IF primeimp[l,z]=sX THEN
  order:=PRED(order);
prime_order:=order
END;

BEGIN
termtotal[0]:=0;
FOR i:=1 TO multiple DO
  termtotal[0]:=termtotal[0]+termtotal[i];
WRITELN('##### Statistics');
FOR i:=0 TO multiple DO
  BEGIN
  WRITELN;
  IF i=0 THEN
    WRITELN('Overall')
  ELSE
    BEGIN
    WRITE('Function ');
    WITH outsignal[i] DO
      BEGIN
      IF NOT state THEN
        WRITE(invert_op);
      WRITE(name)
      END;
    WRITELN
    END;
  WRITELN;
  FOR j:=0 TO variable DO
    primetotal[j]:=0;
  j:=0;
  k:=0;
  IF i=0 THEN
  FOR l:=1 TO prime DO
    BEGIN
    j:=SUCC(j);
    m:=prime_order;
    IF m>1 THEN
      k:=k+PRED(m);
    primetotal[m]:=primetotal[m]+output_order
    END
  ELSE
  FOR l:=1 TO prime DO
  IF outcode[l,i] THEN
    BEGIN
    j:=SUCC(j);
    m:=prime_order;
    IF m>1 THEN
      k:=k+PRED(m);
    primetotal[m]:=SUCC(primetotal[m])
    END;
  j:=max(0,PRED(j));
  WRITELN('Total of Boolean Operators');
  WRITELN('  - OR  operators: ',j:0);
  WRITELN('  - AND operators: ',k:0);
  WRITELN;
  WRITELN('Total of Prime Imps');
  FOR j:=0 TO variable DO
    BEGIN
    WRITE('  - ',j:2,' order Prime Imps: ');
    WRITELN(primetotal[j]:0)
    END;
  WRITELN;
  j:=0;
  k:=primetotal[0];
  l:=0;
  FOR m:=1 TO variable DO
    BEGIN
    j:=j+primetotal[m]*m;
    k:=k+primetotal[m];
    l:=l+SQR(primetotal[m]*m)
    END;
  m:=ROUND(10000.0-10000.0*j/variable/max(1,termtotal[i]));
  WRITELN('Efficiency: ',m DIV 100:0,'.',m MOD 100:0,' %');
  k:=max(1,k);
  m:=ROUND(100.0*j/k);
  WRITELN('Average   : ',m DIV 100:0,'.',m MOD 100:0);
  m:=ROUND(100.0*SQRT(SQR(j)-l)/k);
  WRITELN('Deviation : ',m DIV 100:0,'.',m MOD 100:0)
  END;
WRITELN
END;

BEGIN
WRITELN;
IF table_flag THEN
  truth_table;
IF equat_flag>0 THEN
  equations;
IF stats_flag THEN
  statistics
END;

BEGIN
runtime_error_flag:=TRUE;
ExitProc:=@exit_proc;

input_data;
WRITELN('##### Boolean Functions');
WRITELN;
WRITELN('Total Terms           : ',term:0);
IF term>0 THEN
  BEGIN
  generate_primes;
  reduce_primes;
  IF flag2 THEN
    petrick_primes;
  simplify_primes;
  sort_primes;
  output_data
  END
ELSE
  BEGIN
  WRITELN;
  WRITELN('***** INPUT ERROR: no truth table')
  END;
end_of_program:

runtime_error_flag:=FALSE
END.
