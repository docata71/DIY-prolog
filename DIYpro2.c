/*  DIYpro2.c  DIY-prolog  (float)      2026/4

 DIYpro1.cに実数計算を追加したバージョンです。
 
 実数の記録に配列da[]、定数、変数の名前の記録にca[][16]を用意します。
 「16」は、終端0を入れた名前の長さの最大値となります。
 
 prologプログラムを読み込む際、da[]に定数、ca[][]に定数名を記録しています。（0から9）
 定数に数値を書き込もうとするとfail判定（失敗）するようにしています。
 プロンプトからlixと打つと、その時点の乗数と変数のリストが見れます。
 
 中間記法の数式を逆ポーランド形式に変換するconRPが複雑になっています。

 逆ポーランドへの変換は、読み込んだ文字列が数値ならそのまま記録、
 演算子ならstackに積まれた演算子と 優先順位を調べて高ければpush、
 低ければ演算子を入れ替えて処理します。
 )など数式の区切りに来たら、演算子をpopして記録します。

 整数だけなら+-など1文字で済んでいたのですが、実数となるとsin,cosなど
 複数文字列を 扱うため 判別にコード量が増えています。

 計算時に処理が簡単になるよう、演算子、定数、変数はすべて$をつけて記録しています。
 四則演算は、$+,$-、実数の関数は$a,$b、定数は$0,$1、変数は$0a,$0bです。

 逆ポーランド形式の数式を計算する場合は、 数値をstackへpush、
 演算子でstackの数値を演算し、stackを減じます。
 計算した結果は、大域変数rt2に入れ、当該関数はrt2を整数にして返します。
 rt2は計算の最初にNANをセットして、実数計算がなされたか否かは、isnan関数で判定します。

*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <ctype.h>
#include <time.h>
#include <windows.h>

#define S1 1000000    // program size (char)
#define S2 100000     // stack max number
#define S3 1000000    // stack nakami
#define S4 512        // loacal array size

char buf[S1];   //  program area in plane text
int  bue=0, pge=0, pg[S2], pgn[S2], pgv[S2], vap[S2];   // pgv: var number, vap ; matching history for back track
int  ist, vpe, st[S2], stv[S3], pxe[S1];  // st stack index, stv stack contents; pxe endpoint+1
int  rt1, trmx, erc, iloop, itr=0, ist_max, vpe_max, stv_max, dae, dbe, mfs;
double rt2;
clock_t ct1, ct2;

// stack structure            gS,gI pN,cF, vP, vI,vS, vI, vS....
#define gS 0   // goal Step  (for back)
#define gI 1   // goal Index in buf
#define pN 2   // program Number
#define cF 3   // cut operator Flag
#define vP 4   // matching var Pointer for back track

#define vS 5   // v matching Step           v0
#define vI 6   // v matching Index in buf   v0

#define vN 2   // v1  vI+k*vN, vS+k*vN, 

#define gtVal(i,j)   (stv[st[i]+j])
#define gtVxx(i,j,k) (stv[st[i]+j+k*vN])   // gtVxx(stack,vI,0)  :: v0 index

#define S5 9     // internal prolog program
char ipr[S5][64] = {"not(X):-X,!,fail.",
                    "not(_).",
                    "eq(X,X).",
                    "ne(X,X):-!,fail.",
                    "ne(_,_).",
                    "member(X,[X|_]).",
                    "member(X,[_|Y]):-member(X,Y).",
                    "append([],X,X).",
                    "append([A|X],Y,[A|Z]):-append(X,Y,Z)."};
                    
// numerical functions  16
char mfu[128] = "sin,cos,tan,asin,acos,atan,atan2,exp,log,log10,abs,int,sqrt,pow,rt,neg,";

int cal_int(int, int);
int calRQ(int, int);
void  mkst(int, int);
int   mk_str(int, int);
char  ca[S2][16];  // (double) name list, name length < 15
double  da[S2];    // value
int   fx, fy, fz;  // work h.

void bbe(char c) {
  if(bue >= S1 || bue<0) { printf("buf[] over flow %d at bbe\n",bue); }
  else buf[bue++] = c;
}

void ptVal(int i, int j, int k) { 
  int n = st[i] + j;
  if (n>=S3 || n<0) printf("stv[] over flow %d at ptVal\n",n); else stv[n]=k;
}

void pt_gVal(int s1, int gi, int pn) {
  int k = st[ist];
  if (k<=0 || (k+cF)>=S3) {printf("stv[] over flow %d in pt_gVal\n",k); return;}
  stv[k +gS] = s1; stv[k +gI] = gi; stv[k +pN] = pn; stv[k +cF] = 0;
}

int setVxx(int s1, int j, int sx, int px) {
  int kv = st[s1] +vS +j*vN;
  int m = gtVal(s1, pN);
  if (kv >= S3 || kv < 0) {printf("stv[] over flow %d at setVxx\n",kv); return 0;}
  if (j >= pgv[m]) {printf("error var number j=%d, pN=%d, %d\n",j,m,erc++); return 0; }
  stv[kv] = sx;
  stv[kv+1] = px;
  if (vpe >= S2 || vpe < 0)  {printf("vap[] over flow %d at setVxx\n",vpe); return 0;}
  vap[vpe++] = kv;       // record unify 1st parameter 
  if (vpe > vpe_max) vpe_max = vpe;
  return 1;
}

void clrVxx(int ve) { int i, j;  // clear var unify record
  for (i=vpe-1; i>= ve; i--) {
    j = vap[i]; if (j<0 || j >= S2) {printf("vap[] over %d at clrVxx\n",j); return;}
    stv[j] = 0;
  } 
  vpe=ve;
}

int chAZ(char c) { // _:702 A:0 B:1 C:2,  zz:701 non var:-1
  if ( c == '_') return 702;        // 26+26*26 -> 702
  if (c < 'A' || c > 'Z') return -1;
  return c - 65;
}

int chkk(char c) {
  int i, ie;
  char cst[] = "([|,;=+-/*<>^%! ";
  ie = strlen(cst);
  for (i=0; i < ie; i++) {if (c == cst[i]) return 1;}
  return 0;
}

void pln() {printf("\n");}

int xxlen(int i, int kk) { // kk==0 in equation,  else in clause.
  int j, k=0, ke, k1=0;
  char c, kgi[] = ".,)]|:;=+-/*<>^%!" ;

  if (buf[i] == '[') {  // list
    for (j=1, k1=1; (i+j)<S1 && k1>0; j++) {
      c = buf[i+j];
      if (c == '[') k1++;
      if (c == ']') k1--;
      if (c == 0) return j; 
    }
    return j;
  }
  if (buf[i] == '\"') {  // atom
    for (j=1; (i+j)<S1; j++) {
      if (buf[i+j] == '\"') return j+1;
      if (buf[i+j] == 0) return j;
    }
  }

  trmx = 0;
  if (kk == 0) ke = strlen(kgi); else ke = 7;
  for (j=0, k1=0; (i+j)<S1; j++) {
    c = buf[i+j];
    if (c == '(') {      // term
      trmx = j;
      for (j++, k1=1; (i+j)<S2 && k1>0; j++) {
        c = buf[i+j];
        if (c == '(') k1++;
        if (c == ')') k1--;
        if (c == 0) return j;
      }
      c = buf[i+j];
    }
    if (c == '.' && buf[i+j+1] ==0) { return j; }
    for (k=1; k<ke; k++) {if (c == kgi[k]) return j;}  // kugiri
    if (c == 0) return j;
  }
  return 0;
}

int pxxe(int i) {  // next position in buf
  int k = pxe[i];
  if (k == 0) {k = i + xxlen(i, 1); pxe[i] = k;}
  return k;
}

int vnch(int is) {
int i,j,k, m=0, vp[S4], vl[S4], vc[S4];
char c, cx = ' ';
  for (i=0; i<S4; i++) vc[i]=0;
  for (i=0; i<S3; i++, cx=c) {
    c = buf[is + i];
    bbe(c);
    if (c == 0) break;
    if ( chAZ(c) == -1) continue;  // not var
    if ( chkk(cx) == 0) continue;  // just before c is not "([|,;=+-/*<>^%! "
    int len = xxlen(is + i, 0);
    if (c == '_' && len == 1) continue;
    for (j=0; j < m; j++) {         // var is new ?
      if (strncmp(buf+is+i, buf+vp[j], len) == 0 && len == vl[j]) break; 
    }
    vc[j]++;                        // var counter up
    if (j == m) { vp[m] = is + i; vl[m] = len; m++; }
    if (m > 675) {printf("vp,pl[] over flow %d at vnch\n",m); return 0;}
    buf[bue-1] = j%26 + 65;                     // replace var name
    if (j > 25) { bbe(j/26 + 64); }
    i = i+len-1;
  }
  if (i==S3) { printf("error at vnch  %d\n",erc++); return 0; }
  rt1=bue;
  for (j=0; j<m; j++) {                 // original var name record
    for (k=0; k<vl[j]; k++) { bbe(buf[vp[j]+k]); } bbe(0);
  }
  return m;
}

void bufncpy(int i1, int i2) { int i; for (i=0; i<i2; i++) {bbe(buf[i1+i]);} }

void bufscpy(char *c) { for (; *c!=0;) {bbe(*c++);} }

void li_conv(int i0) {  // list form convert    i0 -> bue in buf[]
  int ly = xxlen(i0 +1, 0);
  if (ly==0) {bbe(']'); return;}
  if (buf[i0 +1] == '[' ) {bbe('['); li_conv(i0 +1);}    // list in list
  else {bufncpy(i0 +1, ly);}                             // 1st arg copy
  bbe(',');
  char c = buf[i0+ly+1];                     // 2nd arg
  if (c == ',') {bbe('['); li_conv(i0+ly+1); bbe(']'); return;}
  if (c == ']') {bufscpy("[]]"); return;}
  if (c == '|') {bufncpy(i0+ly+2, 2); return;}
}

int yusk(char c, int ka) {  //  priority of operator
  if (c=='+' || c=='-') return ka*10 + 1;
  if (c=='*' || c=='/') return ka*10 + 2;
  if (c=='%') return ka*10 + 2;
  if (c=='^') return ka*10 + 3;
  return 0;
}

int ch_ncf(int i0) { // -1:var, 0:numeric, 2:constant, 3:function
  int n, j, je;
  char c = buf[i0];
  if (chAZ(c) >= 0) return -1;         // -1:var
  if (c < 'a' || c > 'z') return 0;    // 0:numeric
  fx = xxlen(i0, 0);
  fz = trmx;
  if (fz == 0) {
    for (n=0; n < dbe; n++) {
      fy = strlen(&ca[n][0]);          // 2:physical constant
      if (fx == fy && strncmp(buf+i0, &ca[n][0], fx) == 0) { break; }
    }
    if (n == dbe) { 
      if (dbe < S2) { strncpy(&ca[n][0], buf+i0, fx); dbe++; }
      else          { printf(" ca[][] over flow %d at ch_ncf\n",dbe); return 0; }
    }
    rt1 = n; return 2;
  }
  je = strlen(mfu);
  for (n=0, j=0; j < je && fz > 0; j++) {  // 3:function
    if (strncmp(buf+i0, mfu+j, fz) == 0 && mfu[j+fz] == ',') { rt1 = n; return 3; }
    for (; j<je; j++) { if (mfu[j] == ',') {n++; break;} }
  }
  return 0;
}

void pushRP(int stP[][4], int s, int i, int j, int k) {
           stP[s][0] = i; stP[s][1] = j; stP[s][2] = k; }
void popRP(int stP[][4], int sp) {
  int i = stP[sp][0];
  int j = stP[sp][1];
  char kg[] = "+-*/%^";
  if (j == 1) { bbe('$'); bbe(kg[i]); return; } // +,-,*
  if (j == 3) { bbe('$'); bbe(i +97); return; } // a,b,c
  return;
}

int conRP(int i0, int len) {  // Reverse Polish Notation
  int i, j, k=0, sp=0, ka=0, n, kx=0, lk, ix, stP[S4][4];  // stP 0:n , 1:length, 2:priority
  char c, cx=' ', kg[]="+-*/%^";
  lk = strlen(kg);
  for (i=0; i<len; i++) { c=buf[i0+i]; if (c=='.' || (c>='a' && c<='z')) break; }
  if (i==len) ix=1; else ix=2;  // 1:integer, 2:float
  if (buf[i0] == '+') { i0++; }
  if (buf[i0] == '-') { i0++; pushRP(stP, sp++, 15, 3, 3);}
  for (i=0; i<len; i++, bue++, cx=c) {
    c = buf[i0+i];
    buf[bue] = c;
    if (c=='(') { ka++; bue--; continue;}
    if (c==')') {
      for (; sp>0; sp--) {
        if (stP[sp-1][2] < ka*10) break;
        bbe(','); popRP(stP, sp-1);
      }
      buf[bue] = 0;
      ka--; bue--; continue;
    }
    j = 0; 
    for (n=0; n<lk; n++) {if (c==kg[n]) break;}   // 0:numeric
    if (n < lk) { 
      if ( i==0 || cx=='(' || cx=='=') { continue; }
      j = 1; kx = yusk(c, ka); k = 1; // 1:+ -
    } else {
      if (chkk(cx)==1 && (j = ch_ncf(i0+i)) > 0) {  // 2:constant, 3:function
        n = rt1; 
        if (j==2) {
          i += fx-1; bbe('$');
          if (n < 10) { bbe(n+48); } else { bbe((n-10)/26 +48); bbe((n-10)%26 +97); }
          bue--; 
          continue;
        } 
        if (j==3) { k = trmx; kx = ka*10 + 4; }
      }
    }
    if (j <= 0) continue;
    bbe(','); if (j==3) {bue--;}
    i = i + k-1;
    if (sp==0) {pushRP(stP, sp++, n, j, kx); bue--; }
    else {
      if (kx > stP[sp-1][2]) { pushRP(stP, sp++, n, j, kx); bue--;}
      else { popRP(stP, sp-1); buf[bue] = ','; pushRP(stP, sp-1, n, j, kx);}
    }
  }
  for (; sp>0; sp--) { bbe(','); popRP(stP, sp-1); } buf[bue] = 0;
  return ix;
}

int calRP(int s1, int i0) {  // integer calculation of Reverse Polish Notation form
  int i,j,k, len, ix=0, iy=0, sp=0, stk[S4];
  char c;
  len = xxlen(i0, 0);
  for (i=3; i<len; i=i+j+1) {
    for (j=1; (i+j) < len; j++) if (buf[i0+i+j]==',' || buf[i0+i+j]==')') break;
    c = buf[i0+i];
    if (c == '$') {
      c = buf[i0+i+1];
      if (sp >= 2) { ix = stk[sp-2]; iy = stk[sp-1];}
      if (c == '+') { stk[sp-2] = ix + iy; sp--; continue; }
      if (c == '-') { stk[sp-2] = ix - iy; sp--; continue; }
      if (c == '*') { stk[sp-2] = ix * iy; sp--; continue; }
      if (c == '/') { stk[sp-2] = ix / iy; sp--; continue; }
      if (c == '%') { stk[sp-2] = ix % iy; sp--; continue; }
      if (c == '^') { for (k=1; iy>0; iy/=2) {if(iy%2==1) {k *=ix;} ix*=ix;}
                      stk[sp-2] = k; sp--; continue;  }
    }
    if (chAZ(c) >= 0) { k = cal_int(s1, i0+i); }
    else              { k = atoi(buf+i0+i); }
    stk[sp++] = k;
  }
  return stk[0];
}

int  cal_int(int s1, int p1) {  // cal integer
  int i,j,k=0, s2, p2;
  char c = buf[p1];
  if ((j=chAZ(c)) >= 0) {
    if ((i=chAZ(buf[p1+1])) >= 0) { j += (i+1)*26; }
    s2 = gtVxx(s1, vS, j); p2 = gtVxx(s1, vI, j);
    if (s2 == 0) {printf(" error no bind at cal_int %c, %d, %d, %d\n",c,s1,p1,erc++); return 0;}
    if (s2 == -1) return p2;
    k = cal_int(s2, p2);
  } else {
    rt2 = NAN;
    if (strncmp(buf+p1, "$p(", 3) == 0) { k = calRP(s1, p1); } 
    else { if (strncmp(buf+p1, "$q(", 3) == 0) { k = calRQ(s1, p1); } 
           else { k = atoi(buf + p1); } 
    }  // numerical string
  }
  return k;
}

double atofx(int i) {
int j = pxxe(i);
double x = atof(buf+i);
char c = buf[j-1];
  if (c >='0' && c <='9') return x;
  if (c == 'k')  { return x * 1.0e3; }
  if (c == 'K')  { return x * 1.0e3; }
  if (c == 'm')  { return x * 1.0e-3; }
  if (c == 'M')  { return x * 1.0e6; }
  if (c == 'u')  { return x * 1.0e-6; }
  if (c == 'G')  { return x * 1.0e9; }
  if (c == 'n')  { return x * 1.0e-9; }
  if (c == 'T')  { return x * 1.0e12; }
  if (c == 'p')  { return x * 1.0e-12; }
  return x;
}

double cal_float(int s1, int p1) {  // cal float
  int i, j, s2, p2;
  double xx=0.0;
  char c = buf[p1];
  if ((j=chAZ(c)) >= 0) {
    if ((i=chAZ(buf[p1+1])) >= 0) { j += (i+1)*26; }
    s2 = gtVxx(s1, vS, j); p2 = gtVxx(s1, vI, j);
    if (s2 == 0) {printf(" error no bind at cal_int %c, %d, %d, %d\n",c,s1,p1,erc++); return 0;}
    if (s2 == -1) return (double)p2;
    if (s2 == -2) return da[p2];
    xx = cal_float(s2, p2);
  } else {
    if (strncmp(buf+p1, "$q(", 3) == 0) { j= calRQ(s1, p1); xx = rt2; }
    else { xx = atofx(p1); }   // numerical string
  }
  return xx;
}

int calRQ(int s1, int i0) {  // float calculation of Reverse Polish Notation form
  int i,j, k, len, sp=0;
  double xx=0.0, yy=0.0, stk[S4];
  char c, d;
  for (i=0; i<4; i++) { stk[i]=0.0; }
  if (strncmp(buf+i0, "$q(", 3) != 0) { printf("no Rev. Pol. at %d\n",i0); return 0.0; }
  len = xxlen(i0, 0);
  for (i=3; i<len; i=i+j+1) {
    for (j=1; (i+j) < len; j++) { if (buf[i0+i+j]==',' || buf[i0+i+j]==')') break; }
    c = buf[i0+i];
    if (c == '$') { 
      c = buf[i0+i+1];
      if (c >= '0' && c <= '9') {
        k = (int)c -48;
        d = buf[i0+i+2]; if (d >= 'a' && d <='z') {k = 10 + k*26 + ((int)d-97); }
        stk[sp++] = da[k]; continue; 
      }
      if (sp >= 1) { yy = stk[sp-1]; }
      if (sp >= 2) { xx = stk[sp-2]; }
      if (c >= 'a' && c <= 'p') {   // 16
        if (c == 'a') { stk[sp-1] = sin(yy); continue; }
        if (c == 'b') { stk[sp-1] = cos(yy); continue; }
        if (c == 'c') { stk[sp-1] = tan(yy); continue; }
        if (c == 'd') { stk[sp-1] = asin(yy); continue; }
        if (c == 'e') { stk[sp-1] = acos(yy); continue; }
        if (c == 'f') { stk[sp-1] = atan(yy); continue; }
        if (c == 'g') { stk[sp-1] = atan2(yy, xx); sp--; continue; }
        if (c == 'h') { stk[sp-1] = exp(yy); continue; }
        if (c == 'i') { stk[sp-1] = log(yy); continue; }
        if (c == 'j') { stk[sp-1] = log10(yy); continue; }
        if (c == 'k') { stk[sp-1] = fabs(yy); continue; }
        if (c == 'l') { stk[sp-1] = (rt1 = yy); continue; }
        if (c == 'm') { stk[sp-1] = sqrt(yy); continue; }
        if (c == 'n') { stk[sp-2] = pow(xx, yy); sp--; continue; }
        if (c == 'o') { stk[sp-1] = sqrt(yy); continue; }
        if (c == 'p') { stk[sp-1] = -yy; continue; }
      }
      if (c == '+') { stk[sp-2] = xx + yy; sp--; continue; }
      if (c == '-') { stk[sp-2] = xx - yy; sp--; continue; }
      if (c == '*') { stk[sp-2] = xx * yy; sp--; continue; }
      if (c == '/') { stk[sp-2] = xx / yy; sp--; continue; }
      if (c == '^') { stk[sp-2] = pow(xx, yy); sp--; continue;  }
    }
    if (chAZ(c) >= 0) { xx = cal_float(s1, i0+i); }
    else              { xx = atofx(i0+i); }
    stk[sp++] = xx;
  }
  rt2 = stk[0];
  return (int)rt2;
}

int zzback(int i) { int k1;
  for (k1=0; i>=0; i--) {
    char c = buf[i];
    if (c == 0) break;
    if (c == ')') {k1++; continue;}
    if (c == '(') {k1--; if (k1 < 0) break; else continue;}
    if (k1 == 0 && (c == ',' || c == '-')) break;
  }
  return i + 1;
}

void cl_conv(int kk) {    // clause convet 1.vnch, 2.list, 3.function 4.re-arrange
  int i,j,k,i0,i1,i2,i3,i3x,i3y,i4x,i4y,i5,i6,len,k1=0,k2=0,ipq;
  char c, cx=' ';
  i0 = pg[kk];
  i1 = bue;                 // pointer in buf
  pgv[kk] = vnch(i0);       // var in buf[i0]...
  i6 = rt1;
  i2 = bue;                 // pointer in buf pgn
  i3x = i3y = i1-1; i4x = i4y = i2;
  for (i=0; i<S4; i++, cx=c) {
    if (bue >= S1) {printf("buf[] over flow at cl_conv\n"); return;}
    i3 = i1 + i;
    c = buf[i3]; bbe(c); if (c==0) break;
    if (chkk(c)==1) {i3y=i3x; i3x=i3; i4y=i4x, i4x=bue;}
    if (c == '(') {k1++; continue;}
    if (c == ')') {k1--; if (k1 < 0) {bue--; bufscpy(",#3"); k1 = 0;} continue;}
    if (c == '\"') {
      len = xxlen(i3, 0); for (j=1; j<len; j++) bbe(buf[i3+j]); i=i+len-1; continue;
    }
    if (c == '[' && chkk(cx) == 1) { 
      if (buf[i3+1] == ']') continue;
      li_conv(i3); i=i +xxlen(i3, 0) -1;
      continue;
    }
    bue--;
    if (chkk(cx) == 1) {
      if (strncmp(buf+i3,"true",4)==0)  { bufscpy("#1");  i=i+3; continue; }
      if (strncmp(buf+i3,"fail",4)==0) { bufscpy("#2");  i=i+3; continue; }
      if (c == '!' && buf[i3+1] != '=') { bufscpy("#4");         continue; }
      if (strncmp(buf+i3,"write(",6)==0)  { bufscpy("#a("); i=i+5; k1++; continue; }
      if (strncmp(buf+i3,"nl",2)==0)      { bufscpy("#b");  i=i+1; continue; }
      if (strncmp(buf+i3,"assert(",7)==0) { bufscpy("#c("); i=i+6; k1++; continue; }
      if (strncmp(buf+i3,"trace(",6)==0)  { bufscpy("#d("); i=i+5; k1++; continue; }
    }
    if (c=='=' && cx !='!' && cx !='>' && cx !='<' && buf[i3+1] !='=') { // #6 sassinment
      i3y = zzback(i3 - 1);
      k = i3-i3y;
      bue -= k; bufscpy("#6(");
      k2 = ch_ncf(i3y);
      if (k2 == -1) { bufncpy(i3y, k);     // var
      } else { if (k2 == 2) { j = rt1; bbe('$'); bbe((j-10)/26+48); bbe((j-10)%26+97); } 
               else printf("left side of = error at cl_conv %s\n",buf+i0);
      }
      ipq = bue+2; bufscpy(",$p(");
      len = xxlen(i3+1, 1);
      if (conRP(i3+1, len)==2) {buf[ipq]='q';}
      i = i+len; bufscpy("))");
      continue;
    }
    if (c=='>' || c=='<' || ((c=='!' || c=='=') && buf[i3+1]=='=')) { // #7 compare
      i5 = 1; if (buf[i3+1] == '=') i5 = 2;
      if (i5==1 && c=='!') {bue++; continue;}
      bue = i4y;
      bufscpy("#7("); bbe(c); 
      if (i5 == 2) {bbe('=');}
      ipq=bue+2; bufscpy(",$p(");
      i3y = zzback(i3 - 1);
      if (conRP(i3y, i3 - i3y)==2) {buf[ipq]='q';} 
      ipq=bue+3; bufscpy("),$p(");
      len = xxlen(i3 + i5, 1);
      if (conRP(i3 + i5, len)==2) {buf[ipq]='q';};
      i = i+len+i5-1; bufscpy("))");
      continue;
    }
    bue++;
  }
  for (i=i6; i<i2; i++) { bbe(buf[i]); }
  for (i=i1, j=i2; j < bue; i++, j++) { buf[i] = buf[j]; }
  bue = i;
  pgn[kk] = i1;
}

void mk_tabl(int kk) {  // make pxe[] table for every term through pxxe()
  int i, j;
  char c;
  if (kk == 0) {
    i = pgn[kk];
  } else {
    i = pxxe(pgn[kk]);
    c = buf[i];
    if (c == '.') { return; }
    if (c != ':' || buf[i+1] != '-') { printf("error at prog.No =%d, %d\n",kk,erc++); return; }
    i += 2;
  }
  for (j=0; j<S4; j++) {
     i = pxxe(i);
     if (buf[i] == '.') { return; }
     i++;
  }
}

int matchX(int s1, int p1, int s2, int p2) {   // matching term
  int i, j, m, p1e, p2e;
  char c1, c2;
  if (s1==s2 && p1== p2) return 1;
  p1e = pxxe(p1);
  p2e = pxxe(p2);

  for (i=0; i<S1; i++, p1++, p2++) {
    c1 = buf[p1];
    c2 = buf[p2];
    if (p1 >= p1e && p2 >= p2e) return 1;
    if (c1 == '_') { p2 = pxxe(p2) - 1; continue;}
    if (c2 == '_') { p1 = pxxe(p1) - 1; continue;}
                               //if (itr==1) printf("  match_1 i,c1,c2=%2d,%c,%c\n",i,c1,c2);
    if ( (j=chAZ(c2)) >= 0) {                    // c2:var
      if ((m=chAZ(buf[p2+1])) >= 0) { j += (m+1)*26; p2++; }
      if (gtVxx(s2, vS, j) == 0) {               // c2:free
        if (setVxx(s2, j, s1, p1) == 0) return 0;
        p1 = pxxe(p1) - 1;
        continue;
      } else {                                    // c2:bind
        if (gtVxx(s2, vS, j) == -1) {             // c2:integer
           if (gtVxx(s2, vI, j) != cal_int(s1, p1) ) return 0;
           p1 = pxxe(p1) - 1;
           continue;
        } else {
          if (matchX(s1, p1, gtVxx(s2, vS, j), gtVxx(s2, vI, j)) == 0) return 0;
          p1 = pxe[p1] - 1; 
          continue;
        }
      }
    }
    if ( (j=chAZ(c1)) >= 0) {                       // c1:var
      if ((m=chAZ(buf[p1+1])) >= 0) { j += (m+1)*26; p1++; }
      if (gtVxx(s1, vS, j) == 0) {                  // c1:free
        if (setVxx(s1, j, s2, p2) == 0) return 0;
        p2 = pxxe(p2) - 1;
        continue;
      } else {                                       // c1:bind
        if (gtVxx(s1, vS, j) == -1) {                // c1;integer
           if (gtVxx(s1, vI, j) != cal_int(s2, p2) ) return 0;
           p2 = pxxe(p2) - 1;
           continue;
        } else {
          if (matchX(gtVxx(s1, vS, j), gtVxx(s1, vI, j), s2, p2) == 0) return 0;
          p2 = pxe[p2] - 1;
          continue;
        }
      }
    }
    if (c1 != c2) break;
  }
  if (i==S1) {printf("error at matchX end  %d\n",erc++); return 0;}
  return 0;
}

int ex_func(int s1, int p1) {
  int i,j,k,m, len, lxx, ix, iy, k1=0, kk, pz;
  double xx;
  char c, c1;
  len = xxlen(p1+3, 1);
  c = buf[p1+1];
  if (c=='1') return 1;   // true
  if (c=='2') return 0;   // fail
  if (c=='4') {for (i=ist; i >= gtVal(ist, gS); i--) {ptVal(i, cF, 1);} return 1;} // cut op.
  if (c=='6') {           // 代入
    k = cal_int(s1, p1+3+len+1); xx = rt2;
    for (p1 = p1+3, kk=0; kk<S4; kk++) {
      if ( (j=chAZ(buf[p1])) < 0) {
        if (buf[p1] == '$') {
           c = buf[p1+1]; c1 = buf[p1+2];
           if (c >= '0' && c <= '9' && c1 >='a' && c1 <= 'z') {
             j = 10 + ((int)c-48)*26 + ((int)c1-97);
             if (isnan(xx)) da[j] = k; else da[j] = xx;
             return 1;
           }
        }
        if (cal_int(s1, p1) == k) return 1; else return 0;
      }
      if ((m=chAZ(buf[p1+1])) >= 0) { j += (m+1)*26; }
      if (gtVxx(s1, vS, j) == 0) {
        if (isnan(xx)) {setVxx(s1, j, -1, k); return 1; }
        else { setVxx(s1, j, -2, dbe); da[dbe++] = xx; return 1;}
      }
      p1 = gtVxx(s1, vI, j); s1 = gtVxx(s1, vS, j); 
    }  printf("error over flow at ex_func #6 %d\n",erc++); return 0;
  }
  if (c=='7') {           // 整数比較
    c = buf[p1+3]; c1= buf[p1+4];
    len =1; if (c1 == '=') len = 2;
    ix = cal_int(s1, p1+3+len+1);
    lxx = xxlen(p1+3+len+1, 1);
    iy = cal_int(s1, p1+3+len+1 +lxx+1);
    if (c == '>') { if (c1 == '=') {if (ix >= iy) return 1; else return 0;}
                    else           {if (ix >  iy) return 1; else return 0;}
                  }
    if (c == '<') { if (c1 == '=') {if (ix <= iy) return 1; else return 0;}
                    else           {if (ix <  iy) return 1; else return 0;}
                  }
    if (c == '!' && c1=='=')       {if (ix != iy) return 1; else return 0;}
    if (c == '=' && c1=='=')       {if (ix == iy) return 1; else return 0;}
  }
  if (c=='a') {
    len = xxlen(p1+2, 1);
    for (j=0, k1=0; j<(len-2); j++) {  
      c = buf[p1+3+j];
      if (c == '\"') {if (k1==0) k1=1; else k1=0; continue;}
      if (c == ',' ) continue;
      if (k1==0 && chAZ(c) >= 0) {pz=mk_str(s1, p1+3+j); printf("%s",buf+pz); continue;}
      putchar(c);
    }
    return 1; }
  if (c=='b') { pln(); return 1; }
  if (c=='c') {
    pgn[pge] = bue; mkst(s1, p1+3); bbe('.'); bbe(0); mk_tabl(pge);
    pg[pge] = pgn[pge]; pge++;
    if (pge >= S2) {printf("pg[] over flow at ex_func\n"); return 0;}
    return 1;
  }
  if (c=='d') {
    itr = atoi(buf+p1+3);
    return 1;
  }
  return 0;
}

void printn(int i) {int j = pxxe(i); for (; i <= j; i++) putchar(buf[i]); }

int ex_goal(int s1, int p1) {
  int i,j,k,m, is, ve, kk, k1, vsx;
  char c;
  is = gtVal(ist, pN) +1;
  for (kk=0; kk<S4; kk++) {
    if ( (j=chAZ(buf[p1])) < 0) break;
    if ((m=chAZ(buf[p1+1])) >= 0) { j += (m+1)*26; }
    if (gtVxx(s1, vS, j) == 0) {printf("error no bind at ex_goal stack=%d, vn=%d, %d\n",s1,j,erc++); return 0; }
    p1 = gtVxx(s1, vI, j); s1 = gtVxx(s1, vS, j); 
  } if (kk>S4) { printf("error over flow at ex_goal stack=%d, %d\n",s1,erc++); return 0; }

  c = buf[p1];   if (itr==1) {printf(" ex_goal %d ",s1); printn(p1); pln();}
  rt1 = 0;
  if (c == '#') {rt1 = 1; return ex_func(s1, p1);}     // 1:function
  k1 = xxlen(p1, 1); if (trmx > 0) k1 = trmx;
  ve = vpe;
  vsx = st[ist] +vS;      // var area start pointer
  for (i=is; i<pge; i++) {
    if (strncmp(buf+p1, buf+pgn[i], k1) != 0) continue;
    ptVal(ist, pN, i);
    for (j=0; j<pgv[i]; j++) { stv[vsx +j*vN]=0; }  // vS clear
    if (matchX(s1, p1, ist, pgn[i]) == 1) {
                  if (itr==1) printf("  prog %d, %s\n",i,buf+pgn[i]);
      if ((ist+1) >= S2 || ist < 0) {printf("st[] over flow %d in ex_goal\n",ist); return 0;}
      st[ist+1] = k = vsx + vN*pgv[i];
      if (k >= S3) {printf("stv[] over flow %d in ex_goal\n",st[ist+1]); return 0;}
      if (k > stv_max) stv_max = k;
      return 1;
    }
    clrVxx(ve);
  }
  return 0;
}

int ex_body(int ifb) {  // forward/back
  int i,j, j1, pn, s1, s2, ii;
  
  if (ifb == 1) {
    for (i=0; i<st[ist]; i++) { stv[i] = 0; }  vpe = 0;
    st[1]=0; st[2] = st[1] + vS + vN*pgv[0];
    for (j=st[1]; j<st[2]; j++) { stv[j]=0; }
    ist=2; pt_gVal(1, pgn[0], 0);
  }
  for (iloop=0; ist < S2 && vpe < S2; iloop++) {
    if (ifb == -1) {    // back track
      for (ist--; ist>1; ist--) { if ( gtVal(ist, cF) != 1 && gtVal(ist, pN) > 0) break; }
      if (ist <= 1) { return 0; }  // "no" return
      clrVxx(gtVal(ist, vP));
      ifb = 1;
    }
    ptVal(ist, vP, vpe);       // for clear var in back track
    ii = ex_goal(gtVal(ist, gS), gtVal(ist, gI));  // goal stack, index
    s1 = ist;
    j1 = pxe[gtVal(s1, gI)];   // next kugiri
    if (buf[j1] == ';') {
      if (ii == 0) {ptVal(s1, gI, j1+1); continue;}  // fail return "or"
      for (j1++; j1<S1; j1++) { // true return "or"  goal skip
        j1 = pxe[j1]; if (buf[j1] != ';') break;
      }
    }
    if (ii == 0) {ifb = -1; continue;}  // back track
    if (rt1 == 0) ist++;                // stack for matching clause
    if (ist > S2) {printf("st[] over flow in ex_body\n"); break;}
    if (ist > ist_max) ist_max = ist;
    pn = gtVal(s1, pN); j1 = pxe[pgn[pn]];
                    if (itr==1) printf(" pn=%d, pgn=%d, pxe=%d, j1=%d, c=%c\n",pn,pgn[pn],pxe[pn],j1,buf[j1]);
    if (rt1 == 0 && buf[j1]==':') { pt_gVal(s1, j1+2, 0); continue; }  // new clause & next goal
    for (; s1 > 0;  s1 = s2) {
      s2 = gtVal(s1, gS); j1 = pxe[gtVal(s1, gI)];
                    if (itr==1) printf(" s2=%d, j1=%d, c=%c\n",s2,j1,buf[j1]);
      if (buf[j1] == ',') { pt_gVal(s2, j1+1, 0); break; } // next goal of original body
      if (s2 == 1) {return 1;}            // "yes" return
    }
    if (erc > 5) break;
  }
  printf("overflow iloop=%d, ist=%d, vpe=%d, erc=%d\n",iloop,ist,vpe,erc);
  return 0;
}

int chVN(int p1) {
  int j = chAZ(buf[p1]);
  if (j < 0) return -1;
  int m = chAZ(buf[p1+1]);
  if (m < 0) return j;
  return j += (m+1)*26;
}

void mkst(int sx, int px) {  // replace var to string
  int i, j, len;
  char c, cx=' ', ss[64];
  if (sx == -1) {
    sprintf(ss,"%d",px); for (i=0; i<64; i++) {c=ss[i]; if (c==0) return; bbe(c);}
  }
  if (sx == -2) {
    if (fabs(da[px]) > 0.1) sprintf(ss,"%g",da[px]); else sprintf(ss,"%e",da[px]);
    for (i=0; i<64; i++) {c=ss[i]; if (c==0) return; bbe(c);}
  }
  len = xxlen(px, 0);
  for (i=0; i<len; i++) {
    c = buf[px+i];
    bbe(c);
    if (c!='_' && (j=chVN(px+i)) >= 0 && chkk(cx) == 1 && gtVxx(sx, vS, j) != 0) {
      bue--; mkst(gtVxx(sx, vS, j), gtVxx(sx, vI, j));
    }
    cx = c;
  }
}

int mk_str(int sx, int px) {
  int i, k, len, py, pz;
  char c, cx=' ';
  py = bue;
  mkst(sx, px); 
  pz = bue;         // list conversion to normal style
  len = pz - py;
  for (i=0, k=0; i<len; i++, cx=c) {
    c = buf[py+i];
    if (cx==',' && c=='[') {
      if (buf[py+i+1] != ']') { k++; continue; }
      else { bue--; i = i+1+k; continue;}
    }
    bbe(c);
  } bbe(0);
  return pz;
}

void getsx(char a[]) { fflush(stdin); fgets(a, S4, stdin); a[strlen(a)-1]=0; }

void go_start() {
  int i,j, ifb, pz;
  char a[S4];
  erc = 0;
  for (ifb=1;;) {
    ist_max=vpe_max=stv_max=0; ct1=clock();
    if (ex_body(ifb) == 0) {   ct2=clock(); printf("no\n"); return; }
    for (i=pgn[0]; buf[i]!=0; i++) ;
    if (pgv[0] > 0) {
      for (j=0; j<pgv[0]; j++) {
        if (gtVxx(1, vS, j) == 0) printf("%s = no bind in go_start",buf+i+1);
        else {pz = mk_str(gtVxx(1, vS, j), gtVxx(1, vI, j));
              printf("%s = %s ",buf+i+1, buf+pz); }
        for (i++; buf[i]!=0 && i<S2; i++) ;
        if (j < (pgv[0]-1) ) printf(", ");
      }
      ct2=clock();
      getsx(a);
      if (a[0] == ';') {ifb = -1; continue;} else break;
    } else { ct2=clock(); }
    printf("yes\n"); 
    return;
  }
}

void clear_array() { int i, j;
 for(i=0; i<S1; i++) {buf[i]=0; pxe[i]=0;}
 for(i=0; i<S2; i++) {pg[i]=pgn[i]=pgv[i]=vap[i]=st[i]=0; 
                      da[i]=0.0; for (j=0; j<16; j++) ca[i][j]=0; }
 for(i=0; i<S3; i++) {stv[i]=0;}
 bue = pge = 0;
}

void prload(char *fname) {
 int i,j,k, k1=0, k2=0, k3=0;
 char c;
 FILE *fp;
   clear_array();
   fp = fopen(fname,"r");
   j = 0;
   k = 1;
   pg[k++] = 0;
   for (i=0; i<S2; i++) {
     c = fgetc(fp);
     if (c == EOF) break;
     if (c == '%') { for (; (c=fgetc(fp)) != 10;) {} }
     if (c == '\"') { if (k3 == 0) k3 = 1; else k3 = 0; }   // double quatation
     if (k3 == 0 && c == ' ') { i--; continue;}             // space skip
     if (c == 9) continue;                                  // tab skip
     if (c == 10) {
       if (buf[i-1] == '.') { c = 0; pg[k++] = i+1; k2 = 0; } 
       else { i--; continue; }                               // line feed skip
     }
     if (c=='-' && buf[i-1]==':') { k2 = 1; }
     buf[i] = c;
     if (c=='_' && k2==1) { buf[++i]=(char)(97+k1++); }      // _ -> _a,_b,.. in body
   }
   fclose(fp);
   bue = i;          // program end point in buf
   k--;
   for (i=0; i<S5; i++) {
     pg[k++] = bue;
     for (j=0; j<64; j++) { c = ipr[i][j]; bbe(c); if (c==0) break;}
   }
   bbe(0);
   da[0]=4.0*atan(1.0);   strcpy(&ca[0][0], "pai");
   da[1]=299792458.0;     strcpy(&ca[1][0], "c0");
   da[2]=6.62606957e-34;  strcpy(&ca[2][0], "h0");
   da[3]=1.60217657e-19;  strcpy(&ca[3][0], "q0");
   da[4]=1.3806488e-23;   strcpy(&ca[4][0], "kB");
   da[5]=8.85418782e-12;  strcpy(&ca[5][0], "e0");
   da[6]=1.25663706e-6;   strcpy(&ca[6][0], "u0");
   da[7]=6.0221409e23;    strcpy(&ca[7][0], "mole");
   da[8]=5.670367e-8;     strcpy(&ca[8][0], "sigma");
   da[9]=da[0]/180.0;     strcpy(&ca[9][0], "deg");
   dae = 10;
   dbe = dae;
   pge = k;          // array end in pg[]
   for (k=1; k<pge; k++) { cl_conv(k); }  // clause convert
   for (k=1; k<pge; k++) { mk_tabl(k); }  // make table
}

void rept_time(double x) {
  printf("buf:%5.3f, ist:%5.3f, vpe:%5.3f, stv:%5.3f, loop=%d, %7.3f s\n",
  (double)bue/S1,(double)ist_max/S2,(double)vpe_max/S2,(double)stv_max/S3,iloop,x);
}

int main(int argc,char *argv[]) {
 int i, j, pz;
char a[S4];
 if (argc >1) prload(argv[1]); else prload("prog.pl");
 for (;;) {
   printf("?- "); 
   getsx(a);
   if (a[0]==0) continue;
   if (a[0]==' ') {system(a+1); continue;}
   if (strcmp(a,"end")==0) exit(0);
   if (strcmp(a,"rept")==0) {rept_time((double)(ct2 - ct1)/1000.0); continue;}
   if (strcmp(a,"list")==0) {
     for (j=1; j<pge; j++) printf("%3d(%4d): %s\n",j,pg[j],buf+pg[j]);
     if (itr==1) {
       pln(); pln();
       for (j=1; j<pge; j++) printf("%3d(%4d,%d): %s\n",j,pgn[j],pgv[j],buf+pgn[j]);
       pln();
       for (j=0; j<dbe; j++) printf("%16s  %g\n",&ca[j][0], da[j]);
     } continue;
   }
   if (strcmp(a,"lix")==0) { for (j=0; j<dbe; j++) printf("%16s  %g\n",&ca[j][0], da[j]); continue; }
   if (strncmp(a,"load(",5)==0) { for(i=6; a[i]!=')'; i++) {} a[i]=0; prload(a+5); continue; }
   if (strcmp(a,"load")==0) { prload("prog.pl"); continue;}

   if (a[0] == ';') {printf("no !\n"); continue;}
   if (a[0] != 0) {
     pg[0] = bue;
     pz = bue;
     for (i=0;  i<S3; i++) { bbe(a[i]); if (a[i]==0) break; }
     if (a[i-1] != '.') { bue--; bbe('.'); bbe(0); }
     cl_conv(0);
     mk_tabl(0);
     go_start();
     if (itr==1) { rept_time((double)(ct2 - ct1)/1000.0); }
     bue = pz;
     for (i=bue; i<S1; i++) { pxe[i] = 0; }
   }
 }
 exit(0);
}
