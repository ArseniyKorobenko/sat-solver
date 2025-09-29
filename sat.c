#define _CRT_SECURE_NO_WARNINGS
#include <assert.h> // assert
#include <stdlib.h> // realloc, free
#include <string.h> // for testing
#include <stdio.h> // printf
typedef float F; typedef void V; typedef int I; typedef unsigned long long u64;
typedef unsigned L; typedef struct{I c;L bl;} Watcher;
/* ----------------USER INTERFACE----------------- */
#define or(a...) {int r[]={a};usr_clause(arrlen(r),r);}
I usr_clause(I,I*),solve();V dump(),reset();I L2I(I);L I2L(I);
enum{_=-1u/2,LITS=(I)1e5,VARS=LITS/2,VARB=VARS/64,GC_SZ=(I)1e6,GC_PERM=(I)3e5};
I attempts=1e6; F decay=0.99; u64 seed=12345;
#define N I n         /*                                                 */
#define W while       /*  HUNDRED LINE SAT SOLVER                        */
#define B break;      /*  Copyright Arseniy Korobenko 2025               */
#define R return      /*                                                 */
#define Z static      /*  Bring Your Own I/O                             */
#define ak a[k]       /*                                                 */
#define ai a[i]       /*  literal = variable*2+sign (3=>6, -3=>7)        */
#define wv gW[v]      /*                                                 */
#define cn gC.a[c]    /*  gQ[0..n]=solution. use L2I to get signed ints  */
#define ca (gC.a+c+1) /*                                                 */
#define i(a,e...)   ({I i=0,$=a;W(i<$){e;i++;}$!=i;})
#define k(a,b,e...) ({I k=a,$=b;W(k<$){e;k++;}$!=k;})
#define r(a,e...) ({typeof(a)r=a;e;r;}) /* ({ GNU C statement expression }) */
#define arrlen(a) (I)(sizeof(a)/sizeof*(a))
#define AS(a) assert(a);
#define p(b,v) r(b.n++,AS(b.n<arrlen(b.a));b.a[r]=v)
#define pf(e...) printf(e); // #define D(a) pf(#a "=%d\n",(I)a);
#define c02(e) {L v=*ca^1,b=ca[1];{e;}v=ca[1]^1;b=*ca;{e;}}
struct{N,a[VARS];} gLv; // backjump levels. Q[ai]. n=depth of decision tree
struct{N;Watcher*a;} gW[LITS]; // c=clause, bl=blocker. TODO: dont use malloc?
struct{N,head;L a[VARS];} gQ; // assignment queue/trail.
struct{N,a[VARS],b[VARS];} gH; // heap. p=(i-1)/2, l=i*2+1, r=i*2+2. b=indexof
struct{u64 av[VARB*2],s[VARB];} gA; // bitvec: assigned, value, seen
struct{N,temp,t,x,end;L a[GC_SZ];} gC; // clauses. temp=start, t=top, x=next
struct{N,c[VARS],lv[VARS];F a[VARS];} gV; // cause, level, activity
V reset(V){i(gV.n/32+1,gA.av[i]=0);i(gV.n+1,gV.c[i]=gV.lv[i]=gV.ai=0);
  i(GC_SZ,gC.ai=0);i(gV.n*2+2,I v=i;free(wv.a);wv.a=0;wv.n=0);
  gLv.n=gQ.n=gQ.head=gV.n=gH.n=gC.n=0;}
I L2I(N){R n&1?-n/2:n/2;}L I2L(N){R r(n<0?-n*2|1:n*2,AS(r<LITS));}
Z V init(V){AS(gV.n<VARS);gC.t=gC.x=gC.temp=GC_PERM;gC.end=GC_SZ*0.9;}
Z I rng(V){seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;R seed&_;} // xorshift
Z I mx(I a,I b){R a>b?a:b;}Z Watcher wat(I c,L b){Watcher r={c,b};R r;}
Z V see(N){n/=2;gA.s[n/64]|=1ull<<n%64;}Z I seen(N){n/=2;R 1&gA.s[n/64]>>n%64;}
Z V unsee(N){n/=2;gA.s[n/64]&=~(1ull<<n%64);}
Z I aav(L v){R 3&gA.av[v/64]>>(v&~1)%64;}Z I av(L v){R aav(v)^v&1;} // 2t 3f 0? 1?
Z V assign(L v){AS(aav(v)==0);gA.av[v/64]|=(u64)(2|v%2)<<(v&~1)%64;}
Z V hp_up(I i){I*a=gH.a,v=ai,k;W(i&&gV.a[v]>gV.a[a[k=(i-1)/2]])
  {gH.b[ai=ak]=i+1;i=k;}ai=v;gH.b[v]=i+1;}
Z V hp_down(I i){I*a=gH.a,v=ai;W(i*2+1<gH.n){I j=i*2+1,r=i*2+2,k=r<gH.n&&
  gV.a[a[r]]>gV.a[a[j]]?r:j;if(gV.a[ak]<=gV.a[v])B;gH.b[ai=ak]=i+1;i=k;}ai=v;}
Z V hp_put(L v){if(gH.b[v/=2])R;gH.b[v]=gH.n;hp_up(p(gH,v));}
Z I hp_pop(){I*a=gH.a;R gH.n?2*r(*a,gH.b[*a=a[--gH.n]]=1;gH.b[r]=0;if(gH.n>1)hp_down(0)):0;}
Z V enq(L v,I c){assign(v);gV.c[v/2]=c;gV.lv[v/2]=gLv.n;p(gQ,v);}
Z V watch1(I c,L v,L b){N=wv.n;n=!n?16:!(n&(n-1|15))?n*2:n; // 0,16,32,64..
  if(wv.n!=n)wv.a=realloc(wv.a,n*sizeof*wv.a);wv.a[wv.n++]=wat(c,b);}
Z V watch(I c){c02(watch1(c,v,b))}Z I locked(I c){R av(*ca)==2&&gV.c[*ca/2]==c;}
Z V rewatch(I c,I new){c02(i(wv.n,if(wv.ai.c==c){wv.ai.c=new;B}));if(locked(c))gV.c[*ca/2]=new;}
Z I make_space(N){I j=1;W(gC.x<=gC.t+n&&(j=gC.a[gC.x])){if(locked(gC.x)&&gLv.n){
  rewatch(gC.x,gC.t);i(j+1,gC.a[gC.t++]=gC.a[gC.x++]);}else{rewatch(gC.x,_);gC.x+=j+1;}}
  R r(gC.t,gC.t+=n+1;k(gC.t,gC.x,gC.ak=0);if(!j){gC.t=gC.x=gC.end<gC.t?gC.temp:gC.t;});}
Z I clause(I c,I usr){AS(usr||c+cn<gC.temp);AS(cn);if(cn==1){enq(*ca,_);gC.n=c;R _;}
  if(!usr&&cn>8)c=r(make_space(cn),i(cn+1,gC.a[r+i]=gC.a[c+i]);gC.n=c);watch(c);R c;}
I usr_clause(N,int*a){R r(p(gC,n),i(n,L v=I2L(ai);AS(v<LITS);
  gV.n=mx(gV.n,v/2);p(gC,v);hp_put(v));clause(r,1));}
Z V back_to(I lv){if(lv>=gLv.n)R;I i;for(i=gQ.n-1;i>=gLv.a[lv];i--)
  {L v=gQ.ai;gA.av[v/64]&=~(3ull<<v/2*2%64);hp_put(v);}gQ.n=gQ.head=i+1; gLv.n=lv;}
Z L branch(V){L v;do{if(gH.n==0)R 0;v=hp_pop();}W(aav(v));R v|rng()<_/2;}
Z V vbump(I i){gV.ai++;if(gH.b[i])hp_up(gH.b[i]-1);}Z V vdecay(V){i(gV.n,gV.ai*=decay);}
Z I prop(V){W(gQ.head<gQ.n){L v=gQ.a[gQ.head++];
 if(!wv.a)continue;Watcher*i,*j,*end=wv.a+wv.n;
 for(i=j=wv.a;i<end;){if(i<end-2)__builtin_prefetch(gC.a+i[2].c);
  if(i->c==_){i++;continue;}if(av(i->bl)==2){*j++=*i++;continue;}
  I c=i->c;L*a=ca,n=v^1;if(*a==n){*a=a[1];a[1]=n;};AS(a[1]==n);
  if(*a!=(*i++).bl&&av(*a)==2){*j++=wat(c,*a);continue;}
  if(k(2,a[-1],if(av(ak)!=3){a[1]=ak;ak=n;watch1(c,a[1]^1,*a);B}))continue;
  *j++=wat(c,*a);if(av(*a)==3){W(i<end)*j++=*i++;wv.n-=i-j;R c;}
  enq(*a,c);}wv.n-=i-j;}R _;}
Z I analyze(I c,I*lv){I r=p(gC,0);p(gC,0);I deps=0,i=gQ.n;L v=0;
 do{AS(c!=_);AS(!v||v==*ca);k(!!v,cn,L v=ca[k];if(!seen(v)&&gV.lv[v/2]>0){
   vbump(v/2);see(v);if(gV.lv[v/2]<gLv.n)p(gC,v);else deps++;});
  W(v=gQ.a[--i],!seen(v));c=gV.c[v/2];unsee(v);}W(--deps>0);
 c=r;cn=gC.n-r-1;L*a=ca;*a=v^1;k(i=1,cn,I c=gV.c[ak/2];if(c==_)a[i++]=ak;else
  {for(I j=1;j<cn;j++){v=ca[j];if(!seen(v)&&gV.lv[v/2]>0){a[i++]=ak;B}}});cn=i;
 if(cn==1)*lv=0;else{i=1;k(2,cn,if(gV.lv[ak/2]>gV.lv[ai/2])i=k);
  *lv=gV.lv[ai/2];r(a[1],a[1]=ai;ai=r);}i(gV.n/64+1,gA.s[i]=0);R c;}
I solve(){init();I confs=999,RST=1000;i(attempts,I conf=prop();if(conf!=_){
 if(gLv.n==0)R 0;I lv=0,c=analyze(conf,&lv);back_to(lv);c=clause(c,0);
 if(c!=_)enq(*ca,c);vdecay();if(++confs>RST){RST*=1.1;confs=0;
 i(gV.n,gV.ai=rng()/(_/15.f));for(I i=gH.n/2-1;i>=0;)hp_down(i--);back_to(0);}
 }else{L v=branch();if(!v)R 1;p(gLv,gQ.n);enq(v,_);});back_to(0);R _;}
V dump(V){
    pf("<Heap>\n")i(gH.n,pf("%d ",gH.ai));
    pf("\n<Queue>\n")i(gQ.n,I r=gV.c[gQ.ai/2];pf("%d=>%d|%d  ",r==_?-1:r,L2I(gQ.ai),gV.lv[gQ.ai/2]));
    pf("\n<Perm Clauses>")i(gC.n,pf("\n[%d|%d]",i,gC.ai);k(0,gC.ai,i++;pf("%d ",L2I(gC.ai))));
    pf("\n<Vars> ")k(1,gV.n,N=k*2;pf("\n% d wb: ",L2I(n))i(gW[n].n,pf("%3d|%d ",gW[n].ai.c,L2I(gW[n].ai.bl))));
    pf("\n<!Vars> ")k(1,gV.n,N=k*2+1;pf("\n% d wb: ",L2I(n))i(gW[n].n,pf("%3d|%d ",gW[n].ai.c,L2I(gW[n].ai.bl))));
    pf("\n<Assigns>")k(1,gV.n,pf("\n%c%d |%.1f",av(k*2)==2?' ':av(k*2)==3?'-':'?',k,gV.ak));
    pf("\n----------END DUMP----------\n")}

/* ---------------- Sudoku example ----------------- */
#define j(a,e) _(I $=a;I j=0;W(j<$){e;j++;}$!=j)
#define l(a,b,e) _(I $=b;I l=a;W(l<$){e;l++;}$!=l)
I pos(I r,I c,I v){R r*81+c*9+v;}
V solve_sudoku(I*sudoku){
  i(9,j(9,
        I c[9]={};
        k(1,10,c[k-1]=pos(i,j,k));usr_clause(9,c);
        // vvv this is very suboptimal, but we're benchmarking the solver here, not the sudoku function
        k(1,10,l(1,10,if(k!=l)or(-pos(i,j,k),-pos(i,j,l))))));
  k(1,10,
      i(9,I c[9]={};j(9,c[j]=pos(i,j,k));usr_clause(9,c));
      i(9,I c[9]={};j(9,c[j]=pos(j,i,k));usr_clause(9,c));
      i(9,I c[9]={};j(9,c[j]=pos(i/3*3+j%3,i%3*3+j/3,k));usr_clause(9,c)));
  i(9,j(9,if(sudoku[i*9+j])or(pos(i,j,sudoku[i*9+j]))));
  I r=solve();
  pf("s %s\n",r==0?"UNSATISFIABLE":r==1?"SATISFIABLE":"UNKNOWN");
  pf("v ");i(gQ.n,printf("%d ",L2I(gQ.ai)));
  pf("\n\n");

  I answer[81]={};
  i(gQ.n,N=L2I(gQ.ai)-1;if(n>=0)answer[n/9]=n%9+1);
  i(9,j(9,pf("%d ",sudoku[i*9+j]));pf("\n")); pf("\n\n");
  i(9,j(9,pf("%d ",answer[i*9+j]));pf("\n"));
  // dump();
}
int main(V){
  I board1[]={ // easy board. 0.014 seconds
    0,0,0,2,6,0,7,0,1,
    6,8,0,0,7,0,0,9,0,
    1,9,0,0,0,4,5,0,0,
    8,2,0,1,0,0,0,4,0,
    0,0,4,6,0,2,9,0,0,
    0,5,0,0,0,3,0,2,8,
    0,0,9,3,0,0,0,7,4,
    0,4,0,0,5,0,0,3,6,
    7,0,3,0,1,8,0,0,0};
  I board2[]={ // hard board. 0.82 seconds (kissat solves in 0.42)
    0,2,0,0,0,0,0,0,0,
    0,0,0,6,0,0,0,0,3,
    0,7,4,0,8,0,0,0,0,
    0,0,0,0,0,3,0,0,2,
    0,8,0,0,4,0,0,1,0,
    6,0,0,5,0,0,0,0,0,
    0,0,0,0,1,0,7,8,0,
    5,0,0,0,0,9,0,0,0,
    0,0,0,0,0,0,0,4,0};
  solve_sudoku(board1);
  reset();
  solve_sudoku(board1);
}
