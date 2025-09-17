// UI: or, usr_clause, solve, reset, attempts, gQ[0..n]=solution
#define _CRT_SECURE_NO_WARNINGS
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
typedef float F;typedef void V;
typedef int I; typedef unsigned long long u64; 
I _=-1u>>1;
#define _(e...) ({e;}) /* a b=args e=body n=name r=result */
#define i(a,e) _(I $=a;I i=0;W(i<$){e;i++;}$!=i)
#define j(a,e) _(I $=a;I j=0;W(j<$){e;j++;}$!=j)
#define k(a,b,e) _(I $=b;I k=a;W(k<$){e;k++;}$!=k)
#define r(a,e...) _(I r=a;e;r)
#define j_ (*j++)
#define i_ (*i++)
#define A I a
#define N I n
#define ai a[i]
#define aj a[j]
#define ak a[k]
#define ar a[r]
#define aij a[i][j]
#define bi b[i]
#define R return
#define B break;
#define AS assert
#define W(e) while(_(e))
#define AL(a) (I)(sizeof(a)/sizeof*(a))
#define F1(n,e) I n(A){R _(e);}
#define F2(n,e) I n(A,I b){R _(e);}
#define s r(_,scanf("%lld",&r))
#define pf printf
#define swp(a,b) r(a,a=b;b=r)
F2(mn,a<b?a:b) F2(mx,a>b?a:b)
I rng(V){static u64 r=12345;r^=r<<13;r^=r>>7;r^=r<<17;R r&_;}
enum{LITS=0x1000000,CLAUSES=LITS,LIT_MAX=LITS,LITB=LITS/128};
typedef unsigned Lit;
typedef struct{N,mark;Lit*a;}Cl;
typedef struct{I c;Lit bl;}Watcher;
// W[lit]=watchers; L=lit arena; C=clauses; Q=queue[q.head]=lit;
// A[var]assigned,val,seen,heap; Q[Lv[n]]backjmp; V[var]=cause,lvl,activity;
struct{N,a[LITS/2];} gH; // heap p=(i-1)/2 l=i*2+1 r=i*2+2
struct{N,a[LITS/2];} gLv;
struct{N;Lit a[LITS];} gL;
struct{N,cap;Watcher*a;} gW[LIT_MAX];
struct{N,head;Lit a[LITS];} gQ;
struct{N,given,garb;Cl a[CLAUSES];} gC;
struct{N,c[LITS/2],lv[LITS/2];F a[LITS/2];} gV;
struct{u64 a[LITB],v[LITB],sn[LITB],in[LITB];} gA;
struct{I props,qn;}simp;
V reset(V){gLv.n=0;gL.n=0;gQ.n=0;gC.n=0;gV.n=0;gH.n=0;} // TODO: ga gw leaks
I attempts=10000;
#define wv gW[v]
#define cc gC.a[cr]
#define or(a...) _(int r[]={a};usr_clause(AL(r),r));
#define v(n,a) b##n(gA.a,v/2)
#define ANL(b) AS(sizeof(b.a)==sizeof(V*)||b.n<AL(b.a));
#define p(b,v) {ANL(b);b.a[b.n++]=v;}
V bset(u64*a,N){a[n/64]|=1ull<<n%64;} I bget(u64*a,N){R a[n/64]>>n%64&1;}
V bclr(u64*a,N){a[n/64]&=~(1ull<<n%64);}
F1(pLit,a&1?-a/2:a/2) F1(vLit,r(a<0?-a*2|1:a*2,AS(r<LIT_MAX)))
V heap_down(I i){I*a=gH.a;I v=ai;W(i*2+1<gH.n){I j=i*2+1,r=i*2+2;
 I k=r<gH.n&&gV.a[ar]>gV.a[aj]?r:j;ai=ak;i=k;}ai=v;}
I heap_pop(){R gH.n?r(*gH.a,*gH.a=gH.a[--gH.n];bclr(gA.in,r);
 if(gH.n>1)heap_down(0);bclr(gA.in,r))*2:0;}
V heap_put(I v){if(v(get,in))R;v/=2;p(gH,v)I i=gH.n;I k=(i-1)/2;
 W(i&&gV.a[v]>gV.a[gH.ak]){gH.ai=gH.ak;i=k;k=(k-1)/2;}gH.ai=v;bset(gA.in,v);}
V dump(V){ pf("<Heap>\n"); i(gH.n,pf("%d ",gH.ai));pf("\n"); i(gC.n,
 pf("<Clause %d>\n",i); j(gC.ai.n, I v = gC.ai.aj; pf("% d:%c wb:",pLit(v),
 v(get,a)?v(get,v)["+-"]:'?'); k(0,wv.n,pf(" %d|%d",wv.ak.c,pLit(wv.ak.bl)));
 pf("\n"););); k(0,gQ.n,pf("%d=>%d|%d ",gV.c[gQ.ak/2],pLit(gQ.ak),
 gV.lv[gQ.ak/2])); pf("\n----------END DUMP----------\n"); }
Lit*la(A){N=gL.n;gL.n+=a;ANL(gL)R gL.a+n;}
V watch(I cr,Lit v,Lit bl){v^=1;if(wv.n>=wv.cap){wv.cap=mx(8,wv.cap*2);
 wv.a=realloc(wv.a,wv.cap*sizeof(*wv.a));}Watcher w={.c=cr,.bl=bl};p(wv,w)}
V assign(Lit v){AS(!v(get,a));v(set,a);if(v&1)v(set,v);}
I val(Lit v){R v(get,a)&&v(get,v)==v%2;}
Lit deq(){AS(gQ.head<gQ.n);R gQ.a[gQ.head++];}
V enq(Lit v,I cr){assign(v);gV.c[v/2]=cr;gV.lv[v/2]=gLv.n;p(gQ,v)}
I clause(Cl c){ AS(c.n); if(c.n==1){enq(*c.a,_);R _;}
 R r(gC.n,p(gC,c)watch(r,*c.a,c.a[1]);watch(r,c.a[1],*c.a));} // TODO: bad unit
I usr_clause(N,int*a){Cl c={.n=n,.a=la(n)};
 i(n,c.ai=r(vLit(ai),heap_put(r)));R clause(c);}
V cancelUntil(I lv){if(lv>=gLv.n)R;I i;for(i=gQ.n-1;i>=gLv.a[lv];i--)
 {I v=gQ.ai;v(clr,a);v(clr,v);heap_put(v);}gQ.n=gQ.head=i+1; gLv.n=lv;}
I locked(I cr){R val(*cc.a)&&gV.c[*cc.a/2]==cr;}
Lit branch(V){Lit v;do{if(gH.n==0)R 0;v=heap_pop();}W(v(get,a));R v|rng()&1;}
// TODO:
V cbump(I cr){}
V vbump(I v){}
V cdecay(V){}
V vdecay(V){}
V simplify(V){R; //TODO:
 AS(gLv.n==0);
 if(simp.props>0||simp.qn==gQ.n)R; // R 0 if (!ok||prop()!=_)
 I k=0;i(gC.n,I cr=i;
  if(j(cc.n,if(val(cc.aj))B)){
   //removeClause
   // detach(cc);
   if(locked(i))gV.c[*cc.a/2]=_;
   cc.mark=1;gC.garb++;
  }
  else gC.a[k++]=cc;
 ); gC.n=k;
 // gc(); rebuildHeap();
 simp.props=gL.n; simp.qn=gQ.n;
}
I prop(V){W(gQ.head<gQ.n){
 Lit v=deq();if(!wv.a)continue; Watcher*i,*j,*end=wv.a+wv.n;simp.props--;
 for(i=j=wv.a;i!=end;){if(i->c==_){i_;continue;}
  if(val(i->bl)){j_=i_;continue;}I cr=i->c;Lit*a=gC.a[cr].a;
  if(*a==(v^1))swp(*a,a[1]);if(*a!=i_.bl&&val(*a)){j_.bl=*a;continue;}
  if(k(2,gC.a[cr].n,if(!val(ak^1)){swp(a[1],ak);watch(cr,a[1],*a);B}))
   continue;j_.bl=*a;if(val(*a^1)){W(i!=end)j_=i_;wv.n-=i-j;R cr;}
  enq(*a,cr);}wv.n-=i-j;}R _;}
Cl analyze(I cr,I*lv){Cl c={.a=gL.a+gL.n,.n=1};I deps=0,i=gQ.n;Lit v=0;
 do{AS(cr!=_);cbump(cr);AS(!v||v==*cc.a);
  k(!!v,cc.n,Lit v=cc.ak;if(!v(get,sn)&&gV.lv[v/2]){vbump(v/2);v(set,sn);
   if(gV.lv[v/2]<gLv.n){AS(c.n<AL(gL.a)-gL.n);p(c,v)}else deps++;});
  W(v=gQ.a[--i];v(get,sn));v=gQ.ai;cr=gV.c[v/2];v(clr,sn);deps--;
 }W(deps>0);*c.a=v^1;la(c.n);i(c.n,gA.sn[c.ai/128]=0);
 if(c.n==1){*lv=0;R c;}i=1;k(2,c.n,if(gV.lv[c.ak/2]>gV.lv[c.ai/2])i=k);
 *lv=gV.lv[c.ai/2];swp(c.a[1],c.ai);R c;}
I solve(){gC.given=gC.n;i(attempts,I conf=prop(); // P(i);P(conf);dump();
 if(conf!=_){if(gLv.n==0)R 0;N=0;Cl lrn=analyze(conf,&n);cancelUntil(n);
  I cr=clause(lrn);if(lrn.n>1){enq(*lrn.a,cr);cbump(cr);}vdecay();cdecay();
  // something something max_learnts
 }else{if(gLv.n==0)simplify();
  // if(gC.n-gC.given-gQ.n >= max_learnts)reduceDB;
  Lit v=branch();if(!v)R 1;p(gLv,gQ.n)enq(v,_);}
 );cancelUntil(0);R _;}
// wiki cdcl
V t2(V) {
 or(1,4)
 or(1,-3,-8)
 or(1,8,12)
 or(2,11)
 or(-7,-3,9)
 or(-7,8,-9)
 or(7,8,-10)
 or(7,10,-12)
 // 1 2 -7 8 10
 P(solve());dump();
}

// https://www.youtube.com/watch?v=DIcRFQ2xzlA&t=394s
V t1(V) {
 or(-1,2)
 or(-1,-3)
 or(-2)
 or(2,3)
 or(1,2,-3,4)
 or(2,-4)
 P(solve());dump();
}
V t3(V) {
 or(-1,2,3)
 or(1,3,4)
 or(1,3,-4)
 or(1,-3,4)
 or(1,-3,-4)
 or(-2,-3,4)
 or(-1,2,-3)
 or(-1,-2,3)
 P(solve());dump();
}
V t4(V) {
 or(-1,-2,3)
 or(1,-2,3)
 or(-3,4)
 or(-3,-4)
 or(-1,3,4)
 or(-1,2,-4)
 or(2,3,-4)
 or(1,2,4)
 P(solve());dump();
}


int main(V){
 t2();
}
